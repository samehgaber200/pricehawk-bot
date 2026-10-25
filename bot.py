"""Telegram bot + Mini App that tracks Amazon product prices and alerts on drops.

Usage in Telegram:
  open the app from the menu button  -> dashboard (add / target / delete)
  send any Amazon link        -> start tracking it
  /add <link> [target]        -> track, optionally alert only below target price
  /list                       -> tracked items
  /target <id> <price>        -> set/replace target price (0 = any drop)
  /remove <id>                -> stop tracking
  /check                      -> check all your items now
"""
import asyncio
import hashlib
import hmac
import json
import logging
import os
import re
import sqlite3
from datetime import datetime
from pathlib import Path
from urllib.parse import parse_qsl

import requests
from aiohttp import web
from bs4 import BeautifulSoup
from telegram import (InlineKeyboardButton, InlineKeyboardMarkup, MenuButtonWebApp,
                      Update, WebAppInfo)
from telegram.ext import (Application, CommandHandler, ContextTypes,
                          MessageHandler, filters)

BASE = Path(__file__).parent
DB_PATH = BASE / "prices.db"
WEBAPP_DIR = BASE / "webapp"


def load_env():
    env = BASE / ".env"
    if env.exists():
        for line in env.read_text(encoding="utf-8").splitlines():
            if "=" in line and not line.strip().startswith("#"):
                k, v = line.split("=", 1)
                os.environ.setdefault(k.strip(), v.strip())


load_env()
TOKEN = os.environ.get("BOT_TOKEN", "")
CHECK_MINUTES = int(os.environ.get("CHECK_MINUTES", "60"))
# Optional: comma-separated chat ids allowed to use the bot (empty = anyone)
ALLOWED = {int(x) for x in os.environ.get("ALLOWED_CHAT_IDS", "").split(",") if x.strip()}
# Hosting platforms (Render) give the port in PORT and need us on all interfaces
WEB_PORT = int(os.environ.get("PORT") or os.environ.get("WEB_PORT") or 8080)
WEB_HOST = "0.0.0.0" if os.environ.get("PORT") else "127.0.0.1"
# public https url of the mini app (Render provides RENDER_EXTERNAL_URL automatically)
WEBAPP_URL = (os.environ.get("WEBAPP_URL") or os.environ.get("RENDER_EXTERNAL_URL") or "").rstrip("/")
# Postgres connection string (e.g. Neon). Empty = local SQLite file.
DATABASE_URL = os.environ.get("DATABASE_URL", "")
# Only for previewing the app in a normal browser on this PC (no Telegram login there)
DEV_CHAT_ID = int(os.environ.get("DEV_CHAT_ID", "0") or 0)

logging.basicConfig(format="%(asctime)s %(levelname)s %(message)s", level=logging.INFO)
logging.getLogger("httpx").setLevel(logging.WARNING)  # its request lines include the bot token
log = logging.getLogger("pricebot")

# ---------------------------------------------------------------- storage

class _Result:
    def __init__(self, rows, rowcount, lastrowid=None):
        self.rows, self.rowcount, self.lastrowid = rows, rowcount, lastrowid

    def fetchall(self):
        return self.rows

    def fetchone(self):
        return self.rows[0] if self.rows else None


class PgConn:
    """Postgres connection that accepts the same '?' SQL the SQLite code uses."""

    def __init__(self):
        import psycopg
        from psycopg.rows import dict_row
        self.conn = psycopg.connect(DATABASE_URL, row_factory=dict_row)

    def execute(self, sql, args=()):
        sql = sql.replace("?", "%s")
        returning = sql.lstrip().upper().startswith("INSERT INTO ITEMS")
        cur = self.conn.execute(sql + (" RETURNING id" if returning else ""), args)
        rows = cur.fetchall() if cur.description else []
        return _Result(rows, cur.rowcount, rows[0]["id"] if returning else None)

    def __enter__(self):
        return self

    def __exit__(self, exc_type, *_):
        if exc_type:
            self.conn.rollback()
        else:
            self.conn.commit()
        self.conn.close()


def init_pg():
    with PgConn() as conn:
        conn.execute("""CREATE TABLE IF NOT EXISTS items (
            id SERIAL PRIMARY KEY, chat_id BIGINT NOT NULL, url TEXT NOT NULL, title TEXT,
            currency TEXT, last_price DOUBLE PRECISION, lowest_price DOUBLE PRECISION,
            target DOUBLE PRECISION, checked_at TEXT, image TEXT, seller TEXT,
            first_price DOUBLE PRECISION, added_at TEXT, target_on INTEGER DEFAULT 1)""")
        conn.execute("""CREATE TABLE IF NOT EXISTS history (
            item_id INTEGER NOT NULL, price DOUBLE PRECISION, at TEXT NOT NULL)""")
        conn.execute("CREATE INDEX IF NOT EXISTS history_item ON history (item_id)")


def db():
    if DATABASE_URL:
        return PgConn()
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    conn.execute("""CREATE TABLE IF NOT EXISTS items (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        chat_id INTEGER NOT NULL,
        url TEXT NOT NULL,
        title TEXT,
        currency TEXT,
        last_price REAL,
        lowest_price REAL,
        target REAL,
        checked_at TEXT)""")
    conn.execute("""CREATE TABLE IF NOT EXISTS history (
        item_id INTEGER NOT NULL,
        price REAL,
        at TEXT NOT NULL)""")
    cols = {r["name"] for r in conn.execute("PRAGMA table_info(items)")}
    for col, typ in (("image", "TEXT"), ("seller", "TEXT"), ("first_price", "REAL"),
                     ("added_at", "TEXT"), ("target_on", "INTEGER DEFAULT 1")):
        if col not in cols:
            conn.execute(f"ALTER TABLE items ADD COLUMN {col} {typ}")
    return conn


def now():
    return datetime.now().isoformat(timespec="minutes")

# ---------------------------------------------------------------- scraping

HEADERS = {
    "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                   "(KHTML, like Gecko) Chrome/129.0.0.0 Safari/537.36"),
    "Accept-Language": "ar-EG,ar;q=0.9,en-US;q=0.8,en;q=0.7",
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
}
URL_RE = re.compile(r"https?://\S*(amazon\.[a-z.]+|amzn\.[a-z]+|a\.co)/\S*", re.I)
ARABIC_DIGITS = str.maketrans("٠١٢٣٤٥٦٧٨٩٫٬", "0123456789.,")
PRICE_SELECTORS = [
    "#corePrice_feature_div .a-offscreen",
    "#corePriceDisplay_desktop_feature_div .a-offscreen",
    "#apex_desktop .a-price .a-offscreen",
    "#priceblock_dealprice",
    "#priceblock_ourprice",
    "#price_inside_buybox",
    "#newBuyBoxPrice",
    ".a-price .a-offscreen",
]
SELLER_SELECTORS = [
    "#sellerProfileTriggerId",
    "#merchantInfoFeature_feature_div .offer-display-feature-text-message",
    "#merchant-info a",
]


def parse_price(text):
    """'EGP 1,299.00' / '1.299,00 €' / '١٬٢٩٩' -> (1299.0, currency)."""
    text = re.sub(r"[‎‏ ]", " ", text.translate(ARABIC_DIGITS)).strip()
    m = re.search(r"\d[\d.,\s]*", text)
    if not m:
        return None, None
    num = m.group(0).replace(" ", "").rstrip(".,")
    currency = (text[:m.start()] + text[m.end():]).strip() or None
    if "," in num and "." in num:
        dec = "," if num.rfind(",") > num.rfind(".") else "."
        num = num.replace("." if dec == "," else ",", "").replace(dec, ".")
    elif "," in num:
        num = num.replace(",", ".") if re.search(r",\d{2}$", num) else num.replace(",", "")
    try:
        return float(num), currency
    except ValueError:
        return None, None


def clean_url(url):
    """Keep only scheme://host/dp/ASIN so the stored link is short and stable."""
    m = re.search(r"(https?://[^/]+).*?/(?:dp|gp/product|gp/aw/d)/([A-Z0-9]{10})", url)
    return f"{m.group(1)}/dp/{m.group(2)}" if m else url


def fetch_product(url):
    """Returns dict(url, title, price, currency, image, seller)."""
    r = requests.get(url, headers=HEADERS, timeout=25, allow_redirects=True)
    r.raise_for_status()
    soup = BeautifulSoup(r.text, "html.parser")
    if soup.select_one("form[action*='validateCaptcha']"):
        raise RuntimeError("أمازون طلب كابتشا، هحاول تاني بعدين")
    out = {"url": clean_url(r.url), "price": None, "currency": None, "image": None, "seller": None}
    title_el = soup.select_one("#productTitle") or soup.select_one("title")
    out["title"] = title_el.get_text(strip=True)[:200] if title_el else out["url"]
    for sel in PRICE_SELECTORS:
        el = soup.select_one(sel)
        if el and el.get_text(strip=True):
            price, currency = parse_price(el.get_text(" ", strip=True))
            if price:
                out["price"], out["currency"] = price, currency
                break
    img = soup.select_one("#landingImage") or soup.select_one("#imgBlkFront")
    if img:
        out["image"] = img.get("data-old-hires") or img.get("src")
    for sel in SELLER_SELECTORS:
        el = soup.select_one(sel)
        if el and el.get_text(strip=True):
            out["seller"] = el.get_text(strip=True)[:60]
            break
    return out

# ---------------------------------------------------------------- shared logic

def fmt(price, currency):
    return "غير متاح" if price is None else f"{price:,.2f} {currency or ''}".strip()


def allowed_chat(chat_id):
    return not ALLOWED or chat_id in ALLOWED


async def create_item(chat_id, url, target=None):
    p = await asyncio.to_thread(fetch_product, url)
    with db() as conn:
        cur = conn.execute(
            "INSERT INTO items (chat_id,url,title,currency,last_price,lowest_price,target,checked_at,"
            "image,seller,first_price,added_at,target_on) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,1)",
            (chat_id, p["url"], p["title"], p["currency"], p["price"], p["price"], target, now(),
             p["image"], p["seller"], p["price"], now()))
        item_id = cur.lastrowid
        conn.execute("INSERT INTO history VALUES (?,?,?)", (item_id, p["price"], now()))
    return item_id, p


def item_dict(conn, r):
    hist = conn.execute("SELECT price, at FROM history WHERE item_id=? ORDER BY at", (r["id"],)).fetchall()
    prices = [h["price"] for h in hist if h["price"] is not None]
    return {
        "id": r["id"], "url": r["url"], "title": r["title"], "image": r["image"],
        "seller": r["seller"], "currency": r["currency"] or "",
        "price": r["last_price"], "lowest": r["lowest_price"], "first": r["first_price"],
        "average": round(sum(prices) / len(prices), 2) if prices else None,
        "highest": max(prices) if prices else None,
        "target": r["target"], "target_on": bool(r["target_on"]),
        "checked_at": r["checked_at"], "added_at": r["added_at"],
        "history": [{"p": h["price"], "t": h["at"]} for h in hist],
    }

# ---------------------------------------------------------------- bot commands

def app_button():
    if not WEBAPP_URL:
        return None
    return InlineKeyboardMarkup([[InlineKeyboardButton("📊 افتح التطبيق", web_app=WebAppInfo(WEBAPP_URL))]])


async def add_item(update: Update, url, target=None):
    msg = await update.message.reply_text("⏳ بجيب بيانات المنتج...")
    try:
        item_id, p = await create_item(update.effective_chat.id, url, target)
    except Exception as e:
        await msg.edit_text(f"❌ مقدرتش أفتح اللينك: {e}")
        return
    t = (f"\n🎯 هنبهك لما يوصل {fmt(target, p['currency'])} أو أقل" if target
         else "\n🔔 هنبهك مع أي نزول في السعر")
    await msg.edit_text(f"✅ #{item_id} اتضاف للمتابعة\n{p['title']}\n💰 السعر الحالي: "
                        f"{fmt(p['price'], p['currency'])}{t}", reply_markup=app_button())


async def start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        "أهلاً 👋 ابعتلي أي لينك منتج من أمازون وأنا هتابعلك سعره.\n\n"
        "/add <لينك> <سعر مستهدف> — متابعة مع سعر مستهدف\n"
        "/list — المنتجات اللي بتابعها\n"
        "/target <رقم> <سعر> — تغيير السعر المستهدف (0 = أي نزول)\n"
        "/remove <رقم> — إلغاء المتابعة\n"
        "/check — افحص الأسعار دلوقتي\n\n"
        f"بفحص الأسعار كل {CHECK_MINUTES} دقيقة.\nالـ chat id بتاعك: {update.effective_chat.id}",
        reply_markup=app_button())


async def add_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    if not allowed_chat(update.effective_chat.id):
        return
    if not ctx.args:
        await update.message.reply_text("الاستخدام: /add <لينك> [سعر مستهدف]")
        return
    target = parse_price(ctx.args[1])[0] if len(ctx.args) > 1 else None
    await add_item(update, ctx.args[0], target)


async def on_text(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    if not allowed_chat(update.effective_chat.id):
        return
    m = URL_RE.search(update.message.text or "")
    if m:
        await add_item(update, m.group(0))
    else:
        await update.message.reply_text("ابعتلي لينك منتج من أمازون، أو /start للمساعدة.")


async def list_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    if not allowed_chat(update.effective_chat.id):
        return
    with db() as conn:
        rows = conn.execute("SELECT * FROM items WHERE chat_id=? ORDER BY id",
                            (update.effective_chat.id,)).fetchall()
    if not rows:
        await update.message.reply_text("مفيش منتجات بتتابعها لسه.")
        return
    lines = []
    for r in rows:
        line = (f"#{r['id']} {r['title'][:70]}\n   💰 {fmt(r['last_price'], r['currency'])}"
                f" | أقل سعر: {fmt(r['lowest_price'], r['currency'])}")
        if r["target"] and r["target_on"]:
            line += f" | 🎯 {fmt(r['target'], r['currency'])}"
        lines.append(line + f"\n   {r['url']}")
    await update.message.reply_text("\n\n".join(lines), disable_web_page_preview=True)


async def remove_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    if not allowed_chat(update.effective_chat.id):
        return
    if not ctx.args or not ctx.args[0].lstrip("#").isdigit():
        await update.message.reply_text("الاستخدام: /remove <رقم>")
        return
    n = delete_item(update.effective_chat.id, int(ctx.args[0].lstrip("#")))
    await update.message.reply_text("🗑️ اتشال." if n else "مش لاقي الرقم ده.")


def delete_item(chat_id, item_id):
    with db() as conn:
        n = conn.execute("DELETE FROM items WHERE id=? AND chat_id=?", (item_id, chat_id)).rowcount
        if n:
            conn.execute("DELETE FROM history WHERE item_id=?", (item_id,))
    return n


async def target_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    if not allowed_chat(update.effective_chat.id):
        return
    if len(ctx.args) < 2 or not ctx.args[0].lstrip("#").isdigit():
        await update.message.reply_text("الاستخدام: /target <رقم> <سعر>")
        return
    target = parse_price(ctx.args[1])[0] or None
    with db() as conn:
        n = conn.execute("UPDATE items SET target=?, target_on=1 WHERE id=? AND chat_id=?",
                         (target, int(ctx.args[0].lstrip("#")), update.effective_chat.id)).rowcount
    await update.message.reply_text("✅ اتحدث." if n else "مش لاقي الرقم ده.")


async def check_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    if not allowed_chat(update.effective_chat.id):
        return
    await update.message.reply_text("⏳ بفحص الأسعار...")
    changed = await check_prices(ctx.application, chat_id=update.effective_chat.id, report_all=True)
    if not changed:
        await update.message.reply_text("مفيش منتجات للفحص.")

# ---------------------------------------------------------------- price checking

async def check_prices(app, chat_id=None, report_all=False, item_id=None):
    with db() as conn:
        q, args = "SELECT * FROM items WHERE 1=1", []
        if chat_id:
            q, args = q + " AND chat_id=?", args + [chat_id]
        if item_id:
            q, args = q + " AND id=?", args + [item_id]
        rows = conn.execute(q, args).fetchall()
    for r in rows:
        try:
            p = await asyncio.to_thread(fetch_product, r["url"])
        except Exception as e:
            log.warning("check #%s failed: %s", r["id"], e)
            if report_all:
                await app.bot.send_message(r["chat_id"], f"⚠️ #{r['id']} مقدرتش أفحصه دلوقتي: {e}")
            continue
        price, title = p["price"], p["title"]
        currency = p["currency"] or r["currency"]
        old = r["last_price"]
        target = r["target"] if r["target_on"] else None
        dropped = price is not None and old is not None and price < old
        back_in_stock = price is not None and old is None
        hit_target = target and price is not None and price <= target
        should_alert = hit_target or (dropped and not target) or back_in_stock

        if should_alert:
            head = "🎯 وصل للسعر المستهدف!" if hit_target else ("📦 رجع متاح!" if back_in_stock else "📉 السعر نزل!")
            change = f"\nكان: {fmt(old, currency)}" if old is not None else ""
            await app.bot.send_message(
                r["chat_id"],
                f"{head}\n#{r['id']} {title}\n💰 دلوقتي: {fmt(price, currency)}{change}\n{r['url']}",
                reply_markup=app_button())
        elif report_all:
            await app.bot.send_message(r["chat_id"], f"#{r['id']} {title[:60]}\n💰 {fmt(price, currency)}",
                                       disable_web_page_preview=True)

        known = [x for x in (price, r["lowest_price"]) if x is not None]
        with db() as conn:
            conn.execute("UPDATE items SET title=?,currency=?,last_price=?,lowest_price=?,checked_at=?,"
                         "image=COALESCE(?,image),seller=COALESCE(?,seller) WHERE id=?",
                         (title, currency, price, min(known) if known else None, now(),
                          p["image"], p["seller"], r["id"]))
            conn.execute("INSERT INTO history VALUES (?,?,?)", (r["id"], price, now()))
        if len(rows) > 1:
            await asyncio.sleep(5)  # be gentle with Amazon between requests
    return len(rows)


async def scheduled_check(ctx: ContextTypes.DEFAULT_TYPE):
    await check_prices(ctx.application)


async def keep_awake(ctx: ContextTypes.DEFAULT_TYPE):
    """Render's free plan sleeps after 15 min without inbound traffic; ping our own public url."""
    try:
        await asyncio.to_thread(requests.get, f"{WEBAPP_URL}/health", timeout=20)
    except Exception as e:
        log.warning("keep-awake ping failed: %s", e)

# ---------------------------------------------------------------- mini app web server

def chat_from_init_data(init_data):
    """Validate Telegram WebApp initData and return the user's id (= private chat id)."""
    data = dict(parse_qsl(init_data, keep_blank_values=True))
    received = data.pop("hash", "")
    check = "\n".join(f"{k}={v}" for k, v in sorted(data.items()))
    secret = hmac.new(b"WebAppData", TOKEN.encode(), hashlib.sha256).digest()
    if not received or not hmac.compare_digest(
            hmac.new(secret, check.encode(), hashlib.sha256).hexdigest(), received):
        return None
    return json.loads(data.get("user", "{}")).get("id")


@web.middleware
async def auth(request, handler):
    if not request.path.startswith("/api/"):
        return await handler(request)
    chat_id = chat_from_init_data(request.headers.get("X-Init-Data", ""))
    if not chat_id and DEV_CHAT_ID and request.remote in ("127.0.0.1", "::1") \
            and "X-Forwarded-For" not in request.headers:
        chat_id = DEV_CHAT_ID
    if not chat_id or not allowed_chat(chat_id):
        return web.json_response({"error": "unauthorized"}, status=401)
    request["chat_id"] = chat_id
    return await handler(request)


async def api_items(request):
    with db() as conn:
        rows = conn.execute("SELECT * FROM items WHERE chat_id=? ORDER BY id DESC",
                            (request["chat_id"],)).fetchall()
        return web.json_response({"items": [item_dict(conn, r) for r in rows],
                                  "check_minutes": CHECK_MINUTES})


async def api_add(request):
    body = await request.json()
    m = URL_RE.search(body.get("url", ""))
    if not m:
        return web.json_response({"error": "ده مش لينك أمازون"}, status=400)
    target = parse_price(str(body["target"]))[0] if body.get("target") else None
    try:
        item_id, _ = await create_item(request["chat_id"], m.group(0), target)
    except Exception as e:
        return web.json_response({"error": f"مقدرتش أفتح اللينك: {e}"}, status=400)
    with db() as conn:
        return web.json_response(item_dict(conn, conn.execute("SELECT * FROM items WHERE id=?",
                                                               (item_id,)).fetchone()))


async def api_update(request):
    item_id = int(request.match_info["id"])
    body = await request.json()
    sets, args = [], []
    if "target" in body:
        sets.append("target=?")
        args.append(parse_price(str(body["target"]))[0] if body["target"] not in (None, "") else None)
    if "target_on" in body:
        sets.append("target_on=?")
        args.append(1 if body["target_on"] else 0)
    if not sets:
        return web.json_response({"error": "nothing to update"}, status=400)
    with db() as conn:
        n = conn.execute(f"UPDATE items SET {','.join(sets)} WHERE id=? AND chat_id=?",
                         args + [item_id, request["chat_id"]]).rowcount
        if not n:
            return web.json_response({"error": "not found"}, status=404)
        return web.json_response(item_dict(conn, conn.execute("SELECT * FROM items WHERE id=?",
                                                               (item_id,)).fetchone()))


async def api_delete(request):
    n = delete_item(request["chat_id"], int(request.match_info["id"]))
    return web.json_response({"ok": bool(n)}, status=200 if n else 404)


async def api_refresh(request):
    item_id = int(request.match_info["id"])
    await check_prices(request.app["bot_app"], chat_id=request["chat_id"], item_id=item_id)
    with db() as conn:
        r = conn.execute("SELECT * FROM items WHERE id=? AND chat_id=?", (item_id, request["chat_id"])).fetchone()
        if not r:
            return web.json_response({"error": "not found"}, status=404)
        return web.json_response(item_dict(conn, r))


async def index(request):
    return web.FileResponse(WEBAPP_DIR / "index.html", headers={"Cache-Control": "no-cache"})


async def start_web(app: Application):
    webapp = web.Application(middlewares=[auth])
    webapp["bot_app"] = app
    webapp.router.add_get("/", index)
    webapp.router.add_get("/health", lambda r: web.Response(text="ok"))  # keep-alive pings
    webapp.router.add_get("/api/items", api_items)
    webapp.router.add_post("/api/items", api_add)
    webapp.router.add_patch("/api/items/{id}", api_update)
    webapp.router.add_delete("/api/items/{id}", api_delete)
    webapp.router.add_post("/api/items/{id}/refresh", api_refresh)
    runner = web.AppRunner(webapp)
    await runner.setup()
    await web.TCPSite(runner, WEB_HOST, WEB_PORT).start()
    app.bot_data["web_runner"] = runner
    log.info("Mini app on http://%s:%s (public: %s)", WEB_HOST, WEB_PORT, WEBAPP_URL or "none")
    if WEBAPP_URL:
        await app.bot.set_chat_menu_button(menu_button=MenuButtonWebApp("التطبيق", WebAppInfo(WEBAPP_URL)))


async def stop_web(app: Application):
    runner = app.bot_data.get("web_runner")
    if runner:
        await runner.cleanup()


def main():
    if not TOKEN:
        raise SystemExit("حط BOT_TOKEN في ملف .env (شوف .env.example)")
    if DATABASE_URL:
        init_pg()
    else:
        db().close()
    app = (Application.builder().token(TOKEN)
           .post_init(start_web).post_shutdown(stop_web).build())
    app.add_handler(CommandHandler(["start", "help"], start))
    app.add_handler(CommandHandler("add", add_cmd))
    app.add_handler(CommandHandler("list", list_cmd))
    app.add_handler(CommandHandler("remove", remove_cmd))
    app.add_handler(CommandHandler("target", target_cmd))
    app.add_handler(CommandHandler("check", check_cmd))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_text))
    app.job_queue.run_repeating(scheduled_check, interval=CHECK_MINUTES * 60, first=60)
    if os.environ.get("RENDER_EXTERNAL_URL"):
        app.job_queue.run_repeating(keep_awake, interval=10 * 60, first=120)
    log.info("Bot running, checking every %s minutes", CHECK_MINUTES)
    app.run_polling()


if __name__ == "__main__":
    main()
