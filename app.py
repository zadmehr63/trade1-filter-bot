"""
ربات تلگرام «فیلتر چارت» برای گروه و کانال ترید
python-telegram-bot >= 20

این نسخه برای اجرا روی سرویس‌هایی مثل Render آماده شده است (دارای وب‌سرور داخلی).
"""

import html
import logging
import os
import re
import sqlite3
import time
from collections import Counter
from contextlib import contextmanager
from datetime import datetime, timedelta, timezone
from threading import Thread
from flask import Flask

from telegram import InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.constants import ParseMode
from telegram.error import BadRequest, TelegramError
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

logging.basicConfig(
    format="%(asctime)s %(levelname)s %(name)s: %(message)s", level=logging.INFO
)
logger = logging.getLogger("trade-filter-bot")

# ----------------------------------------------------------------------------
# تنظیمات
# ----------------------------------------------------------------------------

FILTERS = [
    {"id": 0, "name": "اسپایک"},
    {"id": 1, "name": "لگ ۳"},
    {"id": 2, "name": "درایو یک روی پاز"},
    {"id": 3, "name": "هم جهت با روند"},
    {"id": 4, "name": "تناسب درایوها"},
    {"id": 5, "name": "فیبو"},
    {"id": 6, "name": "RSI"},
]

COLUMNS = 2
ON_MARK = "✅"
OFF_MARK = "🔴"
SUBMIT_TEXT = "📌 ثبت نهایی"
SKIP_TEXT = "💬 فقط توضیح"

QM_TEXT = "QM"
LIQ_TEXT = "تامین نقدینگی"
BACK_TEXT = "↩️ تغییر نوع"
ALLOW_CHANGE_TYPE = True

LIQ_REASONS_TITLE = "دلیل انتخاب محدوده"
LIQ_REASONS = [
    {"id": 0, "name": "OB"},
    {"id": 1, "name": "FVG"},
    {"id": 2, "name": "QM"},
    {"id": 3, "name": "IFVG"},
    {"id": 4, "name": "BPR"},
    {"id": 5, "name": "Liquidity"},
    {"id": 6, "name": "پرتاب قیمت"},
]
LIQ_ENTRIES_TITLE = "نوع ورود"
LIQ_ENTRIES = [
    {"id": 7, "name": "IFC"},
    {"id": 8, "name": "CISD"},
    {"id": 9, "name": "OB"},
    {"id": 10, "name": "FVG"},
    {"id": 11, "name": "BPR"},
    {"id": 12, "name": "IFVG"},
    {"id": 13, "name": "Liquidity"},
    {"id": 14, "name": "Limit"},
]
LIQ_ITEMS_WORD = "شروط"
SWAP_SIDES = False
SPACER_TEXT = "\u2800"

LIQ_BIT = 1 << 20
UNSET_BIT = 1 << 21
PICK_QM, PICK_LIQ, PICK_BACK = 100, 101, 102

DELETE_ORIGINAL = True

ALLOWED_CHAT_IDS = {
    int(x) for x in os.environ.get("ALLOWED_CHAT_IDS", "").split(",") if x.strip()
}

STATS_ADMIN_IDS = {
    int(x) for x in os.environ.get("STATS_ADMIN_IDS", "").split(",") if x.strip()
}

CAPTION_LIMIT = 1024

DB_PATH = os.environ.get("STATS_DB") or os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "stats.db"
)

TEHRAN = timezone(timedelta(hours=3, minutes=30))

MAX_PEOPLE_SHOWN = 30
MAX_PEOPLE_PRIVATE = 15

# ----------------------------------------------------------------------------
# توابع کمکی
# ----------------------------------------------------------------------------

_FA_DIGITS = str.maketrans("0123456789", "۰۱۲۳۴۵۶۷۸۹")


def fa(n) -> str:
    return str(n).translate(_FA_DIGITS)


def is_on(mask: int, filter_id: int) -> bool:
    return bool((mask >> filter_id) & 1)


def active_groups(mask: int):
    if mask & LIQ_BIT:
        return [(LIQ_REASONS_TITLE, LIQ_REASONS), (LIQ_ENTRIES_TITLE, LIQ_ENTRIES)]
    return [(None, FILTERS)]


def active_filters(mask: int):
    return [f for _, group in active_groups(mask) for f in group]


def count_positives(mask: int) -> int:
    return sum(1 for f in active_filters(mask) if is_on(mask, f["id"]))


def apply_toggle(mask: int, fid: int):
    unset = bool(mask & UNSET_BIT)
    if fid == PICK_QM:
        return 0 if unset else None
    if fid == PICK_LIQ:
        return LIQ_BIT if unset else None
    if fid == PICK_BACK:
        return None if unset else UNSET_BIT
    if unset or fid not in {f["id"] for f in active_filters(mask)}:
        return None
    return mask ^ (1 << fid)


def build_keyboard(owner_id: int, mask: int) -> InlineKeyboardMarkup:
    def filter_button(f):
        mark = ON_MARK if is_on(mask, f["id"]) else OFF_MARK
        return InlineKeyboardButton(
            f"{mark} {f['name']}",
            callback_data=f"t|{owner_id}|{mask}|{f['id']}",
        )

    skip_button = InlineKeyboardButton(SKIP_TEXT, callback_data=f"sk|{owner_id}|{mask}")

    if mask & UNSET_BIT:
        return InlineKeyboardMarkup(
            [
                [
                    InlineKeyboardButton(QM_TEXT, callback_data=f"t|{owner_id}|{mask}|{PICK_QM}"),
                    InlineKeyboardButton(LIQ_TEXT, callback_data=f"t|{owner_id}|{mask}|{PICK_LIQ}"),
                ],
                [skip_button],
            ]
        )

    if mask & LIQ_BIT:
        (title_a, group_a), (title_b, group_b) = active_groups(mask)
        if SWAP_SIDES:
            (title_a, group_a), (title_b, group_b) = (title_b, group_b), (title_a, group_a)
        spacer = InlineKeyboardButton(SPACER_TEXT, callback_data="nop")
        rows = [
            [
                InlineKeyboardButton(title_a, callback_data="nop"),
                InlineKeyboardButton(title_b, callback_data="nop"),
            ]
        ]
        for k in range(max(len(group_a), len(group_b))):
            rows.append(
                [
                    filter_button(group_a[k]) if k < len(group_a) else spacer,
                    filter_button(group_b[k]) if k < len(group_b) else spacer,
                ]
            )
    else:
        buttons = [filter_button(f) for f in FILTERS]
        rows = [buttons[i : i + COLUMNS] for i in range(0, len(buttons), COLUMNS)]

    rows.append(
        [InlineKeyboardButton(SUBMIT_TEXT, callback_data=f"ok|{owner_id}|{mask}"), skip_button]
    )
    if ALLOW_CHANGE_TYPE:
        rows.append(
            [InlineKeyboardButton(BACK_TEXT, callback_data=f"t|{owner_id}|{mask}|{PICK_BACK}")]
        )
    return InlineKeyboardMarkup(rows)


def build_summary(mask: int) -> str:
    liq = bool(mask & LIQ_BIT)
    kind_text = LIQ_TEXT if liq else QM_TEXT

    lines = [f"📌 نوع: <b>{html.escape(kind_text)}</b>", ""]

    for title, group in active_groups(mask):
        positives = [f["name"] for f in group if is_on(mask, f["id"])]

        if title:
            lines.append(f"▫️ <b>{html.escape(title)}</b>")

        if liq:
            # در تامین نقدینگی فقط گزینه‌های انتخاب‌شده نمایش داده می‌شوند
            if positives:
                for name in positives:
                    lines.append(f"• {html.escape(name)}")
            else:
                lines.append("• —")
            lines.append("")
        else:
            # در QM هم مثبت و هم منفی + تعداد نمایش داده می‌شود
            negatives = [f["name"] for f in group if not is_on(mask, f["id"])]
            pos_head = "✅ فیلترهای مثبت:"
            neg_head = "❌ فیلترهای منفی:"

            lines.append(pos_head)
            lines += [f"• {html.escape(n)}" for n in positives] or ["• —"]
            lines.append("")
            lines.append(neg_head)
            lines += [f"• {html.escape(n)}" for n in negatives] or ["• —"]
            lines.append("")
            lines.append(f"تعداد فیلترهای مثبت: {fa(len(positives))} از {fa(len(group))}")
            lines.append("")

    return "\n".join(lines).rstrip()


PERSIAN_MONTHS = [
    "فروردین", "اردیبهشت", "خرداد", "تیر", "مرداد", "شهریور",
    "مهر", "آبان", "آذر", "دی", "بهمن", "اسفند",
]


def gregorian_to_jalali(gy: int, gm: int, gd: int):
    g_d_m = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]
    if gy > 1600:
        jy = 979
        gy -= 1600
    else:
        jy = 0
        gy -= 621
    gy2 = gy + 1 if gm > 2 else gy
    days = (
        (365 * gy)
        + ((gy2 + 3) // 4)
        - ((gy2 + 99) // 100)
        + ((gy2 + 399) // 400)
        - 80
        + gd
        + g_d_m[gm - 1]
    )
    jy += 33 * (days // 12053)
    days %= 12053
    jy += 4 * (days // 1461)
    days %= 1461
    if days > 365:
        jy += (days - 1) // 365
        days = (days - 1) % 365
    if days < 186:
        jm = 1 + days // 31
        jd = 1 + days % 31
    else:
        jm = 7 + (days - 186) // 30
        jd = 1 + (days - 186) % 30
    return jy, jm, jd


def jalali_str(dt: datetime) -> str:
    jy, jm, jd = gregorian_to_jalali(dt.year, dt.month, dt.day)
    return fa(f"{jy}/{jm:02d}/{jd:02d}")


def period_start(period: str, now: datetime) -> datetime:
    today = now.replace(hour=0, minute=0, second=0, microsecond=0)
    if period == "day":
        return today
    if period == "week":
        return today - timedelta(days=(today.weekday() - 5) % 7)
    _, _, jd = gregorian_to_jalali(today.year, today.month, today.day)
    return today - timedelta(days=jd - 1)

# ----------------------------------------------------------------------------
# پایگاه‌داده‌ی آمار
# ----------------------------------------------------------------------------

@contextmanager
def db_conn():
    conn = sqlite3.connect(DB_PATH)
    try:
        yield conn
        conn.commit()
    finally:
        conn.close()

def init_db() -> None:
    with db_conn() as db:
        db.execute(
            """CREATE TABLE IF NOT EXISTS charts (
                   chat_id    INTEGER NOT NULL,
                   message_id INTEGER NOT NULL,
                   user_id    INTEGER NOT NULL,
                   user_name  TEXT,
                   status     TEXT NOT NULL,
                   positives  INTEGER,
                   done_at    INTEGER NOT NULL,
                   chat_title TEXT,
                   kind       TEXT,
                   PRIMARY KEY (chat_id, message_id)
               )"""
        )
        cols = [r[1] for r in db.execute("PRAGMA table_info(charts)")]
        if "chat_title" not in cols:
            db.execute("ALTER TABLE charts ADD COLUMN chat_title TEXT")
        if "kind" not in cols:
            db.execute("ALTER TABLE charts ADD COLUMN kind TEXT")
        db.execute(
            "CREATE INDEX IF NOT EXISTS idx_charts_done ON charts (chat_id, status, done_at)"
        )

def record_result(
    chat_id, message_id, user_id, user_name, status, positives=None, chat_title=None, kind=None
) -> None:
    try:
        with db_conn() as db:
            db.execute(
                "INSERT OR REPLACE INTO charts "
                "(chat_id, message_id, user_id, user_name, status, positives, done_at, chat_title, kind) "
                "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
                (chat_id, message_id, user_id, user_name, status, positives,
                 int(time.time()), chat_title, kind),
            )
    except sqlite3.Error:
        logger.exception("ذخیره‌ی آمار ناموفق بود")

PERIOD_TITLES = {"day": "روزانه", "week": "هفتگی", "month": "ماهانه"}
_MEDALS = ["🥇", "🥈", "🥉"]
STATS_NOTE = "چارت‌هایی که «فقط توضیح» شده‌اند شمرده نمی‌شوند."

def _period_info(period: str):
    now = datetime.now(TEHRAN)
    start = period_start(period, now)
    if period == "day":
        label = f"امروز ({jalali_str(now)})"
    elif period == "week":
        label = f"این هفته (از شنبه {jalali_str(start)})"
    else:
        jy, jm, _ = gregorian_to_jalali(start.year, start.month, start.day)
        label = f"این ماه ({PERSIAN_MONTHS[jm - 1]} {fa(jy)})"
    return int(start.timestamp()), label

def _people_lines(db, chat_id: int, start_ts: int, max_people: int):
    rows = db.execute(
        "SELECT user_id, user_name FROM charts "
        "WHERE chat_id = ? AND status = 'final' AND done_at >= ? "
        "ORDER BY done_at",
        (chat_id, start_ts),
    ).fetchall()

    counts: Counter = Counter()
    names = {}
    for uid, name in rows:
        counts[uid] += 1
        names[uid] = name

    total = sum(counts.values())
    lines = [f"✅ چارت‌های ثبت نهایی‌شده: <b>{fa(total)}</b>"]
    if total:
        lines += ["", "👥 سهم هر فرد:"]
        ranked = counts.most_common()
        for i, (uid, c) in enumerate(ranked[:max_people]):
            rank = _MEDALS[i] if i < len(_MEDALS) else f"{fa(i + 1)}."
            name = html.escape(names.get(uid) or "بدون‌نام")
            pct = round(c * 100 / total)
            lines.append(f"{rank} {name} — {fa(c)} چارت ({fa(pct)}٪)")
        rest = ranked[max_people:]
        if rest:
            lines.append(f"و {fa(len(rest))} نفر دیگر ({fa(sum(c for _, c in rest))} چارت)")
    return total, lines

def build_stats_text(chat_id: int, period: str) -> str:
    start_ts, label = _period_info(period)
    with db_conn() as db:
        total, lines = _people_lines(db, chat_id, start_ts, MAX_PEOPLE_SHOWN)
    out = [f"📊 <b>آمار {PERIOD_TITLES[period]}</b>", label, ""] + lines
    if not total:
        out += ["", "هنوز چارتی ثبت نهایی نشده است."]
    out += ["", STATS_NOTE]
    return "\n".join(out)

def build_stats_text_all(period: str) -> str:
    start_ts, label = _period_info(period)
    out = [f"📊 <b>آمار {PERIOD_TITLES[period]}</b> (همه‌ی گروه‌ها و کانال‌ها)", label]
    with db_conn() as db:
        chats = db.execute(
            "SELECT chat_id, MAX(chat_title) FROM charts "
            "WHERE status = 'final' AND done_at >= ? "
            "GROUP BY chat_id ORDER BY COUNT(*) DESC",
            (start_ts,),
        ).fetchall()
        if not chats:
            out += ["", "هنوز چارتی ثبت نهایی نشده است."]
        for chat_id, title in chats:
            _, lines = _people_lines(db, chat_id, start_ts, MAX_PEOPLE_PRIVATE)
            out += ["", f"━━ <b>{html.escape(title or str(chat_id))}</b> ━━"] + lines
    out += ["", STATS_NOTE]
    text = "\n".join(out)
    if len(text) > 4000:
        text = text[: text.rfind("\n", 0, 3990)] + "\n…"
    return text

def stats_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [[
            InlineKeyboardButton("📅 روزانه", callback_data="st|day"),
            InlineKeyboardButton("🗓 هفتگی", callback_data="st|week"),
            InlineKeyboardButton("📆 ماهانه", callback_data="st|month"),
        ]]
    )

def header_for(user) -> str:
    return f"👤 <b>{html.escape(user.full_name)}</b>"

async def is_chat_admin(context: ContextTypes.DEFAULT_TYPE, chat_id: int, user_id: int) -> bool:
    try:
        member = await context.bot.get_chat_member(chat_id, user_id)
    except TelegramError:
        logger.exception("بررسی ادمین بودن ناموفق بود")
        return False
    return member.status in ("administrator", "creator")

# ----------------------------------------------------------------------------
# هندلرهای چارت
# ----------------------------------------------------------------------------

async def on_chart(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg = update.effective_message
    is_channel = update.channel_post is not None

    if is_channel:
        owner_id = 0
        sig = getattr(msg, "author_signature", None)
        header = f"✍️ <b>{html.escape(sig)}</b>" if sig else ""
    else:
        user = msg.from_user
        if user is None or msg.sender_chat is not None:
            return
        owner_id = user.id
        header = header_for(user)

    if ALLOWED_CHAT_IDS and msg.chat_id not in ALLOWED_CHAT_IDS:
        return

    caption = header
    if msg.caption:
        caption = f"{header}\n{msg.caption_html}" if header else msg.caption_html
    if len(caption) > CAPTION_LIMIT:
        caption = header

    kwargs = dict(
        chat_id=msg.chat_id,
        caption=caption or None,
        parse_mode=ParseMode.HTML,
        reply_markup=build_keyboard(owner_id, UNSET_BIT),
        message_thread_id=msg.message_thread_id if msg.is_topic_message else None,
    )
    try:
        if msg.photo:
            await context.bot.send_photo(photo=msg.photo[-1].file_id, **kwargs)
        else:
            await context.bot.send_document(document=msg.document.file_id, **kwargs)
    except TelegramError:
        logger.exception("ارسال مجدد چارت ناموفق بود")
        return

    if DELETE_ORIGINAL:
        try:
            await msg.delete()
        except TelegramError:
            logger.warning(
                "حذف پیام اصلی ممکن نشد. ربات را ادمین کنید و مجوز Delete messages بدهید."
            )

async def on_button(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    parts = (query.data or "").split("|")
    try:
        action, owner_id, mask = parts[0], int(parts[1]), int(parts[2])
    except (IndexError, ValueError):
        await query.answer()
        return

    user = query.from_user
    chat = query.message.chat
    claimed = False

    if owner_id == 0:
        if not await is_chat_admin(context, chat.id, user.id):
            await query.answer(
                "فقط ادمین‌ها می‌توانند این دکمه‌ها را بزنند.", show_alert=True
            )
            return
        owner_id = user.id
        claimed = True
    elif user.id != owner_id:
        await query.answer(
            "فقط صاحب این چارت می‌تواند این دکمه‌ها را تغییر دهد.", show_alert=True
        )
        return

    if action == "t":
        try:
            new_mask = apply_toggle(mask, int(parts[3]))
        except (IndexError, ValueError):
            new_mask = None
        if new_mask is None:
            await query.answer()
            return
        try:
            await query.edit_message_reply_markup(build_keyboard(owner_id, new_mask))
        except BadRequest as e:
            if "not modified" not in str(e).lower():
                raise
        await query.answer("این چارت به نام شما ثبت شد" if claimed else None)

    elif action == "ok":
        if mask & UNSET_BIT:
            await query.answer(
                f"اول نوع چارت ({QM_TEXT} یا {LIQ_TEXT}) را انتخاب کنید.", show_alert=True
            )
            return
        record_result(
            chat.id, query.message.message_id, owner_id, user.full_name,
            "final", count_positives(mask), chat.title,
            "liq" if mask & LIQ_BIT else "qm",
        )
        tail = build_summary(mask)
        is_channel = chat.type == "channel"
        if is_channel:
            tail += f"\n\n👤 ثبت‌کننده: <b>{html.escape(user.full_name)}</b>"
        base = getattr(query.message, "caption_html", None)
        if not base and not is_channel:
            base = header_for(user)
        caption = f"{base}\n\n{tail}" if base else tail
        if len(caption) > CAPTION_LIMIT:
            caption = tail if is_channel else f"{header_for(user)}\n\n{tail}"
        try:
            await query.edit_message_caption(
                caption=caption, parse_mode=ParseMode.HTML, reply_markup=None
            )
        except BadRequest as e:
            if "not modified" not in str(e).lower():
                raise
        await query.answer("ثبت شد ✅")

    elif action == "sk":
        record_result(
            chat.id, query.message.message_id, owner_id, user.full_name,
            "skipped", None, chat.title,
        )
        try:
            await query.edit_message_reply_markup(reply_markup=None)
        except BadRequest as e:
            if "not modified" not in str(e).lower():
                raise
        await query.answer("به‌صورت توضیح ثبت شد")

# ----------------------------------------------------------------------------
# هندلرهای آمار
# ----------------------------------------------------------------------------

STATS_TEXT_RE = re.compile(r"^\s*آمار(?:\s+(روزانه|هفتگی|ماهانه))?\s*$")
_WORD_TO_PERIOD = {"روزانه": "day", "هفتگی": "week", "ماهانه": "month"}
_CMD_TO_PERIOD = {"daily": "day", "weekly": "week", "monthly": "month"}

def _chat_allowed(chat_id: int) -> bool:
    return not ALLOWED_CHAT_IDS or chat_id in ALLOWED_CHAT_IDS

def _stats_allowed(user) -> bool:
    return not STATS_ADMIN_IDS or (user is not None and user.id in STATS_ADMIN_IDS)

def _private_stats_allowed(user) -> bool:
    return bool(STATS_ADMIN_IDS) and user is not None and user.id in STATS_ADMIN_IDS

async def _send_stats(msg, period) -> None:
    chat = msg.chat
    if chat.type == "private":
        if not STATS_ADMIN_IDS:
            await msg.reply_text(
                "آمار خصوصی غیرفعال است. اول STATS_ADMIN_IDS را تنظیم کنید "
                "(آیدی خودتان را با /myid می‌گیرید)."
            )
            return
        if not _private_stats_allowed(msg.from_user):
            return
    elif not _chat_allowed(msg.chat_id) or not _stats_allowed(msg.from_user):
        return

    if period is None:
        await msg.reply_text("آمار کدام بازه؟", reply_markup=stats_keyboard())
        return
    text = (
        build_stats_text_all(period)
        if chat.type == "private"
        else build_stats_text(msg.chat_id, period)
    )
    await msg.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=stats_keyboard())

async def on_stats_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg = update.effective_message
    cmd = (msg.text or "").split()[0].lstrip("/").split("@")[0].lower()
    await _send_stats(msg, _CMD_TO_PERIOD.get(cmd))

async def on_stats_text(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg = update.effective_message
    m = STATS_TEXT_RE.match(msg.text or "")
    word = m.group(1) if m else None
    await _send_stats(msg, _WORD_TO_PERIOD.get(word))

async def on_stats_button(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    chat = query.message.chat
    private = chat.type == "private"
    allowed = (
        _private_stats_allowed(query.from_user)
        if private
        else _stats_allowed(query.from_user)
    )
    if not allowed:
        await query.answer("فقط مدیر ربات می‌تواند آمار را ببیند.", show_alert=True)
        return
    period = (query.data or "").split("|")[-1]
    if period not in PERIOD_TITLES or (not private and not _chat_allowed(chat.id)):
        await query.answer()
        return
    text = build_stats_text_all(period) if private else build_stats_text(chat.id, period)
    try:
        await query.edit_message_text(
            text, parse_mode=ParseMode.HTML, reply_markup=stats_keyboard()
        )
    except BadRequest as e:
        if "not modified" not in str(e).lower():
            raise
    await query.answer()

async def on_myid(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg = update.effective_message
    if msg.from_user is None or msg.sender_chat is not None:
        await msg.reply_text("برای دیدن آیدی، حالت ناشناس (anonymous) را خاموش کنید.")
        return
    await msg.reply_text(f"آیدی عددی شما: {msg.from_user.id}")

async def on_nop(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await update.callback_query.answer()

async def on_error(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    logger.error("خطا در پردازش آپدیت", exc_info=context.error)

# ----------------------------------------------------------------------------
# اجرای ربات و وب‌سرور (برای Render)
# ----------------------------------------------------------------------------

def run_bot():
    token = os.environ.get("BOT_TOKEN", "").strip()
    if not token:
        logger.error("متغیر محیطی BOT_TOKEN تنظیم نشده است.")
        return

    init_db()
    if STATS_ADMIN_IDS:
        logger.info("آمار فقط برای %d کاربر مجاز است", len(STATS_ADMIN_IDS))
    else:
        logger.warning("STATS_ADMIN_IDS تنظیم نشده؛ آمار گروه برای همه‌ی اعضا باز است.")

    app = Application.builder().token(token).build()
    app.add_handler(CommandHandler("myid", on_myid))
    app.add_handler(CommandHandler(["stats", "daily", "weekly", "monthly"], on_stats_command))
    app.add_handler(
        MessageHandler(
            filters.TEXT
            & ~filters.COMMAND
            & filters.UpdateType.MESSAGE
            & filters.Regex(STATS_TEXT_RE),
            on_stats_text,
        )
    )
    app.add_handler(CallbackQueryHandler(on_stats_button, pattern=r"^st\|"))
    app.add_handler(
        MessageHandler(
            (filters.PHOTO | filters.Document.IMAGE)
            & (filters.UpdateType.MESSAGE | filters.UpdateType.CHANNEL_POST),
            on_chart,
        )
    )
    app.add_handler(CallbackQueryHandler(on_button, pattern=r"^(t|ok|sk)\|"))
    app.add_handler(CallbackQueryHandler(on_nop, pattern=r"^nop$"))
    app.add_error_handler(on_error)

    logger.info("ربات در حال اجراست...")
    app.run_polling(
        allowed_updates=["message", "channel_post", "callback_query"],
        bootstrap_retries=-1,
    )

# تنظیمات وب‌سرور Flask برای Render
web_app = Flask(__name__)

@web_app.route('/')
def health():
    return "Bot is running", 200

if __name__ == "__main__":
    # اجرای ربات در پس‌زمینه
    bot_thread = Thread(target=run_bot)
    bot_thread.start()

    # اجرای وب‌سرور روی پورتی که Render اختصاص می‌دهد
    port = int(os.environ.get("PORT", 8080))
    web_app.run(host="0.0.0.0", port=port)
