# -*- coding: utf-8 -*-
"""
ربات تلگرام «جذبان»  (python-telegram-bot 22.x  +  SQLite)

- توکن و شناسه مالک از متغیرهای محیطی خوانده می‌شوند (BOT_TOKEN, OWNER_ID).
- همه داده‌ها (ادمین‌ها، کدها، جذب‌ها، پورسانت‌ها، کارت‌ها، فیش‌ها، تنظیمات) در SQLite ذخیره می‌شوند.
- ثبت جذب از دو مسیر انجام می‌شود:
    1) پیام‌های Telegram Business (ربات به اکانت کارفرما به‌عنوان Chatbot وصل شود)
    2) پیام مستقیم متقاضی به خود ربات
"""
import asyncio
import contextvars
from telethon import TelegramClient, events
from telethon.sessions import StringSession
from telethon.errors import FloodWaitError
from telethon.tl.types import DocumentAttributeVideo, InputMessagesFilterVideo, InputPeerUser, MessageEntityCustomEmoji
import functools
import gzip
import io
import hashlib
import html
import json
import logging
import os
import random
import re
import shutil
import zlib
import sqlite3
import tempfile
import unicodedata
from types import SimpleNamespace
import threading
import time
from contextlib import contextmanager
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo

from telegram import (LinkPreviewOptions, CopyTextButton, InlineKeyboardButton, InlineKeyboardMarkup, ReplyKeyboardMarkup,
                      ReplyKeyboardRemove, KeyboardButton, InputMediaPhoto, Update)
from telegram.constants import ParseMode
from telegram.error import BadRequest, Forbidden, RetryAfter, TelegramError
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    ExtBot,
    MessageHandler,
    TypeHandler,
    filters,
)

# ----------------------------------------------------------------------------
# تنظیمات محیطی
# ----------------------------------------------------------------------------
BOT_TOKEN = os.environ["BOT_TOKEN"]
API_ID = int(os.environ["API_ID"])
API_HASH = os.environ["API_HASH"]
SESSION_STRING = os.environ["SESSION_STRING"]
OWNER_ID = int(os.environ.get("OWNER_ID", "0") or 0)
DB_PATH = os.environ.get("DB_PATH", "jazban.db")
OWNER_NAME = os.environ.get("OWNER_NAME", "معراج")
CONTACT_URL = os.environ.get("CONTACT_URL", "https://t.me/jazban_work")
COLOR_BUTTONS = os.environ.get("COLOR_BUTTONS", "1") != "0"
TZ = ZoneInfo(os.environ.get("TZ_NAME", "Asia/Tehran"))
PAGE_SIZE = 10
H = ParseMode.HTML

logging.basicConfig(format="%(asctime)s %(levelname)s %(name)s: %(message)s", level=logging.INFO)
log = logging.getLogger("jazban")
START_TS = time.time()

# ----------------------------------------------------------------------------
# متن‌ها
# ----------------------------------------------------------------------------
ADMIN_MENU_TEXT = "چه کاری انجام بدم واست ادمین عزیز؟🤖"
BTN_A_REPORT = "💻 پروفایل و گزارش ⭐️"
BTN_A_COMMENT = "💬 دریافت متن کامنت 💬"
BTN_A_REPLY = "👁️‍🗨️ دریافت متن پاسخگویی 👁️‍🗨️"
BTN_A_VIDEO = "🎬 دریافت ویدیو آموزشی 🎬"
BTN_A_RECORDS = "💰 سوابق پورسانت 💰"
BTN_A_CONTACT = "👨🏻ارتباط با کارفرما👨🏻"
BTN_A_RESTART = "🔄 راه اندازی ربات 🔄"
BTN_GET_REPLY = "📄 دریافت متن آماده 📄"
BTN_BACK = "🔙 بازگشت 🔙"
BTN_MAIN = "🏠 بازگشت به منوی اصلی 🏠"

# متن دکمه‌های کیبورد معمولی (جدا از متن دکمه‌های شیشه‌ای)
RBTN_REPORT = "💻 پروفایل و گزارش ⭐️"
RBTN_COMMENT = "💬 متن کامنت 💬"
RBTN_REPLY = "👁️‍🗨️ متن پاسخگویی 👁️‍🗨️"
RBTN_VIDEO = "🎬 دریافت ویدیو آموزشی 🎬"
RBTN_CONTACT = "👨🏻 ارتباط با کارفرما 👨🏻"
RBTN_RECORDS = "💰سوابق پورسانت💰"
RBTN_RESTART = "🔄 راه\u200cاندازی مجدد 🔄"
RBTN_CLEAN = "🧹 پاکسازی متن\u200cها 🧹"
RBTN_CHEAT = "🃏 تقلب 🃏"
# متن‌های قدیمی هم پذیرفته می‌شوند تا کیبوردِ قبلاً نمایش‌داده‌شده برای کاربران از کار نیفتد.
RBTN_ALIASES = {
    "report": {RBTN_REPORT, BTN_A_REPORT, "📊 گزارش فعالیت من 📊", "💻 پروفایل و Level من ⭐️", "💻پروفایل و Level من⭐️"},
    "comment": {RBTN_COMMENT, BTN_A_COMMENT},
    "reply": {RBTN_REPLY, BTN_A_REPLY},
    "video": {RBTN_VIDEO, BTN_A_VIDEO},
    "records": {RBTN_RECORDS, BTN_A_RECORDS},
    "contact": {RBTN_CONTACT, BTN_A_CONTACT},
    "restart": {RBTN_RESTART, BTN_A_RESTART},  # متن قدیمی هم کار میکنه
    "clean": {RBTN_CLEAN},
    "cheat": {RBTN_CHEAT},
}
# پیام حامل کیبورد بعد از آموزش: تلگرام بدون پیام امکان نمایش کیبورد را نمی‌دهد؛ این کاراکتر نامرئی است.
KB_CARRIER_TEXT = "\u2800"
KB_CARRIER_CANDIDATES = ["\u2800", "\u3164", "\u2063", "."]  # آخری فقط آخرین راه نجات است

RLM_C = "\u200f"


def rl(text: str) -> str:
    """راست‌چین کردن همه‌ی خطوط: یک RLM اول هر خط غیرخالی (خط‌هایی مثل ➖➖➖ یا 「85」 بدون این، چپ‌چین می‌شن)."""
    return "\n".join((RLM_C + ln) if (ln.strip() and not ln.startswith(RLM_C)) else ln for ln in text.split("\n"))


# ---------- سطح‌بندی ادمین‌ها ----------
LEVEL_MAX = 3
LEVEL_NAMES = {1: "ادمین تک‌ستاره ⭐️", 2: "ادمین دوستاره ⭐️⭐️", 3: "ادمین سه‌ستاره ⭐️⭐️⭐️"}
LEVEL_WORDS = {1: "اول", 2: "دوم", 3: "سوم"}
LEVEL_AMOUNT_KEYS = {1: "pay_amount", 2: "pay_amount_2", 3: "pay_amount_3"}

TEXT_DEFAULTS = {
    "welcome": rl(
        "<b>سلام دوست خوبم ⭐️💟</b>\n\n"
        "<b>به جمع ادمین‌های مجموعه「جَذبان」</b>\n"
        "خیلی خیلی خوش اومدی!\n\n"
        "امیدوارم همکاری خوبی داشته باشیم 🤝\n"
        "➖➖➖➖➖➖➖➖➖➖\n"
        "<b>🔑 کد اختصاصی شما:</b>「{code}」\n"
        "<b>سطح شما:</b>「 {level} 」\n"
        "<b>درآمد این سطح:</b> هر دوره {income}\n"
        "➖➖➖➖➖➖➖➖➖➖\n"
        "برای شروع همکاری، <b>روی دکمه زیر بزن</b>🔻"
    ),
    "video_caption": (
        "<b>این ویدیو آموزشی</b>\n"
        "<b>صفر تا صد کار ما رو بهت آموزش میده!</b>\n"
        "پس حتما ببینش دوست خوبم\n\n"
        "اگه ام قبلا این ویدیو رو از کارفرما دریافت کردی\n"
        "یا الان کامل تماشاش کردی:\n"
        "روی دکمه «ویدیو رو دیدم» بزن🔻"
    ),
    "congrats": (
        "<b>🎉 تبریک دوست خوبم!</b>\n\n"
        "{target} جذب شما با موفقیت تکمیل شد و پورسانت این دوره به مبلغ {amount} برات ثبت شد!\n\n"
        "📩 بعد از واریز پورسانت، فیش واریزی برات همینجا ارسال میشه و میتونی "
        "سوابق پورسانتت رو هم از بخش «سوابق پورسانت» مشاهده کنی..."
    ),
    "req_success": (
        "✅ درخواست شما با موفقیت ثبت شد ✅\n\n"
        "ادمین گرامی پورسانت شما حداکثر تا یک ساعت آینده براتون واریز، و فیش واریزی همینجا براتون ارسال خواهد شد...\n\n"
        "از همکاری و اعتماد شما متشکریم 🫶"
    ),
}
TEXT_TITLES = {
    "welcome": "پیام خوشامدگویی",
    "video_caption": "متن همراه ویدیو",
    "congrats": "پیام تکمیل دوره",
    "req_success": "پیام ثبت درخواست پورسانت",
}
TEXT_REQUIRED = {"welcome": ["{code}"], "congrats": [], "video_caption": [], "req_success": []}
TEXT_HTML_KEYS = ("welcome", "video_caption", "congrats")  # این متن‌ها با فرمت (بولد و ...) ذخیره و ارسال میشن
TEXT_PLACEHOLDERS = {
    "welcome": "{code} و {level} و {income}",
    "video_caption": "「بدون متغیر」",
    "congrats": "{target} و {amount}",
    "req_success": "{deadline}",
}

STEP1_TEXT = (

    "<b>1️⃣- مرحله اول:</b> کامنت‌گذاری 💬\n\n"

    "<b>ادمین عزیز</b>، لطفا ابتدا متن زیر رو کپی کن\n"
    "و بعدش برو زیر <b>استوری</b> و <b>پست‌های</b> افراد معروف مثل <b>بلاگرها</b> و <b>آرتیست‌ها</b> <b>کامنتش کن</b>!\n\n"

    "<b>👇 متن کامنت: 👇</b>"

)

COMMENT_TEXT = (

    "📢 نیازمند اپراتور پاسخگویی\n"

    "درآمد روزانه ۲۰۰ هزار تا ۱.۲ میلیون تومان\n"

    "استخدام کاملاً رایگان\n\n"

    "📩 جهت همکاری دایرکت پیام بدید"

)

STEP2_TEXT = (

    "<b>2️⃣- مرحله دوم:</b> پاسخگویی به مراجعین 👁️‍🗨️\n\n"

    "بعد از اینکه کامنت گذاشتی، مراجعین به دایرکت شما پیام میدن و درباره کار سوال میپرسن.\n\n"

    "و شما فقط متن آماده زیر رو براشون میفرستی👇"

)
REPLY_TEXT = (

    "سلام دوست خوبم ❤️\n\n"

    "این کار شرایط پیچیده‌ای نداره و فقط به چند ساعت زمان آزاد در روز برای پاسخگویی به مراجعین داخل پلتفرم‌ها نیاز داره؛ دقیقاً مثل کاری که خودم انجام می‌دم.\n\n"

    "💰 درآمد روزانه: ۲۰۰ هزار تا ۱ میلیون و ۲۰۰ هزار تومان\n"

    "👥 ظرفیت استخدام: ۲۰ نفر\n\n"

    "برای استخدام و دریافت اطلاعات بیشتر، لطفا عدد {code} رو به آیدی تلگرام زیر ارسال کن 👇\n\n"

    "🔹 @jazban_work\n\n"

    "⚠️ توجه کنید اگر عدد بالا رو ارسال نکنید\n"

    "پیام شما پاسخ داده نمی‌شود!!"

)
CARD_PROMPT = (
    "لطفا شماره کارت بانکی خود را ارسال نمایید.\n\n"
    "💢توجه کنید💢\n"
    "در ارسال شماره کارت لطفا دقت کامل رو داشته باشید تا در واریز پورسانت مشکلی پیش نیاد!"
)
NO_RECORDS_TEXT = (
    "❎ هنوز واریز پورسانتی برات ثبت نشده:(\n"
    "به محض اولین واریزی، سوابق واریز اینجا برات ذخیره میشه تا هر وقت خواستی بتونی ببینیش!"
)
CONTACT_MENU_TEXT = "یکی از گزینه‌های زیر رو انتخاب کن 👇"
SUGGEST_TEXT = ("دوست خوبم، اگه پیشنهاد، انتقاد یا ایده\u200cای برای بهتر شدن ربات یا روند کار جذبان داری، "
                "همین\u200cجا برام بفرست. قول میدم\u200c با دقت بررسی کنم و برای بهتر شدن مجموعه ازشون استفاده کنم "
                "\U0001F468\U0001F3FB\u200d\U0001F4BC\u2764\ufe0f")
SUGGEST_THANKS = ("ادمین عزیز، پیشنهادت با موفقیت ثبت شد و به\u200cزودی بررسی می\u200cشه\u2026\n\n"
                  "ممنون بابت وقتی که گذاشتی \u270c\ufe0f\U0001F525")
SEP = "━━━━━━━━━━━━━━"
SEP10 = "➖•" * 10   # جداکننده‌ی سرتیتر صفحه‌های مدیر
CHEAT_NOTICE_CB = "o:cknx"   # دکمه‌ی «🆗» زیر اعلان ارسال تقلب: همون پیام پاک میشه
SEP7 = "➖•" * 7      # جداکننده‌ی قالب فیش واریز پورسانت (سمت کارفرما)


def owner_receipt_caption(a, c) -> str:
    """کپشن فیش واریز پورسانت برای کارفرما؛ همه‌ش کامل بولد (HTML)."""
    return (f"<b>{SEP7}\n💸 واریز پورسانت 💸\n{SEP7}\n"
            f"برای ادمین کد「{a['code']}」\n🔗 {link(a)}\n\n"
            f"📅 تاریخ: {jdate(c['paid_at'])}\n"
            f"🕒 ساعت: {jtime(c['paid_at'])}\n{SEP7}</b>")


def fbox(title, body: str) -> str:
    """قالب استاندارد صفحه‌های مدیر: جداکننده، عنوان (اختیاری)، جداکننده، متن، جداکننده؛ همه‌ش کامل بولد (HTML)."""
    head = f"{SEP10}\n{title}\n" if title else ""
    return f"<b>{head}{SEP10}\n{body}\n{SEP10}</b>"


def fb(text, title=None) -> str:
    """متن ساده‌ی مدیر → همون قالب fbox (➖•➖• + بولد)؛ متن escape میشه و برای متن‌های پویا هم امنه."""
    return fbox(title, html.escape(str(text)))

ERROR_TEXT = "مشکلی پیش اومد؛ دوباره امتحان کن."
BTN_CANCEL = "❌ انصراف ❌"
_ACT_SEP = "➖•" * 8 + "➖"  # خط جداکننده‌ی پیام‌های فعال‌سازی ادمین
FIRST_TEXT = (
    f"{_ACT_SEP}\n"
    "<b>🚀 وقتشه شروع کنی❕</b>\n"
    f"{_ACT_SEP}\n"
    "۱- روی دکمه「💬 متن کامنت 💬」بزن\n"
    "و متن رو زیر پست و استوری بلاگرها کامنت کن\n"
    "۲- وقتی کسی بهت پیام داد\n"
    "دکمه「👁️‍🗨️ متن پاسخگویی 👁️‍🗨️」رو بزن\n"
    "و متن رو براش بفرست\n"
    f"{_ACT_SEP}"
)
NUDGE_TEXT = (
    f"{_ACT_SEP}\n"
    "<b>⏰ هنوز اولین جذبت ثبت نشده❗️</b>\n"
    f"{_ACT_SEP}\n"
    "بیشتر ادمین‌ها اولین جذبشون رو روز اول میزنن چند تا کامنت بذار؛ "
    "هر کی پیام داد متن پاسخگویی رو براش بفرست 🔥\n"
    "اگه هنوز شروع نکردی، بگو کجا گیر کردی 👇\n"
    f"{_ACT_SEP}"
)
NUDGE_WHY = {  # دلیل جذب‌نکردن (زیر پیام «هنوز اولین جذبت ثبت نشده»)
    "t:why1": "🤷 نمی‌دونم کجا کامنت بذارم 🤷",
    "t:why2": "🔇 کسی جواب نمی‌ده 🔇",
    "t:why3": "⏳ وقت ندارم ⏳",
}


NUDGE_THANKS = "ممنون، دلیلت ثبت شد✅"  # بعد از زدن یکی از دکمه‌ها جای کل پیام میاد
NUDGE_THANKS_SECS = 3                   # و بعد از چند ثانیه پاک میشه


def NUDGE_KB():
    _st = {"t:why1": "danger", "t:why2": "primary", "t:why3": "success"}
    return KB(*[B(txt, cb, style=_st[cb]) for cb, txt in NUDGE_WHY.items()])

def _tut_nudge(where: str, btn: str) -> str:
    return (f"{_ACT_SEP}\n"
            "<b>⏳ آموزشت نیمه‌کاره موند❕</b>\n"
            f"{_ACT_SEP}\n"
            "فقط چند دقیقه تا فعال شدن پنلت مونده...🏁\n"
            f"👆 به پیام {where} برگرد 👆\n"
            f"و روی دکمه「{btn}」بزن\n"
            f"{_ACT_SEP}")


TUT_NUDGE_WELCOME = _tut_nudge("خوشامد", "🔷 شروع همکاری 🔷")  # فقط پیام خوشامد رو دیده
TUT_NUDGE_VIDEO = _tut_nudge("آموزش", "🎬 ویدیو رو دیدم 🎬")   # ویدیو رو گرفته ولی دکمه‌ش رو نزده
TUT_NUDGE_STEP1 = _tut_nudge("آموزش", "➡️ مرحله بعد ➡️")       # متن کامنت رو دیده
TUT_NUDGE_STEP2 = _tut_nudge("آموزش", BTN_GET_REPLY)           # به مرحله‌ی ۲ رسیده (و حالت‌های نزدیک آخر)


def tut_nudge_text(uid: int) -> str:
    """متن یادآوری بر اساس اینکه ادمین آموزش رو تا کجا رفته (از روی پیام‌های ردیابی‌شده‌ی آموزش)."""
    kinds = {r["kind"] for r in qa("SELECT kind FROM tracked WHERE user_id=?", (uid,))}
    if kinds & {"tut2", "reply", "adphoto"}:
        return TUT_NUDGE_STEP2
    if kinds & {"tut1", "comment"}:
        return TUT_NUDGE_STEP1
    if "video" in kinds:
        return TUT_NUDGE_VIDEO
    return TUT_NUDGE_WELCOME
COMEBACK_AFTER = 86400             # پیام «هنوز دیر نشده»: ۱ روز بعد از حذف خودکار (یک بار)
COMEBACK_HOLD = 2 * 86400          # این پیام تا ۲ روز از پاکسازی خودکار در امانه تا دکمه‌ش بمونه
COMEBACK_CB = "t:again"
COMEBACK_BTN = "✌️شروع دوباره 💪"
COMEBACK_TEXT = (
    f"{_ACT_SEP}\n"
    "<b>🔄 هنوز دیر نشده❕</b>\n"
    f"{_ACT_SEP}\n"
    "حسابت حذف شد ولی می‌تونی دوباره شروع کنی\n"
    "آموزش فقط چند دقیقه طول می‌کشه... 🏁\n"
    "بیا یکم پول دراریم رفیق🦾\n\n"
    "👇 دکمه‌ی زیر رو بزن شروع کنیم👇\n"
    f"{_ACT_SEP}"
)
WELCOME_BACK_TEXT = (
    f"{_ACT_SEP}\n"
    "<b>👋 خوش برگشتی رفیق❕</b>\n"
    f"{_ACT_SEP}\n"
    "این بار از اول شروع می‌کنیم...\n"
    "آموزشت رو تکمیل کن تا پنل جدیدت آماده بشه!\n"
    "🚀🚀 🚀\n"
    f"{_ACT_SEP}"
)
WARN_TEXT = (
    f"{_ACT_SEP}\n"
    "<b>🚨 اخطار حذف حساب ادمینی ⚠️</b>\n"
    f"{_ACT_SEP}\n\n"
    "همکار گرامی،\n"
    "شما هنوز اولین جذبتون رو ثبت نکردید!\n\n"
    "به دلیل محدودیت ظرفیت پنل‌ها و استقبال افراد جدید، حساب ادمین‌هایی که فعالیتی نداشته باشن حذف می‌شه "
    "تا ظرفیت به افراد فعال اختصاص پیدا کنه.\n\n"
    "⏳ فقط ۲۴ ساعت فرصت دارید تا اولین جذبتون رو ثبت کنید و از حذف حسابتون جلوگیری کنید.\n\n"
    "🃏 برای جذب بیشتر می‌تونید از روش‌های متنوع بخش «تقلب‌ها» استفاده کنید.\n\n"
    "فرصتتون رو از دست ندید! 🚀\n"
    f"{_ACT_SEP}"
)
STALL_TEXT = (
    f"{_ACT_SEP}\n"
    "<b>💰 {left} جذب دیگه تا پورسانت!</b>\n"
    f"{_ACT_SEP}\n"
    "تا الان「{period} جذب」داری از「{target} جذب」\n"
    "دوباره چند تا کامنت بذار و به کسایی که پیام میدن متن پاسخگویی رو بفرست 🎯\n"
    f"{_ACT_SEP}"
)
REMOVED_TEXT = (
    "❌ حساب ادمینی شما حذف شد ❌\n\n"
    "چون توی مهلت مشخص هیچ جذبی ثبت نشد، حساب ادمینیت حذف شد\n\n"
    "اگه خواستی دوباره شروع کنی\n"
    "🔻 دستور /start رو بزن 🔻"
)

# منوی اصلی کارفرما (کیبورد معمولی)؛ ترتیب و رنگ‌ها در owner_reply_menu_kb
ORBTN_REPORT = "📊 گزارش جذب 📊"
ORBTN_FIN = "💰 مدیریت مالی 💰"
ORBTN_BC = "📢 پیام همگانی 📢"
ORBTN_SEARCH = "🔎جستجوی ادمین🔎"
ORBTN_SET = "🕹️ تنظیمات 🕹️"
ORBTN_GO = "🚀 راه‌اندازی 🚀"
ORBTN_CLEAN = RBTN_CLEAN  # همون دکمه‌ی پاکسازیِ پنل ادمین
OWNER_KB_MAP = {
    ORBTN_REPORT: "o:rep:top:0",
    ORBTN_FIN: "o:fin",
    ORBTN_BC: "o:bc",
    ORBTN_SEARCH: "o:sr",
    ORBTN_SET: "o:set",
    ORBTN_GO: "o:go",
    ORBTN_CLEAN: "o:clm",
}
OWNER_KB_MAP["🔎 جستوجوی ادمین 🔎"] = "o:sr"  # متن قدیمی هم کار میکنه
OWNER_KB_MAP["🔎 جستجوی ادمین 🔎"] = "o:sr"  # با فاصله هم کار میکنه
OWNER_KB_MAP["⚙️ تنظیمات ⚙️"] = "o:set"  # دکمه‌ی قدیمیِ کیبورد تا وقتی عوض نشده هم کار میکنه

STRAY_TTL = 600            # پیام‌های متفرقه کاربر بعد از ۱۰ دقیقه پاک میشن
MENU_GAP = 600             # منوی اصلی کارفرما حداکثر هر ۱۰ دقیقه یک بار
KB_GAP = 3                 # منوی اصلی ادمین (با کیبورد) بعد از پیام متفرقه: فقط ضداسپم ۳ ثانیه‌ای
THROTTLE_SECS = 2.0        # فاصله بین زدن پشت‌سرهم یک دکمه
STATE_TTL = 1800           # وضعیت موقت ثبت کارت بعد از ۳۰ دقیقه
CMD_DELETE_DELAY = 30         # پیام دستور کاربر، ۳۰ ثانیه بعد از پاک شدن منو پاک میشه
BACKUP_BIG = 19 * 1024 * 1024    # بالاتر از این حجم: فشرده‌سازی و تأیید محتوا
BACKUP_SPLIT = 45 * 1024 * 1024  # سقف امن آپلود Bot API؛ بزرگ‌تر از این تکه‌تکه میشه
PANEL_ACTIVE_TEXT = "<b>\U0001F468\U0001F3FB\u200d\U0001F4BBپنل ادمینی شما با موفقیت فعال شد\U0001F469\U0001F3FB\u200d\U0001F4BB</b>"
INACTIVE_NO_CARD = 8 * 86400   # ادمین بدون جذب: هشدار ۷ روز بعد از پایان آموزش، حذف ۱ روز بعدش (۸ روز)
INACTIVE_CARD = 8 * 86400      # ادمین بدون جذب ولی با کارت ثبت‌شده: مثل بدون‌کارت (هشدار ۷ روز، حذف ۸ روز)
WARN_BEFORE = 86400            # هشدار یک روز قبل از حذف
NUDGE_AFTER = 86400            # پیام تشویق ۲۴ ساعت بعد از پایان آموزش (فقط یک بار)
TUT_NUDGE_AFTER = 1800         # یادآوریِ آموزش نیمه‌کاره: ۳۰ دقیقه بعد از /start (فقط ادمینی که آموزشش تموم نشده، فقط یک بار)
FIRST_AFTER = 900              # پیام راهنمای شروع: ۱۵ دقیقه بعد از پایان آموزش (فقط ادمین بدون جذب، فقط یک بار)
STALL_AFTER = 2 * 86400        # ادمینی که جذب داشته ولی دوره‌ش تموم نشده و ۲ روز جذب نکرده
STALL_EVERY = 7 * 86400        # یادآوریِ «جذب دیگه تا پورسانت»: حداکثر هفته‌ای یک بار برای هر ادمین
STALL_HOURS = (9, 23)          # فقط بین این ساعت‌ها (وقت تهران) فرستاده میشه

AUTO_CUT = 100_000  # کم‌شدن پورسانت دوره‌ی اولِ کسی که «بدون ثبت‌نام» رو تأیید کرده

AUTO_REG_HTML = (
    "🌼 دوست خوبم، برای شروع نیازه در سایت زیر <b>ثبت نام و احراز هویت کنید</b>…\n\n"
    "🌷 <b>تنها دلیل ثبت نام شما در طلاسی</b>، استفاده از <b>سیستم پاداش دعوت جهت تامین حقوق ادمین ها از جمله شما</b> "
    "میباشد و جایگزین <b>دریافت هزینه استخدام</b> هست!\n\n"
    "📸 بعد از ثبت نام، لطفا از قسمت: <b>پروفایل</b> اسکرین شات بگیرید و ارسال کنید تا <b>استخدامتون رو نهایی کنم</b>.\n\n"
    "<b>میتونید مشخصات شخصیتون رو بپوشونید!</b>\n\n"
    "‼️ <b>اگر قبلا در طلاسی ثبت نام کردید</b>، <b>لینک رو برای یکی از دوستان یا اعضای خانواده تون</b> "
    "که هنوز ثبت نام نکرده بفرستید تا به جای شما ثبت نام و احراز هویت کنن.\n\n"
    "🔻 <b>لینک ثبت نام:</b>🔻\n\n"
    "talasea.ir/onboarding?r=easVZLOI"
)
AUTO_ALT_HTML = (
    "اگه قبلا خودتون و تمام اطرافیانتون در سایت ثبت نام کردید یا به هر دلیلی امکان ثبت نام در سایت رو ندارید، "
    "اما همچنان مایل به استخدام هستید، می‌تونید <b>بدون نیاز به ثبت نام در سایت</b> استخدام بشید؛ "
    "فقط مبلغ <b>100,000 تومان</b> از اولین حقوقتون کسر میشه.\n\n"
    "اگه با این شرایط موافق هستید، کلمه <b>«تایید شرایط»</b> رو ارسال کنید."
)

DEFAULT_SETTINGS = {
    "auto_9": "0",
    "auto_reg": "0",
    "auto_alt": "0",
    "auto_vid": "0",
    "auto_vid_btn": "1",
    "auto_alive": "0",
    "auto_msgs": "[]",
    "auto_reg_html": AUTO_REG_HTML,
    "auto_alt_html": AUTO_ALT_HTML,
    "auto_vid_html": "",
    "notify_new": "1",
    "notify_done": "1",
    "notify_sus": "1",
    "shield": "0",
    "shield22": "0",
    "shield_l1": "0",
    "shield_l2": "0",
    "shield_l3": "0",
    "owner_go_btn": "1",
    "questions_last_ts": "0",
    "questions_retry_ts": "0",
    "video_enabled": "0",
    "video_file_id": "",
    "video_kind": "video",
    "pay_amount": "200000",
    "pay_amount_2": "250000",
    "pay_amount_3": "300000",
    "bot_off": "0",
    "bot_off_since": "0",
    "weekly_last": "",
    "levels_v1": "",
    "pay_target": "40",
    "deadline_hours": "1",
    "channel_enabled": "0",
    "channel_id": "",
    "channel_title": "",
    "channel_link": "",
    "channel_guide": "",
    "channel_btn": "",
    "last_backup_ts": "0",
    "backup_every": "86400",
    "backup_saved_log": "[]",
    "backup_fail_notice_ts": "0",
    "profile_level_photo_id": "",
    "ad_photo_id": "",
    "activity_photo_id": "",
    "lvl2_blur_photo_id": "",
    "lvl2_photo_id": "",
    "lvl2_amount_photo_id": "",
    "lvl3_blur_photo_id": "",
    "lvl3_photo_id": "",
    "lvl3_amount_photo_id": "",
    "ac_on": "1",
    "ac_delay": "30",
    "drop_prev": "1",
    "hold_secs": "3600",
    "night_on": "1",
    "night_end": "12",
}

# ----------------------------------------------------------------------------
# ابزارهای متن، عدد و تاریخ
# ----------------------------------------------------------------------------
_FA = str.maketrans("0123456789", "۰۱۲۳۴۵۶۷۸۹")
_AR = str.maketrans("٠١٢٣٤٥٦٧٨٩۰۱۲۳۴۵۶۷۸۹", "01234567890123456789")


def fa(x) -> str:
    """اعداد را فارسی می‌کند."""
    return str(x).translate(_FA)


def normalize(text: str) -> str:
    """ارقام فارسی/عربی -> انگلیسی، حذف اعراب/کشیده/نیم‌فاصله و فاصله‌های اضافه."""
    t = (text or "").translate(_AR)
    t = t.replace("ي", "ی").replace("ك", "ک").replace("ـ", "")
    t = re.sub(r"[\u200c\u200d\u200e\u200f\u202a-\u202e\u2066-\u2069]", " ", t)
    t = re.sub(r"[\u064B-\u065F\u0670]", "", t)
    return re.sub(r"\s+", " ", t).strip()


HIRE_RE = re.compile(r"استخدام\s*(?:کد)?\s*[:：\-]?\s*(\d{2,6})(?!\d)(?!\s*نفر)")


NUM_RE = re.compile(r"(?<!\d)\d{2,6}(?!\d)")

# پیامی که فقط یک عدد باشه (دور و برش فقط فاصله/ایموجی/علامت)
_PURE_RE = re.compile(r"^[\W_]*(\d{2,6})[\W_]*$")
# کلمه‌ی «کد/استخدام/عدد/شماره» قبل از عدد (حداکثر ۲ کلمه فاصله): عدد حتماً کد ادمینه
_HIRE_KW_BEFORE = re.compile(
    r"(?:^|\s)(?:کد|کدم|کدت|کدش|استخدام|عدد|شماره|code)(?:\s+[^\s\d]+){0,2}\s*[:：\-]?\s*$", re.I)
# کلمه‌ای درست قبل از عدد که نشون میده عدد ساعت/سن/سال/مبلغ/بازه‌ست، نه کد
_UNIT_BEFORE = re.compile(
    r"(?:^|\s)(?:ساعت|سن(?:م|ت|ش)?|سال|تاریخ|مبلغ|قیمت|حقوق|درآمد|درامد|روز|ماه|مدل|"
    r"حدود|حدودا|تقریبا|نزدیک|بالای|زیر|از|تا)\s*[:：\-]?\s*$")
# کلمه/نمادی درست بعد از عدد که نشون میده عدد سن/ساعت/مبلغ/تعداده، نه کد
_UNIT_AFTER = re.compile(
    r"^\s*(?:%|٪|\$|€|(?:سال(?:ه|ی|م|مه|گی|ش|ت)?|ساعت(?:ه)?|تومن|تومان|تومنی|تومانی|ریال|هزار|میلیون|"
    r"میلیارد|درصد|نفر(?:ی|ه|ات)?|روز(?:ه)?(?!\s+بخیر)|ماه(?:ه)?|دقیقه|ثانیه|کیلو|گرم|متر|سانت|لیتر|دلار|یورو|"
    r"درجه|امتیاز|نمره|(?:صبح|ظهر|عصر|شب)(?!\s+بخیر))(?!\w))")
_RANGE_AFTER = re.compile(r"\s*(?:تا|الی|–|—|-)\s*\d")
_RANGE_BEFORE = re.compile(r"\d\s*(?:تا|الی|–|—|-)\s*$")
# «سن من ۲۲»، «سن شما حدود ۲۲»
_AGE_WIDE_BEFORE = re.compile(r"(?:^|\s)سن(?:م|ت|ش)?(?:\s+[^\s\d]+){0,2}\s*[:：\-]?\s*$")
_LABEL_NEXT = re.compile(r"\s*[:：\-]?\s*\d")


def _glued_to_number(t: str, s: int, e: int) -> bool:
    """عدد بخشی از ساعت/اعشار/تاریخ/هزارگان باشه (18:30، 3.5، 1,200، 1404/7/20، 10-12)؟"""
    seps = ":.,/٫٬-–"
    if s >= 2 and t[s - 1] in seps and t[s - 2].isdigit():
        return True
    if e + 1 < len(t) and t[e] in seps and t[e + 1].isdigit():
        return True
    return False


def _unit_after_blocks(after: str, strong: bool) -> bool:
    """بعد از عدد واحد (سال/ساعت/تومان/نفر...) هست؟ اگه کنار «کد/استخدام» باشه و اون کلمه برچسب عدد بعدیه
    (مثل «کد ۴۵ ساعت ۱۰»)، به عدد قبلی ربطی نداره."""
    ua = _UNIT_AFTER.match(after)
    if not ua:
        return False
    rest = after[ua.end():]
    if ua.group(0).strip() in ("ساعت", "سال", "روز", "ماه") and _LABEL_NEXT.match(rest):
        return False  # «۲۲ ساعت ۱۸»: ساعت برچسب ۱۸ه، نه واحد ۲۲
    return not (strong and _LABEL_NEXT.match(rest))


def _hire_candidates(t: str) -> list:
    """عددهای واجد شرایط کد بودن، به ترتیب: اول اونایی که کنار «کد/استخدام/عدد/شماره» اومدن، بعد بقیه."""
    pure = _PURE_RE.match(t)
    if pure and not re.search(r"[%٪$€°]", t):  # پیام فقط یک عدده
        return [int(pure.group(1))]
    strong, weak = [], []
    for m in NUM_RE.finditer(t):
        s, e = m.span()
        if _glued_to_number(t, s, e):
            continue
        before, after = t[:s], t[e:]
        if _UNIT_BEFORE.search(before) or _RANGE_AFTER.match(after) or _RANGE_BEFORE.search(before):
            continue
        is_strong = bool(_HIRE_KW_BEFORE.search(before))
        if not is_strong and _AGE_WIDE_BEFORE.search(before):
            continue
        if _unit_after_blocks(after, is_strong):
            continue
        (strong if is_strong else weak).append(int(m.group()))
    out = []
    for v in strong + weak:
        if v not in out:
            out.append(v)
    return out


def parse_hire_codes(text: str, allow_bare: bool = True) -> list:
    """همه‌ی کدهای ممکن توی پیام، به ترتیب (فارسی/انگلیسی، چسبیده یا با فاصله).
    عدد وقتی کد حساب میشه که: پیام فقط همون عدد باشه، یا کنار «کد/استخدام/عدد/شماره» بیاد،
    یا کنارش سال/ساعت/تومان/نفر و امثالش نباشه (ساعت و سن و تاریخ و مبلغ و بازه‌ی عددی کد حساب نمیشن).
    allow_bare=False: فقط فرمت قدیمی «استخدام کد X»."""
    t = normalize(text)
    if not allow_bare:
        for m in HIRE_RE.finditer(t):
            if not _unit_after_blocks(t[m.end(1):], True):
                return [int(m.group(1))]
        return []
    return _hire_candidates(t)


def parse_hire_code(text: str, allow_bare: bool = True):
    codes = parse_hire_codes(text, allow_bare)
    return codes[0] if codes else None


def luhn_ok(num: str) -> bool:
    total = 0
    for i, ch in enumerate(reversed(num)):
        d = int(ch)
        if i % 2 == 1:
            d *= 2
            if d > 9:
                d -= 9
        total += d
    return total % 10 == 0


CARD_RE = re.compile(r"(?<!\d)\d(?:[\s\-./_,\u060c]*\d){15}(?!\d)")


CARD_WRONG_TEXT = ("❗️شماره کارت اشتباه میباشد❗️\n"
                   "شماره کارت ۱۶ رقمی به همراه اسم و فامیل صاحب حساب رو دوباره بفرست.")


def parse_card_input(text: str):
    """خروجی: (شماره_کارت, نام, پیام_خطا)"""
    t = normalize(text)
    m = CARD_RE.search(t)
    if not m:
        if len(re.findall(r"\d", t)) >= 5:
            return None, None, CARD_WRONG_TEXT
        if re.search(r"[^\W\d_]{2,}", t):
            return None, None, "شماره کارت ۱۶ رقمی رو هم همراه اسم و فامیل بفرست."
        return None, None, "شماره کارت ۱۶ رقمی پیدا نشد. لطفا شماره کارت و نام صاحب حساب رو دوباره بفرست."
    number = re.sub(r"\D", "", m.group(0))
    rest = t[: m.start()] + " " + t[m.end():]
    rest = re.sub(r"[^\w\s]|\d|_", " ", rest)
    holder = re.sub(r"\s+", " ", rest).strip()
    if len(holder) < 3:
        return None, None, "اسم و فامیل صاحب حساب رو هم بفرست."
    if len(holder) > 60:
        return None, None, "نام صاحب حساب خیلی طولانیه؛ فقط اسم و فامیل رو بفرست."
    return number, holder, None


CARD_RE2 = re.compile(r"(?<!\d)\d(?:[\s\-./_,\u060c]*\d){15}(?!\d)")


def split_card_input(text: str):
    """(شماره یا None، نام یا None) از یک پیام؛ هرکدوم که توی پیام نبود None میشه."""
    t = normalize(text)
    m = CARD_RE2.search(t)
    number = re.sub(r"\D", "", m.group(0)) if m else None
    rest = (t[: m.start()] + " " + t[m.end():]) if m else t
    rest = re.sub(r"[^\w\s]|\d|_", " ", rest)
    holder = re.sub(r"\s+", " ", rest).strip()
    if not (3 <= len(holder) <= 60):
        holder = None
    return number, holder


def card_hint(text: str, number, holder) -> str:
    if number and not holder:
        return "اسم و فامیل صاحب حساب رو هم بفرست."
    if not number and len(re.findall(r"\d", normalize(text))) >= 5:
        return CARD_WRONG_TEXT  # عدد هست ولی ۱۶ رقمی نیست
    if holder and not number:
        return "شماره کارت ۱۶ رقمی رو هم بفرست."
    return "شماره کارت ۱۶ رقمی به همراه اسم و فامیل صاحب حساب رو بفرست."


def card_fmt(n: str) -> str:
    return "-".join(n[i:i + 4] for i in range(0, 16, 4))


def card_mask(n: str) -> str:
    return f"{n[:4]}-****-****-{n[-4:]}"


def fmt_toman_fa(a: int) -> str:
    if a >= 1000 and a % 1000 == 0:
        k = a // 1000
        if k >= 1000:
            mil, rest = divmod(k, 1000)
            s = f"{fa(mil)} میلیون" + (f" و {fa(rest)} هزار" if rest else "")
        else:
            s = f"{fa(k)} هزار"
        return s + " تومان"
    return fa(f"{a:,}".replace(",", "٬")) + " تومان"


def fmt_toman_bank(a: int) -> str:
    """مبلغ به سبک بانکی: ۲۰۰/۰۰۰ تومان"""
    return fa(f"{a:,}".replace(",", "/")) + " تومان"


def fmt_en(a: int) -> str:
    return f"{a:,}"


def to_jalali(gy: int, gm: int, gd: int):
    g_d_m = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]
    gy2 = gy + 1 if gm > 2 else gy
    days = (355666 + (365 * gy) + ((gy2 + 3) // 4) - ((gy2 + 99) // 100)
            + ((gy2 + 399) // 400) + gd + g_d_m[gm - 1])
    jy = -1595 + (33 * (days // 12053))
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


J_MONTHS = ["فروردین", "اردیبهشت", "خرداد", "تیر", "مرداد", "شهریور", "مهر", "آبان", "آذر", "دی", "بهمن", "اسفند"]
J_WEEKDAYS = ["دوشنبه", "سه‌شنبه", "چهارشنبه", "پنجشنبه", "جمعه", "شنبه", "یکشنبه"]  # weekday(): Mon=0


def dt_of(ts: int) -> datetime:
    return datetime.fromtimestamp(ts, TZ)


def jdate(ts: int) -> str:
    d = dt_of(ts)
    jy, jm, jd = to_jalali(d.year, d.month, d.day)
    return f"{J_WEEKDAYS[d.weekday()]} {fa(jd)} {J_MONTHS[jm - 1]} {fa(jy)}"


def jdate_short(ts: int) -> str:
    d = dt_of(ts)
    jy, jm, jd = to_jalali(d.year, d.month, d.day)
    return f"{fa(jd)} {J_MONTHS[jm - 1]}"


def jdate_plain(ts: int) -> str:
    d = dt_of(ts)
    jy, jm, jd = to_jalali(d.year, d.month, d.day)
    return f"{fa(jd)} {J_MONTHS[jm - 1]} {fa(jy)}"


def jdate_en(ts: int) -> str:
    """مثل jdate_plain ولی با ارقام انگلیسی: 6 آبان 1405"""
    d = dt_of(ts)
    jy, jm, jd = to_jalali(d.year, d.month, d.day)
    return f"{jd} {J_MONTHS[jm - 1]} {jy}"


def jtime(ts: int) -> str:
    return fa(dt_of(ts).strftime("%H:%M"))


def day_key(ts: int) -> str:
    return dt_of(ts).strftime("%Y%m%d")


def deadline_text(hours: int) -> str:
    return "یک ساعت" if hours == 1 else f"{fa(hours)} ساعت"


# ----------------------------------------------------------------------------
# دیتابیس
# ----------------------------------------------------------------------------
_lock = threading.RLock()
CONN: sqlite3.Connection = None  # type: ignore

SCHEMA = """
CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY, value TEXT);
CREATE TABLE IF NOT EXISTS admins(
  user_id INTEGER PRIMARY KEY,
  code INTEGER UNIQUE NOT NULL,
  first_name TEXT, last_name TEXT, username TEXT,
  created_at INTEGER NOT NULL,
  training_done INTEGER NOT NULL DEFAULT 0,
  period_count INTEGER NOT NULL DEFAULT 0,
  total_count INTEGER NOT NULL DEFAULT 0,
  period_no INTEGER NOT NULL DEFAULT 1,
  cur_target INTEGER NOT NULL,
  cur_amount INTEGER NOT NULL,
  last_hire_at INTEGER
);
CREATE TABLE IF NOT EXISTS hires(
  applicant_id INTEGER PRIMARY KEY,
  admin_id INTEGER NOT NULL,
  applicant_name TEXT,
  ts INTEGER NOT NULL
);
CREATE TABLE IF NOT EXISTS commissions(
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  admin_id INTEGER NOT NULL,
  period_no INTEGER NOT NULL,
  amount INTEGER NOT NULL,
  status TEXT NOT NULL DEFAULT 'earned',
  created_at INTEGER NOT NULL,
  card_number TEXT, card_holder TEXT,
  requested_at INTEGER,
  paid_at INTEGER, paid_day TEXT, paid_amount INTEGER,
  receipt_file_id TEXT, receipt_kind TEXT,
  overdue_notified INTEGER NOT NULL DEFAULT 0,
  UNIQUE(admin_id, period_no)
);
CREATE TABLE IF NOT EXISTS cards(
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  admin_id INTEGER NOT NULL,
  number TEXT NOT NULL,
  holder TEXT NOT NULL,
  UNIQUE(admin_id, number)
);
CREATE TABLE IF NOT EXISTS state(user_id INTEGER PRIMARY KEY, state TEXT, data TEXT);
CREATE TABLE IF NOT EXISTS errors(id INTEGER PRIMARY KEY AUTOINCREMENT, ts INTEGER, text TEXT);
CREATE INDEX IF NOT EXISTS idx_comm_status ON commissions(status);
CREATE INDEX IF NOT EXISTS idx_comm_admin ON commissions(admin_id);
CREATE TABLE IF NOT EXISTS audit(
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  ts INTEGER NOT NULL,
  user_id INTEGER,
  action TEXT NOT NULL,
  detail TEXT
);
CREATE INDEX IF NOT EXISTS idx_audit_user ON audit(user_id);
CREATE TABLE IF NOT EXISTS tracked(
  user_id INTEGER NOT NULL,
  kind TEXT NOT NULL,
  chat_id INTEGER NOT NULL,
  message_id INTEGER NOT NULL,
  ts INTEGER NOT NULL,
  PRIMARY KEY(user_id, kind)
);
CREATE TABLE IF NOT EXISTS cleanup(
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  chat_id INTEGER NOT NULL,
  message_id INTEGER NOT NULL,
  due INTEGER NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_cleanup_due ON cleanup(due);
CREATE TABLE IF NOT EXISTS sent_log(
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  chat_id INTEGER NOT NULL,
  message_id INTEGER NOT NULL,
  ts INTEGER NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_sent_log_chat ON sent_log(chat_id);
CREATE TABLE IF NOT EXISTS receipt_msgs(
  chat_id INTEGER NOT NULL,
  message_id INTEGER NOT NULL,
  PRIMARY KEY(chat_id, message_id)
);
CREATE TABLE IF NOT EXISTS retired_codes(code INTEGER PRIMARY KEY, user_id INTEGER, removed_at INTEGER);
CREATE TABLE IF NOT EXISTS holds(
  chat_id INTEGER NOT NULL,
  message_id INTEGER NOT NULL,
  until INTEGER NOT NULL,
  PRIMARY KEY(chat_id, message_id)
);
CREATE TABLE IF NOT EXISTS alert_pairs(
  chat_id INTEGER NOT NULL,
  alert_id INTEGER NOT NULL,
  emoji_id INTEGER NOT NULL,
  PRIMARY KEY(chat_id, alert_id)
);
CREATE TABLE IF NOT EXISTS shield_admins(
  admin_id INTEGER PRIMARY KEY
);
CREATE TABLE IF NOT EXISTS shield_auto(
  admin_id INTEGER PRIMARY KEY
);
CREATE TABLE IF NOT EXISTS perf_orig(
  chat_id INTEGER NOT NULL,
  message_id INTEGER NOT NULL,
  text TEXT NOT NULL,
  ts INTEGER NOT NULL,
  PRIMARY KEY(chat_id, message_id)
);
CREATE TABLE IF NOT EXISTS stat_events(
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  kind TEXT NOT NULL,
  user_id INTEGER NOT NULL,
  admin_id INTEGER,
  ts INTEGER NOT NULL,
  day TEXT NOT NULL
);
CREATE UNIQUE INDEX IF NOT EXISTS ux_stat_events ON stat_events(kind, user_id, day);
CREATE INDEX IF NOT EXISTS ix_stat_events_day ON stat_events(day, kind);
CREATE TABLE IF NOT EXISTS signups(
  applicant_id INTEGER PRIMARY KEY,
  admin_id INTEGER NOT NULL DEFAULT 0,
  ts INTEGER NOT NULL
);
CREATE INDEX IF NOT EXISTS ix_signups_admin ON signups(admin_id);
CREATE TABLE IF NOT EXISTS daily_stats(
  day TEXT PRIMARY KEY,
  data TEXT NOT NULL,
  created_at INTEGER NOT NULL
);
CREATE TABLE IF NOT EXISTS shield_pending(
  applicant_id INTEGER PRIMARY KEY,
  code INTEGER NOT NULL,
  name TEXT,
  stage INTEGER NOT NULL DEFAULT 0,
  ts INTEGER NOT NULL
);
CREATE TABLE IF NOT EXISTS auto_chat(
  user_id INTEGER PRIMARY KEY,
  first_ts INTEGER NOT NULL,
  access_hash INTEGER NOT NULL DEFAULT 0,
  nine_at INTEGER,
  nine_sent INTEGER NOT NULL DEFAULT 0,
  shoro_at INTEGER,
  reg_sent INTEGER NOT NULL DEFAULT 0,
  alt_sent INTEGER NOT NULL DEFAULT 0,
  confirmed INTEGER NOT NULL DEFAULT 0,
  video_sent INTEGER NOT NULL DEFAULT 0,
  cut INTEGER NOT NULL DEFAULT 0,
  cut_from INTEGER NOT NULL DEFAULT 0,
  notice_sent INTEGER NOT NULL DEFAULT 0
);
CREATE TABLE IF NOT EXISTS auto_media(
  key TEXT PRIMARY KEY,
  data BLOB,
  ext TEXT,
  meta TEXT
);
CREATE TABLE IF NOT EXISTS proc_msg(
  user_id INTEGER PRIMARY KEY,
  last_id INTEGER NOT NULL
);
DROP TABLE IF EXISTS questions;
CREATE TABLE IF NOT EXISTS faq_questions(
  id INTEGER PRIMARY KEY AUTOINCREMENT, ts INTEGER NOT NULL, text TEXT NOT NULL, sent INTEGER NOT NULL DEFAULT 0
);
CREATE TABLE IF NOT EXISTS members(user_id INTEGER PRIMARY KEY, first_seen INTEGER NOT NULL);
CREATE TABLE IF NOT EXISTS cheats(
  id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT NOT NULL, kind TEXT NOT NULL DEFAULT 'custom', text TEXT,
  days TEXT NOT NULL DEFAULT '[]', times TEXT NOT NULL DEFAULT '[]', enabled INTEGER NOT NULL DEFAULT 1,
  once_ts INTEGER, once_done INTEGER NOT NULL DEFAULT 0, created_at INTEGER NOT NULL
);
CREATE TABLE IF NOT EXISTS cheat_runs(
  id INTEGER PRIMARY KEY AUTOINCREMENT, cheat_id INTEGER NOT NULL, kind TEXT NOT NULL, slot_key TEXT NOT NULL,
  started_at INTEGER NOT NULL, finished_at INTEGER, sent INTEGER NOT NULL DEFAULT 0, failed INTEGER NOT NULL DEFAULT 0,
  UNIQUE(cheat_id, slot_key)
);
CREATE TABLE IF NOT EXISTS cheat_delivered(
  run_id INTEGER NOT NULL, user_id INTEGER NOT NULL, cheat_id INTEGER NOT NULL, ts INTEGER NOT NULL,
  PRIMARY KEY(run_id, user_id)
);
CREATE INDEX IF NOT EXISTS ix_cheat_delivered ON cheat_delivered(cheat_id, user_id, ts);
CREATE TABLE IF NOT EXISTS cheat_ad_titles(
  user_id INTEGER NOT NULL, title_idx INTEGER NOT NULL, cycle INTEGER NOT NULL, ts INTEGER NOT NULL,
  PRIMARY KEY(user_id, title_idx, cycle)
);
"""


def _migrate():
    """ستون‌های جدید روی دیتابیس‌های قبلی هم اضافه میشن (داده‌های قبلی دست‌نخورده می‌مونن)."""
    def add(table, col, decl):
        cols = {r[1] for r in CONN.execute(f"PRAGMA table_info({table})")}
        if col not in cols:
            CONN.execute(f"ALTER TABLE {table} ADD COLUMN {col} {decl}")
    add("admins", "training_done_at", "INTEGER")
    add("admins", "warn_sent", "INTEGER NOT NULL DEFAULT 0")
    add("admins", "blocked", "INTEGER NOT NULL DEFAULT 0")
    add("admins", "nudge_sent", "INTEGER NOT NULL DEFAULT 0")
    add("admins", "first_sent", "INTEGER NOT NULL DEFAULT 0")
    add("admins", "why_sent", "INTEGER NOT NULL DEFAULT 0")  # پیام ۲۴ ساعته‌ی دارای دکمه‌های «چرا جذب نزدی؟» فرستاده شده؟
    add("admins", "stall_sent_at", "INTEGER NOT NULL DEFAULT 0")
    add("state", "ts", "INTEGER")
    add("tracked", "cmd_id", "INTEGER")
    add("commissions", "target", "INTEGER")
    add("auto_chat", "vid_at", "INTEGER")
    add("auto_chat", "ack_nine", "INTEGER NOT NULL DEFAULT 0")   # شناسه‌ی پیامی که ارسال ۹ پیام رو راه انداخت
    add("auto_chat", "ack_shoro", "INTEGER NOT NULL DEFAULT 0")  # شناسه‌ی پیام «شروع»
    add("auto_chat", "ack_conf", "INTEGER NOT NULL DEFAULT 0")   # شناسه‌ی پیام «تایید شرایط»
    add("cheats", "photo", "TEXT")  # عکس تقلب (file_id)؛ متن تقلب کپشن همین عکسه
    add("cheats", "no_preview", "INTEGER NOT NULL DEFAULT 0")  # مدیر موقع فرستادن متن، پریویو لینک رو بسته؟ (۱ = بدون پریویو)
    # ممبرها: ادمین‌های فعلی یک بار وارد جدول میشن؛ از این به بعد هرکس با ربات کار داشته باشه برای همیشه ثبت میشه
    CONN.execute("INSERT OR IGNORE INTO members(user_id, first_seen) "
                 "SELECT user_id, created_at FROM admins WHERE user_id<>?", (OWNER_ID,))
    # اصلاح یک‌باره: ادمین‌های قدیمی موقع ساخته شدنِ جدول «ممبرها» با زمانِ همون روز ثبت شده بودن و توی «کاربران جدید ربات» همون روز
    # اشتباهاً حساب میشدن. زمانِ ورودِ یک ادمین هیچ‌وقت بعد از ادمین شدنش نیست؛ پس فقط ردیف‌های ناممکن به زمانِ ساخته شدنِ ادمین برمیگردن.
    CONN.execute("UPDATE members SET first_seen=(SELECT a.created_at FROM admins a WHERE a.user_id=members.user_id) "
                 "WHERE user_id IN (SELECT user_id FROM admins) AND first_seen>"
                 "(SELECT a.created_at FROM admins a WHERE a.user_id=members.user_id)")
    # عدد ممبرهای پنل مدیر: هر ادمینی که به «پنل شما فعال شد» رسیده counted=1 میگیره؛ موقع هر بالا اومدنِ ربات هم
    # همه‌ی ادمین‌هایی که آموزششون تموم شده یک‌بار شمرده میشن. ادمین‌های حذف‌شده (retired_codes) از عدد کم نمیشن.
    add("admins", "counted", "INTEGER NOT NULL DEFAULT 0")
    add("admins", "noact_sent_at", "INTEGER NOT NULL DEFAULT 0")  # آخرین اطلاعیه‌ی «۳ روز بی‌جذب»
    add("admins", "tut_nudge_sent", "INTEGER NOT NULL DEFAULT 0")  # یادآوریِ «آموزشت نیمه‌کاره موند» فرستاده شده؟
    # ادمین‌هایی که خودکار (بدون جذب) حذف شدن: sent=پیام «هنوز دیر نشده» رفته، back=دوباره برگشته (پیام «خوش برگشتی» رفته)
    CONN.execute("CREATE TABLE IF NOT EXISTS comeback(user_id INTEGER PRIMARY KEY, removed_at INTEGER NOT NULL, "
                 "sent INTEGER NOT NULL DEFAULT 0, back INTEGER NOT NULL DEFAULT 0)")
    CONN.execute("CREATE TABLE IF NOT EXISTS nudge_why(user_id INTEGER PRIMARY KEY, choice INTEGER NOT NULL, ts INTEGER NOT NULL)")
    add("comeback", "sent_at", "INTEGER NOT NULL DEFAULT 0")      # زمان ارسال «هنوز دیر نشده» (برای آمار)
    add("comeback", "pressed_at", "INTEGER NOT NULL DEFAULT 0")   # زمان زدن «شروع دوباره»
    add("comeback", "done_at", "INTEGER NOT NULL DEFAULT 0")      # زمان فعال شدن پنل بعد از برگشت
    add("comeback", "msg_id", "INTEGER NOT NULL DEFAULT 0")        # شناسه‌ی پیام «هنوز دیر نشده» (با فعال شدن پنل پاک میشه)
    add("admins", "tut_nudge_msg", "INTEGER NOT NULL DEFAULT 0")   # شناسه‌ی پیام یادآوریِ آموزش (با فعال شدن پنل پاک میشه)
    # حذف‌شده‌های قبلی بی‌صدا ثبت میشن (پیام «هنوز دیر نشده» براشون نمیره)؛ فقط اگه خودشون برگشتن «خوش برگشتی» میگیرن
    CONN.execute("INSERT OR IGNORE INTO comeback(user_id, removed_at, sent, back) "
                 "SELECT user_id, MAX(ts), 1, 0 FROM audit WHERE action='admin_removed' "
                 "AND user_id NOT IN (SELECT user_id FROM admins) GROUP BY user_id")
    # یک‌بار: حذف‌شده‌های ۳ روز اخیرِ قبل از این نسخه هم پیام «هنوز دیر نشده» رو بگیرن (comeback_job خودش ساعت ۹–۲۳ و بعد از ۱ روز می‌فرسته)
    if CONN.execute("SELECT 1 FROM settings WHERE key='comeback_once_v1'").fetchone() is None:
        CONN.execute("UPDATE comeback SET sent=0 WHERE back=0 AND removed_at>=? "
                     "AND user_id NOT IN (SELECT user_id FROM admins)", (int(time.time()) - 3 * 86400,))
        CONN.execute("INSERT OR REPLACE INTO settings(key,value) VALUES('comeback_once_v1','1')")
    add("admins", "noact_msg", "INTEGER NOT NULL DEFAULT 0")      # شناسه‌ی پیامش (با ارسال بعدی پاک میشه)
    add("admins", "warn_at", "INTEGER NOT NULL DEFAULT 0")        # زمان ارسال هشدار حذف؛ حذف فقط بعد از هشدار و ۲۴ ساعت فاصله
    add("commissions", "lvl", "INTEGER")                          # سطح واقعی ادمین موقع کامل شدن اون دوره (برای متن تبریک)
    add("admins", "level_pen", "INTEGER NOT NULL DEFAULT 0")       # افت سطح: چند سطح از سطحِ دوره‌ش کم میشه (سطح واقعی = سطح دوره − این عدد)
    add("admins", "drop_done_at", "INTEGER NOT NULL DEFAULT 0")   # زمان آخرین افت سطح
    add("admins", "drop_warn_at", "INTEGER NOT NULL DEFAULT 0")   # زمان آخرین هشدار افت سطح (یک بار به ازای هر دوره‌ی بی‌جذبی)
    CONN.execute("UPDATE admins SET counted=1 WHERE training_done=1 AND counted=0")


def init_db(path: str = None):
    global CONN
    CONN = sqlite3.connect(path or DB_PATH, check_same_thread=False, isolation_level=None, timeout=30)
    CONN.row_factory = sqlite3.Row
    CONN.execute("PRAGMA journal_mode=WAL")
    CONN.execute("PRAGMA synchronous=FULL")
    CONN.executescript(SCHEMA)
    _migrate()
    return CONN


@contextmanager
def tx():
    """تراکنش اتمیک با قفل (BEGIN IMMEDIATE)."""
    with _lock:
        CONN.execute("BEGIN IMMEDIATE")
        try:
            yield CONN
        except BaseException:
            CONN.execute("ROLLBACK")
            raise
        else:
            CONN.execute("COMMIT")


def q1(sql, args=()):
    with _lock:
        return CONN.execute(sql, args).fetchone()


def qa(sql, args=()):
    with _lock:
        return CONN.execute(sql, args).fetchall()


def ex(sql, args=()):
    with _lock:
        return CONN.execute(sql, args)


def get_setting(key: str) -> str:
    r = q1("SELECT value FROM settings WHERE key=?", (key,))
    if r is not None:
        return r["value"]
    return DEFAULT_SETTINGS.get(key, "")


def set_setting(key: str, value: str):
    ex("INSERT INTO settings(key,value) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
       (key, str(value)))


def get_int_setting(key: str) -> int:
    try:
        return int(get_setting(key))
    except ValueError:
        return int(DEFAULT_SETTINGS.get(key, "0") or 0)


def level_for_period(n) -> int:
    """سطح بر اساس شماره‌ی دوره‌ای که ادمین توش کار میکنه: دوره ۱ = سطح ۱، دوره ۲ = سطح ۲، دوره ۳ به بعد = سطح ۳."""
    try:
        n = int(n)
    except (TypeError, ValueError):
        n = 1
    return min(max(n, 1), LEVEL_MAX)


def level_of(a) -> int:
    """سطح واقعی ادمین: سطحِ شماره‌ی دوره منهای افت سطح (level_pen)؛ همه‌ی ربات (پروفایل، ستاره، مبلغ، سپر) از همین میخونه."""
    try:
        pen = int(a["level_pen"] or 0)
    except (KeyError, IndexError, TypeError, ValueError):
        pen = 0
    return max(level_for_period(a["period_no"]) - max(pen, 0), 1)


def level_amount(level: int) -> int:
    return get_int_setting(LEVEL_AMOUNT_KEYS[level_for_period(level)])


def stars_of(a) -> str:
    return "⭐️" * level_of(a)


def migrate_levels():
    """یک‌بار مصرف: دوره‌ی در جریانِ ادمین‌های فعلی با مبلغ سطحشون هماهنگ میشه.
    پورسانت‌های ثبت‌شده (جدول commissions) و جذب‌ها دست‌نخورده می‌مونن."""
    if get_setting("levels_v1") == "1":
        return
    with tx() as c:
        for r in c.execute("SELECT user_id, period_no FROM admins WHERE period_no>1").fetchall():
            c.execute("UPDATE admins SET cur_amount=? WHERE user_id=?",
                      (level_amount(level_for_period(r["period_no"])), r["user_id"]))
        c.execute("INSERT INTO settings(key,value) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                  ("levels_v1", "1"))
    audit(0, "migrate_levels")


def bot_off() -> bool:
    return get_setting("bot_off") == "1"


def set_bot_off(flag: bool):
    """حالت تعمیرات سراسری. فقط یک فلگ توی settings عوض میشه؛ هیچ داده‌ی دیگه‌ای حذف یا تغییر نمیکنه.
    موقع روشن شدن دوباره، مدت خاموشی به تایمر ادمین‌های بدون جذب اضافه میشه تا بابتش حذف نشن."""
    now = int(time.time())
    if flag:
        if not bot_off():
            set_setting("bot_off_since", now)
        set_setting("bot_off", "1")
        audit(OWNER_ID, "bot_off")
        return
    since = get_int_setting("bot_off_since")
    set_setting("bot_off", "0")
    set_setting("bot_off_since", 0)
    if since > 0 and now > since:
        ex("UPDATE admins SET training_done_at=training_done_at+? "
           "WHERE training_done=1 AND total_count=0 AND training_done_at IS NOT NULL", (now - since,))
    audit(OWNER_ID, "bot_on", f"downtime={max(now - since, 0) if since else 0}")


RESET_FLAG = "reset_all_users_v2"  # v2: پاک‌سازی دوباره‌ی دیتای کاربران قبل از تست جذب (یک بار در اولین اجرا)


def reset_all_user_data():
    """یک‌بار مصرف: دیتای همه‌ی افراد ربات (ادمین‌ها، جذب‌ها، پورسانت‌ها، کارت‌ها، وضعیت‌ها) صفر میشه تا
    اکانت‌های تست از اول ثبت بشن. ویدیو، عکس‌ها و تنظیمات دست‌نخورده می‌مونن؛ قبلش یک نسخه‌ی کامل کنار دیتابیس
    ذخیره میشه و با فلگ داخل دیتابیس فقط یک بار اجرا میشه."""
    if get_setting(RESET_FLAG) == "1":
        return
    try:
        bk_path = f"{DB_PATH}.pre_reset_{int(time.time())}.bak"
        dst = sqlite3.connect(bk_path)
        with _lock:
            CONN.backup(dst)
        dst.close()
    except Exception:  # noqa
        log.exception("pre-reset backup failed")
        return  # بدون نسخه‌ی پشتیبان، چیزی پاک نمیشه
    tables = ("hires", "commissions", "cards", "admins", "state", "tracked", "cleanup", "sent_log", "retired_codes", "holds")
    with tx() as c:
        counts = {t: c.execute(f"SELECT COUNT(*) FROM {t}").fetchone()[0] for t in tables}
        for t in tables:
            c.execute(f"DELETE FROM {t}")
        c.execute("DELETE FROM sqlite_sequence WHERE name IN ('commissions','cards')")
        c.execute("INSERT INTO settings(key,value) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                  (RESET_FLAG, "1"))
        c.execute("INSERT INTO settings(key,value) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                  ("reset_notice", json.dumps(counts)))
    audit(0, "reset_all_users", json.dumps(counts))
    log.info("all user data reset: %s", counts)


ADMIN_DATA_TABLES = ("hires", "commissions", "cards", "admins", "state", "tracked", "cleanup", "sent_log", "retired_codes", "holds")


def reset_admin_data():
    """ریست دستیِ دیتای ادمین‌ها از تنظیمات مدیر: فقط جدول‌های ادمین/جذب/پورسانت/کارت و ردیابی پیام‌ها خالی میشن.
    settings (متن‌ها، عکس‌ها، ویدیو، مبلغ‌ها، قوانین) و لاگ‌ها دست‌نخورده می‌مونن. قبلش یک نسخه‌ی پشتیبان ساخته میشه؛
    اگه بکاپ نشد، چیزی پاک نمیشه. خروجی: (تعداد ردیف‌های پاک‌شده، مسیر بکاپ) یا None."""
    bk_path = f"{DB_PATH}.pre_reset_{int(time.time())}.bak"
    try:
        dst = sqlite3.connect(bk_path)
        with _lock:
            CONN.backup(dst)
        dst.close()
    except Exception:  # noqa
        log.exception("manual reset backup failed")
        return None
    with tx() as c:
        counts = {t: c.execute(f"SELECT COUNT(*) FROM {t}").fetchone()[0] for t in ADMIN_DATA_TABLES}
        for t in ADMIN_DATA_TABLES:
            c.execute(f"DELETE FROM {t}")
        c.execute("DELETE FROM sqlite_sequence WHERE name IN ('commissions','cards')")
    _tut_seen.clear()
    _last_act.clear()
    audit(OWNER_ID, "manual_reset_admin_data", json.dumps(counts))
    return counts, bk_path


def reset_one_admin_data(uid: int):
    """ریست دیتای فقط یک ادمین: حسابش، جذب‌ها، پورسانت‌ها، کارت‌ها و ردیابی پیام‌هاش. بقیه‌ی ادمین‌ها و settings دست‌نخورده می‌مونن.
    قبلش یک نسخه‌ی پشتیبان ساخته میشه؛ اگه بکاپ نشد، چیزی پاک نمیشه. کد ادمین برای همیشه رزرو میشه.
    خروجی: (تعداد ردیف‌های پاک‌شده، مسیر بکاپ) یا None."""
    if uid == OWNER_ID:
        return None
    bk_path = f"{DB_PATH}.pre_reset_{int(time.time())}.bak"
    try:
        dst = sqlite3.connect(bk_path)
        with _lock:
            CONN.backup(dst)
        dst.close()
    except Exception:  # noqa
        log.exception("single admin reset backup failed")
        return None
    with tx() as c:
        a = c.execute("SELECT * FROM admins WHERE user_id=?", (uid,)).fetchone()
        if a is None:
            return None
        counts = {
            "hires": c.execute("SELECT COUNT(*) FROM hires WHERE admin_id=?", (uid,)).fetchone()[0],
            "commissions": c.execute("SELECT COUNT(*) FROM commissions WHERE admin_id=?", (uid,)).fetchone()[0],
            "cards": c.execute("SELECT COUNT(*) FROM cards WHERE admin_id=?", (uid,)).fetchone()[0],
        }
        c.execute("INSERT OR IGNORE INTO retired_codes(code,user_id,removed_at) VALUES(?,?,?)",
                  (a["code"], uid, int(time.time())))
        c.execute("DELETE FROM shield_pending WHERE code=?", (a["code"],))
        c.execute("DELETE FROM shield_admins WHERE admin_id=?", (uid,))
        c.execute("DELETE FROM shield_auto WHERE admin_id=?", (uid,))
        c.execute("UPDATE signups SET admin_id=0 WHERE admin_id=?", (uid,))
        c.execute("DELETE FROM hires WHERE admin_id=?", (uid,))
        c.execute("DELETE FROM commissions WHERE admin_id=?", (uid,))
        c.execute("DELETE FROM cards WHERE admin_id=?", (uid,))
        c.execute("DELETE FROM admins WHERE user_id=?", (uid,))
        c.execute("DELETE FROM state WHERE user_id=?", (uid,))
        c.execute("DELETE FROM tracked WHERE user_id=?", (uid,))
        for t in ("cleanup", "sent_log", "holds", "receipt_msgs"):
            c.execute(f"DELETE FROM {t} WHERE chat_id=?", (uid,))
        c.execute("DELETE FROM auto_chat WHERE user_id=?", (uid,))
        c.execute("DELETE FROM proc_msg WHERE user_id=?", (uid,))
    _tut_seen.pop(uid, None)
    _last_act.pop(uid, None)
    audit(OWNER_ID, "manual_reset_one_admin", json.dumps({"user_id": uid, **counts}))
    return counts, bk_path


async def reset_notice_job(context):
    raw = get_setting("reset_notice")
    if not raw:
        return
    try:
        await context.bot.unpin_all_chat_messages(OWNER_ID)  # درخواست‌های پین‌شده‌ی قدیمی
    except TelegramError:
        pass
    try:
        c = json.loads(raw)
    except ValueError:
        c = {}
    ok = await safe_send(context.bot, OWNER_ID,
                         fb(f"👤 ادمین‌ها:「{c.get('admins', 0)}」\n"
                            f"🧲 جذب‌ها:「{c.get('hires', 0)}」\n"
                            f"💰 پورسانت‌ها:「{c.get('commissions', 0)}」\n"
                            f"💳 کارت‌ها:「{c.get('cards', 0)}」\n\n"
                            "ویدیو، عکس‌ها و تنظیمات دست‌نخورده موندن؛ حالا با اکانت‌های تست از اول ثبت‌نام کن.",
                            "🧹 دیتای ربات صفر شد 🧹"),
                         html_mode=True)
    if ok is not None:
        set_setting("reset_notice", "")


PURGE_FLAG = "purged_test_payments_v1"


def purge_test_payments():
    """یک‌بار مصرف: همه‌ی پورسانت‌های ثبت‌شده (در انتظار / پرداخت‌شده / پرداخت‌نشده) که آزمایشی بودن پاک میشن.
    با فلگ داخل دیتابیس فقط یک بار اجرا میشه و دفعه‌های بعد هیچ‌چیز رو پاک نمیکنه."""
    if get_setting(PURGE_FLAG) == "1":
        return
    with tx() as c:
        by = {r[0]: r[1] for r in c.execute("SELECT status, COUNT(*) FROM commissions GROUP BY status")}
        total = sum(by.values())
        c.execute("DELETE FROM commissions")
        c.execute("INSERT INTO settings(key,value) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                  (PURGE_FLAG, "1"))
        if total:
            c.execute("INSERT INTO settings(key,value) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                      ("purge_notice", json.dumps(by)))
    audit(0, "purge_test_payments", json.dumps(by))
    log.info("test payments purged: %s", by)


async def purge_notice_job(context):
    raw = get_setting("purge_notice")
    if not raw:
        return
    try:
        by = json.loads(raw)
    except ValueError:
        by = {}
    ok = await safe_send(context.bot, OWNER_ID,
                         fb(f"🔹 در انتظار واریز:「{by.get('requested', 0)}」\n"
                            f"✅ واریز شده:「{by.get('paid', 0)}」\n"
                            f"🔷 هنوز درخواست نشده:「{by.get('earned', 0)}」",
                            "🧹 پرداخت‌های آزمایشی پاک شدن 🧹"),
                         html_mode=True)
    if ok is not None:
        set_setting("purge_notice", "")


def get_text(key: str) -> str:
    v = get_setting("text_" + key)
    return v if v else TEXT_DEFAULTS[key]


def set_state(uid: int, state: str, data: dict = None):
    ex("INSERT INTO state(user_id,state,data,ts) VALUES(?,?,?,?) ON CONFLICT(user_id) DO UPDATE SET "
       "state=excluded.state, data=excluded.data, ts=excluded.ts",
       (uid, state, json.dumps(data or {}, ensure_ascii=False), int(time.time())))


def get_state(uid: int):
    r = q1("SELECT state,data FROM state WHERE user_id=?", (uid,))
    if not r or not r["state"]:
        return None, {}
    try:
        return r["state"], json.loads(r["data"] or "{}")
    except ValueError:
        return r["state"], {}


def clear_state(uid: int):
    ex("DELETE FROM state WHERE user_id=?", (uid,))


# خطاهای شبکه‌ی گذرا و بی‌اهمیت که توی «گزارش خطاها» نمیان (فقط خطاهای واقعی ثبت میشن)
NOISE_ERRORS = ("NetworkError", "Bad Gateway", "TimedOut", "Query is too old", "Message is not modified",
                "catch_up: بازه")


def is_noise_error(text: str) -> bool:
    return any(k in (text or "") for k in NOISE_ERRORS)


def log_err(text: str):
    if is_noise_error(text):
        return
    try:
        ex("INSERT INTO errors(ts,text) VALUES(?,?)", (int(time.time()), text[:1500]))
        ex("DELETE FROM errors WHERE id NOT IN (SELECT id FROM errors ORDER BY id DESC LIMIT 200)")
    except Exception:  # pragma: no cover
        log.exception("log_err failed")


# ---------------------- ادمین‌ها ----------------------
def alloc_code(c) -> int:
    """کد یکتای تصادفی در ۱۰..۹۹؛ در صورت پر شدن بازه، به ۳ رقمی و بیشتر گسترش می‌یابد."""
    used = {r[0] for r in c.execute("SELECT code FROM admins")}
    used |= {r[0] for r in c.execute("SELECT code FROM retired_codes")}  # کد ادمین‌های حذف‌شده دوباره به کسی داده نمیشه
    digits = 2
    rng = random.SystemRandom()
    while True:
        lo, hi = 10 ** (digits - 1), 10 ** digits - 1
        free = [x for x in range(lo, hi + 1) if x not in used]
        if free:
            return rng.choice(free)
        digits += 1


def codes_full() -> bool:
    """همه‌ی کدهای 10 تا 999 مصرف (یا برای همیشه رزرو) شدن؟"""
    used = {r[0] for r in qa("SELECT code FROM admins")}
    used |= {r[0] for r in qa("SELECT code FROM retired_codes")}
    return all(x in used for x in range(10, 1000))


async def announce_codes_full(bot) -> None:
    """وقتی آخرین کد بین 10 تا 999 پر شد، فقط یک بار پیام تبریک جذب هزارتایی میره پنل مدیر."""
    try:
        if get_setting("codes_full_sent") == "1" or not codes_full():
            return
        set_setting("codes_full_sent", "1")
        await safe_send_hold(
            bot, OWNER_ID,
            "<b>🏆 تبریک! جذب هزارتایی کامل شد 🏆</b>\n\n"
            "همه‌ی کدهای「10」تا「999」پر شدن 🎉\n"
            "از این به بعد ادمین‌های جدید کد 4 رقمی می‌گیرن.")
    except Exception as e:  # noqa
        log_err(f"announce_codes_full: {e!r}")


def create_admin(user) -> sqlite3.Row:
    first = user.first_name or ""
    last = user.last_name or ""
    uname = (user.username or "").lower() or None
    with tx() as c:
        r = c.execute("SELECT * FROM admins WHERE user_id=?", (user.id,)).fetchone()
        if r is None:
            code = alloc_code(c)
            c.execute(
                "INSERT INTO admins(user_id,code,first_name,last_name,username,created_at,cur_target,cur_amount)"
                " VALUES(?,?,?,?,?,?,?,?)",
                (user.id, code, first, last, uname, int(time.time()),
                 get_int_setting("pay_target"), get_int_setting("pay_amount")))
            ac = c.execute("SELECT confirmed, cut FROM auto_chat WHERE user_id=?", (user.id,)).fetchone()
            if ac is not None and ac["confirmed"] and not ac["cut"]:  # «بدون ثبت‌نام» رو تأیید کرده بود
                base = get_int_setting("pay_amount")
                c.execute("UPDATE admins SET cur_amount=? WHERE user_id=?", (max(base - AUTO_CUT, 0), user.id))
                c.execute("UPDATE auto_chat SET cut=1, cut_from=? WHERE user_id=?", (base, user.id))
        elif ((r["first_name"] or "") != first or (r["last_name"] or "") != last
              or (r["username"] or None) != uname or r["blocked"]):
            c.execute("UPDATE admins SET first_name=?, last_name=?, username=?, blocked=0 WHERE user_id=?",
                      (first, last, uname, user.id))
        return c.execute("SELECT * FROM admins WHERE user_id=?", (user.id,)).fetchone()


def get_admin(uid: int):
    return q1("SELECT * FROM admins WHERE user_id=?", (uid,))


def name_of(a) -> str:
    n = " ".join(x for x in [a["first_name"], a["last_name"]] if x).strip()
    if n:
        return n
    return ("@" + a["username"]) if a["username"] else str(a["user_id"])


def link(a) -> str:
    return link_profile(a)


ZW = "\u200c"
RLM, FSI, PDI = "\u200f", "\u2068", "\u2069"  # راست‌به‌چپ، شروع و پایان ایزوله‌ی نام


def _cw(ch: str) -> float:
    """عرض تقریبی یک نویسه (حرف = ۱، ایموجی/نویسه‌ی عریض = ۲، نویسه‌ی نامرئی = ۰)."""
    if ch in "\u200c\u200d\u200e\u200f\u2068\u2069\ufe0f" or unicodedata.combining(ch):
        return 0.0
    if ch == " ":
        return 0.6
    if ord(ch) >= 0x1F000 or unicodedata.east_asian_width(ch) in ("W", "F"):
        return 2.0
    return 1.0


NAME_LINE_UNITS = 12.0  # جای نام داخل 「 」 هم‌عرض خط ➖•➖•➖•➖•➖•➖ پروفایل


def fit_name(s: str, units: float = NAME_LINE_UNITS, ell: str = "…") -> str:
    """نام کامل نشون داده میشه؛ فقط اگه از یک خط بیشتر میشد کمی کوتاه میشه."""
    s = (s or "").strip()
    if sum(_cw(c) for c in s) <= units:
        return s
    out, w = "", 0.0
    for c in s:
        if w + _cw(c) > units - 1:
            break
        out += c
        w += _cw(c)
    return out.rstrip() + ell


def short_name(s: str, limit: int = None, ell: str = "") -> str:
    """کوتاه‌کردن فقط برای نمایش، تا نام در یک خط جا بشه."""
    if limit is None or len(s) <= limit:
        return s
    return s[:limit].rstrip() + ell


def link_profile(a, limit: int = None, ell: str = "") -> str:
    """نام ادمین به پروفایلش لینک میشه (یوزرنیم اگه داشته باشه، وگرنه لینک مستقیم کاربر).
    نام داخل ایزوله‌ی جهت‌دار قرار میگیره تا نام انگلیسی ترتیب متن فارسی کنارش رو بهم نزنه."""
    uname = a["username"]
    url = f"https://t.me/{uname}" if uname else f"tg://user?id={a['user_id']}"
    return f'{RLM}{FSI}<a href="{url}">{html.escape(short_name(name_of(a), limit, ell))}</a>{PDI}{RLM}'


_INVIS = "\u200c\u200b\u200d\u2060\u200e\u200f\ufe0f\u3164\u2800\u00a0 "


def link_list_name(a, limit: int = 26, ell: str = "…") -> str:
    """لیست ادمین‌ها: نام همیشه لینکه. اگه اسم کمتر از دو حرف باشه (زدنش سخته) و آیدی داشته باشه، آیدی لینک میشه؛
    اگه آیدی نداشت، همون اسم با لینک tg://user?id (و اگه اسم کمتر از دو حرف بود «بی‌نام»)."""
    uname = a["username"]
    raw = " ".join(x for x in [a["first_name"], a["last_name"]] if x).strip()
    visible = "".join(ch for ch in raw if ch not in _INVIS)
    if uname:
        url = f"https://t.me/{uname}"
        label = ("@" + uname) if len(visible) < 2 else name_of(a)
    else:
        url = f"tg://user?id={a['user_id']}"
        label = name_of(a) if len(visible) >= 2 else "بی‌نام"
    return f'{RLM}{FSI}<a href="{url}">{html.escape(short_name(label, limit, ell))}</a>{PDI}{RLM}'


SHIELD_AT = {1: 22, 2: 15, 3: 7}  # سپر خودکار هر سطح: هرکس در دوره به این عدد برسه سپر مخصوص خودش میگیره و می‌مونه


def shield_level_on(lvl: int) -> bool:
    """سپر خودکارِ یک سطح روشنه؟ (اگه هنوز دست نخورده باشه، تنظیم قدیمیِ «سپر 22» برای سطح ۱ حساب میشه)"""
    r = q1("SELECT value FROM settings WHERE key=?", (f"shield_l{lvl}",))
    if r is not None:
        return r["value"] == "1"
    return lvl == 1 and get_setting("shield22") == "1"


def activity_lines(period, target, total, remaining, level, amount) -> str:
    """خطوط مشترک گزارش فعالیت و اعلان جذب جدید ادمین (جذب، سطح، مبلغ دوره)؛ همه اعداد از دیتای واقعی میان."""
    return (
        f"<b>➕ </b>جذب این دوره<b> ›「 {period} نفر 」</b>از<b>「 {target} نفر 」</b>\n"
        f"<b>🧲 </b>مجموع جذب{ZW}ها<b> ›「 {total} نفر 」</b>\n"
        f"<b>🏅 </b>سطح شما<b> ›「 {LEVEL_NAMES[level]} 」</b>\n"
        f"<b>💰 </b>پورسانت این دوره<b> ›「 {fmt_en(amount)} تومان 」</b>\n"
        "➖•➖•➖\n"
        f"<b>🎯 {remaining} جذب دیگه تا دریافت پورسانت!</b>"
    )


STAR, LOCK = "\u2b50\ufe0f", "\U0001F512"
LEVEL_LABELS = {1: "تک‌ستاره " + STAR, 2: "دوستاره " + STAR * 2, 3: "سه‌ستاره " + STAR * 3}
WELCOME_LEVEL = {n: "ادمین <b>" + LEVEL_LABELS[n].split(" ", 1)[0] + "</b> " + LEVEL_LABELS[n].split(" ", 1)[1] for n in (1, 2, 3)}


def profile_caption(a, view=None) -> str:
    """کپشن پروفایل؛ نام لینک‌دار کوتاه می‌شود تا در یک خط باقی بماند.
    view = سطحی که نمایش داده میشه؛ اگه از سطح فعلی ادمین بالاتر باشه، به‌جای ستاره‌ها قفل میاد."""
    lvl = level_of(a)
    view = view or lvl
    uname = a["username"]
    _url = f"https://t.me/{uname}" if uname else f"tg://user?id={a['user_id']}"
    name_link = f'{RLM}{FSI}<a href="{_url}">{html.escape(fit_name(name_of(a)))}</a>{PDI}{RLM}'
    level_label = LEVEL_LABELS[view]
    if view > lvl:
        level_label = level_label.replace(STAR, LOCK)
    return (
        "<b>👤پروفایل کاربری شما در جذبان👤</b>\n"
        f"<b>「سطح {level_label}」</b>\n"
        "➖•➖•➖\n"
        f"<b>🔗 نام کاربری:</b> 🔻\n「{name_link}」\n"
        f"<b>🆔 کد اختصاصی:</b>「<b>{a['code']}</b>」\n"
        + (f"<b>{LOCK}شما هنوز به این سطح نرسیدی{LOCK}</b>\n" if view > lvl else "")
        + "➖•➖•➖•➖•➖•➖"
    )


def activity_report_text(a, view=None) -> str:
    lvl = level_of(a)
    locked = bool(view) and view > lvl
    left = max(a["cur_target"] - a["period_count"], 0)
    paid = q1("SELECT COALESCE(SUM(COALESCE(paid_amount,amount)),0) total FROM commissions "
              "WHERE admin_id=? AND status='paid'", (a["user_id"],))["total"]
    if locked:
        return ("<b>🖥️ گزارش فعالیت شما تا این لحظه: 🖥️</b>\n\n"
                f"<b>{LOCK}شما هنوز به این سطح نرسیدی{LOCK}</b>\n"
                "➖•➖")
    else:
        period_v = f"{a['period_count']} از {a['cur_target']}"
        total_v, left_v, paid_v = a["total_count"], left, fmt_en(paid)
        head = ("<b>🖥️ گزارش فعالیت شما تا این لحظه: 🖥️</b>\n"
                "➖•➖\n\n")
    return head + (
        f"➕ جذب این دوره:「 {period_v} نفر 」\n"
        "➖•➖\n\n"
        f"🧲 مجموع جذب‌ها:「 {total_v} نفر 」\n"
        "➖•➖\n\n"
        f"<b>🎯 {left_v} جذب دیگه تا دریافت پورسانت!</b>\n"
        "➖•➖\n\n"
        f"<b>💵 مجموع پورسانت‌های دریافت‌شده:</b> 「 {paid_v} تومان 」\n"
        "➖•➖"
    )


def admin_hire_text(period, target, total, remaining, level, amount) -> str:
    return ("<b>🎉 یک جذب جدید برات ثبت شد!</b>\n"
            "➖•➖•➖\n" + activity_lines(period, target, total, remaining, level, amount))


def levelup_congrats_text(new_level: int, target, amount, new_target, new_amount) -> str:
    """پیام تبریک تکمیل دوره‌ای که ادمین باهاش وارد سطح بعدی میشه (فقط همین یک متن میاد)؛
    همه‌ی اعداد از دیتای واقعی، با ارقام انگلیسی."""
    done = (
        "🎉 <b>تبریک ادمین گرامی!</b> 🎉\n\n"
        f"شما با موفقیت <b>{target} جذب</b> رو تکمیل کردی!\n"
        "و پورسانت این دوره به مبلغ:🔻\n"
        f"「<b>{fmt_en(amount)} تومان</b>」برات ثبت شد 💰\n"
        "➖•➖•➖\n\n"
    )
    if new_level >= 3:
        nxt = (
            "🔻 <b>همچنین وارد سطح بعدی شدی</b> 🔻\n"
            "🔝ارتقا به:「<b>ادمین سه‌ستاره⭐️⭐️⭐️</b>」\n\n"
        )
    else:
        nxt = (
            "🔻 <b>همچنین وارد سطح بعدی شدی</b> 🔻\n"
            "🔝 ارتقا به:「 <b>ادمین دو ستاره ⭐️⭐️</b> 」\n\n"
        )
    income = (
        "🔻 <b>درآمد سطح جدید:</b> 🔻\n"
        f"💵 هر <b>{new_target} جذب</b>:「<b>{fmt_en(new_amount)} تومان</b>」\n"
        "➖•➖•➖\n\n"
    )
    tail = (
        "📩 بعد از واریز پورسانت، فیش واریزی همینجا برات ارسال میشه…\n"
        "برای دیدن پورسانت‌های قبلیت هم می‌تونی وارد بخش <b>«سوابق پورسانت»</b> شی!\n"
        "➖•➖•➖"
    )
    return rl(done + nxt + income + tail)


def weekly_text() -> str:
    a1, a2, a3 = (fmt_en(level_amount(i)) for i in (1, 2, 3))
    return rl(
        "<b>💡می‌دونستی با هر لول‌آپ</b>\n"
        "<b>می‌تونی درآمدت رو بیشتر کنی؟ 🔥</b>\n"
        "➖➖➖➖➖➖➖➖\n"
        "<b>⭐️ سطح اول: 🔻</b>\n"
        f"「{a1} تومان」 بابت هر دوره\n"
        "<b>⭐️⭐️ سطح دوم:🔻</b>\n"
        f"「{a2} تومان」 بابت هر دوره\n"
        "<b>⭐️⭐️⭐️ سطح سوم:🔻</b>\n"
        f"「{a3} تومان」 بابت هر دوره\n"
        "➖➖➖➖➖➖➖➖\n"
        "<b>🚀 لول‌آپ کن🚀</b>\n"
        "بیشتر درآمد داشته باش و به سطح بعدی برس!"
    )


MAINT_TEXT = rl(
    "<b>❗️ادمین گرامی❗️</b>\n\n"
    "<b>🔧ربات فعلاً در حال تعمیر می‌باشد⚙️</b>\n\n"
    "به‌زودی با قدرت بیشتر به حالت عادی برمی‌گردیم\n\n"
    "نگران نباشید؛ تمامی اطلاعات، جذب‌های ثبت‌شده، سوابق فعالیت و پورسانت‌های شما محفوظ هستند "
    "و هیچ اطلاعاتی حذف یا تغییر داده نمی‌شه. ❤"
)
MAINT_EMOJI = "🛠️"
_maint_seen = {}


async def send_maintenance(bot, chat_id, uid, with_kb=False):
    """دو پیام تعمیرات (متن + 🛠️) ارسال میشه و دو پیام تعمیراتِ قبلیِ همین کاربر پاک میشه.
    with_kb=True: کیبورد منوی اصلی هم روی پیام دوم میاد تا فعال بمونه."""
    kb = admin_reply_menu_kb() if with_kb else None
    m1 = await safe_send(bot, chat_id, MAINT_TEXT)
    m2 = await safe_send(bot, chat_id, MAINT_EMOJI, kb, html_mode=False)
    await replace_tracked(bot, uid, "maint1", m1)
    if with_kb:
        await track_menu_msg(bot, uid, m2, True)  # این پیام حامل کیبورده؛ با پیام‌های بعدی پاک نمیشه
    else:
        await replace_tracked(bot, uid, "maint2", m2)


async def maintenance_reply(bot, chat_id, uid):
    """پیام تعمیرات برای ادمین (حداکثر هر ۲ ثانیه یک بار برای هر نفر؛ چون پیام‌های قبلی پاک میشن چت شلوغ نمیشه)."""
    now = time.monotonic()
    if now - _maint_seen.get(uid, -1000.0) < 2:
        return
    _maint_seen[uid] = now
    if len(_maint_seen) > 5000:
        for k in [k for k, v in _maint_seen.items() if now - v > 60]:
            _maint_seen.pop(k, None)
    a = get_admin(uid)
    await send_maintenance(bot, chat_id, uid, with_kb=False)


# دکمه‌هایی که در حالت تعمیرات هم کار میکنن: مسیر آموزش (برای تازه‌واردها) و بخش ارتباط/پیشنهادات
MAINT_OK_CB = {"t:start", "t:seen", "t:rsp", "t:gr", COMEBACK_CB, "chk", "a:ct", "a:sg", "a:menu", "a:can"}


def is_kb_text(text: str) -> bool:
    return any(text in v for v in RBTN_ALIASES.values())


def owner_hire_text(a, period, total) -> str:
    sep = "➖•➖•➖"
    su_p, su_t = admin_signups(a, period)
    return (f"<b>{sep}\n🔔 جذب جدید ثبت شد 🔔\n{sep}\n"
            f"👤 ادمین جذب{ZW}کننده🔻\n"
            f"{link_profile(a, 24)} {stars_of(a)}\n"
            f"\u25aa\ufe0fکد: {a['code']}\u25aa\ufe0f\n"
            f"{sep}\n"
            f"➕ این دوره ›「 {period} جذب 」\n"
            f"🧲 مجموع جذب{ZW}ها ›「 {total} جذب 」\n"
            f"🪪 ثبت نام این دوره ›「 {su_p} ثبت نام 」\n"
            f"🪪 مجموع ثبت نام ›「 {su_t} ثبت نام 」\n"
            f"{sep}</b>")


def record_hire(applicant_id: int, applicant_name: str, code: int):
    """ثبت اتمیک جذب. هر متقاضی فقط یک بار شمرده می‌شود. خروجی None یعنی ثبت نشد."""
    if applicant_id == OWNER_ID:
        return None
    with tx() as c:
        a = c.execute("SELECT * FROM admins WHERE code=?", (code,)).fetchone()
        if a is None or a["user_id"] == applicant_id:
            return None
        if c.execute("SELECT 1 FROM admins WHERE user_id=?", (applicant_id,)).fetchone():
            return None  # ادمین‌ها به‌عنوان متقاضی شمرده نمی‌شوند
        ts = int(time.time())
        cur = c.execute("INSERT OR IGNORE INTO hires(applicant_id,admin_id,applicant_name,ts) VALUES(?,?,?,?)",
                        (applicant_id, a["user_id"], applicant_name, ts))
        if cur.rowcount == 0:
            return None
        period = a["period_count"] + 1
        total = a["total_count"] + 1
        target, amount, period_no = a["cur_target"], a["cur_amount"], a["period_no"]
        completed = period >= target
        level_up = None
        # سپر خودکار: سطح ۱ در ۲۲، سطح ۲ در ۱۵، سطح ۳ در ۷ جذب (در دوره) سپر مخصوص خودش میگیره و می‌مونه
        shield22 = False
        _lvl = level_of(a)
        if not completed and period >= SHIELD_AT[_lvl] and shield_level_on(_lvl):
            shield22 = bool(c.execute("INSERT OR IGNORE INTO shield_admins(admin_id) VALUES(?)",
                                      (a["user_id"],)).rowcount)
            if shield22:  # فقط سپرِ خودکارِ «22» علامت میخوره تا پایان دوره خاموش بشه (سپر دستی/سراسری دست‌نخورده)
                c.execute("INSERT OR IGNORE INTO shield_auto(admin_id) VALUES(?)", (a["user_id"],))
        if completed and c.execute("SELECT 1 FROM shield_auto WHERE admin_id=?", (a["user_id"],)).fetchone():
            # پایان دوره: سپرِ «22» ریست میشه تا دوره‌ی بعد دوباره در ۲۲ روشن بشه؛ اگه متقاضیِ در انتظار برای
            # این ادمین مونده باشه، سپر می‌مونه تا اون‌ها گم نشن و با تموم شدن‌شون خاموش میشه (shield22_release)
            if not c.execute("SELECT 1 FROM shield_pending WHERE code=?", (a["code"],)).fetchone():
                c.execute("DELETE FROM shield_admins WHERE admin_id=?", (a["user_id"],))
                c.execute("DELETE FROM shield_auto WHERE admin_id=?", (a["user_id"],))
        if completed:
            card = c.execute("SELECT number, holder FROM cards WHERE admin_id=? ORDER BY id DESC LIMIT 1",
                             (a["user_id"],)).fetchone()
            c.execute("INSERT INTO commissions(admin_id,period_no,amount,status,created_at,card_number,card_holder,target,lvl) "
                      "VALUES(?,?,?,?,?,?,?,?,?)",
                      (a["user_id"], period_no, amount, "earned", ts,
                       card["number"] if card else None, card["holder"] if card else None, target, level_of(a)))
            # مبلغ دوره‌ی بعد از روی سطح جدید ادمین تعیین میشه (سطح ۱: pay_amount، سطح ۲: pay_amount_2، ...)
            _cur_lvl = level_of(a)
            nxt_level = min(_cur_lvl + 1, LEVEL_MAX)  # بعد از هر دوره یک سطح بالا؛ ادمینِ افت‌کرده با کامل کردن دوره یک پله برمیگرده
            if nxt_level > _cur_lvl:
                level_up = nxt_level
            new_pen = max(level_for_period(period_no + 1) - nxt_level, 0)
            c.execute("UPDATE admins SET period_count=0,total_count=?,period_no=period_no+1,level_pen=?,"
                      "cur_target=?,cur_amount=?,last_hire_at=? WHERE user_id=?",
                      (total, new_pen, get_int_setting("pay_target"), level_amount(nxt_level), ts, a["user_id"]))
        else:
            c.execute("UPDATE admins SET period_count=?,total_count=?,last_hire_at=? WHERE user_id=?",
                      (period, total, ts, a["user_id"]))
        admin = c.execute("SELECT * FROM admins WHERE user_id=?", (a["user_id"],)).fetchone()
        return {"admin": admin, "period": period, "total": total, "target": target, "amount": amount,
                "completed": completed, "remaining": max(target - period, 0), "level_up": level_up,
                "shield22": shield22}


# ---------------------- لاگ عملیات حساس، بلاک، پاک‌سازی و ضداسپم ----------------------
def save_question(text: str):
    """پیوی اکانت شخصی: هر پیامی که علامت سوال (? یا ؟) داشته باشه فقط متنش ذخیره میشه (بدون نام و کاربر)؛
    هر ۷ روز یه فایل «سوالات متداول» از این‌ها میره Saved Messages."""
    t = (text or "").strip()
    if not t or ("?" not in t and "؟" not in t):
        return
    ex("INSERT INTO faq_questions(ts,text) VALUES(?,?)", (int(time.time()), t[:4000]))


def audit(user_id: int, action: str, detail: str = ""):
    """لاگ عملیات حساس با زمان و شناسه کاربر (جدول audit)."""
    try:
        ex("INSERT INTO audit(ts,user_id,action,detail) VALUES(?,?,?,?)",
           (int(time.time()), user_id, action, (detail or "")[:500]))
    except Exception:  # pragma: no cover
        log.exception("audit failed")


def mark_blocked(uid: int):
    """کاربری که ربات رو بلاک کرده علامت میخوره و از پیام همگانی و آمار کنار میره."""
    try:
        ex("UPDATE admins SET blocked=1 WHERE user_id=?", (uid,))
    except Exception:  # pragma: no cover
        log.exception("mark_blocked failed")


def fix_pinky_counts() -> None:
    """یک بار: عدد ادمین @Pinky_snw میشه «این دوره 17» و «کلا 57»؛ از اون به بعد جذب‌های جدید روی همین عددها اضافه میشن."""
    try:
        if get_setting("fix_pinky_v2") == "1":
            return
        a = q1("SELECT * FROM admins WHERE LOWER(COALESCE(username,''))='pinky_snw'")
        if a is None:
            return
        ex("UPDATE admins SET period_count=17, total_count=57 WHERE user_id=?", (a["user_id"],))
        set_setting("fix_pinky_v2", "1")
        audit(OWNER_ID, "fix_counts", json.dumps({"user_id": a["user_id"], "old_period": a["period_count"],
                                                  "old_total": a["total_count"]}))
    except Exception as e:  # noqa
        log_err(f"fix_pinky_counts: {e!r}")


def reset_training(uid: int):
    ex("UPDATE admins SET training_done=0, training_done_at=NULL, warn_sent=0, warn_at=0, nudge_sent=0, first_sent=0 WHERE user_id=?", (uid,))
    audit(uid, "training_reset")


def remove_admin(uid: int) -> bool:
    """حذف ادمین بدون سابقه؛ کدش برای همیشه رزرو میشه و به ادمین جدید داده نمیشه.
    ادمینی که سابقه جذب یا پورسانت داره هرگز حذف نمیشه تا سوابق حفظ بشن."""
    with tx() as c:
        r = c.execute("SELECT code FROM admins WHERE user_id=?", (uid,)).fetchone()
        if r is None:
            return False
        if (c.execute("SELECT 1 FROM hires WHERE admin_id=?", (uid,)).fetchone()
                or c.execute("SELECT 1 FROM commissions WHERE admin_id=?", (uid,)).fetchone()):
            return False
        c.execute("INSERT OR IGNORE INTO retired_codes(code,user_id,removed_at) VALUES(?,?,?)",
                  (r["code"], uid, int(time.time())))
        c.execute("DELETE FROM admins WHERE user_id=?", (uid,))
        c.execute("DELETE FROM cards WHERE admin_id=?", (uid,))
        c.execute("DELETE FROM state WHERE user_id=?", (uid,))
        c.execute("DELETE FROM tracked WHERE user_id=?", (uid,))
    audit(uid, "admin_removed", "no hires")
    return True


_last_hit = {}


def throttled(uid: int, key: str) -> bool:
    """ضداسپم: زدن پشت‌سرهم همون دکمه در کمتر از ۲ ثانیه نادیده گرفته میشه."""
    now = time.monotonic()
    k = (uid, key)
    last = _last_hit.get(k)
    if last is not None and now - last < THROTTLE_SECS:
        return True
    _last_hit[k] = now
    if len(_last_hit) > 5000:
        for kk in [kk for kk, v in _last_hit.items() if now - v > 60]:
            _last_hit.pop(kk, None)
    return False


_tut_seen = {}


def tut_first_time(q, data: str) -> bool:
    """قفل دکمه‌های آموزش: هر دکمه (روی همون پیام) فقط یک بار اجرا میشه."""
    msg = q.message
    key = (q.from_user.id, msg.message_id if msg else 0, data)
    if key in _tut_seen:
        return False
    _tut_seen[key] = time.time()
    return True


def track_get(uid: int, kind: str):
    return q1("SELECT * FROM tracked WHERE user_id=? AND kind=?", (uid, kind))


def track_set(uid: int, kind: str, chat_id: int, message_id: int, cmd_id: int = None):
    ex("INSERT INTO tracked(user_id,kind,chat_id,message_id,ts,cmd_id) VALUES(?,?,?,?,?,?) "
       "ON CONFLICT(user_id,kind) DO UPDATE SET chat_id=excluded.chat_id, message_id=excluded.message_id, "
       "ts=excluded.ts, cmd_id=excluded.cmd_id", (uid, kind, chat_id, message_id, int(time.time()), cmd_id))


MENU_KINDS = ("menu", "report")


BOT_REF = {}  # ربات اصلی؛ برای پاک کردن آنی پیام‌ها از جاهایی که context ندارن
INSTANT_CMD = set()  # پیام‌های ورودی (مثل آیدی جستجو) که با پاک شدن منو همون لحظه پاک میشن، نه ۳۰ ثانیه بعد


def drop_cmd(chat_id: int, cmd_id: int):
    if cmd_id in INSTANT_CMD:
        INSTANT_CMD.discard(cmd_id)
        if BOT_REF.get("bot") is not None:
            bg(_safe_delete(BOT_REF["bot"], chat_id, cmd_id))
        else:
            schedule_delete(chat_id, cmd_id, 0)
    else:
        schedule_delete(chat_id, cmd_id, CMD_DELETE_DELAY)


def release_cmd(uid: int, message_id: int):
    """منوی شیشه‌ای پاک شد: پیام دستوری که کاربر برای ساخت اون منو فرستاده بود ۳۰ ثانیه بعد پاک میشه."""
    r = q1("SELECT * FROM tracked WHERE user_id=? AND message_id=? AND kind IN ('menu','report')", (uid, message_id))
    if r is not None and r["cmd_id"]:
        drop_cmd(r["chat_id"], r["cmd_id"])
        ex("UPDATE tracked SET cmd_id=NULL WHERE user_id=? AND kind=?", (uid, r["kind"]))


async def replace_tracked(bot, uid: int, kind: str, msg, cmd_id: int = None):
    """پیام جدید ثبت میشه و پیام قبلیِ همون نوع (کامنت، پاسخگویی، ویدیو، گزارش، منو) پاک میشه."""
    if msg is None:
        return
    old = track_get(uid, kind)
    track_set(uid, kind, msg.chat_id, msg.message_id, cmd_id)
    if kind == "kb" and old is not None:
        _te = track_get(uid, "tutend")
        if _te is not None and _te["message_id"] == old["message_id"]:
            old = None  # 💻 پایان آموزش هیچ‌وقت پاک نمیشه؛ حامل کیبورد جدید کنارش میاد
    if old is not None and old["message_id"] != msg.message_id:
        bg(_safe_delete(bot, old["chat_id"], old["message_id"]))
        if kind in MENU_KINDS and old["cmd_id"]:
            drop_cmd(old["chat_id"], old["cmd_id"])


def schedule_delete(chat_id: int, message_id: int, delay: int = STRAY_TTL):
    ex("INSERT INTO cleanup(chat_id,message_id,due) VALUES(?,?,?)", (chat_id, message_id, int(time.time()) + delay))


def menu_due(uid: int, gap: int = MENU_GAP) -> bool:
    last = [r["ts"] for r in (track_get(uid, "main"), track_get(uid, "kb")) if r is not None]
    return not last or int(time.time()) - max(last) >= gap


async def track_menu_msg(bot, uid: int, msg, carries_kb: bool):
    """ثبت پیام منوی اصلی. پیامی که خودِ کیبورد معمولی روشه (حامل) زیر نوع «kb» ثبت میشه و با منوهای بعدی
    پاک نمیشه؛ چون با پاک‌شدن اون پیام، دکمه‌ی باز‌کردن کیبورد کنار فیلد پیام تلگرام هم می‌پره.
    فقط وقتی حامل جدیدی (با کیبورد) فرستاده بشه، حامل قبلی پاک میشه."""
    if msg is None:
        return
    if not carries_kb:
        await replace_tracked(bot, uid, "main", msg)
        return
    old = track_get(uid, "main")
    if old is not None:
        ex("DELETE FROM tracked WHERE user_id=? AND kind='main'", (uid,))
        bg(_safe_delete(bot, old["chat_id"], old["message_id"]))
    await replace_tracked(bot, uid, "kb", msg)


# ---------------------- پورسانت و کارت ----------------------
def save_card(admin_id: int, number: str, holder: str) -> int:
    with tx() as c:
        c.execute("INSERT INTO cards(admin_id,number,holder) VALUES(?,?,?) "
                  "ON CONFLICT(admin_id,number) DO UPDATE SET holder=excluded.holder", (admin_id, number, holder))
        return c.execute("SELECT id FROM cards WHERE admin_id=? AND number=?", (admin_id, number)).fetchone()["id"]


def create_request(admin_id: int, cid: int, number: str, holder: str) -> bool:
    """تبدیل اتمیک earned -> requested؛ درخواست تکراری برای یک دوره ناموفق می‌شود."""
    with tx() as c:
        cur = c.execute(
            "UPDATE commissions SET status='requested', card_number=?, card_holder=?, requested_at=? "
            "WHERE id=? AND admin_id=? AND status='earned'",
            (number, holder, int(time.time()), cid, admin_id))
        return cur.rowcount == 1


def mark_paid(cid: int, ts: int, file_id: str, kind: str, amount: int) -> bool:
    with tx() as c:
        cur = c.execute(
            "UPDATE commissions SET status='paid', paid_at=?, paid_day=?, paid_amount=?, receipt_file_id=?, "
            "receipt_kind=? WHERE id=? AND status='requested'",
            (ts, day_key(ts), amount, file_id, kind, cid))
        return cur.rowcount == 1


# ----------------------------------------------------------------------------
# کیبوردها
# ----------------------------------------------------------------------------
def B(text, cb=None, url=None, copy=None, style=None):
    kw = {}
    if COLOR_BUTTONS and style:
        kw["api_kwargs"] = {"style": style}  # primary(آبی) / success(سبز) / danger(قرمز)
    if url:
        return InlineKeyboardButton(text, url=url, **kw)
    if copy:
        return InlineKeyboardButton(text, copy_text=CopyTextButton(text=copy), **kw)
    return InlineKeyboardButton(text, callback_data=cb, **kw)


def onoff_label(name: str, on: bool) -> str:
    """متن دکمه‌ی خاموش/روشن: «اسم | ON 🟢» یا «اسم | OFF 🔘»."""
    return f"{name} | {'ON 🟢' if on else 'OFF 🔘'}"


def onoff_btn(name: str, on: bool, cb: str):
    """دکمه‌ی خاموش/روشن: روشن سبز، خاموش قرمز."""
    return B(onoff_label(name, on), cb, style="success" if on else "danger")


def KB(*rows):
    return InlineKeyboardMarkup([list(r) if isinstance(r, (list, tuple)) else [r] for r in rows])


def BACK(cb):
    # بخش‌های مدیریت (o:) بیرنگ؛ بخش ادمین‌ها مثل قبل قرمز
    return B(BTN_BACK, cb, style=None if str(cb).startswith("o:") else "danger")


def BACK_PLAIN(cb):
    """بازگشتِ بیرنگ (زیر محتوای تقلب‌ها برای ادمین)."""
    return B(BTN_BACK, cb)


def BACK_G(cb):
    """بازگشتِ سبز (فقط تنظیمات پیشرفته و گزارش خطاها)."""
    return B(BTN_BACK, cb, style=None if str(cb).startswith("o:") else "success")


def MAIN(cb="a:menu"):
    """بازگشت به منوی اصلی؛ فقط جاهایی که واقعا لازمه."""
    return B(BTN_MAIN, cb, style="danger")


def cyc(i: int, *styles) -> str:
    """رنگ‌ها نوبتی میان تا لیست‌ها فقط آبی و سبز نباشن."""
    return styles[i % len(styles)]


def nav_row(make_cb, page, pages, plain=False):
    row = []
    if page > 0:
        row.append(B("◀️ قبلی ◀️", make_cb(page - 1), style=None if plain else "danger"))
    if page < pages - 1:
        row.append(B("▶️ بعدی ▶️", make_cb(page + 1), style=None if plain else "success"))
    return row


def admin_menu_kb():
    return KB(
        B(BTN_A_REPORT, "a:rep", style="danger"),
        B(BTN_A_COMMENT, "a:cmt", style="primary"),
        B(BTN_A_REPLY, "a:rsp", style="primary"),
        B(BTN_A_VIDEO, "a:vid", style="primary"),
        B(BTN_A_RECORDS, "a:rec", style="success"),
        B(BTN_A_CONTACT, url=CONTACT_URL, style="success"),
    )


def RB(text, style=None):
    """دکمه کیبورد معمولی؛ رنگ از طریق فیلد style در Bot API (آبی primary / سبز success / قرمز danger)."""
    if COLOR_BUTTONS and style:
        return KeyboardButton(text, api_kwargs={"style": style})
    return KeyboardButton(text)


def contact_menu_kb():
    return KB(B("👔 ارتباط با کارفرما 👔", url=CONTACT_URL, style="success"),
              B("💡 پیشنهادات و انتقادات 💡", "a:sg", style="primary"),
              BACK("a:menu"))


def admin_reply_menu_kb():
    return ReplyKeyboardMarkup(
        [
            [RB(RBTN_REPORT, "danger")],
            [RB(RBTN_COMMENT, "primary"), RB(RBTN_REPLY, "primary")],
            [RB(RBTN_VIDEO, "primary")],
            [RB(RBTN_CONTACT, "success"), RB(RBTN_RECORDS, "success")],
            [RB(RBTN_CLEAN, "danger"), RB(RBTN_CHEAT, "primary")],
        ],
        resize_keyboard=True,
        is_persistent=True,  # بعد از پنل فعال شد هیچ‌وقت خودکار مخفی نمیشه
    )


CHEAT_HOLDER = "🃏"                      # اموجی نگه‌دارنده‌ی منوی تقلب (پیام بالای منو)
_CK_SEP = "➖•" * 9
CHEAT_MENU_TEXT = (  # متن منوی تقلب (ادمین)؛ HTML
    f"{_CK_SEP}\n"
    "<b>🃏 ترفندهای جذب چندبرابری🃏</b>\n"
    f"{_CK_SEP}\n\n"
    "در این بخش، روش‌های مختلفی برای جذب سریع‌تر و چندبرابری آماده کردیم که "
    "<b>همگی توسط ادمین‌های دیگه تست شدن و نتیجه‌بخش بودن.</b>\n\n"
    "هرکدوم از این روش‌ها می‌تونه به‌تنهایی جذب‌هاتون رو افزایش بده؛ اما برای رسیدن به نهایت سرعت جذب، "
    "می‌تونید <b>همه روش‌ها رو هم‌زمان اجرا کنید.</b>\n"
    f"{_CK_SEP}"
)
CHEAT_EMPTY_TEXT = "هنوز تقلبی توسط کارفرما ثبت نشده."


def cheat_admin_kb():
    """منوی شیشه‌ای تقلب برای ادمین: یک دکمه برای هر تقلبی که کارفرما اضافه کرده (به ترتیب ساخت)؛ تقلبِ بدون متن نمیاد."""
    btns = [B(str(c["name"])[:CHEAT_NAME_MAX], f"a:ckv:{c['id']}", style="primary")
            for c in cheat_list() if c["kind"] == "ad" or (c["text"] or "").strip()]
    return KB(*btns, BACK("a:menu")) if btns else None


def ad_title_for_view(uid: int) -> int:
    """عنوان آگهی‌ای که ادمین موقع باز کردن «تقلب آگهی» از منو میبینه: آخرین عنوانی که گرفته؛ اگه هنوز نگرفته یکی
    انتخاب و ثبت میشه تا بعداً هم تکراری برای همین نفر نره."""
    r = q1("SELECT title_idx FROM cheat_ad_titles WHERE user_id=? ORDER BY ts DESC, cycle DESC LIMIT 1", (uid,))
    if r is not None and 0 <= int(r["title_idx"]) < len(AD_TITLES):
        return int(r["title_idx"])
    idx, cyc = ad_pick_title(uid)
    ex("INSERT OR IGNORE INTO cheat_ad_titles(user_id,title_idx,cycle,ts) VALUES(?,?,?,?)", (uid, idx, cyc, int(time.time())))
    return idx


_bg_tasks = set()


def bg(coro):
    """اجرا در پس‌زمینه؛ جواب کاربر منتظر پاک‌کردن پیام‌ها نمی‌مونه."""
    t = asyncio.ensure_future(coro)
    _bg_tasks.add(t)
    t.add_done_callback(_bg_tasks.discard)
    return t


async def _drop_alert_emoji(bot, chat_id, message_id):
    """متن هشدار پاک شد: 🚨 تکیِ بالاش هم همون لحظه پاک میشه."""
    try:
        r = q1("SELECT emoji_id FROM alert_pairs WHERE chat_id=? AND alert_id=?", (chat_id, message_id))
        if r is None:
            return
        ex("DELETE FROM alert_pairs WHERE chat_id=? AND alert_id=?", (chat_id, message_id))
        try:
            await bot.delete_message(chat_id, r["emoji_id"])
        except TelegramError:
            pass  # از قبل پاک شده یا پاک شدنش به صف پاکسازی (cleanup) سپرده شده
    except Exception as e:  # noqa
        log_err(f"drop_alert_emoji: {e!r}")


async def _safe_delete(bot, chat_id, message_id):
    ok = await _safe_delete_one(bot, chat_id, message_id)
    if ok:
        await _drop_alert_emoji(bot, chat_id, message_id)
    return ok


async def _safe_delete_one(bot, chat_id, message_id):
    try:
        if q1("SELECT 1 FROM tracked WHERE chat_id=? AND message_id=? AND kind='kb'", (chat_id, message_id)):
            return True  # حامل کیبورد (آیکن کنار فیلد پیام) دست‌نخورده می‌مونه
    except Exception:  # noqa
        pass
    try:
        await bot.delete_message(chat_id, message_id)
        return True
    except BadRequest as e:
        msg = str(e).lower()
        # اگر پیام از قبل پاک شده یا دیگر وجود ندارد، عملیات از نظر پاک‌سازی تمام است.
        if ("message to delete not found" in msg or "message_id_invalid" in msg
                or "message can't be deleted" in msg or "48 hours" in msg):
            return True
        log_err(f"delete message failed chat={chat_id} message={message_id}: {e!r}")
        return False
    except TelegramError as e:
        log_err(f"delete message failed chat={chat_id} message={message_id}: {e!r}")
        return False


async def _del_msg(m):
    try:
        await m.delete()
    except TelegramError:
        pass


async def del_cmd(m):
    """متن دکمه‌ای که کاربر زده بلافاصله پاک میشه تا فقط نتیجه بمونه (در پس‌زمینه، بدون معطلی)."""
    bg(_del_msg(m))


async def hide_reply_keyboard(bot, chat_id, uid: int):
    """از شروع آموزش تا «پنل شما فعال شد» کیبورد مخفیه؛ اگه از قبل (مثلا قبل از شروع مجدد) کیبورد داشت جمعش میکنه."""
    r = track_get(uid, "kb")
    if r is None:
        return
    ex("DELETE FROM tracked WHERE user_id=? AND kind IN ('kb','main')", (uid,))
    try:
        hint = await bot.send_message(chat_id, "چه کاری انجام بدم واست ادمین عزیز؟🤖", reply_markup=ReplyKeyboardRemove())
        track_set(uid, "kbhint", hint.chat_id, hint.message_id)  # با زدن اولین دکمه‌ی آموزش پاک میشه
    except TelegramError as e:
        log_err(f"hide keyboard {uid}: {e!r}")
    bg(_safe_delete(bot, r["chat_id"], r["message_id"]))


async def send_reply_keyboard(bot, chat_id, carrier=None):
    """نمایش کیبورد معمولی. بدون carrier از پیام نامرئی استفاده میشه؛ با carrier همون متن (مثل 💻) فرستاده میشه."""
    last = None
    for txt in ([carrier] if carrier else KB_CARRIER_CANDIDATES):
        try:
            msg = await bot.send_message(chat_id=chat_id, text=txt, reply_markup=admin_reply_menu_kb())
            await track_menu_msg(bot, chat_id, msg, True)
            return msg
        except TelegramError as e:
            last = e
            log_err(f"reply keyboard carrier {txt!r} failed: {e!r}")
    if last:
        raise last


def bot_status_line() -> str:
    return "🔴 ربات خاموشه" if bot_off() else "🟢 ربات روشنه"


OWNER_MENU_EMOJIS = ("🤖", "👾", "🌟", "🧨", "💣", "🚀", "⚡️", "💸")


def owner_menu_text() -> str:
    """متن منوی مدیر (حامل کیبورد): فقط یک اموجی تکی که هر بار رندوم از این لیست میاد."""
    return random.choice(OWNER_MENU_EMOJIS)


OWNER_EXTRA_KINDS = ("ownemoji", "ownsep", "owncount")


def admins_total_count() -> int:
    """عدد ممبرهای بالای منوی مدیر: همه‌ی کسایی که تا حالا به «پنل شما فعال شد» رسیدن
    (ادمین‌های فعلی که آموزش رو تموم کردن + ادمین‌های حذف‌شده‌ی بی‌جذب). هر بار زنده از دیتابیس شمرده میشه."""
    a = q1("SELECT COUNT(*) n FROM admins WHERE counted=1 AND user_id<>?", (OWNER_ID,))
    r = q1("SELECT COUNT(*) n FROM retired_codes")
    return int(a["n"] if a else 0) + int(r["n"] if r else 0)


def members_count() -> int:
    r = q1("SELECT COUNT(*) n FROM members WHERE user_id<>?", (OWNER_ID,))
    return int(r["n"]) if r is not None else 0


OWNER_COUNT_PAD = 8  # تعداد فاصله‌ی نامرئی دو طرف عدد؛ بیشتر = عدد بیشتر میره وسط (برای تنظیم دقیق‌تر عوضش کن)


def centered_count_text(n: int) -> str:
    """عدد ممبرها با فاصله‌ی نامرئی (U+2800) دو طرفش تا زیر وسط متن منو بیفته، نه گوشه."""
    return keycap_digits(n)  # بدون فاصله‌ی اضافه


def keycap_digits(n: int) -> str:
    """عدد با اموجی‌های عددی: 32 -> 3️⃣2️⃣"""
    return "".join(d + "\ufe0f\u20e3" for d in str(n))


async def drop_owner_emoji(bot):
    """👾 و ➖➖➖ و اموجی عددی زیر منوی مدیر؛ همراه منو پاک میشن."""
    for kind in OWNER_EXTRA_KINDS:
        r = track_get(OWNER_ID, kind)
        if r is not None:
            ex("DELETE FROM tracked WHERE user_id=? AND kind=?", (OWNER_ID, kind))
            bg(_safe_delete(bot, r["chat_id"], r["message_id"]))


# اموجی نگه‌دارنده‌ی مخصوص هر بخش تنظیمات (پیام بالای منو)؛ منوهایی که اینجا نیستن همون عدد اعضا رو نگه می‌دارن
OWNER_HOLDER_RULES = (
    (re.compile(r"^o:ntf(:|$)"), "📳"),
    (re.compile(r"^o:(shm|shd|sh22)$"), "🛡️"),
    (re.compile(r"^o:vid[ts]?$"), "🎬"),
    (re.compile(r"^o:(ch|cha|cht|chd)$"), "📢"),
    (re.compile(r"^o:cyt?$"), "📺"),
    (re.compile(r"^o:offy$"), "🔌"),
    (re.compile(r"^o:(sts:\d+|stm|std:.+)$"), "🧮"),
    (re.compile(r"^o:(com|comamt|comamt2|comamt3|comtgt|dl)$"), "💰"),
    (re.compile(r"^o:erc?$"), "🐞"),
    (re.compile(r"^o:(tsm|tst|rsd)$"), "🧪"),
    (re.compile(r"^o:au(:|$)"), "🤖"),
    (re.compile(r"^o:(ac|actg|acl|aca|act)$|^o:acd:"), "💭"),
)


# بخشی که مدیر الان توشه: کلید دکمه‌ای که زده (o:...) یا وضعیت ورودی متنی (st:...)؛ اموجی نگه‌دارنده از روی همین
# تعیین میشه، نه از روی شکل دکمه‌های صفحه (که باعث قاطی شدن اموجی‌ها میشد).
_CUR_KEY = contextvars.ContextVar("owner_cur_key", default="")
_nav_lock_obj = None


def nav_lock():
    """قفل ناوبری مدیر: با concurrent_updates دو کلیک پشت‌سرهم نباید همزمان نگه‌دارنده/منو بسازن (اموجی تکراری می‌موند)."""
    global _nav_lock_obj
    if _nav_lock_obj is None:
        _nav_lock_obj = asyncio.Lock()
    return _nav_lock_obj


SECTION_HOLDERS = (
    (re.compile(r"^o:ntf(:|$)"), "📳"),
    (re.compile(r"^o:(shm|shd|sh22)$"), "🛡️"),
    (re.compile(r"^o:vid[ts]?$|^st:vid$"), "🎬"),
    (re.compile(r"^o:(ch|cha|cht|chd)$|^st:ch[123]$"), "📢"),
    (re.compile(r"^o:cyt?$"), "📺"),
    (re.compile(r"^o:(off|offy|on)$"), "🔌"),
    (re.compile(r"^o:(sts:\d+|stm|std:.+|st|stl)$|^st:stdate$"), "🧮"),
    (re.compile(r"^o:(com|comamt|comamt2|comamt3|comtgt)$|^st:(amt|amt2|amt3|tgt)$"), "💰"),
    (re.compile(r"^o:erc?$"), "🐞"),
    (re.compile(r"^o:(tsm|tst|tst1:.+|tst2:.+|rsd|rsd:y.*)$|^st:(tst|rsd)$"), "🧪"),
    (re.compile(r"^o:au(:|$)|^st:au(9|r|a|v1|v2)$"), "🤖"),
    (re.compile(r"^o:(ac|actg|acl|aca|act)$|^o:acd:|^st:ac[12]$"), "💭"),
    (re.compile(r"^o:(adv|bk|bki:\d+|rst|rst:y)$|^st:(rst|rst_ok)$"), "💻"),
    (re.compile(r"^o:ck(:|$)|^st:ck[AE]_\w+$"), "🃏"),
)


def _section_of(key: str):
    for rx, em in SECTION_HOLDERS:
        if rx.match(key or ""):
            return em
    return None


def _kb_cbs(kb) -> set:
    cbs = set()
    try:
        for row in (kb.inline_keyboard if kb is not None else ()):
            for b in row:
                d = getattr(b, "callback_data", None)
                if d:
                    cbs.add(d)
    except Exception:  # noqa
        return set()
    return cbs


_PAGED = re.compile(r"^o:(rep|fd|fu|sts):")


def same_screen(q, kb) -> bool:
    """دکمه روی همون صفحه کار میکنه (روشن/خاموش، صفحه‌بندی)؛ پس همون‌جا ویرایش میشه. غیر از این (رفتن به صفحه‌ی دیگه
    یا بازگشت) منوی جدید پایین چت میاد و قبلی با اموجیش پاک میشه."""
    try:
        old = _kb_cbs(q.message.reply_markup)
    except Exception:  # noqa
        return False
    new = _kb_cbs(kb)
    if old == new:
        return True
    d = q.data or ""
    return bool(_PAGED.match(d)) and "o:noop" in old and "o:noop" in new


def owner_holder_for(kb=None, explicit=None, sync: bool = False):
    """متن پیام نگه‌دارنده‌ی بالای منو. عدد اعضا فقط برای منوی اولِ تنظیمات؛ بقیه اموجی بخش خودشون.
    sync=True (ویرایش درجا): اگه بخش مشخص نبود None برمیگردونه تا نگه‌دارنده‌ی فعلی دست‌نخورده بمونه."""
    if explicit:
        return explicit
    _c = _kb_cbs(kb)
    if {"o:ntf", "o:shm"} <= _c:  # منوی اولِ تنظیمات: فقط اینجا عدد اعضا
        return centered_count_text(admins_total_count())
    if {"o:com", "o:au"} <= _c:  # تنظیمات پیشرفته
        return "💻"
    sec = _section_of(_CUR_KEY.get())
    if sec:
        return sec
    if sync:
        return None
    found = set()
    try:
        for row in (kb.inline_keyboard if kb is not None else ()):
            for b in row:
                d = getattr(b, "callback_data", None)
                if not d:
                    continue
                for rx, em in OWNER_HOLDER_RULES:
                    if rx.match(d):
                        found.add(em)
                        break
    except Exception:  # noqa
        found = set()
    if len(found) == 1:
        return next(iter(found))
    if sync:
        return None  # بخش نامشخص: نگه‌دارنده‌ی فعلی دست‌نخورده می‌مونه (اموجی رندوم هر بار عوض نشه)
    return random.choice(OWNER_MENU_EMOJIS)  # بقیه‌ی منوها: اموجی رندوم، نه عدد اعضا


async def owner_holder_sync(bot, text):
    """منو سر جاش ویرایش شده (پیام جدید نیومده): پیام نگه‌دارنده‌ی بالاش هم به اموجی این بخش عوض میشه."""
    if not text:
        return
    r = track_get(OWNER_ID, "owncount")
    if r is None:
        return
    try:
        await bot.edit_message_text(text, chat_id=r["chat_id"], message_id=r["message_id"])
    except BadRequest as e:
        if "not modified" not in str(e).lower():
            log_err(f"owner holder sync failed: {e!r}")
    except TelegramError as e:
        log_err(f"owner holder sync failed: {e!r}")


async def owner_count_swap(bot, chat_id, holder=None):
    """قبل از هر صفحه‌ی منوی مدیر (پیام جدید): اول پیام نگه‌دارنده (اموجی مخصوص بخش یا عدد ممبرها) میاد، بعد صفحه؛ قبلی پاک میشه.
    - بخش‌ها: اموجی بخش خودش حامل کیبورد میشه و اموجی رندومِ منوی اصلی پاک میشه (دو اموجی توی صفحه نمی‌مونه).
    - منوی اولِ تنظیمات (عدد ممبرها): اموجی رندوم (حامل کیبورد) بالای اموجی عدد ممبر میاد."""
    old = track_get(OWNER_ID, "owncount")
    is_count = holder is None or "\u20e3" in str(holder)
    try:
        if is_count:
            rnd = await bot.send_message(chat_id, owner_menu_text(), reply_markup=owner_reply_menu_kb(), parse_mode=H)
            await track_menu_msg(bot, OWNER_ID, rnd, True)  # حامل قبلی (اموجی بخش یا رندوم قبلی) پاک میشه
            m = await bot.send_message(chat_id, holder or centered_count_text(admins_total_count()))
        else:
            # حامل کیبورد: همین اموجی بخش؛ اموجی رندومِ قبلی با track_menu_msg پاک میشه ولی کیبورد نمی‌پره
            m = await bot.send_message(chat_id, holder, reply_markup=owner_reply_menu_kb())
            await track_menu_msg(bot, OWNER_ID, m, True)
    except TelegramError as e:
        log_err(f"owner count failed: {e!r}")
        return
    track_set(OWNER_ID, "owncount", m.chat_id, m.message_id)
    if old is not None and old["message_id"] != m.message_id:
        bg(_safe_delete(bot, old["chat_id"], old["message_id"]))


async def send_owner_extras(bot, chat_id):
    """زیر متن منوی مدیر (استارت/بازگشت): 👾. عدد ممبرها اینجا نمیاد؛ فقط قبل صفحه‌های منو میاد."""
    for kind, txt in ():  # دیگه 👾 جدا نمیاد؛ خود منو یک اموجی رندومه
        try:
            m = await bot.send_message(chat_id, txt)
            track_set(OWNER_ID, kind, m.chat_id, m.message_id)
        except TelegramError as e:
            log_err(f"owner extra {kind} failed: {e!r}")


def owner_menu_kb():
    return KB(
        B("📊 گزارش جذب 📊", "o:rep:top:0", style="primary"),
        B("💰 مدیریت مالی 💰", "o:fin", style="success"),
        B("📢 پیام همگانی 📢", "o:bc", style="primary"),
        B("🔎 جستجوی ادمین 🔎", "o:sr", style="primary"),
        B("🕹️ تنظیمات 🕹️", "o:set", style="primary"),
        *([B(ORBTN_GO, "o:go", style="success")] if get_setting("owner_go_btn") == "1" else []),
    )


def owner_reply_menu_kb():
    """منوی اصلی کارفرما: کیبورد معمولی ماندگار با رنگ‌های قرمز، سبز و آبی."""
    rows = [
        [RB(ORBTN_REPORT, "primary")],
        [RB(ORBTN_FIN, "success")],
        [RB(ORBTN_BC, "primary"), RB(ORBTN_SEARCH, "primary")],
        [RB(ORBTN_CLEAN, "danger"), RB(ORBTN_SET, "primary")],
    ]
    if get_setting("owner_go_btn") == "1":
        rows.append([RB(ORBTN_GO, "success")])  # تا وقتی از تنظیمات پاکش نکنی میمونه
    return ReplyKeyboardMarkup(rows, resize_keyboard=True, one_time_keyboard=False, is_persistent=True)


# ----------------------------------------------------------------------------
# ارسال و ویرایش پیام
# ----------------------------------------------------------------------------
_PROFILE_HREF = re.compile(r'<a href="(https://t\.me/[^"]+)">')


def preview_opts(text, html_mode=True, preview=None):
    """پریویو پروفایل: وقتی متن دقیقاً یک لینک پروفایل داره همیشه نشون داده میشه؛
    در لیست‌ها (چند لینک) یا وقتی preview=False باشه خاموشه."""
    if not html_mode:
        return None
    if preview is False:
        return LinkPreviewOptions(is_disabled=True)
    urls = list(dict.fromkeys(_PROFILE_HREF.findall(text or "")))
    if len(urls) == 1:
        return LinkPreviewOptions(url=urls[0])
    if len(urls) > 1:
        return LinkPreviewOptions(is_disabled=True)
    return None


def _strip_html(t: str) -> str:
    return html.unescape(re.sub(r"</?[a-zA-Z][^>]*>", "", t or ""))


_last_sent = {}  # آخرین پیام (با send) که برای هر چت فرستاده شده؛ برای فهمیدن اینکه منوی کارفرما هنوز پایین چته یا نه


async def send(bot, chat_id, text, kb=None, html_mode=True, preview=None):
    try:
        m = await bot.send_message(chat_id=chat_id, text=text, reply_markup=kb,
                                   parse_mode=H if html_mode else None,
                                   link_preview_options=preview_opts(text, html_mode, preview))
    except BadRequest as e:
        if html_mode and "parse entities" in str(e).lower():
            # متن (مثلا متن ویرایش‌شده‌ی قدیمی) فرمت نامعتبر داشت: بدون فرمت ارسال میشه تا پیام گم نشه
            m = await bot.send_message(chat_id=chat_id, text=_strip_html(text), reply_markup=kb)
        else:
            raise
    if m is not None and chat_id == OWNER_ID:
        _last_sent[chat_id] = max(_last_sent.get(chat_id, 0), m.message_id)
    return m


async def safe_send(bot, chat_id, text, kb=None, html_mode=True, preview=None):
    try:
        return await send(bot, chat_id, text, kb, html_mode, preview)
    except RetryAfter as e:
        await asyncio.sleep(e.retry_after + 1)
        try:
            return await send(bot, chat_id, text, kb, html_mode, preview)
        except Exception as e2:  # noqa
            log_err(f"send retry to {chat_id}: {e2!r}")
    except Forbidden as e:
        mark_blocked(chat_id)
        log_err(f"send to {chat_id}: blocked ({e!r})")
    except Exception as e:  # noqa
        log_err(f"send to {chat_id}: {e!r}")
    return None


class loading:
    """لودینگ ⏳ (ایموجی متحرک) برای عملیات پردازشی؛ بعد از پایان پردازش پاک میشه."""

    def __init__(self, bot, chat_id):
        self.bot, self.chat_id, self.msg = bot, chat_id, None

    async def __aenter__(self):
        try:
            self.msg = await self.bot.send_message(self.chat_id, "⏳")
        except TelegramError:
            self.msg = None
        return self

    async def __aexit__(self, exc_type, exc, tb):
        if self.msg is not None:
            try:
                await self.bot.delete_message(self.chat_id, self.msg.message_id)
            except TelegramError:
                pass
        return False


async def show(update: Update, context, text, kb=None, html_mode=True, preview=None, fresh: bool = False, holder=None):
    """برای مدیر زیر قفل ناوبری اجرا میشه تا کلیک‌های پشت‌سرهم اموجی/منوی تکراری نسازن."""
    if update.effective_user is not None and update.effective_user.id == OWNER_ID:
        async with nav_lock():
            return await _show_impl(update, context, text, kb, html_mode, preview, fresh, holder)
    return await _show_impl(update, context, text, kb, html_mode, preview, fresh, holder)


async def _show_impl(update: Update, context, text, kb=None, html_mode=True, preview=None, fresh: bool = False, holder=None):
    """اگر از دکمه آمده، همان پیام ویرایش می‌شود (چت خلوت می‌ماند)؛ وگرنه پیام جدید.
    fresh=True: دکمه زیر یک متن ثابت (مثل پیام تبریک) بوده؛ اون پیام دست‌نخورده می‌مونه و مرحله‌ی بعد
    به‌صورت پیام جدید پایین چت میاد (مرحله‌های بعدی همون روند روی همین پیام جدید ویرایش میشن).
    مدیر: رفتن به صفحه‌ی دیگه یا بازگشت = اموجی+منوی جدید پایین چت و منوی قبلی با اموجیش پاک میشه؛
    فقط دکمه‌هایی که روی همون صفحه کار میکنن (روشن/خاموش، صفحه‌بندی) همون‌جا ویرایش میشن."""
    q = update.callback_query
    _own = update.effective_user is not None and update.effective_user.id == OWNER_ID
    if fresh and q and q.message:
        if _own:
            await owner_count_swap(context.bot, update.effective_chat.id, owner_holder_for(kb, holder))
        msg = await send(context.bot, update.effective_chat.id, text, kb, html_mode, preview)
        await replace_tracked(context.bot, update.effective_user.id, "menu", msg)
        return msg
    if (q and q.message and _own
            and (q.message.message_id < _last_sent.get(q.message.chat_id, 0) or not same_screen(q, kb))):
        # صفحه‌ی دیگه / بازگشت / بعد از این منو پیام جدید اومده: اموجی و منوی تازه پایین چت میان و قدیمی‌ها پاک میشن
        old_id = q.message.message_id
        await owner_count_swap(context.bot, update.effective_chat.id, owner_holder_for(kb, holder))
        msg = await send(context.bot, update.effective_chat.id, text, kb, html_mode, preview)
        release_cmd(update.effective_user.id, old_id)
        try:
            await context.bot.delete_message(update.effective_chat.id, old_id)
        except TelegramError:
            pass
        await replace_tracked(context.bot, update.effective_user.id, "menu", msg)
        return msg
    if q and q.message:
        try:
            await q.edit_message_text(text, reply_markup=kb, parse_mode=H if html_mode else None,
                                      link_preview_options=preview_opts(text, html_mode, preview))
            if _own:
                await owner_holder_sync(context.bot, owner_holder_for(kb, holder, sync=True))
            return
        except BadRequest as e:
            if "not modified" in str(e).lower():
                if _own:
                    await owner_holder_sync(context.bot, owner_holder_for(kb, holder, sync=True))
                return
        release_cmd(update.effective_user.id, q.message.message_id)
        try:
            await q.message.delete()
        except TelegramError:
            pass
    if _own:
        await owner_count_swap(context.bot, update.effective_chat.id, owner_holder_for(kb, holder))
    msg = await send(context.bot, update.effective_chat.id, text, kb, html_mode, preview)
    if not q:
        # منوی شیشه‌ای جدید (از دکمه‌های کیبوردی): منوی شیشه‌ای قبلی بلافاصله پاک میشه
        em = update.effective_message
        cmd = None  # متن دکمه کیبورد همون لحظه پاک شده
        await replace_tracked(context.bot, update.effective_user.id, "menu", msg, cmd_id=cmd)
    else:
        # دکمه روی پیام غیرمتنی (مثل فیش عکس‌دار) زده شده و ویرایش ممکن نبود: منوی قبلیِ بالای فیش هم پاک میشه
        await replace_tracked(context.bot, update.effective_user.id, "menu", msg)
    return msg


async def send_media(bot, chat_id, kind, file_id, caption=None, kb=None, html_mode=False, spoiler=False):
    async def go(cap, pm):
        kw = dict(caption=cap, reply_markup=kb, parse_mode=pm)
        if kind == "photo":
            if spoiler:
                kw["has_spoiler"] = True  # تاری خودکار تلگرام برای عکس سطحِ قفل
            return await bot.send_photo(chat_id, file_id, **kw)
        if kind == "video":
            return await bot.send_video(chat_id, file_id, **kw)
        return await bot.send_document(chat_id, file_id, **kw)
    try:
        return await go(caption, H if html_mode else None)
    except BadRequest as e:
        if html_mode and caption and "parse entities" in str(e).lower():
            return await go(_strip_html(caption), None)
        raise


def receipt_caption_for_admin(c) -> str:
    amt = c["paid_amount"] or c["amount"]
    return ("<b>💸 واریز پورسانت 💸</b>\n\n"
            "پورسانت شما با موفقیت واریز شد\n\n"
            f"💰 <b>مبلغ</b>:「{fmt_toman_fa(amt)}」\n\n"
            f"📅 <b>تاریخ</b>: {jdate(c['paid_at'])}\n"
            f"🕒 <b>ساعت</b>: {jtime(c['paid_at'])}")


# ----------------------------------------------------------------------------
# عضویت اجباری کانال
# ----------------------------------------------------------------------------
def channel_active() -> bool:
    return get_setting("channel_enabled") == "1" and bool(get_setting("channel_id"))


async def is_member(bot, user_id: int) -> bool:
    if not channel_active():
        return True
    try:
        m = await bot.get_chat_member(chat_id=int(get_setting("channel_id")), user_id=user_id)
    except Exception as e:  # noqa
        log_err(f"membership check failed: {e!r}")
        return True  # اگر ربات نتواند بررسی کند، کاربر قفل نشود
    if m.status in ("member", "administrator", "creator"):
        return True
    return m.status == "restricted" and bool(getattr(m, "is_member", False))


async def gate(update: Update, context) -> bool:
    uid = update.effective_user.id
    if uid == OWNER_ID or await is_member(context.bot, uid):
        return True
    kb = KB(B(get_setting("channel_btn") or "📢 عضویت در کانال 📢", url=get_setting("channel_link"), style="primary"),
            B("✅ بررسی عضویت ✅", "chk", style="success"))
    text = get_setting("channel_guide") or "برای ادامه ابتدا در کانال عضو شو."
    q = update.callback_query
    if q:
        try:
            await q.answer()
        except TelegramError:
            pass
    await send(context.bot, update.effective_chat.id, text, kb, html_mode=False)
    return False


# ----------------------------------------------------------------------------
# مسیر ادمین
# ----------------------------------------------------------------------------
async def send_admin_menu(context, chat_id, show_kb: bool = True):
    """متن منوی اصلی ادمین؛ منوی اصلی قبلی پاک میشه. کیبورد فقط با show_kb=True (مثل /start) خودش باز میشه."""
    msg = await context.bot.send_message(chat_id, ADMIN_MENU_TEXT,
                                         reply_markup=admin_reply_menu_kb() if show_kb else None)
    await track_menu_msg(context.bot, chat_id, msg, show_kb)


# ---------------------- تست تجربه‌ی اولین ورود ادمین (دکمه‌ی «راه‌اندازی» کارفرما) ----------------------
_preview = {}


def preview_admin() -> dict:
    """ادمین نمایشی برای تست: هیچ ردیفی تو دیتابیس ساخته نمیشه و هیچ کدی مصرف نمیشه؛ کد فقط یه کد آزاده."""
    code = _preview.get("code")
    if code is None:
        with tx() as c:
            code = alloc_code(c)
        _preview["code"] = code
    return {"user_id": OWNER_ID, "code": code, "first_name": OWNER_NAME, "last_name": "", "username": None,
            "period_no": 1, "period_count": 0, "total_count": 0, "training_done": 0,
            "cur_target": get_int_setting("pay_target"), "cur_amount": level_amount(1)}


async def owner_back_after_test(context, chat_id):
    """بعد از «پنل فعال شد» ده ثانیه کیبورد ادمین دیده میشه، بعد منوی کارفرما با کیبورد خودش برمیگرده."""
    await asyncio.sleep(10)
    try:
        await drop_owner_emoji(context.bot)
        msg = await context.bot.send_message(chat_id, "🧪 تست راه‌اندازی تموم شد…\n\n" + owner_menu_text(),
                                             reply_markup=owner_reply_menu_kb(), parse_mode=H)
        await track_menu_msg(context.bot, OWNER_ID, msg, True)
        await send_owner_extras(context.bot, chat_id)
    except Exception as e:  # noqa
        log_err(f"owner back after test: {e!r}")


async def send_owner_menu(context, chat_id, show_kb: bool = False):
    old_extra = {k: track_get(OWNER_ID, k) for k in OWNER_EXTRA_KINDS}  # اول پیام‌های جدید میان، بعد قدیمی‌ها پاک میشن (چت هیچ‌وقت خالی نمیشه)
    msg = await context.bot.send_message(chat_id, owner_menu_text(),
                                         reply_markup=owner_reply_menu_kb(), parse_mode=H)
    await track_menu_msg(context.bot, OWNER_ID, msg, True)
    await send_owner_extras(context.bot, chat_id)  # 👾 جدید
    cnt = old_extra.pop("owncount", None)  # برگشت به منوی اصلی: عدد اعضا کامل پاک میشه
    if cnt is not None:
        ex("DELETE FROM tracked WHERE user_id=? AND kind=?", (OWNER_ID, "owncount"))
        bg(_safe_delete(context.bot, cnt["chat_id"], cnt["message_id"]))
    for kind, old in old_extra.items():
        cur = track_get(OWNER_ID, kind)
        if old is not None and (cur is None or old["message_id"] != cur["message_id"]):
            bg(_safe_delete(context.bot, old["chat_id"], old["message_id"]))


async def close_glass(update: Update, context):
    """بازگشت به منوی اصلی: پیام شیشه‌ای بسته میشه و کیبورد منوی اصلی همون‌جا هست."""
    q = update.callback_query
    uid = update.effective_user.id
    # اول منوی اصلی میاد، بعد پیام شیشه‌ای پاک میشه؛ چت لحظه‌ای خالی نمیشه تا دکمه‌ی «شروع» تلگرام نیاد
    if uid == OWNER_ID:
        await send_owner_menu(context, update.effective_chat.id)
    else:
        await send_admin_menu(context, update.effective_chat.id)
    if q and q.message:
        release_cmd(uid, q.message.message_id)
        try:
            await q.message.delete()
        except TelegramError:
            try:
                await q.edit_message_reply_markup(reply_markup=None)
            except TelegramError:
                pass


async def send_comment_text(bot, uid, chat_id):
    msg = await bot.send_message(chat_id, COMMENT_TEXT, parse_mode=H)
    await replace_tracked(bot, uid, "comment", msg)


async def send_reply_text(bot, uid, chat_id, admin):
    msg = await bot.send_message(chat_id, REPLY_TEXT.replace('{code}', str(admin["code"])), parse_mode=H)
    await replace_tracked(bot, uid, "reply", msg)


async def send_video_tracked(bot, uid, chat_id, fid):
    msg = await send_media(bot, chat_id, get_setting("video_kind"), fid)  # اول خودِ ویدیو (بدون کپشن)
    await replace_tracked(bot, uid, "video", msg)
    txt = await send(bot, chat_id, "<b>ویدیو آموزش خدمت شما، ادمین عزیز📼</b>", html_mode=True)  # بعدش متن، جدا
    await replace_tracked(bot, uid, "videotxt", txt)


# عکس‌های هر سطح: (عکس اصلی پروفایل، عکس تارِ پروفایل برای وقتی قفله، عکس مبلغ زیر گزارش فعالیت)
LEVEL_PHOTO_KEYS = {
    1: ("profile_level_photo_id", None, "activity_photo_id"),
    2: ("lvl2_photo_id", "lvl2_blur_photo_id", "lvl2_amount_photo_id"),
    3: ("lvl3_photo_id", "lvl3_blur_photo_id", "lvl3_amount_photo_id"),
}
CONTENT_KINDS = ("comment", "reply", "video", "videotxt", "profile", "activity", "menu", "cardem", "tut1", "tut2",
                 "chold", "cheatv")  # chold = اموجی نگه‌دارنده‌ی منوی تقلب، cheatv = تقلبی که ادمین بازش کرده


def drop_contents(bot, uid: int, keep=()):
    """دکمه‌ی جدید زده شد: متن‌ها و منوهای ردیابی‌شده‌ی دکمه‌های قبلی پاک میشن (به‌جز نوع‌های keep).
    پیام‌های جذب جدید (report)، پیام خوشامد و پیام کیبورد اصلی دست‌نخورده می‌مونن."""
    for kind in CONTENT_KINDS:
        if kind in keep:
            continue
        r = track_get(uid, kind)
        if r is None:
            continue
        ex("DELETE FROM tracked WHERE user_id=? AND kind=?", (uid, kind))
        bg(_safe_delete(bot, r["chat_id"], r["message_id"]))
        if kind in MENU_KINDS and r["cmd_id"]:
            schedule_delete(r["chat_id"], r["cmd_id"], CMD_DELETE_DELAY)


def profile_photo_for(view: int, locked: bool):
    real, blur, _ = LEVEL_PHOTO_KEYS[view]
    if locked:
        fid = get_setting(blur) if blur else ""
        if fid:
            return fid, False
        fid = get_setting(real)  # عکس تار ثبت نشده: همون عکس اصلی با تاری خودکار تلگرام
        return (fid, True) if fid else (None, False)
    fid = get_setting(real)
    return (fid, False) if fid else (None, False)


def amount_photo_for(view: int, locked: bool):
    fid = get_setting(LEVEL_PHOTO_KEYS[view][2])
    return (fid, locked) if fid else (None, False)


def level_buttons(admin_level: int, view: int):
    """دکمه‌های سطح؛ همه قرمز، فقط دکمه‌ی سطحی که الان نمایش داده میشه آبیه.
    دکمه‌ی سطح‌هایی که ادمین ازشون رد شده نمیاد؛ در بالاترین سطح هیچ دکمه‌ای نیست."""
    if admin_level >= LEVEL_MAX:
        return None
    rows = []
    for n in (1, 2, 3):
        if n < admin_level:
            continue
        if n == admin_level:
            txt = "⭐️ سطح فعلی ⭐️"
        elif n < admin_level:
            txt = f"سطح {n}"
        else:
            txt = f"🔒ارتقا به سطح {n}🔒"
        rows.append(B(txt, f"a:lv:{n}", style="primary" if n == view else "danger"))
    return KB(*rows)


async def send_profile_msg(bot, uid: int, chat_id: int, admin, view: int):
    lvl = level_of(admin)
    locked = view > lvl
    cap = profile_caption(admin, view)
    kb = level_buttons(lvl, view)
    fid, spoil = profile_photo_for(view, locked)
    if fid:
        msg = await send_media(bot, chat_id, "photo", fid, caption=cap, html_mode=True, kb=kb, spoiler=spoil)
    else:
        msg = await send(bot, chat_id, cap, kb, html_mode=True)
    await replace_tracked(bot, uid, "profile", msg)
    return msg


async def send_activity_msg(bot, uid: int, chat_id: int, admin, view: int):
    lvl = level_of(admin)
    locked = view > lvl
    cap = activity_report_text(admin, view)
    kb = KB(MAIN())
    fid, spoil = amount_photo_for(view, locked)
    if fid:
        msg = await send_media(bot, chat_id, "photo", fid, caption=cap, html_mode=True, kb=kb, spoiler=spoil)
    else:
        msg = await send(bot, chat_id, cap, kb, html_mode=True)
    await replace_tracked(bot, uid, "activity", msg)
    return msg


async def send_profile_report(bot, uid: int, chat_id: int, admin, view: int = None):
    lvl = level_of(admin)
    view = view if view in (1, 2, 3) else lvl
    await send_profile_msg(bot, uid, chat_id, admin, view)
    if amount_photo_for(view, view > lvl)[0]:
        await asyncio.sleep(2)
    await send_activity_msg(bot, uid, chat_id, admin, view)


async def switch_level_view(context, uid: int, chat_id: int, q, admin, view: int):
    """زدن دکمه‌ی یک سطح: همون پیام پروفایل (عکس + کپشن + رنگ دکمه‌ها) ویرایش میشه."""
    lvl = level_of(admin)
    locked = view > lvl
    kb = level_buttons(lvl, view)
    cap = profile_caption(admin, view)
    fid, spoil = profile_photo_for(view, locked)
    is_photo = bool(q.message and q.message.photo)
    redo = False
    try:
        if fid and is_photo:
            await context.bot.edit_message_media(
                InputMediaPhoto(fid, caption=cap, parse_mode=H, has_spoiler=bool(spoil)),
                chat_id=chat_id, message_id=q.message.message_id, reply_markup=kb)
        elif not fid and not is_photo:
            await q.edit_message_text(cap, reply_markup=kb, parse_mode=H, link_preview_options=preview_opts(cap))
        else:
            redo = True
    except BadRequest as e:
        if "not modified" not in str(e).lower():
            redo = True
    if redo:
        await send_profile_msg(context.bot, uid, chat_id, admin, view)


async def refresh_activity(context, uid: int, chat_id: int, admin, view: int):
    """پیام دوم (گزارش فعالیت) هم با همون سطح هماهنگ میشه؛ اگه ویرایش ممکن نبود، دوباره فرستاده میشه."""
    row = track_get(uid, "activity")
    if row is None or row["chat_id"] != chat_id:
        await send_activity_msg(context.bot, uid, chat_id, admin, view)
        return
    locked = view > level_of(admin)
    cap = activity_report_text(admin, view)
    kb = KB(MAIN())
    fid, spoil = amount_photo_for(view, locked)
    redo = False
    try:
        if fid:
            await context.bot.edit_message_media(
                InputMediaPhoto(fid, caption=cap, parse_mode=H, has_spoiler=bool(spoil)),
                chat_id=chat_id, message_id=row["message_id"], reply_markup=kb)
        else:
            await context.bot.edit_message_text(cap, chat_id=chat_id, message_id=row["message_id"],
                                                reply_markup=kb, parse_mode=H)
    except BadRequest as e:
        if "not modified" not in str(e).lower():
            redo = True
    if redo:
        await send_activity_msg(context.bot, uid, chat_id, admin, view)


def welcome_text(admin, with_prompt: bool = False) -> str:
    text = (TEXT_DEFAULTS["welcome"].replace("{code}", str(admin["code"]))
            .replace("「 {level} 」", ("\n\u200f" if level_of(admin) == 3 else "") + "「 {level} 」")  # فقط سطح ۳: سطح یه خط پایین‌تر
            .replace("{level}", WELCOME_LEVEL[level_of(admin)])
            .replace("{income}", f"{fmt_en(admin['cur_amount'])} تومان"))
    if not with_prompt:
        # حذف آخرین خط («برای شروع همکاری، روی دکمه زیر بزن🔻»)
        text = text.rsplit("\n", 1)[0]
    return text


async def finalize_welcome(q, admin):
    """بعد از زدن «شروع همکاری»: فقط دکمه‌ی زیر پیام خوشامد حذف میشه؛ متن ادیت نمیشه و برچسب «ویرایش‌شده» نمیخوره."""
    if q.message is None:
        return
    for _try in range(3):  # اگه ادیت یه بار خطا داد (کندی/محدودیت تلگرام)، دکمه نباید بمونه؛ تا ۳ بار تلاش
        try:
            await q.edit_message_reply_markup(reply_markup=None)
            return
        except RetryAfter as e:
            await asyncio.sleep(min(e.retry_after + 0.5, 5))
        except TelegramError as e:
            if "not modified" in str(e).lower():
                return  # دکمه از قبل برداشته شده
            log_err(f"finalize_welcome try {_try + 1}: {e!r}")
            await asyncio.sleep(0.7)


async def send_welcome(context, chat_id, admin):
    # کیبورد معمولی حذف نمیشه تا آیکن بازکردنش کنار فیلد پیام همیشه بمونه؛ خودش فقط با «پنل فعال شد» و
    # «چه کاری انجام بدم» باز میشه (one_time_keyboard=True: با اولین دکمه جمع میشه).
    text = welcome_text(admin)
    kb = KB(B("🔷 شروع همکاری 🔷", "t:start", style="danger"))
    photo_id = get_setting(LEVEL_PHOTO_KEYS[level_of(admin)][0])
    if photo_id:
        msg = await send_media(context.bot, chat_id, "photo", photo_id, caption=text, kb=kb, html_mode=True)
    else:
        msg = await send(context.bot, chat_id, text, kb, html_mode=True)
    await replace_tracked(context.bot, chat_id, "welcome", msg)


async def drop_welcome_back(bot, uid: int):
    """پیام‌های «خوش برگشتی»، «هنوز دیر نشده» و یادآوریِ آموزش بعد از فعال شدن پنل پاک میشن."""
    r = track_get(uid, "wb")
    if r is not None:
        ex("DELETE FROM tracked WHERE user_id=? AND kind='wb'", (uid,))
        await _safe_delete(bot, r["chat_id"], r["message_id"])
    # «هنوز دیر نشده» (اگه با دکمه نیومده بود) و یادآوریِ تکمیل آموزش هم با فعال شدن پنل پاک میشن
    c = q1("SELECT msg_id FROM comeback WHERE user_id=?", (uid,))
    if c is not None and c["msg_id"]:
        ex("UPDATE comeback SET msg_id=0 WHERE user_id=?", (uid,))
        await _safe_delete(bot, uid, c["msg_id"])
    a = q1("SELECT tut_nudge_msg FROM admins WHERE user_id=?", (uid,))
    if a is not None and a["tut_nudge_msg"]:
        ex("UPDATE admins SET tut_nudge_msg=0 WHERE user_id=?", (uid,))
        await _safe_delete(bot, uid, a["tut_nudge_msg"])


async def entry(update: Update, context):
    user = update.effective_user
    was_new = get_admin(user.id) is None
    admin = create_admin(user)
    chat_id = update.effective_chat.id
    await announce_codes_full(context.bot)
    if was_new and comeback_returned(user.id):  # ادمینِ خودکار-حذف‌شده که دوباره اومده
        _wb = await safe_send(context.bot, chat_id, WELCOME_BACK_TEXT, html_mode=True)
        if _wb is not None:
            track_set(user.id, "wb", _wb.chat_id, _wb.message_id)  # با فعال شدن پنل پاک میشه
    if admin["training_done"]:
        await send_admin_menu(context, chat_id, show_kb=True)
    else:
        await send_welcome(context, chat_id, admin)


async def _del_start_later(m, sec: float = 4):
    await asyncio.sleep(sec)
    await _del_msg(m)


async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    if not user or user.is_bot:
        return
    if user.id == OWNER_ID:
        clear_state(user.id)
        _om = update.effective_message
        if _om is not None:
            bg(_del_start_later(_om))  # /start بعد از ۴ ثانیه پاک میشه (پاک شدن فوری، دکمه‌ی START تلگرام رو نگه میداره)
        await send_owner_menu(context, update.effective_chat.id, show_kb=True)
        return
    _sm = update.effective_message
    if _sm is not None:
        schedule_delete(update.effective_chat.id, _sm.message_id, CMD_DELETE_DELAY)  # پشتیبان
        bg(_del_start_later(_sm))  # /start چند ثانیه بعد پاک میشه (پاک شدن فوری باعث میشه دکمه‌ی START تلگرام بمونه)
    if bot_off():
        _a = get_admin(user.id)
        if _a is not None and _a["training_done"]:
            await maintenance_reply(context.bot, update.effective_chat.id, user.id)
            return
        # تازه‌وارد یا آموزش‌ندیده: مسیر آموزش عادی طی میشه؛ فقط آخرش به‌جای «پنل فعال شد» پیام تعمیرات میاد
    if not await gate(update, context):
        return
    # شروع مجدد /start وضعیت‌های نیمه‌کاره (مثل ورود کارت) را لغو می‌کند؛ داده‌های ذخیره‌شده دست‌نخورده می‌مانند.
    await drop_card_emoji(context.bot, update.effective_chat.id, user.id)
    clear_state(user.id)
    drop_contents(context.bot, user.id)
    _a2 = get_admin(user.id)
    if _a2 is not None and not _a2["training_done"]:
        await hide_reply_keyboard(context.bot, update.effective_chat.id, user.id)
    await entry(update, context)


async def drop_msgs(bot, uid: int, chat_id: int, q, kinds):
    """پیام‌های آموزش هیچ‌وقت پاک نمیشن؛ فقط از ردیابی خارج میشن و دکمه‌ی پیامی که زده شد برداشته میشه."""
    for kind in kinds:
        ex("DELETE FROM tracked WHERE user_id=? AND kind=?", (uid, kind))
    if q is not None and q.message is not None:
        try:
            await q.edit_message_reply_markup(reply_markup=None)
        except TelegramError:
            pass


async def send_step1(context, chat_id, edit_query=None):
    if edit_query is not None:
        try:
            await edit_query.edit_message_text(STEP1_TEXT, parse_mode=H)
            s1 = edit_query.message
        except TelegramError:
            s1 = await context.bot.send_message(chat_id, STEP1_TEXT, parse_mode=H)
    else:
        s1 = await context.bot.send_message(chat_id, STEP1_TEXT, parse_mode=H)
    await replace_tracked(context.bot, chat_id, "tut1", s1)

    await asyncio.sleep(1)

    sent_cmt = await context.bot.send_message(
        chat_id,
        COMMENT_TEXT,
        parse_mode=H,
        reply_markup=KB(B("➡️ مرحله بعد ➡️", "t:rsp", style="danger"))
    )
    await replace_tracked(context.bot, chat_id, "comment", sent_cmt)



def records_view(uid: int):
    paid = q1("SELECT COUNT(*) n FROM commissions WHERE admin_id=? AND status='paid'", (uid,))["n"]
    earned = q1("SELECT COUNT(*) n FROM commissions WHERE admin_id=? AND status='earned'", (uid,))["n"]
    rows = []
    if paid:
        rows.append(B("📂 دریافت تمام سوابق پورسانت 📂", "a:rall", style="danger"))
        rows.append(B("📅 سوابق پورسانت بر اساس تاریخ 📅", "a:rdate", style="danger"))
    rows.append(BACK("a:menu"))
    return ("💰 سوابق پورسانت 💰" if paid else NO_RECORDS_TEXT), KB(*rows)


def st_merge(uid: int, state: str, **kw) -> dict:
    """وضعیت رو عوض میکنه ولی داده‌های قبلی (کارت، مبدا، پیام) رو نگه میداره."""
    _, d = get_state(uid)
    d.update(kw)
    set_state(uid, state, d)
    return d


def set_pm(uid: int, msg):
    """شناسه‌ی پیامی که الان صفحه‌ی ثبت کارت روشه (اگه show پیام جدید فرستاده باشه)."""
    if msg is None:
        return
    st, d = get_state(uid)
    if st:
        d["pm"] = msg.message_id
        set_state(uid, st, d)


async def edit_or_send(bot, chat_id, mid, text, kb):
    if mid:
        try:
            await bot.edit_message_text(text, chat_id=chat_id, message_id=mid, reply_markup=kb)
            return mid
        except BadRequest as e:
            if "not modified" in str(e).lower():
                return mid
        except TelegramError:
            pass
    msg = await send(bot, chat_id, text, kb, html_mode=False)
    return msg.message_id


def prompt_back(pf: str) -> str:
    return {"l": "a:bl", "e": "a:bc"}.get(pf, "a:bo")


async def drop_card_emoji(bot, chat_id: int, uid: int):
    """💳 تکیِ زیر متن شماره کارت وقتی اون صفحه عوض میشه پاک میشه."""
    r = track_get(uid, "cardem")
    if r is not None:
        ex("DELETE FROM tracked WHERE user_id=? AND kind='cardem'", (uid,))
        bg(_safe_delete(bot, r["chat_id"], r["message_id"]))


async def show_prompt(update, context, uid: int, pf: str, fresh: bool = False):
    chat_id = update.effective_chat.id
    r = await show(update, context, CARD_PROMPT, KB(BACK(prompt_back(pf)), MAIN()), html_mode=False, fresh=fresh)
    set_pm(uid, r)
    try:
        e = await context.bot.send_message(chat_id, "💳")  # بلافاصله بعد از متن، یک 💳 تکی
        await replace_tracked(context.bot, uid, "cardem", e)
    except TelegramError as ex_:
        log_err(f"card emoji failed: {ex_!r}")


async def show_confirm(update, context, uid: int, d: dict):
    back = "a:bl" if d.get("via") == "p" else "a:bp"
    await drop_card_emoji(context.bot, update.effective_chat.id, uid)
    r = await show(update, context, confirm_text(d["number"], d["holder"]), confirm_kb(back), html_mode=False)
    set_pm(uid, r)


async def show_card_list(update, context, uid: int, fresh: bool = False):
    await drop_card_emoji(context.bot, update.effective_chat.id, uid)
    cards = qa("SELECT * FROM cards WHERE admin_id=? ORDER BY id", (uid,))
    rows = [B(f"💳 {card_mask(k['number'])}", f"a:pc:{k['id']}", style=cyc(i, "primary", "danger", "success"))
            for i, k in enumerate(cards)]
    rows.append(B("➕ ثبت کارت جدید ➕", "a:new", style="success"))
    rows.append(BACK("a:bo"))
    rows.append(MAIN())
    r = await show(update, context, "لطفا کارت بانکی خود را از لیست زیر انتخاب کنید", KB(*rows), html_mode=False, fresh=fresh)
    set_pm(uid, r)


async def req_step(update, context, uid: int, cid: int, src: str, om=None):
    """شروع درخواست پورسانت: مبدا (پیام تبریک یا سوابق) توی وضعیت ذخیره میشه تا «بازگشت» همونجا برگرده.
    اگه از دکمه‌ی پیام تبریک اومده (src=c)، پیام تبریک دست‌نخورده می‌مونه و مراحل پایینش میان."""
    q = update.callback_query
    has_msg = q is not None and q.message is not None
    fresh = src == "c" and om is None and has_msg
    if fresh:
        om = q.message.message_id
        pm = None
        _st, _d = get_state(uid)
        _old = _d.get("pm") if isinstance(_d, dict) else None
        if isinstance(_old, int) and _old != om:  # مرحله‌ی نیمه‌کاره‌ی قبلی پاک میشه تا تکراری نشه
            bg(_safe_delete(context.bot, update.effective_chat.id, _old))
    else:
        pm = q.message.message_id if has_msg else None
    if not qa("SELECT 1 FROM cards WHERE admin_id=?", (uid,)):
        set_state(uid, "card_input", {"cid": cid, "src": src, "pf": "o", "pm": pm, "om": om})
        await show_prompt(update, context, uid, "o", fresh=fresh)
        return
    set_state(uid, "pay", {"cid": cid, "src": src, "pf": "o", "pm": pm, "om": om})
    await show_card_list(update, context, uid, fresh=fresh)


async def _origin_alive(bot, chat_id: int, mid, kb) -> bool:
    """بررسی میکنه پیام تبریک بالای چت هنوز هست یا نه (ویرایش بی‌تغییر دکمه)."""
    if not isinstance(mid, int):
        return False
    try:
        await bot.edit_message_reply_markup(chat_id=chat_id, message_id=mid, reply_markup=kb)
        return True
    except BadRequest as e:
        return "not modified" in str(e).lower()
    except TelegramError:
        return False


async def show_req_origin(update, context, uid: int, src: str, cid, om=None):
    if src == "c" and cid:
        c = q1("SELECT * FROM commissions WHERE id=? AND admin_id=? AND status='earned'", (cid, uid))
        a = get_admin(uid)
        if c is not None and a is not None:
            ckb = KB(B("💵 دریافت پورسانت 💵", "a:reqc", style="success"))
            q = update.callback_query
            if q and q.message and await _origin_alive(context.bot, update.effective_chat.id, om, ckb):
                # پیام تبریک هنوز بالاست: فقط مرحله‌ی پایینی بسته میشه
                release_cmd(uid, q.message.message_id)
                ex("DELETE FROM tracked WHERE user_id=? AND message_id=? AND kind='menu'", (uid, q.message.message_id))
                try:
                    await q.message.delete()
                except TelegramError:
                    pass
                return
            await show(update, context,
                       congrats_for_commission(c["target"] or a["cur_target"], c["amount"], c["period_no"], c["lvl"]),
                       ckb, html_mode=True)
            return
    text, kb = records_view(uid)
    await show(update, context, text, kb, html_mode=False)


CLEAN_KINDS = ("comment", "reply", "video", "videotxt", "report", "menu")

SENT_KEEP = 47 * 3600  # تلگرام فقط پیام‌های کمتر از ۴۸ ساعت رو اجازه‌ی حذف میده
_SEND_METHODS = ("send_message", "send_photo", "send_video", "send_document", "send_animation", "send_audio",
                 "send_voice", "send_sticker", "send_video_note", "send_media_group", "send_poll",
                 "send_location", "send_contact", "send_dice", "copy_message", "copy_messages")


def _log_sent(res, a, kw):
    """فقط شناسه‌ی پیام‌های فرستاده‌شده توی چت خصوصی ثبت میشه؛ خطا هیچ‌وقت ارسال رو خراب نمی‌کنه."""
    try:
        chat_id = kw.get("chat_id", a[0] if a else None)
        items = res if isinstance(res, (list, tuple)) else [res]
        now = int(time.time())
        for it in items:
            mid = getattr(it, "message_id", None)
            cid = getattr(it, "chat_id", None) or chat_id
            if isinstance(cid, int) and cid > 0 and isinstance(mid, int):
                ex("INSERT INTO sent_log(chat_id,message_id,ts) VALUES(?,?,?)", (cid, mid, now))
    except Exception:  # noqa
        pass


def _wrap_send(orig):
    @functools.wraps(orig)
    async def wrapper(self, *a, **kw):
        res = await orig(self, *a, **kw)
        _log_sent(res, a, kw)
        return res
    return wrapper


def patch_send_tracking():
    for name in _SEND_METHODS:
        fn = getattr(ExtBot, name, None)
        if fn is not None and not getattr(fn, "_sent_logged", False):
            w = _wrap_send(fn)
            w._sent_logged = True
            setattr(ExtBot, name, w)

OWNER_CLEAN_TEXT = "🧹 این گزینه برای پاکسازی پیام‌های رباته تا همه‌چیز مثل روز اول مرتب و تمیز بشه 😀👌🏼"

CLEAN_TEXT = (
    "🧹 این گزینه برای پاکسازی تمام پیام‌های رباته تا همه‌چیز مثل روز اول مرتب و تمیز بشه 😀👌🏼\n\n"
    "خیالت راحت باشه…\n"
    "هیچ اطلاعاتی ازت حذف نمی‌شه؛ فقط پیام‌های ربات پاکسازی می‌شن ❤️"
)


def clean_menu_kb():
    return KB(B("🧹 پاکسازی 🧹", "a:cln", style="danger"),
              BACK("a:menu"))


def levelup_hold_ids(uid: int) -> set:
    """پیام تبریک ارتقای سطح و 🎉 تکیِ زیرش: تا وقتی ادمین کارتش رو ثبت و تأیید نکرده، پاکسازی خودکار بهشون دست نمیزنه.
    (بعد از تأیید، clean_card_flow همه‌ی اینا رو باهم پاک میکنه.)"""
    h = track_get(uid, "lvlhold")
    if h is None:
        return set()
    cg = track_get(uid, "congrats")
    if cg is None or cg["message_id"] != h["message_id"] or h["chat_id"] != uid:
        return set()  # تبریک عوض شده؛ دیگه تبریک ارتقا نیست
    ids = {h["message_id"]}
    cf = track_get(uid, "confetti")
    if cf is not None and cf["chat_id"] == uid:
        ids.add(cf["message_id"])
    return ids


async def clean_texts(bot, uid: int, keep_message_id: int = None, auto: bool = False, keep_hold: bool = False):
    """پاک‌سازی پیام‌های شناخته‌شده‌ی این چت (ربات و کاربر)؛ داده‌های کسب‌وکار حذف نمی‌شوند.
    auto=True (پاکسازی خودکار ۳۰ ثانیه‌ای): پیام‌های آموزش تا 💻 (پنل فعال شد، مراحل آموزش و ...) و آخرین پیام ربات دست‌نخورده می‌مونن."""
    ids = {r["message_id"] for r in qa("SELECT message_id FROM sent_log WHERE chat_id=?", (uid,))}
    ids.update(r["message_id"] for r in qa("SELECT message_id FROM cleanup WHERE chat_id=?", (uid,)))
    for r in qa("SELECT chat_id,message_id FROM tracked WHERE user_id=?", (uid,)):
        if r["chat_id"] == uid:
            ids.add(r["message_id"])
    _st, state_data = get_state(uid)
    if isinstance(state_data, dict):
        ids.update(mid for mid in (state_data.get("um") or []) if isinstance(mid, int))
    if keep_message_id is not None:
        ids.discard(keep_message_id)
    # پیام حامل کیبورد (مثل 💻) پاک نمیشه؛ با پاک‌شدنش آیکن کیبورد کنار فیلد پیام هم می‌پره
    keep_kb = {r["message_id"] for r in qa("SELECT message_id FROM tracked WHERE user_id=? AND kind='kb'", (uid,))}
    lo_b = hi_b = 0       # بازه‌ی محافظت‌شده‌ی آموزش (از پیام خوشامد تا 💻) فقط در حالت خودکار
    last_keep = None      # آخرین پیام ربات فقط در حالت خودکار
    tb = track_get(uid, "tutend")
    if tb is not None and tb["chat_id"] == uid:
        hi_b = tb["message_id"]
        lo_b = tb["cmd_id"] or 0
    ids = {m for m in ids if isinstance(m, int) and not (lo_b <= m <= hi_b)}
    hold = ((levelup_hold_ids(uid) | receipt_hold_ids(uid) | report_hold_ids(uid)) if auto
            else (hold_ids(uid) if keep_hold else set()))  # تبریک ارتقا + 🎉 تا تأیید کارت دست‌نخورده می‌مونن؛ پاکسازی دستی مدیر: درخواست‌های واریز در انتظار هم می‌مونن
    if auto:
        _rc = receipt_ids(uid)
        cand = {m for m in (ids | hold) if isinstance(m, int) and m > 0} | keep_kb
        cand -= _rc  # فیش واریز جزو پاکسازی ۳۰ ثانیه‌ایه و هیچ‌وقت به‌عنوان آخرین پیام نمی‌مونه
        last_keep = max(cand) if cand else None
        ids.discard(last_keep)
        ids -= hold
    known = sorted(mid for mid in ids if isinstance(mid, int) and mid > 0)
    if known:
        # شناسه‌ی پیام‌ها توی چت خصوصی پشت‌سرهمه؛ پس کل بازه رو پاک میکنیم تا پیام‌های ثبت‌نشده (مثل /start) هم بره.
        lo = max(1, known[0] - 3, known[-1] - 1500)
        ids = set(range(lo, known[-1] + 1)) | set(known)
    ids -= keep_kb
    ids -= hold
    ids = {m for m in ids if not (lo_b <= m <= hi_b)}
    ids.discard(last_keep)
    todo = sorted(mid for mid in ids if isinstance(mid, int) and mid > 0)
    for i in range(0, len(todo), 100):
        chunk = todo[i:i + 100]
        try:
            await bot.delete_messages(uid, chunk)
        except RetryAfter as e:
            await asyncio.sleep(e.retry_after + 1)
            try:
                await bot.delete_messages(uid, chunk)
            except TelegramError:
                pass
        except TelegramError:
            for mid in chunk:
                if mid in known:
                    await _safe_delete(bot, uid, mid)
        await asyncio.sleep(0.05)
    # بازه‌ی آموزش (و در حالت خودکار آخرین پیام ربات) توی دیتابیس می‌مونن
    args = (uid, lo_b, hi_b, last_keep or 0)
    hold_sql = (" AND message_id NOT IN (%s)" % ",".join("?" * len(hold))) if hold else ""
    hold_args = tuple(hold)
    ex("DELETE FROM sent_log WHERE chat_id=? AND NOT (message_id BETWEEN ? AND ?) AND message_id<>?" + hold_sql,
       args + hold_args)
    ex("DELETE FROM tracked WHERE user_id=? AND kind NOT IN ('kb','tutend') "
       "AND NOT (message_id BETWEEN ? AND ?) AND message_id<>?" + hold_sql, args + hold_args)
    ex("DELETE FROM cleanup WHERE chat_id=? AND NOT (message_id BETWEEN ? AND ?) AND message_id<>?" + hold_sql,
       args + hold_args)
    ex("DELETE FROM receipt_msgs WHERE chat_id=?", (uid,))
    clear_state(uid)


# ---------- پاکسازی خودکار بعد از ۳۰ ثانیه ----------
AUTO_CLEAN_DELAY = 30
_last_act = {}


_member_seen = set()


async def track_activity(update: Update, context):
    """هر پیام یا دکمه‌ای که کاربر میزنه: زمان آخرین فعالیت ثبت میشه و شناسه‌ی پیامش (مثل /start) برای پاکسازی ذخیره میشه."""
    try:
        chat = update.effective_chat
        user = update.effective_user
        if chat is None or user is None or chat.type != "private":
            return
        if update.message is None and update.callback_query is None:
            return
        is_owner = user.id == OWNER_ID
        _last_act[user.id] = time.time()
        if not is_owner and user.id not in _member_seen:
            _member_seen.add(user.id)
            ex("INSERT OR IGNORE INTO members(user_id, first_seen) VALUES(?,?)", (user.id, int(time.time())))
        if (not is_owner and drop_prev_on()
                and (update.callback_query is not None
                     or (update.message is not None and is_kb_text(update.message.text or "")))):
            drop_receipts(context.bot, user.id)  # دکمه‌ی جدید زده شد؛ فیش قبلی پاک میشه
        if is_owner and (update.message is None or not update.message.text):
            return  # عکس و ویدیوی مدیر (فیش، ویدیوی آموزشی و ...) توی پاکسازی ثبت نمیشه
        if update.message is not None and not is_kb_text(update.message.text or ""):
            # متن دکمه‌های کیبورد فوری پاک میشه؛ ثبتش نمی‌کنیم تا آخرین پیام ربات اشتباه تشخیص داده نشه
            ex("INSERT INTO sent_log(chat_id,message_id,ts) VALUES(?,?,?)",
               (chat.id, update.message.message_id, int(time.time())))
    except Exception:  # noqa
        pass


async def auto_clean_job(context: ContextTypes.DEFAULT_TYPE):
    if not ac_on():
        return
    """۳۰ ثانیه بعد از آخرین فعالیت ادمین: دستورهای خودش و پیام‌های قبلیِ ربات پاک میشن.
    می‌مونه: آخرین پیام ربات (منو یا متن)، 💻 حامل کیبورد و همه‌ی پیام‌های آموزش از خوشامد تا 💻.
    ادمینی که وسط ثبت کارت یا ارسال پیشنهاد باشه یا آموزشش تموم نشده باشه، دست‌نخورده می‌مونه."""
    now = time.time()
    delay = ac_delay()
    rows = qa("SELECT chat_id, MAX(ts) last FROM sent_log WHERE chat_id>0 "
              "AND message_id NOT IN (SELECT message_id FROM tracked WHERE kind='kb') "
              "GROUP BY chat_id HAVING MAX(ts)<=?", (int(now) - delay,))
    for r in rows:
        uid = r["chat_id"]
        if now - _last_act.get(uid, 0) < delay:
            continue
        if uid == OWNER_ID:
            # پنل مدیر: وسط کار (فیش، پیام همگانی، تنظیمات و ...) دست‌نخورده می‌مونه
            _s = q1("SELECT state, ts FROM state WHERE user_id=?", (uid,))
            if _s is not None and _s["state"] and now - (_s["ts"] or 0) < STATE_TTL:
                continue
        else:
            a = get_admin(uid)
            if a is None or not a["training_done"] or a["blocked"]:
                continue
            if get_state(uid)[0] in ("card_input", "pay", "suggest"):
                continue
        tb = track_get(uid, "tutend")
        lo_b = hi_b = 0
        if tb is not None and tb["chat_id"] == uid:
            hi_b, lo_b = tb["message_id"], (tb["cmd_id"] or 0)
        hold = levelup_hold_ids(uid) | receipt_hold_ids(uid) | report_hold_ids(uid)  # تبریک ارتقا + فیش + متن جذب جدید
        ids_all = {r["message_id"] for r in qa(
            "SELECT message_id FROM sent_log WHERE chat_id=? AND NOT (message_id BETWEEN ? AND ?) "
            "AND message_id NOT IN (SELECT message_id FROM tracked WHERE kind='kb')", (uid, lo_b, hi_b))}
        rcpt = receipt_ids(uid)
        rest = ids_all - hold
        rest_nr = rest - rcpt  # بدون فیش‌ها (فیش همیشه پاک میشه)
        _nr_all = (ids_all | hold) - rcpt
        keep_one = 0 if (hold and (not rest_nr or max(_nr_all) in hold)) else 1
        if len(rest_nr) <= keep_one and not (rest & rcpt):
            continue  # فقط آخرین پیام ربات (و تبریک ارتقا) مونده؛ چیزی برای پاک کردن نیست
        try:
            await clean_texts(context.bot, uid, auto=True)
        except Exception as e:  # noqa
            log_err(f"auto clean {uid}: {e!r}")


async def clean_card_flow(bot, uid: int, chat_id: int, q, d: dict):
    """بعد از ثبت کارت: فقط پیام‌های شماره کارت و اسم (پیام‌های خود کاربر، پیام‌های راهنما و منوی تأیید) فوری پاک میشن.
    متن کامنت، پاسخگویی، ویدیو و بقیه‌ی پیام‌ها دست‌نخورده می‌مونن."""
    ids = {i for i in (d.get("cm") or []) if isinstance(i, int)}
    for i in (q.message.message_id if q is not None and q.message else None, d.get("pm"), d.get("em")):
        if isinstance(i, int):
            ids.add(i)
    om = d.get("om")  # پیام تبریک بالای چت (اگه از دکمه‌ی تبریک اومده بود)
    if isinstance(om, int) and om > 0:
        ids.add(om)
    for kind in ("congrats", "confetti", "lvlhold"):  # تبریک قبلی و 🎉 تکی بعد از ثبت درخواست پاک میشن تا گیج‌کننده نباشن
        r = track_get(uid, kind)
        if r is not None:
            ex("DELETE FROM tracked WHERE user_id=? AND kind=?", (uid, kind))
            if r["chat_id"] == chat_id:
                ids.add(r["message_id"])
    for mid in ids:
        bg(_safe_delete(bot, chat_id, mid))
    await drop_card_emoji(bot, chat_id, uid)
    clear_state(uid)


async def send_suggestion(context, admin, m):
    # متن پیشنهاد زیر همون «🔻متن پیام🔻» توی یک پیام میاد و دکمه‌ی «پنل عملکرد» روی همین پیامه
    body = m.text_html if m.text else html.escape(m.caption or "")
    await safe_send_hold(context.bot, OWNER_ID,
                    "<b>💡 پیشنهاد یا انتقاد جدید 💡</b>\n\n"
                    f"<b>👤 ادمین:🔻</b>\u25aa\ufe0f<b>کد:</b> {admin['code']}\u25aa\ufe0f\n"
                    f"{link(admin)}\n"
                    "<b>🔻متن پیام🔻</b>\n"
                    f"{body}",
                    KB(B("🧬 پنل عملکرد 🧬", f"o:perf:{admin['user_id']}")))  # بازگشت از پنل همین متن رو برمیگردونه
    audit(admin["user_id"], "suggestion")


async def admin_cb(update: Update, context, data: str):
    q = update.callback_query
    user = q.from_user
    chat_id = update.effective_chat.id

    if data == COMEBACK_CB:  # دکمه‌ی «شروع دوباره» زیر پیام «هنوز دیر نشده»
        if not await gate(update, context):
            return None
        ex("UPDATE comeback SET pressed_at=? WHERE user_id=? AND pressed_at=0", (int(time.time()), user.id))
        if q.message is not None:  # خود پیام «هنوز دیر نشده» با زدن دکمه پاک میشه
            await _safe_delete(context.bot, q.message.chat_id, q.message.message_id)
        await entry(update, context)
        return None
    if data == "chk":
        if await is_member(context.bot, user.id):
            await entry(update, context)
            return None
        return "هنوز عضو کانال نشدی؛ اول عضو شو و دوباره بزن."

    admin = get_admin(user.id)
    preview = False
    if admin is None and user.id == OWNER_ID and data.startswith("t:"):
        admin, preview = preview_admin(), True  # تست کارفرما: مراحل آموزش مثل یک ادمین تازه‌وارد
    if admin is None and not (user.id == OWNER_ID and data in (AD_BTN_CB, AD_PHOTO_BTN_CB, AD_BACK_CB)):  # پیش‌نمایش تقلب آگهی برای کارفرما (ردیف ادمین نداره)
        return "ابتدا /start رو بزن"
    if not await gate(update, context):
        return None
    if data in NUDGE_WHY:  # جواب «چرا هنوز جذب نزدی؟»؛ فقط یک جواب برای هر ادمین (آخرین جواب)
        if not preview:
            ex("INSERT OR REPLACE INTO nudge_why(user_id, choice, ts) VALUES(?,?,?)",
               (user.id, int(data[-1]), int(time.time())))
        if q.message is not None:
            _cid, _mid = q.message.chat_id, q.message.message_id
            try:  # کل پیام با دکمه‌ها میشه فقط یک جمله‌ی تشکر و چند ثانیه بعد پاک میشه
                await q.edit_message_text(NUDGE_THANKS)
            except TelegramError:
                pass
            ex("DELETE FROM holds WHERE chat_id=? AND message_id=?", (_cid, _mid))
            ex("DELETE FROM cleanup WHERE chat_id=? AND message_id=?", (_cid, _mid))
            async def _nudge_thanks_del(bot=context.bot, c=_cid, m=_mid):
                await asyncio.sleep(NUDGE_THANKS_SECS)
                await _safe_delete(bot, c, m)
            bg(_nudge_thanks_del())
        return None
    if data not in ("a:bp", "a:new", "a:ed"):
        await drop_card_emoji(context.bot, chat_id, user.id)

    if data == AD_BTN_CB:  # دکمه‌ی «دریافت متن آگهی» زیر تقلب با آگهی
        _ad_msg = await send_ad_body(context.bot, user.id, chat_id,
                                     back=(user.id == OWNER_ID or _src_has_back(update.callback_query)))
        if user.id == OWNER_ID and _ad_msg is not None and update.callback_query is not None \
                and update.callback_query.message is not None:
            _ck_preview_ads.setdefault(update.callback_query.message.message_id, []).append(_ad_msg.message_id)
        return None
    if data == AD_BACK_CB:  # «بازگشت» زیر متن یا عکس آگهی: همون پیام پاک میشه
        try:
            await q.message.delete()
        except TelegramError:
            pass
        return None
    if data == AD_PHOTO_BTN_CB:  # دکمه‌ی «دریافت عکس آگهی» زیر تقلب با آگهی
        _ad_msg = await send_ad_photo(context.bot, user.id, chat_id,
                                      back=(user.id == OWNER_ID or _src_has_back(update.callback_query)))
        if user.id == OWNER_ID and _ad_msg is not None and update.callback_query is not None \
                and update.callback_query.message is not None:
            _ck_preview_ads.setdefault(update.callback_query.message.message_id, []).append(_ad_msg.message_id)
        return None

    # ----- آموزش -----
    if data == "t:start":
        _h = track_get(user.id, "kbhint")
        if _h is not None:
            ex("DELETE FROM tracked WHERE user_id=? AND kind='kbhint'", (user.id,))
            bg(_safe_delete(context.bot, _h["chat_id"], _h["message_id"]))
        await finalize_welcome(q, admin)  # ادیت پیام خوشامد در همون جا (بدون ارسال پیام جدید)
        if get_setting("video_enabled") == "1" and get_setting("video_file_id"):
            sent_vid = await send_media(context.bot, chat_id, get_setting("video_kind"), get_setting("video_file_id"),
                             caption=get_text("video_caption"), html_mode=True,
                             kb=KB(B("🎬 ویدیو رو دیدم 🎬", "t:seen", style="success")))
            await replace_tracked(context.bot, user.id, "video", sent_vid)
        else:
            await send_step1(context, chat_id)
        return None
    if data == "t:seen":
        if not tut_first_time(q, data):
            return None
        await drop_msgs(context.bot, user.id, chat_id, q, ("video",))  # ویدیوی مرحله‌ی قبل پاک میشه
        await send_step1(context, chat_id)
        return None
    if data == "t:rsp":
        if not tut_first_time(q, data):
            return None
        await drop_msgs(context.bot, user.id, chat_id, q, ("tut1", "comment"))  # متن‌های مرحله‌ی اول پاک میشن
        s2 = await context.bot.send_message(chat_id, STEP2_TEXT, parse_mode=H,
                                            reply_markup=KB(B(BTN_GET_REPLY, "t:gr", style="danger")))
        await replace_tracked(context.bot, user.id, "tut2", s2)
        return None
    if data == "t:gr":
        if not tut_first_time(q, data):
            return None
        await drop_msgs(context.bot, user.id, chat_id, q, ("tut2",))  # متن مرحله‌ی دوم پاک میشه
        # متن پاسخگویی فقط با زدن دکمه و بدون هیچ تأخیری ارسال میشه
        sent_rsp = await context.bot.send_message(chat_id, REPLY_TEXT.replace('{code}', str(admin["code"])), parse_mode=H)
        await replace_tracked(context.bot, user.id, "reply", sent_rsp)
        ex("UPDATE admins SET training_done=1, training_done_at=?, warn_sent=0, warn_at=0, nudge_sent=0 WHERE user_id=?",
           (int(time.time()), user.id))
        ex("UPDATE comeback SET done_at=? WHERE user_id=? AND back=1 AND done_at=0", (int(time.time()), user.id))
        # اولین بار که این ادمین به «پنل شما فعال شد» میرسه توی عدد ممبرها حساب میشه (راه‌اندازی مجدد دوباره حساب نمیشه)
        ex("UPDATE admins SET counted=1 WHERE user_id=?", (user.id,))
        await asyncio.sleep(3)  # تنها اسلیپر این مرحله: ۳ ثانیه تا فعال شدن پنل
        _w = track_get(user.id, "welcome")
        _w_id = _w["message_id"] if _w is not None and _w["chat_id"] == chat_id else None
        for _k in ("welcome", "tut1", "tut2", "comment", "reply", "video"):  # پیام‌های آموزش دیگه هیچ‌وقت پاک نمیشن
            ex("DELETE FROM tracked WHERE user_id=? AND kind=?", (user.id, _k))
        if bot_off() and not preview:
            await send_maintenance(context.bot, chat_id, user.id, with_kb=True)
            _kb = track_get(user.id, "kb")
            if _kb is not None:
                track_set(user.id, "tutend", _kb["chat_id"], _kb["message_id"], _w_id)
            await drop_welcome_back(context.bot, user.id)
        else:
            await send_panel_active(context.bot, chat_id)
            await drop_welcome_back(context.bot, user.id)
            _carrier = await send_reply_keyboard(context.bot, chat_id, carrier="💻")
            if _carrier is not None:
                # مرز آموزش: از پیام خوشامد تا 💻؛ پاکسازی خودکار ۳۰ ثانیه‌ای این بازه رو پاک نمیکنه
                track_set(user.id, "tutend", _carrier.chat_id, _carrier.message_id, _w_id)
            if preview:
                bg(owner_back_after_test(context, chat_id))
        return None
    # ----- منوی ادمین -----
    if data == NOACT_CK_CB:  # «🃏 مشاهده تقلب‌ها 🃏» زیر اطلاعیه‌ی ۳ روز بی‌جذب: همون بخش دکمه‌ی «تقلب»
        drop_contents(context.bot, user.id, keep=("menu", "chold"))
        _ckb = cheat_admin_kb()
        _hold = await send(context.bot, chat_id, CHEAT_HOLDER, html_mode=False)
        await replace_tracked(context.bot, user.id, "chold", _hold)
        _sent = await send(context.bot, chat_id, CHEAT_MENU_TEXT if _ckb else CHEAT_EMPTY_TEXT,
                           _ckb or KB(BACK("a:menu")), html_mode=True)
        await replace_tracked(context.bot, user.id, "menu", _sent, cmd_id=None)
        return None
    if data.startswith("a:ckv:"):  # ادمین روی یکی از دکمه‌های منوی تقلب زد
        _cid = data[6:]
        _c = cheat_get(int(_cid)) if _cid.isdigit() else None
        if _c is None:
            return "این تقلب پیدا نشد."
        if _c["kind"] == "ad":
            _t, _ak = ad_cheat_message(ad_title_for_view(user.id))
            _k = KB(*ad_buttons(), BACK_PLAIN(AD_BACK_CB))  # بازگشتِ بیرنگ زیر تقلب آگهی
        elif (_c["text"] or "").strip():
            _t, _k = _c["text"], (story_cheat_kb(BACK_PLAIN(AD_BACK_CB)) if is_story_cheat(_c) else KB(BACK_PLAIN(AD_BACK_CB)))  # بازگشتِ بیرنگ: همون پیام پاک میشه و منوی تقلب می‌مونه
        else:
            return "این تقلب هنوز متن نداره."
        _msg = await send_cheat_msg(context.bot, chat_id, _t, _k, photo=(_c["photo"] if _c["kind"] != "ad" else None),
                                    no_preview=(bool(_c["no_preview"]) if _c["kind"] != "ad" else False))
        await replace_tracked(context.bot, user.id, "cheatv", _msg)
        return None
    if data in ("a:menu", "a:can"):
        clear_state(user.id)
        # اگر کاربر از گزارش تصویری برگردد، هر دو تصویر قبلی هم پاک شوند.
        for kind in ("profile", "activity", "chold", "cheatv"):
            tracked = track_get(user.id, kind)
            if tracked is not None and tracked["chat_id"] == chat_id:
                await _safe_delete(context.bot, tracked["chat_id"], tracked["message_id"])
                ex("DELETE FROM tracked WHERE user_id=? AND kind=?", (user.id, kind))
        await close_glass(update, context)
        return None
    if data == "a:rep":
        drop_contents(context.bot, user.id, keep=("profile", "activity", "menu"))
        await send_profile_report(context.bot, user.id, chat_id, admin)
        return None
    if data in ("a:up2", "a:up3") or data.startswith("a:lv:"):
        try:
            view = int(data[-1])
        except ValueError:
            return None
        if view not in (1, 2, 3):
            return None
        view = max(view, level_of(admin))  # دکمه‌ی قدیمیِ سطحی که ازش رد شده (پیام‌های قبلی) به سطح فعلی میره
        await switch_level_view(context, user.id, chat_id, q, admin, view)
        await refresh_activity(context, user.id, chat_id, admin, view)
        return None
    if data == "a:cmt":
        drop_contents(context.bot, user.id, keep=("comment", "menu"))
        await send_comment_text(context.bot, user.id, chat_id)
        return None
    if data == "a:rsp":
        drop_contents(context.bot, user.id, keep=("reply", "menu"))
        await send_reply_text(context.bot, user.id, chat_id, admin)
        return None
    if data == "a:vid":
        fid = get_setting("video_file_id")
        if not fid:
            return "ویدیوی آموزشی هنوز توسط کارفرما ثبت نشده."
        drop_contents(context.bot, user.id, keep=("video", "menu"))
        await send_video_tracked(context.bot, user.id, chat_id, fid)
        return None
    if data == "a:ct":
        clear_state(user.id)
        await show(update, context, CONTACT_MENU_TEXT, contact_menu_kb(), html_mode=False)
        return None
    if data == "a:sg":
        set_state(user.id, "suggest", {})
        await show(update, context, SUGGEST_TEXT, KB(BACK("a:ct")), html_mode=False)
        return None
    if data == "a:cln":
        await clean_texts(context.bot, user.id)
        await send_reply_keyboard(context.bot, chat_id, carrier=ADMIN_MENU_TEXT)  # بدون استارت دوباره؛ فقط منو + کیبورد
        return None
    if data == "a:rst":
        clear_state(user.id)
        reset_training(user.id)
        try:
            await q.message.delete()
        except TelegramError:
            pass
        await hide_reply_keyboard(context.bot, chat_id, user.id)
        await send_welcome(context, chat_id, admin)
        return None

    # ----- سوابق پورسانت -----
    if data == "a:rec":
        clear_state(user.id)
        text, kb = records_view(user.id)
        await show(update, context, text, kb, html_mode=False)
        return None
    if data == "a:rall":
        rows = qa("SELECT * FROM commissions WHERE admin_id=? AND status='paid' ORDER BY paid_at DESC", (user.id,))
        if not rows:
            return "سابقه‌ای پیدا نشد."
        async with loading(context.bot, chat_id):
            for c in rows:
                await send_receipt_to(context.bot, chat_id, c, receipt_caption_for_admin(c), html_mode=True, kb=ADMIN_RECEIPT_KB())
        return None
    if data == "a:rdate" or data.startswith("a:rdp:"):
        page = int(data[6:]) if data.startswith("a:rdp:") else 0
        days = qa("SELECT paid_day, MAX(paid_at) ts FROM commissions WHERE admin_id=? AND status='paid' "
                  "GROUP BY paid_day ORDER BY paid_day DESC", (user.id,))
        if not days:
            return "سابقه‌ای پیدا نشد."
        pages = max((len(days) + PAGE_SIZE - 1) // PAGE_SIZE, 1)
        page = min(max(page, 0), pages - 1)
        rows = [B(f"🔷{jdate(d['ts'])}🔷", f"a:rd:{d['paid_day']}", style=cyc(i, "primary", "danger", "success"))
                for i, d in enumerate(days[page * PAGE_SIZE:(page + 1) * PAGE_SIZE])]
        nav = nav_row(lambda p: f"a:rdp:{p}", page, pages)
        if nav:
            rows.append(nav)
        rows.append(BACK("a:rec"))
        rows.append(MAIN())
        await show(update, context,
                   "📅 لطفا تاریخ موردنظرت رو از جدول زیر انتخاب کن تا فیش واریزی همون تاریخ برات ارسال بشه🔻",
                   KB(*rows), html_mode=False)
        return None
    if data.startswith("a:rd:"):
        key = data[5:]
        rows = qa("SELECT * FROM commissions WHERE admin_id=? AND status='paid' AND paid_day=? ORDER BY paid_at DESC",
                  (user.id, key))
        if not rows:
            return "برای این تاریخ فیشی پیدا نشد."
        async with loading(context.bot, chat_id):
            for c in rows:
                await send_receipt_to(context.bot, chat_id, c, receipt_caption_for_admin(c), html_mode=True, kb=ADMIN_RECEIPT_KB())
        return None

    # ----- درخواست پورسانت -----
    if data in ("a:req", "a:reqc"):
        src = "c" if data == "a:reqc" else "r"
        c = q1("SELECT * FROM commissions WHERE admin_id=? AND status='earned' ORDER BY period_no LIMIT 1",
               (user.id,))
        if c is None:
            return "شما در حال حاضر پورسانتی برای دریافت ندارید."
        await req_step(update, context, user.id, c["id"], src)
        return None
    if data == "a:bo":  # بازگشت به مبدا: پیام تبریک یا سوابق پورسانت
        st, d = get_state(user.id)
        clear_state(user.id)
        await show_req_origin(update, context, user.id, d.get("src", "r"), d.get("cid"), d.get("om"))
        return None
    if data == "a:bl":  # بازگشت به لیست کارت‌ها
        st, d = get_state(user.id)
        if "cid" not in d:
            clear_state(user.id)
            await show_req_origin(update, context, user.id, "r", None)
            return None
        st_merge(user.id, "pay", pf="o")
        await show_card_list(update, context, user.id)
        return None
    if data == "a:bc":  # بازگشت به تأیید اطلاعات
        st, d = get_state(user.id)
        if "number" not in d or "cid" not in d:
            return "این درخواست منقضی شده؛ دوباره از «سوابق پورسانت» شروع کن."
        d = st_merge(user.id, "pay")
        await show_confirm(update, context, user.id, d)
        return None
    if data == "a:bp":  # بازگشت به صفحه‌ی ارسال کارت
        st, d = get_state(user.id)
        if "cid" not in d:
            return "این درخواست منقضی شده؛ دوباره از «سوابق پورسانت» شروع کن."
        d = st_merge(user.id, "card_input")
        await show_prompt(update, context, user.id, d.get("pf", "o"))
        return None
    if data == "a:dc":  # حذف کارت: از کارت‌های ذخیره‌شده پاک میشه و برمیگرده به لیست (یا ثبت کارت اگه کارتی نمونده)
        st, d = get_state(user.id)
        if st != "pay" or "cid" not in d or "number" not in d:
            return "این درخواست منقضی شده؛ دوباره از «سوابق پورسانت» شروع کن."
        ex("DELETE FROM cards WHERE admin_id=? AND number=?", (user.id, d["number"]))
        audit(user.id, "card_delete", card_mask(d["number"]))
        await req_step(update, context, user.id, d["cid"], d.get("src", "r"), d.get("om") or 0)
        return None
    if data == "a:new":
        st, d = get_state(user.id)
        if st not in ("pay", "card_input") or "cid" not in d:
            return "این درخواست منقضی شده؛ دوباره از «سوابق پورسانت» شروع کن."
        st_merge(user.id, "card_input", pf="l")
        await show_prompt(update, context, user.id, "l")
        return None
    if data == "a:ed":
        st, d = get_state(user.id)
        if st != "pay" or "cid" not in d or "number" not in d:
            return "این درخواست منقضی شده؛ دوباره از «سوابق پورسانت» شروع کن."
        st_merge(user.id, "card_input", pf="e")
        await show_prompt(update, context, user.id, "e")
        return None
    if data.startswith("a:pc:"):
        st, d = get_state(user.id)
        card = q1("SELECT * FROM cards WHERE id=? AND admin_id=?", (int(data[5:]), user.id))
        if st != "pay" or "cid" not in d or card is None:
            return "این درخواست منقضی شده؛ دوباره از «سوابق پورسانت» شروع کن."
        d = st_merge(user.id, "pay", number=card["number"], holder=card["holder"], via="p")
        await show_confirm(update, context, user.id, d)
        return None
    if data == "a:ok":
        st, d = get_state(user.id)
        if st != "pay" or "number" not in d:
            return "این درخواست منقضی شده؛ دوباره از «سوابق پورسانت» شروع کن."
        save_card(user.id, d["number"], d["holder"])
        audit(user.id, "card_save", f"{card_mask(d['number'])} | {d['holder']}")
        ok = create_request(user.id, d["cid"], d["number"], d["holder"])
        await clean_card_flow(context.bot, user.id, chat_id, q, d)
        if not ok:
            await send(context.bot, chat_id, "برای این دوره قبلا درخواست پرداخت ثبت شده و تکراری قابل ثبت نیست.",
                       KB(MAIN()), html_mode=False)
            return None
        text = get_text("req_success").replace("{deadline}", "یک ساعت")  # مهلت ثابت: حداکثر یک ساعت
        _ok = await send(context.bot, chat_id, text, KB(MAIN()), html_mode=False)
        try:
            track_set(user.id, f"reqok:{d['cid']}", _ok.chat_id, _ok.message_id)
        except Exception:  # noqa
            pass
        c = q1("SELECT * FROM commissions WHERE id=?", (d["cid"],))
        audit(user.id, "commission_request", f"cid={d['cid']} period={c['period_no']} amount={c['amount']}")
        _rq_msg = await safe_send(context.bot, OWNER_ID,
                        fbox("💳 درخواست واریز جدید داری!!",
                             f"👤 ادمین: {link(admin)} | کد「{admin['code']}」\n"
                             f"💰 مبلغ:「{fmt_en(c['amount'])}」تومان"),
                        KB(*([B(f"به نام: {c['card_holder']}", "o:noop")] if c["card_holder"] else []),
                           B("پرداخت", copy=c["card_number"], style="success"),
                           B("📩 ارسال فیش واریزی 📩", f"o:fs:{c['id']}", style="primary")))
        await pin_request(context.bot, c["id"], _rq_msg)
        return None
    return None


def confirm_text(number: str, holder: str) -> str:
    return ("📋 اطلاعات ثبت‌شده شما:\n\n"
            f"💳 شماره کارت: {card_fmt(number)}\n\n"
            f"👤 نام صاحب حساب: {FSI}{holder}{PDI}\n\n"
            "آیا اطلاعات بالا صحیح است؟")


def confirm_kb(back: str = "a:bl"):
    return KB([B("✏️ ویرایش", "a:ed", style="danger"), B("✅ تأیید", "a:ok", style="success")],
              B("🗑️ حذف کارت 🗑️", "a:dc", style="danger"),
              BACK(back), MAIN())


def mark_receipt(msg):
    """پیام فیش واریز (برای ادمین): توی پاکسازی ۳۰ ثانیه‌ای هم پاک میشه و «آخرین پیام» حساب نمیشه."""
    try:
        if msg is not None and msg.chat_id != OWNER_ID:
            ex("INSERT OR IGNORE INTO receipt_msgs(chat_id,message_id) VALUES(?,?)", (msg.chat_id, msg.message_id))
    except Exception:  # noqa
        pass


async def hold_receipt(bot, uid: int, cid: int, msg):
    """فیش واریز تازه: پاکسازی خودکار بهش دست نمیزنه و فقط وقتی ادمین دکمه‌ی جدیدی بزنه پاک میشه (شاید آفلاین باشه).
    پیام «درخواست شما با موفقیت ثبت شد» همون لحظه پاک میشه تا فیش آخرین پیام چت بمونه."""
    try:
        if msg is None or msg.chat_id == OWNER_ID:
            return
        track_set(uid, f"receipt:{cid}", msg.chat_id, msg.message_id)
        r = track_get(uid, f"reqok:{cid}")
        if r is not None:
            ex("DELETE FROM tracked WHERE user_id=? AND kind=?", (uid, f"reqok:{cid}"))
            await _safe_delete(bot, r["chat_id"], r["message_id"])
    except Exception as e:  # noqa
        log_err(f"hold_receipt {uid}: {e!r}")


# ---------- پیام‌های نگه‌داشته‌شده: جذب جدید، اعلان‌های مدیر، درخواست‌های واریز ----------
AC_DELAYS = (10, 30, 60, 300)            # زمان پاکسازی خودکار بعد از آخرین فعالیت (ثانیه)
OWNER_DAY_ROLL = 6                         # ساعت عوض شدن «روز» برای گزارش جذب‌های پنل مدیر (۶ صبح تا ۶ صبح روز بعد)
ADMIN_HIRE_HOLD = 10800                    # مدت ماندن پیام جذب توی پنل ادمین (۳ ساعت؛ بازه‌ی شبانه مثل قبل رعایت میشه)
HOLD_OPTS = (1800, 3600, 7200, 10800)    # مدت ماندن پیام‌های جذب و اعلان‌ها (ثانیه)
NIGHT_ENDS = (6, 8, 10, 12)              # پایان بازه‌ی شبانه (ساعت)؛ شروعش همیشه ۱۲ شبه
HOLD_FOREVER = 9999999999                # درخواست واریز تا «ثبت شد» می‌مونه


def _int_setting(key: str, default: int) -> int:
    try:
        return int(get_setting(key))
    except (TypeError, ValueError):
        return default


def ac_on() -> bool:
    return get_setting("ac_on") != "0"


def ac_delay() -> int:
    v = _int_setting("ac_delay", 30)
    return v if v in AC_DELAYS else 30


def drop_prev_on() -> bool:
    return get_setting("drop_prev") != "0"


def hold_secs() -> int:
    v = _int_setting("hold_secs", 3600)
    return v if v in HOLD_OPTS else 3600


def night_on() -> bool:
    return get_setting("night_on") != "0"


def night_end() -> int:
    v = _int_setting("night_end", 12)
    return v if v in NIGHT_ENDS else 12


def notice_deadline(now: float = None, secs: int = None) -> int:
    """زمان پاک شدن پیام جذب/اعلان: زمان رسیدن + مدت ماندن؛ اگه تو بازه‌ی شبانه (۱۲ شب تا ساعت پایان) افتاد، به پایان بازه میره."""
    t = (now if now is not None else time.time()) + (secs if secs else hold_secs())
    if night_on():
        dt = datetime.fromtimestamp(t, TZ)
        end = night_end()
        if dt.hour < end:
            t = dt.replace(hour=end, minute=0, second=0, microsecond=0).timestamp()
    return int(t)


def day_end_deadline(now: float = None) -> int:
    """پایان «روزِ» جاری (ساعت OWNER_DAY_ROLL به وقت تهران)؛ همه‌ی جذب‌های یک روز همزمان پاک میشن."""
    dt = datetime.fromtimestamp(now if now is not None else time.time(), TZ)
    end = dt.replace(hour=OWNER_DAY_ROLL, minute=0, second=0, microsecond=0)
    if end <= dt:
        end = end + timedelta(days=1)
    return int(end.timestamp())


def hold_notice(msg, chat_id: int = None, day_end: bool = False, secs: int = None):
    """پیام جذب/اعلان: تا موعدش از پاکسازی خودکار در امانه و بعدش خودش پاک میشه."""
    try:
        if msg is None:
            return
        cid = getattr(msg, "chat_id", None) or chat_id
        mid = getattr(msg, "message_id", None)
        if not isinstance(cid, int) or not isinstance(mid, int):
            return
        until = day_end_deadline() if day_end else notice_deadline(secs=secs)
        ex("INSERT OR REPLACE INTO holds(chat_id,message_id,until) VALUES(?,?,?)", (cid, mid, until))
        ex("INSERT INTO cleanup(chat_id,message_id,due) VALUES(?,?,?)", (cid, mid, until))
    except Exception as e:  # noqa
        log_err(f"hold_notice: {e!r}")


async def safe_send_hold(bot, chat_id, text, kb=None, html_mode=True, day_end: bool = False):
    m = await safe_send(bot, chat_id, text, kb, html_mode)
    hold_notice(m, day_end=day_end)
    return m


ALERT_EMOJI = "🚨"


async def send_alert(bot, chat_id, text, kb=None, html_mode=True, secs: int = None):
    """هر هشدار: اول یه 🚨 تکی، بعدش متن هشدار. هر دو تا موعد از پاکسازی خودکار در امانن و با پاک شدن متن هشدار
    (چه با موعدش، چه با پاکسازی دستی) اموجی هم پاک میشه. اگه متن هشدار ارسال نشد، اموجی هم برداشته میشه."""
    e = await safe_send(bot, chat_id, ALERT_EMOJI, html_mode=False)
    m = await safe_send(bot, chat_id, text, kb, html_mode)
    if m is None:
        if e is not None:
            bg(_safe_delete_one(bot, chat_id, e.message_id))
        return None
    if e is not None:
        ex("INSERT OR REPLACE INTO alert_pairs(chat_id,alert_id,emoji_id) VALUES(?,?,?)",
           (chat_id, m.message_id, e.message_id))
        hold_notice(e, chat_id=chat_id, secs=secs)
    hold_notice(m, chat_id=chat_id, secs=secs)
    return m


def hold_ids(uid: int) -> set:
    return {r["message_id"] for r in qa("SELECT message_id FROM holds WHERE chat_id=? AND until>?",
                                        (uid, int(time.time())))}


def report_hold_ids(uid: int) -> set:
    """پیام‌های نگه‌داشته‌شده از پاکسازی خودکار: متن جذب جدید + پروفایل و گزارش فعالیت (با «بازگشت» پاک میشن)."""
    ids = hold_ids(uid)
    for _k in (("profile", "activity", "owncount") if uid == OWNER_ID else ("profile", "activity")):  # عدد اعضا تو پاکسازی خودکار پاک نمیشه
        _r = track_get(uid, _k)
        if _r is not None and _r["chat_id"] == uid:
            ids.add(_r["message_id"])
    return ids


async def pin_request(bot, cid: int, msg):
    """درخواست واریز جدید توی پنل مدیر: بی‌صدا پین میشه و تا «ثبت شد» از پاکسازی در امانه."""
    try:
        if msg is None:
            return
        track_set(OWNER_ID, f"req:{cid}", msg.chat_id, msg.message_id)
        ex("INSERT OR REPLACE INTO holds(chat_id,message_id,until) VALUES(?,?,?)",
           (msg.chat_id, msg.message_id, HOLD_FOREVER))
        await bot.pin_chat_message(msg.chat_id, msg.message_id, disable_notification=True)
    except Exception as e:  # noqa
        log_err(f"pin_request {cid}: {e!r}")


async def pin_quiet(bot, chat_id: int, msg) -> None:
    """پین بی‌صدا؛ پیام سرویس «پین شد» رو del_pin_service همون لحظه پاک می‌کنه. خطا هیچ‌وقت ارسال رو خراب نمی‌کنه."""
    try:
        if msg is not None:
            await bot.pin_chat_message(chat_id, msg.message_id, disable_notification=True)
    except Exception as e:  # noqa
        log_err(f"pin_quiet {chat_id}: {e!r}")


async def finish_request(bot, cid: int, extra=(), delay: int = 3):
    """واریز ثبت شد: درخواست از پین درمیاد؛ بعد از چند ثانیه خود درخواست و پیام‌های مربوطش پاک میشن."""
    ids = [m for m in extra if isinstance(m, int)]
    r = track_get(OWNER_ID, f"req:{cid}")
    if r is not None:
        try:
            await bot.unpin_chat_message(r["chat_id"], r["message_id"])
        except TelegramError:
            pass
        ids.append(r["message_id"])
        ex("DELETE FROM tracked WHERE user_id=? AND kind=?", (OWNER_ID, f"req:{cid}"))
        ex("DELETE FROM holds WHERE chat_id=? AND message_id=?", (r["chat_id"], r["message_id"]))
    if not ids:
        return
    for mid in ids:
        schedule_delete(OWNER_ID, mid, 60)  # پشتیبان: اگه ربات وسط کار ری‌استارت شد

    async def _later():
        if delay:
            await asyncio.sleep(delay)
        for mid in ids:
            await _safe_delete(bot, OWNER_ID, mid)
    bg(_later())


async def release_stale_requests(bot):
    """درخواستی که دیگه در انتظار واریز نیست (مثلا ادمین حذف شده) از پین درمیاد و پاک میشه."""
    now = int(time.time())
    for r in qa("SELECT kind FROM tracked WHERE user_id=? AND kind LIKE 'req:%'", (OWNER_ID,)):
        try:
            cid = int(r["kind"][4:])
        except ValueError:
            continue
        c = q1("SELECT status, paid_at FROM commissions WHERE id=?", (cid,))
        if c is not None and (c["status"] == "requested" or (c["status"] == "paid" and now - (c["paid_at"] or 0) < 15)):
            continue
        await finish_request(bot, cid, delay=0)


def receipt_hold_ids(uid: int) -> set:
    return {r["message_id"] for r in qa(
        "SELECT message_id FROM tracked WHERE user_id=? AND chat_id=? AND kind LIKE 'receipt:%'", (uid, uid))}


def drop_receipts(bot, uid: int):
    """ادمین دکمه‌ی جدیدی زد: فیش‌های نگه‌داشته‌شده پاک میشن."""
    for r in qa("SELECT kind, chat_id, message_id FROM tracked WHERE user_id=? AND kind LIKE 'receipt:%'", (uid,)):
        ex("DELETE FROM tracked WHERE user_id=? AND kind=?", (uid, r["kind"]))
        bg(_safe_delete(bot, r["chat_id"], r["message_id"]))


def receipt_ids(uid: int) -> set:
    return {r["message_id"] for r in qa("SELECT message_id FROM receipt_msgs WHERE chat_id=?", (uid,))}


def ADMIN_RECEIPT_KB():
    """زیر فیش‌های واریزِ ادمین: بازگشت به سوابق + بازگشت به منوی اصلی."""
    return KB(BACK("a:rec"), MAIN())


async def send_receipt_to(bot, chat_id, c, caption, html_mode=False, kb=None):
    """بدون اسلیپ ثابت؛ فقط اگه تلگرام flood_wait داد مکث میکنه و دوباره میفرسته."""
    try:
        for attempt in range(4):
            try:
                _rm = await send_media(bot, chat_id, c["receipt_kind"] or "document", c["receipt_file_id"],
                                       caption=caption, kb=kb, html_mode=html_mode)
                mark_receipt(_rm)
                return
            except RetryAfter as e:
                if attempt == 3:
                    raise
                await asyncio.sleep(e.retry_after + 1)
    except Exception as e:  # noqa
        log_err(f"receipt send failed: {e!r}")
        await safe_send(bot, chat_id, caption, kb, html_mode=html_mode)


async def admin_message(update: Update, context):
    user = update.effective_user
    m = update.effective_message
    # پیام استخدام متقاضی که ادمین نیست: فقط جذب ثبت می‌شود؛ هرگز ادمین جدید ساخته نمی‌شود.
    text = (m.text or m.caption or "")
    if get_admin(user.id) is None:
        if text:
            stat_code_only(user, text, ts=_event_ts(m))
        if text and await process_hire(context, user, text):
            return
        return
    if not await gate(update, context):
        return
    create_admin(user)
    admin = get_admin(user.id)
    chat_id = update.effective_chat.id

    # دکمه‌های کیبورد معمولی همان عملیات دکمه‌های اصلی شیشه‌ای را اجرا می‌کنند.
    # زیرمنوها و دکمه‌های داخل آن‌ها همچنان از callbackهای فعلی استفاده می‌کنند.
    if admin["training_done"] or any(text in _v for _v in RBTN_ALIASES.values()):
        kb_key = next((k for k, v in RBTN_ALIASES.items() if text in v), None)
        if kb_key:
            if get_state(user.id)[0] in ("suggest", "card_input", "pay"):
                clear_state(user.id)  # دکمه‌ی دیگه‌ای زده؛ حالت دریافت پیشنهاد بسته میشه
            await del_cmd(m)  # متن دکمه فوری پاک میشه؛ فقط نتیجه میاد
        if kb_key and throttled(user.id, "kb:" + kb_key):
            return  # ضداسپم: فاصله ۲ ثانیه بین زدن پشت‌سرهم یک دکمه
        if text in RBTN_ALIASES["report"]:
            drop_contents(context.bot, user.id, keep=("profile", "activity"))
            await send_profile_report(context.bot, user.id, chat_id, admin)
            return
        if text in RBTN_ALIASES["comment"]:
            drop_contents(context.bot, user.id, keep=("comment",))
            await send_comment_text(context.bot, user.id, chat_id)
            return
        if text in RBTN_ALIASES["reply"]:
            drop_contents(context.bot, user.id, keep=("reply",))
            await send_reply_text(context.bot, user.id, chat_id, admin)
            return
        if text in RBTN_ALIASES["video"]:
            fid = get_setting("video_file_id")
            if not fid:
                drop_contents(context.bot, user.id, keep=("video",))
                _nv = await send(context.bot, chat_id, "ویدیوی آموزشی هنوز توسط کارفرما ثبت نشده.", html_mode=False)
                await replace_tracked(context.bot, user.id, "video", _nv)
                return
            drop_contents(context.bot, user.id, keep=("video",))
            await send_video_tracked(context.bot, user.id, chat_id, fid)
            return
        if text in RBTN_ALIASES["records"]:
            drop_contents(context.bot, user.id, keep=("menu",))
            rtext, rkb = records_view(user.id)
            sent_menu = await send(context.bot, chat_id, rtext, rkb, html_mode=False)
            await replace_tracked(context.bot, user.id, "menu", sent_menu, cmd_id=None)
            return
        if text in RBTN_ALIASES["contact"]:
            drop_contents(context.bot, user.id, keep=("menu",))
            sent_c = await send(context.bot, chat_id, CONTACT_MENU_TEXT, contact_menu_kb(), html_mode=False)
            await replace_tracked(context.bot, user.id, "menu", sent_c)
            return
        if text in RBTN_ALIASES["clean"]:
            drop_contents(context.bot, user.id, keep=("menu",))
            sent_cl = await send(context.bot, chat_id, CLEAN_TEXT, clean_menu_kb(), html_mode=False)
            await replace_tracked(context.bot, user.id, "menu", sent_cl, cmd_id=None)
            return
        if text in RBTN_ALIASES["cheat"]:
            drop_contents(context.bot, user.id, keep=("menu", "chold"))
            _ckb = cheat_admin_kb()
            _hold = await send(context.bot, chat_id, CHEAT_HOLDER, html_mode=False)
            await replace_tracked(context.bot, user.id, "chold", _hold)
            sent_ck = await send(context.bot, chat_id, CHEAT_MENU_TEXT if _ckb else CHEAT_EMPTY_TEXT,
                                 _ckb or KB(BACK("a:menu")), html_mode=True)
            await replace_tracked(context.bot, user.id, "menu", sent_ck, cmd_id=None)
            return
        if text in RBTN_ALIASES["restart"]:
            clear_state(user.id)
            reset_training(user.id)
            drop_contents(context.bot, user.id)
            await hide_reply_keyboard(context.bot, chat_id, user.id)
            await send_welcome(context, chat_id, admin)
            return

    st, d = get_state(user.id)
    if st == "suggest":
        if not m.text:  # عکس، ویدیو و هر رسانه‌ی دیگه: حالت پیشنهاد باز می‌مونه تا متن بفرسته
            await send(context.bot, chat_id,
                       "🚧 متاسفانه داخل این بخش امکان ارسال رسانه وجود نداره دوست خوبم🚧",
                       html_mode=False)
            return
        clear_state(user.id)
        await send_suggestion(context, admin, m)
        sent_t = await send(context.bot, chat_id, SUGGEST_THANKS, KB(MAIN()), html_mode=False)
        await replace_tracked(context.bot, user.id, "menu", sent_t)
        return
    if st == "card_input" and "cid" in d:
        if not m.text:
            await send(context.bot, chat_id, "لطفا شماره کارت و نام صاحب حساب رو به صورت متن بفرست.", html_mode=False)
            return
        _n, _h = split_card_input(m.text)
        num = _n or d.get("pn")
        hold = _h or d.get("ph")
        um = list(d.get("um") or []) + [m.message_id]
        if not (num and hold):
            schedule_delete(chat_id, m.message_id, STRAY_TTL)
            hint_msg = await send(context.bot, chat_id, card_hint(m.text, _n, _h), html_mode=False)
            st_merge(user.id, "card_input", pn=num, ph=hold, um=um + [hint_msg.message_id])
            return
        cm = list(d.get("cm") or []) + um
        nd = st_merge(user.id, "pay", number=num, holder=hold, via="t", pn=None, ph=None, um=None, cm=cm)
        for _mid in um:
            schedule_delete(chat_id, _mid, 40)
        # منوی قبلی (ارسال کارت) پاک میشه و منوی جدید (تأیید و ویرایش) به‌صورت پیام تازه میاد
        if nd.get("pm"):
            bg(_safe_delete(context.bot, chat_id, nd["pm"]))
        await drop_card_emoji(context.bot, chat_id, user.id)
        new_pm = await send(context.bot, chat_id, confirm_text(num, hold), confirm_kb("a:bp"), html_mode=False)
        st_merge(user.id, "pay", pm=new_pm.message_id)
        return
    # پیام متفرقه: خودش بعد از ۱۰ دقیقه پاک میشه و منوی اصلی (کیبورد معمولی) حداکثر هر ۱۰ دقیقه یک بار میاد
    schedule_delete(chat_id, m.message_id)
    if admin["training_done"] and menu_due(user.id, KB_GAP):
        await send_admin_menu(context, chat_id)


# ----------------------------------------------------------------------------
# ثبت جذب و اعلان‌ها
# ----------------------------------------------------------------------------
def congrats_text(target, amount) -> str:
    return (TEXT_DEFAULTS["congrats"].replace("{target}", str(target))
            .replace("{amount}", f"{fmt_en(amount)} تومان"))


def congrats_for_commission(target, amount, period_no, lvl=None) -> str:
    """متن تبریکِ یک پورسانتِ ثبت‌شده: اگه اون دوره ارتقای سطح داشته، متن ارتقا؛ وگرنه متن تبریک عادی."""
    cur = int(lvl) if lvl else level_for_period(int(period_no))  # سطح واقعی موقع کامل شدن دوره (ادمینِ افت‌کرده هم تبریک ارتقا میگیره)
    nxt = min(cur + 1, LEVEL_MAX)
    if nxt > cur:
        return levelup_congrats_text(nxt, target, amount, get_int_setting("pay_target"), level_amount(nxt))
    return congrats_text(target, amount)


CONFETTI_EFFECT = "5046509860389126442"  # افکت 🎉 تلگرام (فقط چت خصوصی)


async def send_panel_active(bot, chat_id):
    """پیام «پنل شما فعال شد» با افکت 🎉 تلگرام؛ اگه افکت ممکن نبود همون پیام بدون افکت میره."""
    for kw in ({"message_effect_id": CONFETTI_EFFECT}, {}):
        try:
            return await bot.send_message(chat_id, PANEL_ACTIVE_TEXT, parse_mode=H, **kw)
        except RetryAfter as e:
            await asyncio.sleep(e.retry_after + 1)
        except Exception as e:  # noqa
            log_err(f"panel active msg to {chat_id}: {e!r}")
    return None


async def send_levelup_congrats(bot, a, text, kb):
    """پیام تبریک ارتقا: عکس اصلی سطح جدید + افکت 🎉 تلگرام + دکمه‌ی دریافت پورسانت.
    اگه عکس یا افکت ممکن نبود، ساده‌تر فرستاده میشه تا پیام هیچ‌وقت گم نشه."""
    uid = a["user_id"]
    fid = get_setting(LEVEL_PHOTO_KEYS[level_of(a)][0])
    attempts = []
    if fid:
        attempts += [("photo", {"message_effect_id": CONFETTI_EFFECT}), ("photo", {})]
    attempts += [("text", {"message_effect_id": CONFETTI_EFFECT}), ("text", {})]
    for kind, kw in attempts:
        try:
            if kind == "photo":
                return await bot.send_photo(uid, fid, caption=text, parse_mode=H, reply_markup=kb, **kw)
            return await bot.send_message(uid, text, parse_mode=H, reply_markup=kb, **kw)
        except RetryAfter as e:
            await asyncio.sleep(e.retry_after + 1)
        except Forbidden:
            mark_blocked(uid)
            return None
        except Exception as e:  # noqa
            log_err(f"levelup congrats {kind} to {uid}: {e!r}")
    return await safe_send(bot, uid, text, kb)


async def send_congrats_effect(bot, uid, text, kb):
    """تبریک تکمیل دوره (بدون ارتقا): فقط متن + افکت 🎉 تلگرام؛ اگه افکت ممکن نبود همون متن بدون افکت میره."""
    for kw in ({"message_effect_id": CONFETTI_EFFECT}, {}):
        try:
            return await bot.send_message(uid, text, parse_mode=H, reply_markup=kb, **kw)
        except RetryAfter as e:
            await asyncio.sleep(e.retry_after + 1)
        except Forbidden:
            mark_blocked(uid)
            return None
        except Exception as e:  # noqa
            log_err(f"congrats effect to {uid}: {e!r}")
    return await safe_send(bot, uid, text, kb)


def shield_on() -> bool:
    return get_setting("shield") == "1"


def admin_shield_on(admin_id) -> bool:
    """سپر مخصوص یک ادمین (از دکمه‌ی جستجوی ادمین)."""
    try:
        return admin_id is not None and q1("SELECT 1 FROM shield_admins WHERE admin_id=?", (admin_id,)) is not None
    except Exception as e:  # noqa
        log_err(f"admin_shield_on: {e!r}")
        return False


def admin_shield_by_code(code) -> bool:
    r = q1("SELECT user_id FROM admins WHERE code=?", (code,))
    return r is not None and admin_shield_on(r["user_id"])


def shield_owner_replied(applicant_id) -> None:
    """سپر: هر تعداد پیام کارفرما بعد از پیام اول متقاضی، یک پیام حساب میشه."""
    try:
        if applicant_id:  # ردیف pending فقط وقتی هست که سپر (کلی یا مخصوص ادمین) روشن بوده
            ex("UPDATE shield_pending SET stage=1 WHERE applicant_id=? AND stage=0", (applicant_id,))
    except Exception as e:  # noqa
        log_err(f"shield_owner_replied: {e!r}")


SUS_WINDOW = 600  # 10 دقیقه
SUS_LIMIT = 7     # بیشتر از 7 جذب در بازه
_sus_last = {}


async def check_suspicious(bot, a) -> None:
    try:
        now = time.time()
        n = q1("SELECT COUNT(*) n FROM hires WHERE admin_id=? AND ts>=?", (a["user_id"], int(now) - SUS_WINDOW))["n"]
        if n > SUS_LIMIT and now - _sus_last.get(a["user_id"], 0) >= SUS_WINDOW and get_setting("notify_sus") == "1":
            _sus_last[a["user_id"]] = now
            await send_alert(bot, OWNER_ID,
                            fbox("🚨 هشدار جذب مشکوک 🚨",
                             f"👤 ادمین: {link(a)}\n"
                             f"🔢 کد اختصاصی:「{a['code']}」\n"
                             f"⏱️ جذب در 10 دقیقه‌ی اخیر:「{n}」\n\n"
                             "تعداد جذب‌ها غیرعادیه؛ ثبت‌ها رو بررسی کن."))
    except Exception as e:  # noqa
        log_err(f"check_suspicious: {e!r}")


ADMIN_FOLDER_TITLE = "Admin"  # اسم پوشه‌ی تلگرام اکانت شخصی که ادمین‌ها بعد از اولین جذب بهش اضافه میشن
ADMIN_FOLDER_NAMES = {"admin", "ادمین"}  # هر دو اسم (انگلیسی و فارسی) پذیرفته میشه


async def add_admin_to_folder(user_id: int) -> None:
    """چت ادمین (با سشن اکانت شخصی) به پوشه‌ی «ادمین» اضافه میشه؛ بدون اثر روی بقیه‌ی چت‌های پوشه."""
    try:
        if not await saved_ready():
            return
        from telethon.tl.functions.messages import GetDialogFiltersRequest, UpdateDialogFilterRequest
        client = SESSION_CLIENT
        try:
            peer = await client.get_input_entity(user_id)
        except ValueError:
            await client.get_dialogs(limit=200)  # کش تلگرام تازه میشه و دوباره تلاش میشه
            try:
                peer = await client.get_input_entity(user_id)
            except ValueError:
                # ادمینی که فقط با ربات حرف زده برای اکانت شخصی ناشناسه؛ با یوزرنیم پیدا میشه
                _a = get_admin(user_id)
                _un = (_a["username"] if _a is not None else None) or ""
                if not _un:
                    raise
                peer = await client.get_input_entity(_un.lstrip("@"))
        res = await client(GetDialogFiltersRequest())
        filters = getattr(res, "filters", res)
        target = None
        for f in filters:
            title = getattr(f, "title", None)
            title = getattr(title, "text", title)
            if isinstance(title, str) and title.strip().lower() in ADMIN_FOLDER_NAMES and hasattr(f, "include_peers"):
                target = f
                break
        if target is None:
            log_err(f"admin folder '{ADMIN_FOLDER_TITLE}' not found")
            return
        have = {getattr(x, "user_id", None) for x in target.include_peers}
        if user_id in have:
            return
        target.include_peers.append(peer)
        await client(UpdateDialogFilterRequest(id=target.id, filter=target))
        audit(user_id, "admin_folder_added")
    except FloodWaitError as e:
        log_err(f"admin folder flood wait {e.seconds}s")
    except Exception as e:  # noqa
        log_err(f"add_admin_to_folder({user_id}): {e!r}")


async def notify_hire(bot, res) -> None:
    """اعلان‌های یک جذب ثبت‌شده؛ مشترک بین همه مسیرهای جذب (ربات، Business، سشن)."""
    a = res["admin"]
    if res.get("total") == 1:
        bg(add_admin_to_folder(a["user_id"]))  # اولین جذب ادمین: چتش میره تو پوشه‌ی «ادمین» اکانت شخصی
    notify_on = get_setting("notify_new") == "1"
    if not res["completed"]:
        sent_h = await safe_send(bot, a["user_id"],
                                 admin_hire_text(res["period"], res["target"], res["total"], res["remaining"],
                                                 level_of(a), a["cur_amount"]))
        hold_notice(sent_h, secs=ADMIN_HIRE_HOLD)  # ۳ ساعت (بازه‌ی شبانه هم رعایت میشه) پاک نمیشه
    if notify_on:
        await safe_send_hold(bot, OWNER_ID, owner_hire_text(a, res["period"], res["total"]),
                             KB(B("🧬 پنل عملکرد 🧬", f"o:perf:{a['user_id']}")),  # شیشه‌ای بیرنگ
                             day_end=True)  # گزارش جذب پنل مدیر: از ۶ صبح تا ۶ صبح روز بعد می‌مونه، بعد با هم پاک میشن
    if res["completed"]:
        req_kb = KB(B("💵 دریافت پورسانت 💵", "a:reqc", style="success"))
        if res.get("level_up"):
            # دوره‌ای که ادمین با اون وارد سطح بعدی میشه: فقط یک پیام تبریک (عکس سطح جدید + افکت 🎉)، بلافاصله یک 🎉 تکی
            text_c = levelup_congrats_text(res["level_up"], res["target"], res["amount"],
                                           a["cur_target"], a["cur_amount"])
            m_c = await send_levelup_congrats(bot, a, text_c, req_kb)
            await replace_tracked(bot, a["user_id"], "congrats", m_c)
            m_f = await safe_send(bot, a["user_id"], "🎉", html_mode=False)
            await replace_tracked(bot, a["user_id"], "confetti", m_f)
            if m_c is not None:  # پاکسازی خودکار به این دو پیام دست نمیزنه تا ادمین کارتش رو تأیید کنه
                track_set(a["user_id"], "lvlhold", m_c.chat_id, m_c.message_id)
        else:
            text_c = congrats_text(res["target"], res["amount"])
            m_c = await send_congrats_effect(bot, a["user_id"], text_c, req_kb)
            await replace_tracked(bot, a["user_id"], "congrats", m_c)
            if m_c is not None:  # پاکسازی خودکار بهش دست نمیزنه تا ادمین کارتش رو تأیید کنه
                track_set(a["user_id"], "lvlhold", m_c.chat_id, m_c.message_id)
        try:  # «بدون ثبت‌نام»: بعد از تبریک، توضیح کم‌شدن پورسانت این دوره
            ac = q1("SELECT cut, cut_from, notice_sent FROM auto_chat WHERE user_id=?", (a["user_id"],))
            if ac is not None and ac["cut"] and not ac["notice_sent"] and ac["cut_from"] > res["amount"]:
                ex("UPDATE auto_chat SET notice_sent=1 WHERE user_id=?", (a["user_id"],))
                m_n = await safe_send(bot, a["user_id"], auto_notice_text(ac["cut_from"], res["amount"]))
                hold_notice(m_n)
        except Exception as e:  # noqa
            log_err(f"auto notice: {e!r}")
        up_line = f"🏅 ارتقا به:「{LEVEL_NAMES[res['level_up']]}」\n" if res.get("level_up") else ""
        if get_setting("notify_done") == "1":
            await safe_send_hold(bot, OWNER_ID,
                            f"⚡️{link(a)}\n{res['target']} جذبش رو تکمیل کرد!\n\n"
                            f"👤 ادمین: {link(a)}\n"
                            f"🔢 کد اختصاصی:「{a['code']}」\n"
                            f"📊 جذبهای تکمیل شده:「{res['target']}」\n"
                            f"💰 مبلغ پورسانت:「{fmt_en(res['amount'])}」تومان\n"
                            f"{up_line}"
                            "📌 وضعیت: در انتظار درخواست واریز...")
    if res.get("shield22"):
        await safe_send_hold(bot, OWNER_ID, shield22_text(a))  # فقط برای مدیر؛ به کاربر چیزی نمیره
    await check_suspicious(bot, a)


def shield22_release(code) -> None:
    """بعد از تموم شدنِ یک متقاضیِ در انتظار: اگه ادمین سپر «22» داره، دوره‌ش تموم شده (زیر ۲۲) و دیگه متقاضیِ
    در انتظار نداره، سپرش خاموش میشه."""
    try:
        r = q1("SELECT user_id, period_count, period_no, level_pen FROM admins WHERE code=?", (code,))
        if (r is not None and r["period_count"] < SHIELD_AT[level_of(r)]
                and q1("SELECT 1 FROM shield_auto WHERE admin_id=?", (r["user_id"],)) is not None
                and q1("SELECT 1 FROM shield_pending WHERE code=?", (code,)) is None):
            ex("DELETE FROM shield_admins WHERE admin_id=?", (r["user_id"],))
            ex("DELETE FROM shield_auto WHERE admin_id=?", (r["user_id"],))
    except Exception as e:  # noqa
        log_err(f"shield22_release: {e!r}")


def shield22_text(a) -> str:
    return f"<b>🛡️مکانیزم سپر برای این کاربر فعال شد🛡️</b>\n🆔: {link(a)}"


async def shield22_apply_existing(bot, lvl: int = 1) -> int:
    """وقتی سپرِ یک سطح روشن میشه: هر ادمینِ همون سطح که الان به عدد اون سطح یا بیشتر رسیده سپر میگیره (برای هرکدوم پیام میاد)."""
    n = 0
    for a in qa("SELECT * FROM admins WHERE period_count>=? AND user_id NOT IN (SELECT admin_id FROM shield_admins)",
                (SHIELD_AT[lvl],)):
        if level_of(a) != lvl:
            continue
        if ex("INSERT OR IGNORE INTO shield_admins(admin_id) VALUES(?)", (a["user_id"],)).rowcount:
            ex("INSERT OR IGNORE INTO shield_auto(admin_id) VALUES(?)", (a["user_id"],))
            n += 1
            await safe_send_hold(bot, OWNER_ID, shield22_text(a))
    return n


def shield_level_counts() -> dict:
    """هر سطح چند ادمین الان سپر فعال دارن (سپر روشن + جذب این دورهشون بین عدد سپر اون سطح و حدنصاب)."""
    cnt = {1: 0, 2: 0, 3: 0}
    try:
        for r in qa("SELECT a.period_no, a.level_pen, a.period_count, a.cur_target FROM admins a "
                    "JOIN shield_admins s ON s.admin_id=a.user_id"):
            lv = level_of(r)
            # سطح ۱: از ۲۲ به بالا، سطح ۲: از ۱۵، سطح ۳: از ۷؛ به حدنصاب (مثلا ۴۰) که برسه سپرش خاموش میشه و از عدد کم میشه
            if lv in cnt and SHIELD_AT[lv] <= r["period_count"] < r["cur_target"]:
                cnt[lv] += 1
    except Exception as e:  # noqa
        log_err(f"shield_level_counts: {e!r}")
    return cnt


def shield_menu(extra: str = ""):
    sep = "➖•➖•➖•➖•➖•➖•➖•➖•➖"
    text = f"<b>{sep}\nSHIELD SETTINGS 🛡️تنظیمات سپر\n{sep}</b>"
    _cnt = shield_level_counts()
    kb = KB(onoff_btn("سپر سراسری", shield_on(), "o:shd"),
            *[onoff_btn(f"سپر سطح {'⭐️' * lv} [{_cnt[lv]}]", shield_level_on(lv), f"o:shl:{lv}") for lv in (1, 2, 3)],
            BACK("o:set"))
    return text, kb


async def process_hire(context, user, text: str, allow_bare: bool = True, shield: bool = False, catchup: bool = False) -> bool:
    name = " ".join(x for x in [user.first_name, user.last_name] if x) or (user.username or str(user.id))
    if shield:
        # سپر: پیام اول (با کد) در انتظار میمونه؛ بعد از پیام(های) کارفرما، پیام دوم متقاضی جذب رو ثبت میکنه
        # متقاضیِ در انتظار همیشه بررسی میشه؛ حتی اگه سپر بین راه خاموش شده باشه (قبلا این‌ها برای همیشه گم می‌شدن)
        p = q1("SELECT * FROM shield_pending WHERE applicant_id=?", (user.id,))
        if p is not None:
            guarded = shield_on() or admin_shield_by_code(p["code"])
            _w = _aw(text)
            # بعد از پیام(های) تو (یا ۹ پیام خودکار)، وقتی متقاضی «شروع» بگه جذب ثبت میشه
            _auto_replied = q1("SELECT 1 FROM auto_chat WHERE user_id=? AND nine_sent=1 AND nine_at IS NOT NULL",
                               (user.id,)) is not None  # ۹ پیام خودکار برای این چت رفته؛ مثل جواب خودت حساب میشه
            _stage_ok = p["stage"] == 1 or _auto_replied or (catchup and get_setting("auto_9") == "1")  # بعد از خاموشی، ۹ پیام خودکار جواب اون چت رو میده
            if _w.startswith("شروع") and len(_w) <= 12 and (_stage_ok or not guarded):
                ex("DELETE FROM shield_pending WHERE applicant_id=?", (user.id,))
                res = record_hire(user.id, p["name"] or name, p["code"])
                if res is not None:
                    await notify_hire(context.bot, res)
                shield22_release(p["code"])
                return True
            if guarded:
                return True
            # سپر این ادمین الان خاموشه: پیام معمولی پردازش میشه (اگه کد داشته باشه همون لحظه ثبت میشه)
    # اولین عددِ پیام که کد یکی از ادمین‌هاست؛ بقیه‌ی عددها (ساعت، قیمت و ...) نادیده گرفته میشن
    code = next((c for c in parse_hire_codes(text, allow_bare)
                 if q1("SELECT 1 FROM admins WHERE code=?", (c,))), None)
    if code is None:
        try:  # عیب‌یابی: عددی که کد یه ادمینه ولی فیلتر ردش کرده توی لاگ میاد تا اگه متقاضی واقعی رد شد پیداش کنی
            skipped = [int(x) for x in NUM_RE.findall(normalize(text)) if q1("SELECT 1 FROM admins WHERE code=?", (int(x),))]
            if skipped:
                log.info("hire number skipped by filter: applicant_id=%s numbers=%s", user.id, skipped)
        except Exception:  # noqa
            pass
        return False
    if shield and (shield_on() or admin_shield_by_code(code)):
        if q1("SELECT 1 FROM hires WHERE applicant_id=?", (user.id,)) is None:
            ex("INSERT OR IGNORE INTO shield_pending(applicant_id,code,name,stage,ts) VALUES(?,?,?,0,?)",
               (user.id, code, name, int(time.time())))
        return True
    res = record_hire(user.id, name, code)
    if shield:
        ex("DELETE FROM shield_pending WHERE applicant_id=?", (user.id,))  # سپر خاموش بود و مستقیم ثبت شد
    if res is None:
        # برای عیب‌یابی تست: کد پیدا شده، اما ثبت جذب به‌دلیل کد نامعتبر، خودجذبی،
        # ادمین بودن متقاضی یا ثبت قبلی انجام نشده است.
        log.debug("hire not recorded: applicant_id=%s code=%s (invalid code/admin/self/duplicate)", user.id, code)
        return True
    await notify_hire(context.bot, res)
    return True


_biz_owner_cache = {}


async def on_business(update: Update, context):
    m = update.business_message
    if m is None or m.from_user is None or m.from_user.is_bot:
        return
    uid = m.from_user.id
    if uid == OWNER_ID:
        shield_owner_replied(m.chat.id)
        return
    # پیام‌هایی که خود صاحب اکانت Business می‌فرستد جذب حساب نمی‌شوند
    cid = m.business_connection_id
    if cid:
        if cid not in _biz_owner_cache:
            try:
                bc = await context.bot.get_business_connection(cid)
                _biz_owner_cache[cid] = bc.user.id
            except Exception as e:  # noqa
                log_err(f"business connection lookup failed: {e!r}")
                _biz_owner_cache[cid] = None
        if _biz_owner_cache.get(cid) == uid:
            shield_owner_replied(m.chat.id)
            return
    text = m.text or m.caption or ""
    if text or shield_on():
        stat_code_only(m.from_user, text, ts=_event_ts(m))
        await process_hire(context, m.from_user, text, shield=True)


# ----------------------------------------------------------------------------
# پنل کارفرما
# ----------------------------------------------------------------------------
REP_SEP = "➖•" * 10


def admin_block(a) -> str:
    su_p, su_t = admin_signups(a)
    return (f"👤 <b>ادمین جذب{ZW}کننده</b>🔻\n"
            f"{link_list_name(a)}\n"
            f"🎚️<b>سطح</b>:「{stars_of(a)} 」\u25aa\ufe0f<b>کد</b>: {a['code']}\u25aa\ufe0f\n"
            f"➕ <b>این دوره</b> › <b>「 {a['period_count']} جذب 」</b>\n"
            f"🧲 <b>کلا</b> › <b>「 {a['total_count']} جذب 」</b>\n"
            f"🪪 <b>ثبت نام این دوره</b> › <b>「 {su_p} ثبت نام 」</b>\n"
            f"🪪 <b>مجموع ثبت نام</b> › <b>「 {su_t} ثبت نام 」</b>")


async def owner_report(update, context, mode: str, page: int):
    if mode == "top":      # بیشترین جذبِ این دوره
        order = "period_count DESC, total_count DESC, COALESCE(last_hire_at,0) DESC, user_id"
    elif mode == "lvl":    # بر اساس سطح (کل جذب‌ها)؛ همون ترتیب قبلی
        order = "total_count DESC, COALESCE(last_hire_at,0) DESC, user_id"
    elif mode == "reg":    # بیشترین ثبت‌نام (اول این دوره، بعد مجموع)
        order = None
    else:
        mode = "new"
        order = "(last_hire_at IS NULL), last_hire_at DESC, user_id"
    if order is None:
        _all = qa("SELECT * FROM admins")
        _sc = {a["user_id"]: admin_signups(a) for a in _all}
        _all.sort(key=lambda a: (-_sc[a["user_id"]][0], -_sc[a["user_id"]][1], -(a["total_count"] or 0), a["user_id"]))
        total = len(_all)
    else:
        total = q1("SELECT COUNT(*) n FROM admins")["n"]
    pages = max((total + PAGE_SIZE - 1) // PAGE_SIZE, 1)
    page = min(max(page, 0), pages - 1)
    if order is None:
        rows = _all[page * PAGE_SIZE:(page + 1) * PAGE_SIZE]
    else:
        rows = qa(f"SELECT * FROM admins ORDER BY {order} LIMIT ? OFFSET ?", (PAGE_SIZE, page * PAGE_SIZE))
    if not rows:
        body = "هنوز ادمینی ثبت نشده."
    else:
        body = f"\n{REP_SEP}\n".join(admin_block(a) for a in rows) + f"\n{REP_SEP}"
    text = REP_SEP + "\n<b>👨🏻\u200d💻 گزارش جذب ادمین\u200cها 👨🏻\u200d💻</b>\n" + REP_SEP + "\n" + body
    _modes = (("top", "📈 بر اساس بیشترین جذب 📈"), ("reg", "🪪 بر اساس ثبت نام 🪪"), ("lvl", "⭐️ بر اساس سطح ⭐️"), ("new", "🕒 بر اساس جدیدترین 🕒"))
    kb_rows = [B(lbl, f"o:rep:{m}:0", style="primary") for m, lbl in _modes if m != mode]
    nav = nav_row(lambda p: f"o:rep:{mode}:{p}", page, pages)
    if nav:
        kb_rows.append(nav)
    kb_rows.append(B(BTN_BACK, "o:menu", style="danger"))
    # دکمه شماره صفحه؛ فقط نمایشی و بدون عملکرد
    kb_rows.append(B(f"صفحه {page + 1} از {pages}", "o:noop"))
    await show(update, context, text, KB(*kb_rows), preview=False)


def search_kb(a, perf: bool = False):
    on = admin_shield_on(a["user_id"])
    return KB(B("📂 دریافت فیش‌های واریزی 📂", f"o:srr:{a['user_id']}", style="success"),
              B("✉️ پیام به این کاربر ✉️", f"o:smg:{a['user_id']}", style="primary"),
              *([] if perf else [B("✏️ تغییر جذب ✏️", f"o:chg:{a['user_id']}", style="primary")]),  # فقط از جستجوی ادمین، نه از زیر نوتیف
              B(f"🛡️ سپر: {'روشن' if on else 'خاموش'} 🛡️", f"o:ash:{a['user_id']}", style="success" if on else "danger"),
              # پنل از زیر نوتیف جذب باز شده: بازگشت فقط همون نوتیف رو برمیگردونه (نه منوی اصلی)
              BACK(f"o:pbk:{a['user_id']}") if perf else BACK("o:menu"))


def perf_text_get(chat_id, message_id):
    r = q1("SELECT text FROM perf_orig WHERE chat_id=? AND message_id=?", (chat_id, message_id))
    return r["text"] if r is not None else None


def perf_text_save(chat_id, message_id, text) -> None:
    """متن اصلی نوتیف جذب؛ فقط بار اول ذخیره میشه تا کلیک دوباره/قدیمی متن پنل رو جاش ننویسه."""
    ex("DELETE FROM perf_orig WHERE ts<?", (int(time.time()) - 5 * 86400,))
    ex("INSERT OR IGNORE INTO perf_orig(chat_id,message_id,text,ts) VALUES(?,?,?,?)",
       (chat_id, message_id, text, int(time.time())))


async def edit_in_place(q, text, kb) -> bool:
    """ویرایش همون پیام (بدون پاک کردن/ارسال دوباره)."""
    try:
        await q.edit_message_text(text, reply_markup=kb, parse_mode=H,
                                  link_preview_options=preview_opts(text, True, None))
        return True
    except BadRequest as e:
        if "not modified" in str(e).lower():
            return True
        log_err(f"edit_in_place: {e!r}")
    except TelegramError as e:
        log_err(f"edit_in_place: {e!r}")
    return False


def search_report_text(a) -> str:
    paid = qa("SELECT * FROM commissions WHERE admin_id=? AND status='paid' ORDER BY paid_at DESC", (a["user_id"],))
    paid_sum = sum((c["paid_amount"] or c["amount"]) for c in paid)
    sep = "➖•" * 8 + "➖"
    uname = ("@" + html.escape(a["username"])) if a["username"] else "ندارد"
    return (f"<b>{sep}\n🔎گزارش ادمین🔎\n{sep}\n"
            f"👤 نام: {link(a)}\n"
            f"🔑 کد اختصاصی:「{a['code']}」\n"
            f"🎚️سطح :「{stars_of(a)}」\n"
            f"🆔 یوزرنیم: {uname}\n"
            f"{sep}\n"
            f"🔹 این دوره:「{a['period_count']}」از「{a['cur_target']}」\n"
            f"🔷 کلا:「{a['total_count']} جذب」\n"
            f"💰 جمع دریافتی:「{fmt_en(paid_sum)} تومان」\n"
            f"{sep}\n"
            f"📅 تاریخ عضویت: {jdate(a['created_at'])}\n"
            f"{sep}</b>")


PH_ITEMS = {
    "1p": ("profile_level_photo_id", "عکس سطح یک"),
    "1a": ("activity_photo_id", "عکس دویست هزار تومان"),
    "2b": ("lvl2_blur_photo_id", "عکس تار سطح دو (برای وقتی هنوز به این سطح نرسیده)"),
    "2p": ("lvl2_photo_id", "عکس اصلی سطح دو"),
    "2a": ("lvl2_amount_photo_id", "عکس دویست و پنجاه هزار تومان"),
    "3b": ("lvl3_blur_photo_id", "عکس تار سطح سه (برای وقتی هنوز به این سطح نرسیده)"),
    "3p": ("lvl3_photo_id", "عکس اصلی سطح سه"),
    "3a": ("lvl3_amount_photo_id", "عکس سیصد هزار تومان"),
    "ad": ("ad_photo_id", "عکس آگهی (تقلب با آگهی)"),
}


def keycap(n: int) -> str:
    """۳۲ ← 3️⃣2️⃣"""
    return "".join(f"{d}\ufe0f\u20e3" for d in str(int(n)))


def active_admins_count() -> int:
    """ادمین فعال: کسی که حداقل یک عضو آورده."""
    r = q1("SELECT COUNT(*) n FROM admins WHERE total_count>0 "
           "OR EXISTS (SELECT 1 FROM hires h WHERE h.admin_id=admins.user_id)")
    return int(r["n"]) if r else 0


async def send_member_count(bot, chat_id: int) -> None:
    """قبل از منوی تنظیمات: تعداد کل اعضای ربات با ایموجی عددی."""
    try:
        await send(bot, chat_id, keycap(admins_total_count()), html_mode=False)
    except Exception as e:  # noqa
        log_err(f"member count: {e!r}")


def settings_text(extra: str = "") -> str:
    try:
        a = active_admins_count()
    except Exception:  # noqa
        a = 0
    sep = "➖•➖•➖•➖•➖•➖•➖•➖•"
    return (f"<b>{sep}\n"
            "🕹️تنظیمات پنل مدیریت🕹️\n\n"
            f"ادمین های فعال:「 {a} 」اعضا 🔺\n"
            f"{sep}</b>") + (("\n\n" + html.escape(extra)) if extra else "")


def adv_text(extra: str = "") -> str:
    sep = "➖•➖•➖•➖•➖•➖•➖•➖•➖•➖•"
    return f"<b>{sep}\nADVANCE SETTINGS ⚙️‌ تنظیمات پیشرفته\n{sep}</b>" + (("\n\n" + html.escape(extra)) if extra else "")


def settings_kb():
    power = (B("🟢 روشن کردن ربات 🟢", "o:on", style="success") if bot_off()
             else B("🔌 خاموش کردن ربات 🔌", "o:off", style="danger"))
    return KB(
        B("🔔 نوتیفیکیشن 🔔", "o:ntf", style="danger"),
        B("🛡️ تنظیمات سپر 🛡️", "o:shm", style="primary"),
        B("🎬 ویدیوی آموزشی 🎬", "o:vid", style="danger"),
        B("📢 اضافه کردن کانال 📢", "o:ch", style="primary"),
        power,
        B("🛰️ تنظیمات پیشرفته 🛰️", "o:adv", style="primary"),
        B("🔄 رفرش 🔄", "o:rf", style="success"),
        *([B("🗑️ پاک کردن دکمه راه‌اندازی 🗑️", "o:rmgo", style="danger")] if get_setting("owner_go_btn") == "1" else []),
        B(BTN_BACK, "o:menu"),
    )


NTF_KEYS = (
    ("new", "notify_new", "اعلان جذب جدید"),
    ("done", "notify_done", "اعلان تکمیل جذب ادمین"),
    ("sus", "notify_sus", "هشدار جذب مشکوک"),
)


def ntf_menu():
    rows = [onoff_btn(label, get_setting(key) == "1", f"o:ntf:{short}") for short, key, label in NTF_KEYS]
    sep = "➖•➖•➖•➖•➖•➖•➖"
    text = f"<b>{sep}\nNOTIFICATION 🔔 اعلان‌ها\n{sep}</b>"
    return text, KB(*rows, BACK("o:set"))


BACKUP_CHOICES = ((600, "۱۰ دقیقه"), (3600, "۱ ساعت"), (18000, "۵ ساعت"), (36000, "۱۰ ساعت"), (86400, "۲۴ ساعت"))


def backup_every() -> int:
    v = get_int_setting("backup_every")
    return v if v in {x for x, _ in BACKUP_CHOICES} else 86400


def backup_choice_rows():
    cur = backup_every()
    btns = [B(("✅ " if sec == cur else "") + label, f"o:bki:{sec}", style="success" if sec == cur else "primary")
            for sec, label in BACKUP_CHOICES]
    return [btns[:3], btns[3:]]


def advanced_settings_kb(bk_open: bool = False):
    # دکمه‌ی پشتیبان: با زدنش گزینه‌هاش زیرش باز میشن (منو عوض نمیشه)؛ دوباره بزنی بسته میشه
    bk_rows = [B("🔺 🗄️ پشتیبان دیتابیس 🗄️ 🔺", "o:adv", style="primary"),
               *backup_choice_rows(),
               B("📥 بکاپ همین الان 📥", "o:bkn", style="danger")] if bk_open else [
               B("🔻 🗄️ پشتیبان دیتابیس 🗄️ 🔻", "o:bk", style="primary")]
    return KB(
        B("📉 آمار سیستم 📉", "o:sts:0", style="success"),
        *bk_rows,
        B("♻️ بازیابی بکاپ ♻️", "o:rst", style="primary"),
        [B("💷 تغییر پورسانت 💷", "o:com", style="danger"), B("🧪 تست 🧪", "o:tsm", style="danger")],
        [B("🐞 گزارش خطا 🐞", "o:er", style="danger"), B("📺 ChannelYAB 📺", "o:cy", style="danger")],
        [B("🤖 ارسال خودکار 🤖", "o:au", style="danger"), B("💭 کامنت خودکار 💭", "o:ac", style="danger")],
        B("🃏 تقلب هفتگی 🃏", "o:ck", style="danger"),
        BACK_G("o:set"),
    )


def test_menu_text() -> str:
    sep = "➖•➖•➖•➖"
    return f"<b>{sep}\nتست ⚗️ TEST\n{sep}</b>"


def test_menu_kb():
    return KB(
        B("🧪 تست پورسانت 🧪", "o:tst", style="primary"),
        B("🧹 ریست دیتای ادمین 🧹", "o:rsd", style="danger"),
        BACK("o:adv"),
    )


def video_menu():
    fid = get_setting("video_file_id")
    on = get_setting("video_enabled") == "1"
    sep = SEP10
    text = (f"<b>{sep}\nTUTORIAL VIDEO 🎬 ویدیوی آموزشی\n{sep}</b>\n"
            f"وضعیت ویدیو: {'ثبت شده ✅' if fid else 'ثبت نشده ❎'}\n"
            f"<b>{sep}</b>")
    kb = KB(
        onoff_btn("ویدیوی آموزشی", on, "o:vidt"),
        B("📼 ثبت یا تعویض ویدیو 📼", "o:vids", style="danger"),
        BACK("o:set"),
    )
    return text, kb


def commission_menu():
    sep = "➖•➖•➖•➖•➖•➖•➖"
    text = (f"<b>{sep}\nCOMMISSION 💰 | پورسانت\n{sep}</b>\n"
            f"⭐️ مبلغ پورسانت سطح یک:\n「{fmt_en(level_amount(1))}」تومان\n"
            f"⭐️⭐️ مبلغ پورسانت سطح دو:\n「{fmt_en(level_amount(2))}」تومان\n"
            f"⭐️⭐️⭐️ مبلغ پورسانت سطح سه:\n「{fmt_en(level_amount(3))}」تومان\n"
            f"حدنصاب جذب برای دوره‌های جدید:\n「{get_int_setting('pay_target')}」جذب\n"
            f"<b>{sep}</b>")
    kb = KB(B("💵 تغییر مبلغ سطح یک ⭐️", "o:comamt", style="danger"),
            B("💵 تغییر مبلغ سطح دو ⭐️⭐️", "o:comamt2", style="danger"),
            B("💵 تغییر مبلغ سطح سه ⭐️⭐️⭐️", "o:comamt3", style="danger"),
            B("🎯 تغییر حدنصاب جذب 🎯", "o:comtgt", style="danger"),
            BACK("o:adv"))
    return text, kb


def channel_menu():
    if not get_setting("channel_id"):
        return None, None
    on = channel_active()
    text = fbox("📢 کانال اجباری 📢",
            f"کانال: {html.escape(get_setting('channel_title'))}\n"
            f"لینک: {html.escape(get_setting('channel_link'))}\n"
            f"دکمه ورود: {html.escape(get_setting('channel_btn'))}\n"
            f"وضعیت: {'فعال' if on else 'غیرفعال'}")
    kb = KB(B("🔕 غیرفعال کردن 🔕" if on else "📢 فعال کردن 📢", "o:cht", style="danger"),
            B("📢 اضافه کردن کانال 📢", "o:cha", style="danger"),
            B("🗑️ حذف کانال 🗑️", "o:chd", style="danger"),
            BACK("o:set"))
    return text, kb


def status_text() -> str:
    now = int(time.time())
    today = day_key(now)
    admins = q1("SELECT COUNT(*) n FROM admins WHERE blocked=0")["n"]
    hires = q1("SELECT COUNT(*) n FROM hires")["n"]
    hires_today = sum(1 for r in qa("SELECT ts FROM hires WHERE ts>?", (now - 172800,)) if day_key(r["ts"]) == today)
    pend = q1("SELECT COUNT(*) n, COALESCE(SUM(amount),0) s FROM commissions WHERE status IN ('earned','requested')")
    req = q1("SELECT COUNT(*) n FROM commissions WHERE status='requested'")["n"]
    paid = q1("SELECT COUNT(*) n, COALESCE(SUM(COALESCE(paid_amount,amount)),0) s FROM commissions WHERE status='paid'")
    errs = sum(1 for r in qa("SELECT text FROM errors") if not is_noise_error(r["text"]))
    up = int(now - START_TS)
    size = os.path.getsize(DB_PATH) // 1024 if os.path.exists(DB_PATH) else 0
    return fbox("📊 وضعیت ربات 📊",
            f"🤖 {bot_status_line()}\n"
            f"👥 تعداد ادمین‌ها:「{admins}」\n"
            f"🔷 کل جذب‌ها:「{hires}」| امروز:「{hires_today}」\n"
            f"⏳ پورسانت پرداخت‌نشده:「{pend['n']}」مورد،「{fmt_en(pend['s'])}」تومان「درخواست‌شده:「{req}」」\n"
            f"✅ پرداخت‌شده:「{paid['n']}」مورد،「{fmt_en(paid['s'])}」تومان\n"
            f"🔔 اعلان جذب جدید: {'روشن' if get_setting('notify_new') == '1' else 'خاموش'}\n"
            f"🎬 ویدیوی آموزشی: {'روشن' if get_setting('video_enabled') == '1' else 'خاموش'}\n"
            f"📢 کانال اجباری: {'فعال' if channel_active() else 'غیرفعال'}\n"
            f"🗄️ حجم دیتابیس:「{size}」KB\n"
            f"🧾 خطاهای ثبت‌شده:「{errs}」\n"
            f"⏱️ مدت فعالیت از آخرین اجرا:「{up // 3600}」ساعت و「{(up % 3600) // 60}」دقیقه")


BACKUP_PREFIX = "jazban_bk_"
SESSION_CLIENT = None  # کلاینت سشن اکانت شخصی (برای Saved Messages)
SAVED_VERIFY_MAX = 150 * 1024 * 1024  # تا این حجم، فایل ارسال‌شده دوباره دانلود و هش مقایسه میشه


def _sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _table_counts(conn) -> dict:
    return {t: conn.execute(f"SELECT COUNT(*) FROM {t}").fetchone()[0]
            for t in ("admins", "hires", "commissions", "cards")}


def _safe_rmtree(path: str):
    """حذف پوشه موقت بکاپ؛ فقط داخل پوشه temp و با پیشوند مخصوص، هرگز دیتابیس اصلی."""
    real = os.path.realpath(path)
    base = os.path.realpath(tempfile.gettempdir())
    db_real = os.path.realpath(DB_PATH)
    if (real.startswith(base + os.sep) and os.path.basename(real).startswith(BACKUP_PREFIX)
            and db_real != real and not db_real.startswith(real + os.sep)):
        shutil.rmtree(real, ignore_errors=True)


def _cleanup_old_backups():
    """پوشه‌های موقتِ بکاپ‌های ناموفقِ قدیمی (بیش از ۲۴ ساعت) پاک میشن."""
    base = tempfile.gettempdir()
    try:
        for name in os.listdir(base):
            full = os.path.join(base, name)
            if name.startswith(BACKUP_PREFIX) and os.path.isdir(full) and time.time() - os.path.getmtime(full) > 86400:
                _safe_rmtree(full)
    except OSError:
        pass


def make_backup() -> dict:
    """بکاپ سازگار از دیتابیس + تأیید محتوا قبل از ارسال (integrity_check، تطابق تعداد رکوردها، هش SHA-256؛
    برای فایل‌های بزرگ‌تر از ۲۵ مگابایت: فشرده‌سازی با تأیید هشِ محتوای بازشده و در صورت لزوم تکه‌تکه کردن)."""
    _cleanup_old_backups()
    tmpdir = tempfile.mkdtemp(prefix=BACKUP_PREFIX)
    db_name = f"jazban_backup_{dt_of(int(time.time())).strftime('%Y%m%d_%H%M')}.db"
    db_path = os.path.join(tmpdir, db_name)
    with _lock:
        dst = sqlite3.connect(db_path)
        try:
            CONN.backup(dst)
        finally:
            dst.close()
        live = _table_counts(CONN)
    chk = sqlite3.connect(f"file:{db_path}?mode=ro", uri=True)
    try:
        integrity = chk.execute("PRAGMA integrity_check").fetchone()[0]
        copy = _table_counts(chk)
    finally:
        chk.close()
    if integrity != "ok":
        raise RuntimeError(f"integrity_check failed: {integrity}")
    if copy != live:
        raise RuntimeError(f"row counts mismatch: live={live} copy={copy}")
    db_sha = _sha256_file(db_path)
    db_size = os.path.getsize(db_path)
    files, packed = [], False
    if db_size <= BACKUP_BIG:
        files.append((db_path, db_name))
    else:
        packed = True
        gz_path = db_path + ".gz"
        with open(db_path, "rb") as src, gzip.open(gz_path, "wb", compresslevel=6) as gz:
            shutil.copyfileobj(src, gz, 1024 * 1024)
        h = hashlib.sha256()
        with gzip.open(gz_path, "rb") as gz:  # محتوای فایل فشرده باز میشه و هشش باید با دیتابیس یکی باشه
            for chunk in iter(lambda: gz.read(1024 * 1024), b""):
                h.update(chunk)
        if h.hexdigest() != db_sha:
            raise RuntimeError("gzip content verification failed")
        if os.path.getsize(gz_path) <= BACKUP_SPLIT:
            files.append((gz_path, db_name + ".gz"))
        else:
            n = 0
            with open(gz_path, "rb") as src:
                while True:
                    chunk = src.read(BACKUP_SPLIT)
                    if not chunk:
                        break
                    n += 1
                    part = os.path.join(tmpdir, f"{db_name}.gz.part{n:03d}")
                    with open(part, "wb") as pf:
                        pf.write(chunk)
                    files.append((part, os.path.basename(part)))
            joined = hashlib.sha256()
            for part, _ in files:
                with open(part, "rb") as pf:
                    for chunk in iter(lambda: pf.read(1024 * 1024), b""):
                        joined.update(chunk)
            if joined.hexdigest() != _sha256_file(gz_path):
                raise RuntimeError("split parts verification failed")
    items = [{"path": pth, "name": nm, "size": os.path.getsize(pth), "sha": _sha256_file(pth)} for pth, nm in files]
    return {"tmpdir": tmpdir, "items": items, "db_sha": db_sha, "db_size": db_size, "packed": packed}


async def saved_ready() -> bool:
    """سشن اکانت شخصی فقط وقتی استفاده میشه که موجود، متصل و معتبر باشه."""
    c = SESSION_CLIENT
    if c is None:
        return False
    try:
        return bool(c.is_connected() and await c.is_user_authorized())
    except Exception:  # noqa
        return False


def _saved_log_load() -> list:
    try:
        v = json.loads(get_setting("backup_saved_log") or "[]")
    except ValueError:
        return []
    return [e for e in v if isinstance(e, dict) and isinstance(e.get("ids"), list)] if isinstance(v, list) else []


async def _saved_prune(client, new_ids: list) -> None:
    """بکاپ‌های قبلیِ Saved Messages پاک میشن؛ فقط آخرین بکاپ و اولین بکاپِ هر روز (تا ۷ روز) میمونن
    تا اگه دیتابیس خراب یا خالی شد و بکاپ خراب جای سالم رو گرفت، نسخه‌ی سالمِ همون روز یا دیروز موجود باشه."""
    try:
        log_ = _saved_log_load()
        log_.append({"ids": [int(i) for i in new_ids], "ts": int(time.time())})
        keep = {len(log_) - 1}
        first_of_day = {}
        for i, e in enumerate(log_):
            first_of_day.setdefault(day_key(int(e.get("ts") or 0)), i)
        if backup_every() >= 86400:  # بکاپ ۲۴ ساعته: تاریخچه‌ی هفت‌روزه می‌مونه؛ تایم‌های کوتاه‌تر: فقط آخرین بکاپ
            for d in sorted(first_of_day)[-7:]:
                keep.add(first_of_day[d])
        drop = [int(x) for i, e in enumerate(log_) if i not in keep for x in e["ids"]]
        if drop:
            try:
                await client.delete_messages("me", drop)
            except Exception as e:  # noqa
                log_err(f"saved prune delete: {e!r}")
        set_setting("backup_saved_log", json.dumps([e for i, e in enumerate(log_) if i in keep]))
    except Exception as e:  # noqa
        log_err(f"saved prune: {e!r}")


def _is_triple_premium_dash(m) -> bool:
    """پیام اصلیِ «➖➖➖ پریمیوم»: دقیقاً سه اموجی پریمیوم (custom emoji) و بدون هیچ متن دیگه.
    پیام فوروارد‌شده (کپی قبلی) حساب نمیشه."""
    try:
        if m is None or getattr(m, "fwd_from", None) is not None:
            return False
        ents = [e for e in (m.entities or []) if isinstance(e, MessageEntityCustomEmoji)]
        if len(ents) != 3:
            return False
        txt = (m.raw_text or "").replace("\ufe0f", "").replace("\u200f", "").strip()
        return txt != "" and all(ch in "➖ \n" for ch in txt)
    except Exception:  # noqa
        return False


async def _saved_sep_refresh(client) -> None:
    """به‌جای ➖➖➖: پیامِ «سه تا ➖ اموجی پریمیوم» از بالای Saved Messages زیر آخرین بکاپ فوروارد میشه؛
    فورواردِ قبلی پاک میشه و تازه‌اش بعد از بکاپ جدید میاد.
    پیدا کردن پیام بر اساس محتواشه (سه اموجی پریمیوم ➖)، نه شماره‌ی جایگاه؛ فقط اگه پیدا نشد،
    سومین پیام از قدیمی‌ترین‌ها جایگزین میشه."""
    try:
        old = get_int_setting("saved_sep_id")
        # قدیمی‌ترین پیام‌ها اول (reverse=True)؛ کپی فورواردِ قبلی رو کنار میذاریم
        oldest = [m for m in await client.get_messages("me", limit=60, reverse=True)
                  if m is not None and m.id != old]
        target = next((m for m in oldest if _is_triple_premium_dash(m)), None)
        if target is None:
            top = [m for m in oldest if getattr(m, "fwd_from", None) is None]
            if len(top) < 3:
                return  # هنوز سه پیام نیست؛ چیزی فوروارد نمیشه
            target = top[2]  # جایگزین: سومین پیام از قدیمی‌ترین‌ها
            log.warning("saved sep: premium ➖➖➖ message not found, fell back to 3rd oldest id=%s", target.id)
        fwd = await client.forward_messages("me", target.id, "me")
        m = fwd[0] if isinstance(fwd, (list, tuple)) else fwd
        set_setting("saved_sep_id", str(m.id))
        log.info("saved sep: forwarded message id=%s (triple premium dash)", target.id)
        if old:
            try:
                await client.delete_messages("me", [old])
            except Exception as e:  # noqa
                log_err(f"saved sep delete: {e!r}")
    except Exception as e:  # noqa
        log_err(f"saved sep: {e!r}")


async def send_backup_saved(meta: dict) -> str:
    """ارسال بکاپ به Saved Messages با سشن اکانت شخصی. هر فایل بعد از ارسال بررسی میشه:
    حجم، و (تا SAVED_VERIFY_MAX) دانلود مجدد و مقایسه هش. هر خطا باعث exception میشه
    و فایل موقت پاک نمیشه."""
    client = SESSION_CLIENT
    items = meta["items"]
    total = len(items)
    full_check = True
    new_ids = []
    for i, it in enumerate(items, 1):
        cap = f"☁️ بک‌آپ ☁️「 {jdate_en(int(time.time()))} 」"  # کپشن: تاریخ همون روز به فارسی
        if meta["packed"]:
            cap += f"\n\n🔹 فایل「{i}」از「{total}」\n🔐 هش: {it['sha'][:16]}"
        msg = None
        for _ in range(3):
            try:
                msg = await client.send_file("me", it["path"], caption=cap, force_document=True)
                break
            except FloodWaitError as e:
                await asyncio.sleep(e.seconds + 1)
        if msg is None or getattr(msg, "document", None) is None:
            raise RuntimeError(f"saved send failed for {it['name']}")
        new_ids.append(msg.id)
        if msg.document.size != it["size"]:
            raise RuntimeError(f"saved size mismatch for {it['name']}: sent={it['size']} telegram={msg.document.size}")
        if it["size"] <= SAVED_VERIFY_MAX:
            data = await client.download_media(msg, file=bytes)
            if not data or hashlib.sha256(data).hexdigest() != it["sha"]:
                raise RuntimeError(f"saved downloaded hash mismatch for {it['name']}")
        else:
            full_check = False
    await _saved_prune(client, new_ids)  # فقط بعد از اینکه بکاپ جدید کامل ارسال و تأیید شد
    await _saved_sep_refresh(client)
    mb = f"{meta['db_size'] / 1048576:.1f}"
    lines = ["✅ پشتیبان در Saved Messages ذخیره و تأیید شد ✅\n",
             f"🔹 حجم دیتابیس:「{mb}」مگابایت",
             f"🔷 تعداد فایل ارسال‌شده:「{total}」",
             f"🔐 هش SHA-256 دیتابیس:\n<code>{meta['db_sha']}</code>"]
    if meta["packed"]:
        lines.append("\n🗜️ فایل بزرگ بود؛ فشرده شد و محتوای فشرده با دیتابیس اصلی تطبیق داده شد")
        if total > 1:
            lines.append("برای بازیابی: فایل‌ها رو به ترتیب شماره کنار هم بذار و بعد با gunzip باز کن")
    if full_check:
        lines.append("\n✅ فایل ارسال‌شده دوباره دانلود و محتواش با فایل اصلی یکی بود")
    else:
        lines.append("\n⚠️ فایل خیلی بزرگ بود؛ فقط حجم فایل ارسال‌شده با فایل اصلی تطبیق داده شد")
    return "\n".join(lines)


def backup_fail_register() -> int:
    """بکاپ ارسال نشد: خودش با فاصله‌ی بیشتر و بیشتر (۵، ۱۰، ۲۰ و حداکثر ۳۰ دقیقه) دوباره تلاش میکنه تا بره.
    خروجی: شماره‌ی شکست پشت‌سرهم؛ پیام خطا فقط برای اولیش میره."""
    n = get_int_setting("backup_fail_n") + 1
    set_setting("backup_fail_n", str(n))
    delay = min(300 * 2 ** min(n - 1, 4), 1800)
    every = backup_every()
    set_setting("last_backup_ts", str(int(time.time()) - every + min(delay, every)))
    return n


async def run_backup(bot, chat_id) -> str:
    """بکاپ می‌سازه؛ اول Saved Messages، و اگه سشن نبود یا ارسال شکست خورد، چت ربات با کارفرما.
    فایل موقت فقط بعد از ارسال و تأیید موفق پاک میشه. اگه هر دو مسیر شکست بخورن exception میاد
    و فایل موقت برای بررسی می‌مونه. دیتابیس اصلی هرگز پاک نمیشه."""
    meta = await asyncio.to_thread(make_backup)
    note = ""
    if await saved_ready():
        try:
            text = await send_backup_saved(meta)
            _safe_rmtree(meta["tmpdir"])
            set_setting("backup_fail_n", "0")
            return text
        except Exception as e:  # noqa
            log.exception("saved backup failed")
            log_err(f"saved backup failed: {e!r}")
            note = "⚠️ ارسال به Saved Messages ناموفق بود؛ به‌جاش بکاپ به چت ربات فرستاده شد\n\n"
    else:
        note = "ℹ️ سشن اکانت شخصی در دسترس نبود؛ بکاپ به چت ربات فرستاده شد\n\n"
    _res = note + await send_backup(bot, chat_id, meta)
    set_setting("backup_fail_n", "0")
    return _res


_backup_busy = False


async def daily_backup_job(context: ContextTypes.DEFAULT_TYPE):
    """بکاپ خودکار؛ فاصله‌اش از تنظیمات پیشرفته انتخاب میشه (۱۰ دقیقه تا ۲۴ ساعت).
    در صورت خطا خودش با فاصله‌ی ۵ تا ۳۰ دقیقه دوباره تلاش میکنه تا ارسال بشه و فقط یک پیام خطا میاد."""
    global _backup_busy
    now = int(time.time())
    every = backup_every()
    if _backup_busy or now - get_int_setting("last_backup_ts") < every:
        return
    _backup_busy = True
    try:
        result = await run_backup(context.bot, OWNER_ID)
        set_setting("last_backup_ts", str(int(time.time())))
        if every >= 86400:  # بکاپ‌های پی‌درپی پیام جدا نمیفرستن؛ فایل توی Saved Messages هست
            hold_notice(await context.bot.send_message(OWNER_ID, fb("بکاپ ارسال شد ✅"), parse_mode=H, disable_notification=True))  # مثل نوتیف خطا، بعد از موعدش خودش پاک میشه
    except Exception as e:  # noqa
        log.exception("daily backup failed")
        log_err(f"daily backup failed: {e!r}")
        if backup_fail_register() == 1:  # فقط یک پیام؛ ربات خودش تا ارسال بشه دوباره تلاش میکنه
            await safe_send_hold(context.bot, OWNER_ID, fb("بکاپ ارسال نشد ❌"), html_mode=True)
    finally:
        _backup_busy = False


QUESTIONS_EVERY = 7 * 86400
QUESTIONS_RETRY = 6 * 3600


def build_questions_text(rows) -> str:
    return ("\n" + "-" * 20 + "\n").join(r["text"] for r in rows) + "\n"


async def questions_export_job(context: ContextTypes.DEFAULT_TYPE):
    """هر ۷ روز همه‌ی پیام‌های دارای علامت سوال که هنوز نرفتن، به‌صورت یک فایل متنی میرن Saved Messages.
    علامت «فرستاده شد» فقط بعد از ارسال و تأیید (حجم + هش) خورده میشه؛ فایل موقت هم همون موقع پاک میشه."""
    now = int(time.time())
    last = get_int_setting("questions_last_ts")
    if last == 0:
        set_setting("questions_last_ts", str(now))
        return
    if now - last < QUESTIONS_EVERY:
        return
    rows = qa("SELECT * FROM faq_questions WHERE sent=0 ORDER BY id")
    if not rows:
        set_setting("questions_last_ts", str(now))
        return
    if now - get_int_setting("questions_retry_ts") < QUESTIONS_RETRY:
        return
    tmpdir = None
    try:
        if not await saved_ready():
            raise RuntimeError("سشن اکانت شخصی در دسترس نیست")
        data = build_questions_text(rows).encode("utf-8")
        tmpdir = tempfile.mkdtemp(prefix="jazban_q_")
        path = os.path.join(tmpdir, "سوالات متداول.txt")
        with open(path, "wb") as f:
            f.write(data)
        client = SESSION_CLIENT
        msg = None
        for _ in range(3):
            try:
                msg = await client.send_file("me", path, caption=f"❓ سوالات متداول\n{jdate_en(now)}",
                                             force_document=True)
                break
            except FloodWaitError as e:
                await asyncio.sleep(e.seconds + 1)
        if msg is None or getattr(msg, "document", None) is None:
            raise RuntimeError("ارسال به Saved Messages انجام نشد")
        if msg.document.size != len(data):
            raise RuntimeError("حجم فایل ارسال‌شده با فایل اصلی یکی نیست")
        back = await client.download_media(msg, file=bytes)
        if not back or hashlib.sha256(back).hexdigest() != hashlib.sha256(data).hexdigest():
            raise RuntimeError("هش فایل ارسال‌شده با فایل اصلی یکی نیست")
        ex("UPDATE faq_questions SET sent=1 WHERE sent=0 AND id<=?", (rows[-1]["id"],))
        set_setting("questions_last_ts", str(now))
        _safe_rmtree(tmpdir)
        await safe_send(context.bot, OWNER_ID,
                        fb(f"✅ فایل سوال‌های این هفته「{len(rows)}」تا تو Saved Messages ذخیره و تأیید شد ✅"), html_mode=True)
    except Exception as e:  # noqa
        log.exception("questions export failed")
        log_err(f"questions export failed: {e!r}")
        set_setting("questions_retry_ts", str(now))
        await safe_send_hold(context.bot, OWNER_ID,
                        f"❌ ارسال فایل سوال‌ها به Saved Messages ناموفق بود ❌\n\n{e}\n\n"
                        "سوال‌ها ذخیره موندن و ۶ ساعت دیگه دوباره تلاش میشه.", html_mode=False)


async def send_backup(bot, chat_id, meta: dict) -> str:
    """ارسال بکاپ. فایل موقت فقط بعد از تأیید موفقیت ارسال پاک میشه (و برای فایل‌های تا ۲۰ مگابایت
    فایل ارسال‌شده دوباره از تلگرام دانلود و هشش با فایل اصلی مقایسه میشه)."""
    items = meta["items"]
    total = len(items)
    downloaded_ok = True
    for i, it in enumerate(items, 1):
        cap = f"☁️ بک‌آپ ☁️「 {jdate_en(int(time.time()))} 」"  # کپشن: تاریخ همون روز به فارسی
        if meta["packed"]:
            cap += f"\n\n🔹 فایل「{i}」از「{total}」\n🔐 هش: {it['sha'][:16]}"
        msg = None
        for _ in range(3):
            try:
                with open(it["path"], "rb") as f:
                    msg = await bot.send_document(chat_id, f, filename=it["name"], caption=cap,
                                                  read_timeout=600, write_timeout=600,
                                                  connect_timeout=60, pool_timeout=60)
                break
            except RetryAfter as e:  # مکث flood_wait حفظ میشه
                await asyncio.sleep(e.retry_after + 1)
        if msg is None or msg.document is None:
            raise RuntimeError(f"send failed for {it['name']}")
        if msg.document.file_size != it["size"]:
            raise RuntimeError(f"size mismatch for {it['name']}: sent={it['size']} telegram={msg.document.file_size}")
        if it["size"] <= 20 * 1024 * 1024:
            tg_file = await bot.get_file(msg.document.file_id)
            data = await tg_file.download_as_bytearray()
            if hashlib.sha256(bytes(data)).hexdigest() != it["sha"]:
                raise RuntimeError(f"downloaded hash mismatch for {it['name']}")
        else:
            downloaded_ok = False  # Bot API دانلود فایل بالای ۲۰ مگابایت رو اجازه نمیده
    _safe_rmtree(meta["tmpdir"])
    mb = fa(f"{meta['db_size'] / 1048576:.1f}")
    lines = ["✅ پشتیبان با موفقیت ارسال و تأیید شد ✅\n",
             f"🔹 حجم دیتابیس:「{mb}」مگابایت",
             f"🔷 تعداد فایل ارسال‌شده:「{total}」",
             f"🔐 هش SHA-256 دیتابیس:\n<code>{meta['db_sha']}</code>"]
    if meta["packed"]:
        lines.append("\n🗜️ فایل بزرگ بود؛ فشرده شد و محتوای فایل فشرده با دیتابیس اصلی تطبیق داده شد")
        if total > 1:
            lines.append("برای بازیابی: فایل‌ها رو به ترتیب شماره کنار هم بذار و بعد با gunzip باز کن")
    if downloaded_ok:
        lines.append("\n✅ فایل ارسال‌شده دوباره دانلود و محتواش با فایل اصلی یکی بود")
    else:
        lines.append("\n⚠️ فایل بزرگ‌تر از ۲۰ مگابایته و تلگرام اجازه دانلود مجدد نمیده؛ "
                     "صحت محتوا قبل از ارسال تأیید شد و حجم فایل ارسال‌شده با فایل اصلی یکی بود")
    return "\n".join(lines)


# ----------------------------------------------------------------------------
# آمار روزانه‌ی سیستم (بازه‌ی آماری: ۶ صبح تا ۶ صبح روز بعد؛ تاریخ گزارش = روزی که بازه ازش شروع شده)
# ----------------------------------------------------------------------------
STATS_ROLL = 6            # ساعت شروع بازه‌ی آماری (به وقت TZ)
STATS_TREND_DAYS = 5      # روند: حداکثر چند روز اخیر
STATS_PER_PAGE = 30       # تعداد دکمه‌ی تاریخ در هر صفحه
STATS_RETRY = 600         # بعد از شکست ارسال، چند ثانیه بعد دوباره تلاش بشه
STATS_DELAY = 300         # گزارش هر بازه دقیقاً ۵ دقیقه بعد از پایان بازه (۶:۰۵) محاسبه و ارسال میشه
STATS_BASELINE_DAY = "2026-10-29"   # شروع آمار نسخه‌ی جدید: ۶ صبح پنج‌شنبه ۷ آبان ۱۴۰۵ (آمار قبلی دست‌نخورده می‌مونه ولی توی گزارش‌ها حساب نمیشه)
CONGRATS_PHRASE = "تبریک استخدام شما نهایی شد"   # متنی که بعد از ویدیوی شروع برای هر نفر میره
STAT_NO_DATA = "「داده کافی برای {} نیست」"


def stat_day(ts=None) -> str:
    """تاریخ (میلادی، YYYY-MM-DD) روزی که بازه‌ی آماریِ شامل این لحظه از اون شروع شده."""
    dt = dt_of(int(ts if ts is not None else time.time())) - timedelta(hours=STATS_ROLL)
    return dt.strftime("%Y-%m-%d")


def stat_window(day: str):
    d = datetime.strptime(day, "%Y-%m-%d")
    s = datetime(d.year, d.month, d.day, STATS_ROLL, tzinfo=TZ)
    return int(s.timestamp()), int((s + timedelta(days=1)).timestamp())


def _event_ts(event):
    """زمان واقعیِ یک پیام تلگرام (ثانیه)؛ اگه نبود، همین لحظه."""
    try:
        return int(event.date.timestamp())
    except Exception:  # noqa
        return int(time.time())


def stats_baseline() -> str:
    """اولین روزِ آمارِ معتبر (YYYY-MM-DD)؛ آمارِ روزهای قبلش توی دیتابیس می‌مونه ولی توی گزارش و روند و رشد حساب نمیشه."""
    return get_setting("stats_baseline_day") or STATS_BASELINE_DAY


def stat_log(kind: str, user_id: int, admin_id=None, once_ever: bool = False, ts=None) -> bool:
    """ثبت یک رویداد آماری؛ هر نفر در هر بازه برای هر نوع فقط یک بار (once_ever: فقط یک بار در کل).
    ts = زمان واقعیِ پیام (برای پیام‌های وقت خاموشی/بازسازی)؛ بدون ts زمان همین لحظه ثبت میشه."""
    try:
        if once_ever and q1("SELECT 1 FROM stat_events WHERE kind=? AND user_id=?", (kind, user_id)) is not None:
            return False
        ts = int(ts) if ts else int(time.time())
        cur = ex("INSERT OR IGNORE INTO stat_events(kind,user_id,admin_id,ts,day) VALUES(?,?,?,?,?)",
                 (kind, int(user_id), admin_id, ts, stat_day(ts)))
        return cur.rowcount > 0
    except Exception as e:  # noqa
        log_err(f"stat_log {kind}: {e!r}")
        return False


def _stat_already_hired(uid: int, ts=None) -> bool:
    """قبل از این پیام، این نفر توی جدول جذب‌ها ثبت شده بوده (جذب قدیمی)؛ دوباره «جذب با کد» حساب نمیشه.
    فقط جذب‌های قبل از زمان پیام حساب میشن، تا بازسازی/جبران خاموشیِ جذب‌های همون بازه خراب نشه."""
    t = int(ts) if ts else int(time.time())
    return q1("SELECT 1 FROM hires WHERE applicant_id=? AND ts<?", (uid, t)) is not None


def stat_code_only(user, text: str, allow_bare: bool = True, ts=None) -> None:
    """مسیرهای ربات (Business و پیام مستقیم به ربات): فقط «جذب با کد» ثبت میشه (جذب مستقیم/شروع/ثبت‌نام فقط از اکانت شخصیه).
    هر نفر برای هر نوع فقط یک بار ثبت میشه، پس اگه همون پیام از مسیر اکانت شخصی هم بیاد دوبار شمرده نمیشه."""
    try:
        uid = user.id
        if getattr(user, "bot", False) or uid == OWNER_ID or q1("SELECT 1 FROM admins WHERE user_id=?", (uid,)):
            return
        code_admin = _stat_code_admin(uid, text, allow_bare)
        if code_admin is not None and not _stat_already_hired(uid, ts):
            stat_log("code", uid, code_admin, once_ever=True, ts=ts)
    except Exception as e:  # noqa
        log_err(f"stat_code_only: {e!r}")


def _stat_code_admin(uid: int, text: str, allow_bare: bool = True):
    """ادمینی که کدش توی این پیام اومده (اولین کدِ معتبر)؛ کد خودِ ادمین برای خودش حساب نمیشه."""
    code_admin = None
    for c in parse_hire_codes(text, allow_bare):
        r = q1("SELECT user_id FROM admins WHERE code=?", (c,))
        if r is not None:
            code_admin = r["user_id"]
            break
    return None if code_admin == uid else code_admin


async def stat_incoming(sender, text: str, allow_bare: bool = True, ts=None) -> None:
    """پیام خصوصیِ ورودی: «جذب با کد» (از لحظه‌ی ارسال کد، مستقل از سپر) و «جذب مستقیم» (اولین پیام بدون کد)."""
    uid = sender.id
    if getattr(sender, "bot", False) or uid == OWNER_ID or q1("SELECT 1 FROM admins WHERE user_id=?", (uid,)):
        return
    code_admin = _stat_code_admin(uid, text, allow_bare)
    if code_admin is not None and not _stat_already_hired(uid, ts):
        stat_log("code", uid, code_admin, once_ever=True, ts=ts)
    if q1("SELECT 1 FROM stat_events WHERE user_id=? AND kind IN ('lead','old')", (uid,)) is None:
        # اولین پیامِ این آدم که تا حالا دیده شده: آدم تازه (lead) یا چت قدیمی (old)؛ علامتش میخوره تا دوباره چک نشه
        _new = await _auto_is_new_ex(sender)
        if _new is None:
            return  # خطای موقت: برچسب دائمی نمیخوره؛ با پیام بعدیِ همین آدم دوباره بررسی میشه
        if _new:
            stat_log("lead", uid, code_admin, once_ever=True, ts=ts)
        else:
            stat_log("old", uid, once_ever=True, ts=ts)


def stat_words(uid: int, text: str, ts=None, alt_hint: bool = False, nine_hint: bool = False) -> None:
    """«شروع» (بعد از ۹ پیام) و «تایید شرایط» (راه جایگزین) که متقاضی فرستاده.
    alt_hint: توی بازسازی از تاریخچه، یعنی «راه جایگزین» قبلاً توی همین چت برای اون آدم نوشته شده."""
    if uid == OWNER_ID:
        return
    w = _aw(text)
    if not w:
        return
    row = _auto_row(uid)
    if w.startswith("شروع") and len(w) <= 12 and ((row is not None and row["nine_sent"] in (1, 2)) or nine_hint):
        stat_log("shoro", uid, once_ever=True, ts=ts)
    if w.startswith("تاییدشرایط") or (w == "تایید" and ((row is not None and row["alt_sent"]) or alt_hint)):
        stat_log("alt", uid, once_ever=True, ts=ts)


def signup_admin_of(uid: int) -> int:
    """ادمینی که کدش توی چت این نفر اومده: جذبِ ثبت‌شده، یا (سپر) کدِ در انتظار. اگه کدی نیومده باشه 0."""
    r = q1("SELECT admin_id FROM hires WHERE applicant_id=?", (uid,))
    if r is not None:
        return int(r["admin_id"])
    p = q1("SELECT a.user_id FROM shield_pending s JOIN admins a ON a.code=s.code WHERE s.applicant_id=?", (uid,))
    return int(p["user_id"]) if p is not None else 0


def signup_record(uid: int, ts=None) -> bool:
    """«تایید استخدام» توی چت یک نفر = یک ثبت‌نام برای ادمینی که کدش توی همون چت اومده. هر نفر فقط یک بار."""
    try:
        if uid == OWNER_ID or q1("SELECT 1 FROM admins WHERE user_id=?", (uid,)):
            return False
        aid = signup_admin_of(uid)
        cur = ex("INSERT OR IGNORE INTO signups(applicant_id,admin_id,ts) VALUES(?,?,?)",
                 (uid, aid, int(ts) if ts else int(time.time())))
        if cur.rowcount == 0 and aid:
            ex("UPDATE signups SET admin_id=? WHERE applicant_id=? AND admin_id=0", (aid, uid))
        return cur.rowcount > 0
    except Exception as e:  # noqa
        log_err(f"signup_record: {e!r}")
        return False


def admin_signups(a, period_n=None) -> tuple:
    """(ثبت‌نام‌های این دوره, مجموع ثبت‌نام‌ها) یک ادمین. این دوره = ثبت‌نامِ همون نفراتی که جذبشون توی دوره‌ی فعلی شمرده شده."""
    try:
        uid = a["user_id"]
        n = int(a["period_count"] or 0) if period_n is None else int(period_n)
        tot = q1("SELECT COUNT(*) n FROM signups WHERE admin_id=?", (uid,))["n"]
        per = q1("SELECT COUNT(*) n FROM signups s WHERE s.admin_id=? AND ("
                 "s.applicant_id IN (SELECT applicant_id FROM hires WHERE admin_id=? ORDER BY ts DESC, rowid DESC LIMIT ?) "
                 "OR s.applicant_id IN (SELECT applicant_id FROM shield_pending))", (uid, uid, n))["n"]
        return int(per), int(tot)
    except Exception as e:  # noqa
        log_err(f"admin_signups: {e!r}")
        return 0, 0


def stat_outgoing(uid: int, text: str, ts=None) -> None:
    """پیام خودت توی چت یک نفر. «تایید استخدام» بعد از ارسال درجا پاک میشه، پس همون لحظه ثبت میشه."""
    if uid == OWNER_ID:
        return
    if _aw(text or "") == _aw(AUTO_VIDEO_TRIGGER):
        stat_log("signup", uid, once_ever=True, ts=ts)
        signup_record(uid, ts)  # ثبت‌نام برای ادمینی که کدش توی این چت اومده


def _stat_slope(ys):
    n = len(ys)
    mx, my = (n - 1) / 2, sum(ys) / n
    den = sum((x - mx) ** 2 for x in range(n)) or 1
    return sum((x - mx) * (y - my) for x, y in enumerate(ys)) / den, my


def stats_trend(day: str, total: int, active: int):
    """روند چندروزه‌ی «جذب کل» و «ادمین‌های فعال» از تاریخچه‌ی روزانه‌ی همین نسخه (نه آمار تجمعی)؛ کمتر از ۳ روز داده = None."""
    prev = qa("SELECT day, data FROM daily_stats WHERE day<? AND day>=? ORDER BY day DESC LIMIT ?",
              (day, stats_baseline(), STATS_TREND_DAYS - 1))
    ys_c, ys_a = [], []
    for r in reversed(prev):
        try:
            d = json.loads(r["data"])
            if "total" not in d:
                continue
            ys_c.append(int(d.get("total", 0)))
            ys_a.append(int(d.get("active", 0)))
        except Exception:  # noqa
            continue
    ys_c.append(total)
    ys_a.append(active)
    if len(ys_c) < 3:
        return None
    sc, mc = _stat_slope(ys_c)
    sa, ma = _stat_slope(ys_a)
    rel_c = sc / mc if mc > 0 else 0.0
    rel_a = sa / ma if ma > 0 else 0.0
    score = rel_c if ma == 0 else (rel_c + rel_a) / 2
    if score > 0.08:
        return "شتاب‌گیرنده"
    if score < -0.08:
        return "کاهشی"
    return "ثابت"


def paid_sum(start=None, end=None) -> int:
    """جمع پورسانت‌های واریزشده (تومان)؛ با start/end فقط پرداخت‌هایی که تو اون بازه‌ی زمانی واریز شدن."""
    sql = "SELECT COALESCE(SUM(COALESCE(NULLIF(paid_amount,0),amount)),0) n FROM commissions WHERE status='paid'"
    args = []
    if start is not None:
        sql += " AND paid_at>=?"
        args.append(int(start))
    if end is not None:
        sql += " AND paid_at<?"
        args.append(int(end))
    r = q1(sql, tuple(args))
    return int(r["n"] or 0) if r is not None else 0


def comeback_stat(col: str, start=None, end=None) -> int:
    """تعداد نفرهای بازگشت (پیام ارسال‌شده / دکمه‌ی شروع دوباره / تکمیل آموزش) در بازه؛ بدون بازه = از ابتدا."""
    if col not in ("sent_at", "pressed_at", "done_at"):
        return 0
    sql, args = f"SELECT COUNT(*) n FROM comeback WHERE {col}>0", []
    if start is not None:
        sql += f" AND {col}>=?"
        args.append(int(start))
    if end is not None:
        sql += f" AND {col}<?"
        args.append(int(end))
    r = q1(sql, tuple(args))
    return int(r["n"] or 0) if r is not None else 0


def stats_cumulative() -> dict:
    """آمار تجمعی از ابتدای فعالیت (جدا از آمار روزانه؛ هیچ‌وقت وارد شمارش‌های ۲۴ ساعته نمیشه)."""
    def n(sql, *a):
        r = q1(sql, a)
        return int(r["n"] or 0) if r is not None else 0
    return {
        "cum_users": n("SELECT COUNT(*) n FROM members WHERE user_id<>?", OWNER_ID),
        "cum_admins": n("SELECT COUNT(*) n FROM admins WHERE user_id<>?", OWNER_ID),
        "cum_hires": n("SELECT COALESCE(SUM(total_count),0) n FROM admins WHERE user_id<>?", OWNER_ID),
        "cum_signup_alt": n("SELECT COUNT(DISTINCT user_id) n FROM stat_events WHERE kind IN ('signup','alt')"),
        "cum_paid": paid_sum(),
        "cum_cb_sent": comeback_stat("sent_at"),
        "cum_cb_btn": comeback_stat("pressed_at"),
        "cum_cb_done": comeback_stat("done_at"),
        "cum_why1": n("SELECT COUNT(*) n FROM nudge_why WHERE choice=1"),
        "cum_why2": n("SELECT COUNT(*) n FROM nudge_why WHERE choice=2"),
        "cum_why3": n("SELECT COUNT(*) n FROM nudge_why WHERE choice=3"),
    }


def stats_compute(day: str, until=None) -> dict:
    """آمار یک بازه‌ی ۶ صبح تا ۶ صبح. until: برای گزارش لحظه‌ایِ بازه‌ی در حال گذر (تا همین الان)."""
    s, e = stat_window(day)
    if until is not None:
        e = min(e, int(until))

    def n(sql, *a):
        return q1(sql, a)["n"]

    code = n("SELECT COUNT(*) n FROM stat_events WHERE day=? AND kind='code'", day)
    active = n("SELECT COUNT(DISTINCT admin_id) n FROM stat_events WHERE day=? AND kind='code'", day)
    total = n("SELECT COUNT(DISTINCT user_id) n FROM stat_events WHERE day=? AND kind IN ('code','lead')", day)
    # ثبت‌نام = «تایید استخدام» که فرستادی؛ راه جایگزین = «تایید شرایط» که متقاضی فرستاده
    signup = n("SELECT COUNT(DISTINCT user_id) n FROM stat_events WHERE day=? AND kind='signup'", day)
    alt = n("SELECT COUNT(DISTINCT user_id) n FROM stat_events WHERE day=? AND kind='alt'", day)
    data = {
        "shoro": n("SELECT COUNT(*) n FROM stat_events WHERE day=? AND kind='shoro'", day),
        "signup": signup,
        "alt": alt,
        "active": active,
        "code": code,
        # جذب مستقیم: اولین پیام بدون کد، به شرطی که بعدش با کد ادمینی هم جذب نشده باشه (تا دوبار شمرده نشه)
        "direct": n("SELECT COUNT(*) n FROM stat_events WHERE day=? AND kind='lead' AND admin_id IS NULL "
                    "AND user_id NOT IN (SELECT user_id FROM stat_events WHERE kind='code')", day),
        "total": total,
        "new_users": n("SELECT COUNT(*) n FROM members WHERE first_seen>=? AND first_seen<? AND user_id<>?",
                       s, e, OWNER_ID),
        "delchat": n("SELECT COUNT(*) n FROM stat_events WHERE day=? AND kind='delchat'", day),
        "paid_today": paid_sum(s, e),
        "cb_sent": comeback_stat("sent_at", s, e),
        "cb_btn": comeback_stat("pressed_at", s, e),
        "cb_done": comeback_stat("done_at", s, e),
        "growth": None, "avg": None, "trend": None,
    }
    data.update(stats_cumulative())
    _partial = until is not None and until < stat_window(day)[1]
    if _partial:
        data["partial_until"] = int(until)
    prev_day = (datetime.strptime(day, "%Y-%m-%d") - timedelta(days=1)).strftime("%Y-%m-%d")
    pr = q1("SELECT data FROM daily_stats WHERE day=? AND day>=?", (prev_day, stats_baseline()))
    if pr is not None and not _partial:  # گزارش لحظه‌ای با روز کامل قبل مقایسه نمیشه
        try:
            pd = json.loads(pr["data"])
            if "total" in pd:
                pc = int(pd["total"])
                data["growth"] = {"diff": total - pc, "pct": (round((total - pc) * 100 / pc) if pc > 0 else None)}
        except Exception:  # noqa
            pass
    if active > 0:
        data["avg"] = round(code / active, 1)  # جذب با کدِ ۲۴ ساعت ÷ ادمین‌هایی که همون بازه جذب داشتن
    data["trend"] = None if _partial else stats_trend(day, total, active)
    return data


def jalali_label(day: str, with_year: bool = True) -> str:
    y, m, d = (int(x) for x in day.split("-"))
    jy, jm, jd = to_jalali(y, m, d)
    return f"{jd} {J_MONTHS[jm - 1]}" + (f" {jy}" if with_year else "")


def stats_text(day: str, d: dict) -> str:
    g = d.get("growth")
    if g is None:
        growth = STAT_NO_DATA.format("مقایسه")
    else:
        diff = int(g["diff"])
        growth = f"「{diff:+d} نفر" + (f" | {int(g['pct']):+d}%" if g.get("pct") is not None else "") + "」"
        if diff == 0:
            growth = "「0 نفر | 0%」" if g.get("pct") is not None else "「0 نفر」"
    avg = f"「{d['avg']} جذب」" if d.get("avg") is not None else STAT_NO_DATA.format("محاسبه")
    trend = f"「{d['trend']}」" if d.get("trend") else STAT_NO_DATA.format("تحلیل روند")
    sep = "➖•➖•➖•➖•➖•➖•➖•➖•➖•➖"
    _pu = d.get("partial_until")
    partial = f"⏱️ <b>گزارش لحظه‌ای</b>: از ساعت 6:00 تا {dt_of(int(_pu)).strftime('%H:%M')}\n" if _pu else ""

    def cum(k, unit):
        return f"「{d[k]} {unit}」" if d.get(k) is not None else "「ثبت نشده」"

    def money(k):
        return f"「{fmt_en(int(d[k]))} تومان」" if d.get(k) is not None else "「ثبت نشده」"
    _cs, _cb = d.get("cum_cb_sent"), d.get("cum_cb_btn")
    if _cs and _cb is not None:
        cb_rate = f"「{round(_cb * 100 / _cs)}% | {_cb} از {_cs} نفر」"
    else:
        cb_rate = STAT_NO_DATA.format("محاسبه")
    return (
        f"{sep}\n"
        "📉 <b>آمار سیستم</b>🔻\n"
        f"🗓️ <b>تاریخ</b>:「{jalali_label(day)}」\n"
        f"{partial}"
        f"{sep}\n"
        "🕕 <b>آمار ۲۴ ساعت اخیر</b> (6 صبح تا 6 صبح)\n\n"
        f"✧ <b>ارسال پیام شروع</b>:\n「{d['shoro']} نفر」\n"
        f"✧ <b>ثبت‌نام</b>:\n「{d['signup']} نفر」\n"
        f"✧ <b>راه جایگزین</b>:\n「{d['alt']} نفر」\n"
        f"✧ <b>ادمین‌های فعال</b>:\n「{d['active']} ادمین」\n"
        f"✧ <b>جذب با کد ادمین‌ها</b>:\n「{d['code']} نفر」\n"
        f"✧ <b>جذب مستقیم</b>:「{d['direct']} نفر」\n"
        f"✧ <b>جذب کل</b>:「{d['total']} نفر」\n"
        f"✧ <b>کاربران جدید ربات</b>:「{d['new_users']} نفر」\n"
        f"✧ <b>دلیت چت</b>:「{d['delchat']} نفر」\n"
        f"✧ <b>پیام بازگشت</b>:{cum('cb_sent', 'نفر')}\n"
        f"✧ <b>بازگشت با دکمه</b>:{cum('cb_btn', 'نفر')}\n"
        f"✧ <b>تکمیل آموزش بعد از بازگشت</b>:{cum('cb_done', 'نفر')}\n"
        f"✧ <b>پرداخت پورسانت</b>:{money('paid_today')}\n"
        f"{sep}\n"
        "🗄️ <b>آمار تجمعی از ابتدای فعالیت</b>\n\n"
        f"✧ <b>کل کاربران ثبت‌شده</b>:\n{cum('cum_users', 'نفر')}\n"
        f"✧ <b>کل ادمین‌ها</b>:\n{cum('cum_admins', 'ادمین')}\n"
        f"✧ <b>مجموع جذب‌های ادمین‌ها</b>:\n{cum('cum_hires', 'نفر')}\n"
        f"✧ <b>مجموع ثبت‌نام و راه جایگزین</b>:\n{cum('cum_signup_alt', 'نفر')}\n"
        f"✧ <b>مجموع پیام بازگشت</b>:\n{cum('cum_cb_sent', 'نفر')}\n"
        f"✧ <b>مجموع بازگشت با دکمه</b>:\n{cum('cum_cb_btn', 'نفر')}\n"
        f"✧ <b>مجموع تکمیل آموزش بعد از بازگشت</b>:\n{cum('cum_cb_done', 'نفر')}\n"
        f"✧ <b>دلیل جذب‌نکردن، نمی‌دونم کجا کامنت بذارم</b>:{cum('cum_why1', 'نفر')}\n"
        f"✧ <b>دلیل جذب‌نکردن، کسی جواب نمی‌ده</b>:\n{cum('cum_why2', 'نفر')}\n"
        f"✧ <b>دلیل جذب‌نکردن، وقت ندارم</b>:\n{cum('cum_why3', 'نفر')}\n"
        f"✧ <b>مجموع پرداخت پورسانت</b>:\n{money('cum_paid')}\n"
        f"{sep}\n"
        "📈 <b>شاخص‌های تحلیلی</b>\n\n"
        f"🪜 <b>رشد جذب نسبت به روز قبل</b>: \n{growth}\n\n"
        f"🪜 <b>میانگین جذب ادمین فعال</b>: \n{avg}\n\n"
        f"🪜 <b>نرخ بازگشت بعد از پیام</b>: \n{cb_rate}\n\n"
        f"🪜 <b>روند تصاعد شبکه جذب</b>:\n{trend}\n"
        f"{sep}"
    )


def stats_row_text(r) -> str:
    try:
        d = json.loads(r["data"])
        if "paid_today" not in d:  # روزهای قبل از اضافه شدن این خط: از دیتابیس محاسبه میشه
            _s, _e = stat_window(r["day"])
            d["paid_today"] = paid_sum(_s, _e)
            d["cum_paid"] = paid_sum(None, _e)
        if "cb_sent" not in d:  # روزهای قبل از اضافه شدن خطوط بازگشت
            _s, _e = stat_window(r["day"])
            d["cb_sent"], d["cb_btn"], d["cb_done"] = (comeback_stat(c, _s, _e) for c in ("sent_at", "pressed_at", "done_at"))
            d["cum_cb_sent"], d["cum_cb_btn"], d["cum_cb_done"] = (comeback_stat(c, None, _e) for c in ("sent_at", "pressed_at", "done_at"))
        if "cum_why1" not in d:  # روزهای قبل از اضافه شدن خطوط دلیل جذب‌نکردن
            _s, _e = stat_window(r["day"])
            for _i in (1, 2, 3):
                _r = q1("SELECT COUNT(*) n FROM nudge_why WHERE choice=? AND ts<?", (_i, _e))
                d[f"cum_why{_i}"] = int(_r["n"] or 0) if _r is not None else 0
        return stats_text(r["day"], d)
    except Exception as e:  # noqa
        log_err(f"stats_row_text {r['day']}: {e!r}")
        return ""


def stats_row(day: str):
    """ردیف آمار یک روز؛ فقط از روز شروعِ آمار جدید به بعد (روزهای قبلش دست‌نخورده توی دیتابیسن ولی نمایش داده نمیشن)."""
    return q1("SELECT day, data FROM daily_stats WHERE day=? AND day>=?", (day, stats_baseline()))


def stats_last_row():
    return q1("SELECT day, data FROM daily_stats WHERE day>=? ORDER BY day DESC LIMIT 1", (stats_baseline(),))


def stats_file_text() -> str:
    """فایل متنیِ آمار: همه‌ی روزها با همون قالب گزارش (جدیدترین بالا)."""
    rows = qa("SELECT day, data FROM daily_stats WHERE day>=? ORDER BY day DESC", (stats_baseline(),))
    return "\n\n".join(_strip_html(stats_row_text(r)) for r in rows) + "\n"


def jalali_to_gregorian(jy: int, jm: int, jd: int):
    jy += 1595
    days = (-355668 + (365 * jy) + (jy // 33) * 8 + (((jy % 33) + 3) // 4) + jd
            + ((jm - 1) * 31 if jm < 7 else ((jm - 7) * 30) + 186))
    gy = 400 * (days // 146097)
    days %= 146097
    if days > 36524:
        days -= 1
        gy += 100 * (days // 36524)
        days %= 36524
        if days >= 365:
            days += 1
    gy += 4 * (days // 1461)
    days %= 1461
    if days > 365:
        gy += (days - 1) // 365
        days = (days - 1) % 365
    gd = days + 1
    leap = (gy % 4 == 0 and gy % 100 != 0) or gy % 400 == 0
    sal = [0, 31, 29 if leap else 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
    gm = 0
    while gm < 13 and gd > sal[gm]:
        gd -= sal[gm]
        gm += 1
    return gy, gm, gd


def parse_jalali_day(text: str):
    """«1405/07/13» یا «13 مهر 1405» (ارقام فارسی هم قبوله) -> تاریخ میلادیِ YYYY-MM-DD؛ نامعتبر = None."""
    t = normalize(text or "")
    nums = [int(x) for x in re.findall(r"\d+", t)]
    jy = jm = jd = None
    _t = t.replace(" ", "")
    named = next((i for i, nm in enumerate(J_MONTHS, 1) if nm in _t), None)
    if named and len(nums) == 2:
        jm = named
        jd, jy = (nums[0], nums[1]) if nums[0] <= 31 else (nums[1], nums[0])
    elif len(nums) == 3:
        if nums[0] > 31:
            jy, jm, jd = nums
        elif nums[2] > 31:
            jd, jm, jy = nums
    if jy is None:
        return None
    if jy < 100:
        jy += 1400
    if not (1 <= jm <= 12 and 1 <= jd <= 31 and 1300 <= jy <= 1600):
        return None
    try:
        gy, gm, gd = jalali_to_gregorian(jy, jm, jd)
        if to_jalali(gy, gm, gd) != (jy, jm, jd):
            return None
        return datetime(gy, gm, gd).strftime("%Y-%m-%d")
    except (ValueError, IndexError):
        return None


def stats_list_menu(page: int = 0):
    days = [r["day"] for r in qa("SELECT day FROM daily_stats WHERE day>=? ORDER BY day DESC", (stats_baseline(),))]
    pages = max((len(days) + STATS_PER_PAGE - 1) // STATS_PER_PAGE, 1)
    page = min(max(page, 0), pages - 1)
    chunk = days[page * STATS_PER_PAGE:(page + 1) * STATS_PER_PAGE]
    btns = []
    for d in chunk:
        y_, m_, d_ = (int(x) for x in d.split("-"))
        jy_, jm_, jd_ = to_jalali(y_, m_, d_)
        btns.append(B(f"{fa(jd_)} {J_MONTHS[jm_ - 1]} {fa(jy_)}", f"o:std:{d}",
                      style="danger"))  # مثل «۱۲ مهر ۱۴۰۵»؛ همه قرمز
    rows = [btns[i:i + 2] for i in range(0, len(btns), 2)]
    nav = nav_row(lambda p: f"o:sts:{p}", page, pages)
    if nav:
        rows.append(nav)
    rows.append(B("♨️ دریافت آخرین آمار ♨️", "o:stl", style="primary"))
    rows.append(B("✍️ وارد کردن دستی تاریخ ✍️", "o:stm", style="success"))
    rows.append(BACK("o:adv"))
    sep = "➖•➖•➖•➖•➖•➖•➖•➖•➖•➖"
    head = f"<b>{sep}\nSYSTEM STATISTICS 📉 | آمار سیستم</b>\n\n"
    text = (head + f"تاریخ مورد نظرت رو انتخاب کن: 📅\n<b>{sep}</b>" if days else
            head + f"هنوز آماری ذخیره نشده؛ گزارش هر بازه ساعت 6:05 صبحِ بعدش ساخته و ارسال میشه.\n<b>{sep}</b>")
    return text, KB(*rows)


_stats_busy = False


async def stats_deliver(bot, day: str) -> None:
    """گزارش آمار (فقط متن) میره Saved Messages؛ گزارش قبلی بعد از ارسال موفق پاک میشه؛ بعدش بکاپ."""
    global _backup_busy
    if not await saved_ready():
        raise RuntimeError("سشن اکانت شخصی در دسترس نیست")
    client = SESSION_CLIENT
    r = stats_row(day)
    if r is None:
        return
    # ترتیب ارسال روزانه: اول گزارش (فقط متن، بدون فایل)، بعد بکاپ، بعد فورواردِ سومین پیام Saved Messages پشت‌بندش
    text = stats_row_text(r)
    try:
        old = [int(x) for x in json.loads(get_setting("stats_saved_ids") or "[]")]
    except (ValueError, TypeError):
        old = []
    m1 = None
    for _ in range(3):
        try:
            m1 = await client.send_message("me", text, parse_mode="html")
            break
        except FloodWaitError as e:
            await asyncio.sleep(e.seconds + 1)
    if m1 is None:
        raise RuntimeError("ارسال گزارش آمار به Saved Messages انجام نشد")
    set_setting("stats_saved_ids", json.dumps([m1.id]))
    set_setting("stats_sent_day", day)
    if old:
        try:
            await client.delete_messages("me", old)
        except Exception as e:  # noqa
            log_err(f"stats old delete: {e!r}")
    if _backup_busy:
        return
    _backup_busy = True
    try:
        await run_backup(bot, OWNER_ID)  # بکاپ زیر گزارش؛ فورواردِ سومین پیام هم پشت‌بندش میاد (داخل send_backup_saved)
        set_setting("last_backup_ts", str(int(time.time())))
    except Exception as e:  # noqa
        log_err(f"stats backup failed: {e!r}")
        if backup_fail_register() == 1:  # بکاپ خودش دوباره تلاش میکنه؛ فقط یک پیام خطا
            await safe_send_hold(bot, OWNER_ID, "بکاپ ارسال نشد ❌", html_mode=False)
    finally:
        _backup_busy = False


def stats_v2_migrate() -> None:
    """یک‌بار: آمار از روز شروعِ جدید دوباره محاسبه میشه (ردیف‌های قبلی حذف نمیشن؛ فقط توی گزارش‌ها حساب نمیشن)."""
    base = stats_baseline()
    if get_setting("stats_v2_base") == base:
        return
    prev = (datetime.strptime(base, "%Y-%m-%d") - timedelta(days=1)).strftime("%Y-%m-%d")
    set_setting("stats_last_day", prev)
    set_setting("stats_sent_day", "")
    set_setting("stats_v2_base", base)


SIGNUP_SCAN_MSGS = 150   # از ابتدای هر چت حداکثر چند پیام خونده میشه (ویدیوی تایید استخدام همون اوایل چته)
_signup_scan_running = False


async def signups_scan(client, bot=None) -> None:
    """موقع روشن شدن: همه‌ی چت‌های اکانت شخصی چک میشن. «تایید استخدام» درجا پاک میشه، پس هر ویدیویی که فرستادی
    (به‌جای اون کلمه) یک ثبت‌نامه، منهای چت‌هایی که قبل از ویدیو «🔹 راه جایگزین شما:» توشون نوشتی و منهای ویدیوی «شروع».
    ثبت‌نام به ادمینی میره که کدش توی همون چت اومده. فقط اضافه میکنه؛ چیزی حذف یا تکراری نمیشه."""
    global _signup_scan_running
    if _signup_scan_running:
        return
    _signup_scan_running = True
    try:
        added = chats = 0
        alt_w = _aw("راه جایگزین")
        shoro_w = _aw(AUTO_SHORO_TEXT[:30])
        async for d in client.iter_dialogs(limit=2000):
            ent = d.entity
            if (not d.is_user or getattr(ent, "bot", False) or getattr(ent, "is_self", False)
                    or d.id in FINDER_IGNORE_CHATS):
                continue
            uid = ent.id
            if uid == OWNER_ID or q1("SELECT 1 FROM admins WHERE user_id=?", (uid,)):
                continue
            try:
                hist = [m async for m in client.iter_messages(ent, limit=SIGNUP_SCAN_MSGS, reverse=True)]
            except FloodWaitError as e:
                await asyncio.sleep(min(e.seconds + 1, 120))
                continue
            except Exception as e:  # noqa
                log_err(f"signups scan {uid}: {e!r}")
                continue
            chats += 1
            alt_seen = False
            for i, m in enumerate(hist):
                if not m.out:
                    continue
                if alt_w in _aw(m.raw_text or ""):
                    alt_seen = True
                    continue
                if alt_seen or not _is_video_msg(m):
                    continue
                nxt = hist[i + 1] if i + 1 < len(hist) else None
                if nxt is not None and nxt.out and shoro_w in _aw(nxt.raw_text or ""):
                    continue  # ویدیوی «شروع» (آموزش)، نه تایید استخدام
                if signup_record(uid, int(m.date.timestamp())):
                    added += 1
                break
            await asyncio.sleep(0.4)
        total = q1("SELECT COUNT(*) n FROM signups")["n"]
        by_code = q1("SELECT COUNT(*) n FROM signups WHERE admin_id<>0")["n"]
        log.info("signups scan: chats=%s added=%s total=%s", chats, added, total)
        if bot is not None and added > 0:
            rows = qa("SELECT a.*, (SELECT COUNT(*) FROM signups s WHERE s.admin_id=a.user_id) su FROM admins a "
                      "WHERE su>0 ORDER BY su DESC, a.total_count DESC LIMIT 40")
            sep = "➖•➖•➖"
            lines = "\n".join(f"{i}. {link_list_name(a)} ›「 {a['su']} ثبت نام 」" for i, a in enumerate(rows, 1))
            txt = (f"<b>{sep}\n🪪 بررسی ثبت‌نام‌ها 🪪\n{sep}\n"
                   f"🔎 چت بررسی‌شده: {chats}\n"
                   f"➕ ثبت‌نام جدید: {added}\n"
                   f"🧾 کل «تایید استخدام»: {total}\n"
                   f"🪪 با کد ادمین: {by_code}\n{sep}\n</b>{lines}")
            try:
                await bot.send_message(OWNER_ID, txt[:4000], parse_mode=H)
            except Exception:  # noqa
                pass
    except Exception as e:  # noqa
        log.exception("signups scan failed")
        log_err(f"signups scan failed: {e!r}")
    finally:
        _signup_scan_running = False


STATS_BACKFILL_MSGS = 300   # از هر چت حداکثر چند پیام اخیر برای بازسازی خونده میشه
STATS_BACKFILL_TRIES = 3


_backfill_running = False


async def stats_backfill(client, bot=None) -> None:
    """هم‌زمان فقط یک اجرا؛ شکست‌ها توی stats_job خودکار دوباره تلاش میشن."""
    global _backfill_running
    if _backfill_running:
        return
    _backfill_running = True
    try:
        await _stats_backfill_impl(client, bot)
    finally:
        _backfill_running = False


async def _stats_backfill_impl(client, bot=None) -> None:
    """بازسازی آمار از ۶ صبحِ روز شروع تا همین الان از روی تاریخچه‌ی چت‌های اکانت شخصی (فقط اضافه میکنه؛ چیزی حذف یا تکراری نمیشه).
    «تایید استخدام» درجا پاک میشه، پس استخدام‌ها از روی متن «تبریک استخدام شما نهایی شد» شمرده میشن و
    کسایی که توی چتشون «راه جایگزین» نوشته شده از ثبت‌نام کم میشن (توی stats_compute)."""
    base = stats_baseline()
    if get_setting("stats_backfill_done") == base:
        return
    tries = get_int_setting("stats_backfill_tries") + 1
    set_setting("stats_backfill_tries", str(tries))
    since = stat_window(base)[0]
    st = {"chats": 0, "events": 0, "errors": 0}
    try:
        async for d in client.iter_dialogs(limit=1000):
            ent = d.entity
            if (not d.is_user or getattr(ent, "bot", False) or getattr(ent, "is_self", False)
                    or d.id in FINDER_IGNORE_CHATS or d.message is None or d.message.date.timestamp() < since):
                continue
            uid = ent.id
            if uid == OWNER_ID or q1("SELECT 1 FROM admins WHERE user_id=?", (uid,)):
                continue
            try:
                hist = [m async for m in client.iter_messages(ent, limit=STATS_BACKFILL_MSGS)]
            except FloodWaitError as e:
                await asyncio.sleep(min(e.seconds + 1, 120))
                st["errors"] += 1
                continue
            except Exception as e:  # noqa
                log_err(f"stats backfill {uid}: {e!r}")
                st["errors"] += 1
                continue
            hist.reverse()  # قدیمی -> جدید
            st["chats"] += 1
            is_contact = bool(getattr(ent, "contact", False) or getattr(ent, "mutual_contact", False))
            alt_flag = any(m.out and _aw("راه جایگزین") in _aw(m.raw_text or "") for m in hist)
            first = hist[0] if hist else None
            for m in hist:
                ts = int(m.date.timestamp())
                text = m.raw_text or ""
                if m.out:
                    # فقط برای بازسازیِ امروز: چون «تایید استخدام» پاک شده، استخدام = متن تبریک، منهای چت‌هایی که «راه جایگزین» توشون نوشته شده
                    if ts >= since and not alt_flag and _aw(CONGRATS_PHRASE) in _aw(text):
                        stat_log("signup", uid, once_ever=True, ts=ts)
                    continue
                if ts < since:
                    continue
                code_admin = _stat_code_admin(uid, text, not is_contact)
                if code_admin is not None and not _stat_already_hired(uid, ts):
                    stat_log("code", uid, code_admin, once_ever=True, ts=ts)
                if (m is first and len(hist) < STATS_BACKFILL_MSGS and not is_contact
                        and q1("SELECT 1 FROM stat_events WHERE user_id=? AND kind IN ('lead','old')", (uid,)) is None):
                    stat_log("lead", uid, code_admin, once_ever=True, ts=ts)  # اولین پیامِ یک چتِ تازه داخل بازه
                _outs = sum(1 for x in hist if x.out and x.date < m.date)
                stat_words(uid, text, ts=ts, alt_hint=alt_flag, nine_hint=_outs >= 9)  # «شروع» بعد از ۹ پیامِ ارسالی
            await asyncio.sleep(0.4)
        set_setting("stats_backfill_done", base)
        log.info("stats backfill: %s", st)
        if bot is not None:
            try:
                await bot.send_message(OWNER_ID, fb(f"✅ آمار از ساعت 6 صبح تا الان از روی چت‌ها بازیابی شد ({st['chats']} چت بررسی شد)."), parse_mode=H)
            except Exception:  # noqa
                pass
    except Exception as e:  # noqa
        log.exception("stats backfill failed")
        log_err(f"stats backfill failed (try {tries}): {e!r}")
        if bot is not None:
            try:
                await bot.send_message(OWNER_ID, fb(f"❌ بازیابی آمار از چت‌ها خطا داد: {e}"), parse_mode=H)
            except Exception:  # noqa
                pass
        if tries >= STATS_BACKFILL_TRIES:
            set_setting("stats_backfill_done", base)  # بعد از چند بار شکست، گزارش‌ها منتظر نمیمونن


async def stats_deliver_partial(bot, day: str) -> None:
    """گزارش لحظه‌ایِ بازه‌ی در حال گذر (از ۶ صبح تا همین الان) به Saved Messages؛ گزارش نهایی ۶:۰۵ جاش رو میگیره."""
    if not await saved_ready():
        raise RuntimeError("سشن اکانت شخصی در دسترس نیست")
    client = SESSION_CLIENT
    data = await asyncio.to_thread(stats_compute, day, int(time.time()))
    text = stats_text(day, data)
    try:
        old = [int(x) for x in json.loads(get_setting("stats_saved_ids") or "[]")]
    except (ValueError, TypeError):
        old = []
    m1 = None
    for _ in range(3):
        try:
            m1 = await client.send_message("me", text, parse_mode="html")
            break
        except FloodWaitError as e:
            await asyncio.sleep(e.seconds + 1)
    if m1 is None:
        raise RuntimeError("ارسال گزارش لحظه‌ای به Saved Messages انجام نشد")
    set_setting("stats_saved_ids", json.dumps([m1.id]))
    set_setting("stats_partial_sent", day)
    if old:
        try:
            await client.delete_messages("me", old)
        except Exception as e:  # noqa
            log_err(f"stats partial old delete: {e!r}")


async def stats_job(context: ContextTypes.DEFAULT_TYPE):
    """هر دقیقه چک میشه: هر بازه‌ی ۶ صبح تا ۶ صبح، ۵ دقیقه بعد از تموم شدنش (6:05) محاسبه، برای همیشه ذخیره و ارسال میشه."""
    global _stats_busy
    if _stats_busy:
        return
    _stats_busy = True
    try:
        stats_v2_migrate()
        base = stats_baseline()
        if get_setting("stats_backfill_done") != base:
            # بازسازی از ۶ صبحِ روز شروع هنوز تموم نشده؛ قبلش گزارش ساخته نمیشه. اگه قبلاً شکست خورده، خودکار دوباره تلاش میشه
            # (بعد از STATS_BACKFILL_TRIES شکست، پرچم تموم‌شدن زده میشه و گزارش‌ها ادامه پیدا میکنن)
            if (SESSION_CLIENT is not None and not _backfill_running
                    and time.time() - get_int_setting("stats_backfill_retry_ts") >= STATS_RETRY):
                set_setting("stats_backfill_retry_ts", str(int(time.time())))
                await stats_backfill(SESSION_CLIENT, context.bot)
            if get_setting("stats_backfill_done") != base:
                return
        now = int(time.time())
        # گزارش لحظه‌ایِ اولِ بازه‌ی شروع (فقط یک بار، فقط اگه بازه هنوز تموم نشده باشه)
        if get_setting("stats_partial_sent") != base:
            if now >= stat_window(base)[1] + STATS_DELAY:
                set_setting("stats_partial_sent", base)  # بازه تموم شده؛ مستقیم گزارش نهایی میره
            elif now - get_int_setting("stats_partial_retry") >= STATS_RETRY:
                try:
                    await stats_deliver_partial(context.bot, base)
                except Exception as e:  # noqa
                    log_err(f"stats partial failed: {e!r}")
                    set_setting("stats_partial_retry", str(int(time.time())))
        last = get_setting("stats_last_day")
        d = datetime.strptime(last, "%Y-%m-%d") + timedelta(days=1) if (last and last >= base) \
            else datetime.strptime(base, "%Y-%m-%d")
        d = max(d, datetime.strptime(base, "%Y-%m-%d"))
        while stat_window(d.strftime("%Y-%m-%d"))[1] + STATS_DELAY <= now:  # بازه تموم شده و ۵ دقیقه گذشته (6:05)
            key = d.strftime("%Y-%m-%d")
            data = await asyncio.to_thread(stats_compute, key)
            ex("INSERT OR REPLACE INTO daily_stats(day,data,created_at) VALUES(?,?,?)",
               (key, json.dumps(data, ensure_ascii=False), int(time.time())))
            set_setting("stats_last_day", key)
            d += timedelta(days=1)
        last = get_setting("stats_last_day")
        if last and last >= base and get_setting("stats_sent_day") != last and \
                time.time() - get_int_setting("stats_retry_ts") >= STATS_RETRY:
            try:
                await stats_deliver(context.bot, last)
            except Exception as e:  # noqa
                log.exception("stats deliver failed")
                log_err(f"stats deliver failed: {e!r}")
                set_setting("stats_retry_ts", str(int(time.time())))
                if get_setting("stats_fail_day") != last:
                    set_setting("stats_fail_day", last)
                    await safe_send_hold(context.bot, OWNER_ID,
                                         f"❌ ارسال آمار سیستم به Saved Messages ناموفق بود ❌\n\n{e}\n\n"
                                         "آمار ذخیره شده و چند دقیقه دیگه دوباره تلاش میشه.", html_mode=False)
    except Exception as e:  # noqa
        log.exception("stats job failed")
        log_err(f"stats job failed: {e!r}")
    finally:
        _stats_busy = False


RESTORE_MAX_BYTES = 20 * 1024 * 1024        # سقف دانلود فایل توسط ربات (محدودیت Bot API)
RESTORE_MAX_UNPACKED = 600 * 1024 * 1024
RESTORE_TABLES = ("admins", "hires", "commissions", "cards", "settings")


def restore_prepare(raw: bytes, filename: str) -> dict:
    """فایل بکاپ رو توی پوشه‌ی موقت میذاره و بررسی میکنه؛ هیچ‌چیز از دیتابیس زنده رو عوض نمیکنه."""
    name = (filename or "").lower()
    if ".part" in name:
        raise ValueError("این فایل یکی از تکه‌های بکاپه. تکه‌ها رو کنار هم بذار، با gunzip باز کن و فایل .db رو بفرست.")
    tmpdir = tempfile.mkdtemp(prefix=BACKUP_PREFIX + "rs_")
    try:
        path = os.path.join(tmpdir, "restore.db")
        if name.endswith(".gz"):
            try:
                total = 0
                with gzip.open(io.BytesIO(raw), "rb") as gz, open(path, "wb") as out:
                    for chunk in iter(lambda: gz.read(1024 * 1024), b""):
                        total += len(chunk)
                        if total > RESTORE_MAX_UNPACKED:
                            raise ValueError("فایل بعد از باز شدن خیلی بزرگه.")
                        out.write(chunk)
            except (OSError, EOFError, zlib.error):
                raise ValueError("فایل فشرده خراب یا ناقصه.")
        else:
            with open(path, "wb") as out:
                out.write(raw)
        with open(path, "rb") as f:
            if f.read(16) != b"SQLite format 3\x00":
                raise ValueError("این فایل دیتابیس معتبر نیست. فایل بکاپ (.db یا .db.gz) رو بفرست.")
        chk = sqlite3.connect(f"file:{path}?mode=ro", uri=True)
        try:
            if chk.execute("PRAGMA integrity_check").fetchone()[0] != "ok":
                raise ValueError("فایل خرابه (integrity_check) و قابل بازیابی نیست.")
            tables = {r[0] for r in chk.execute("SELECT name FROM sqlite_master WHERE type='table'")}
            if any(t not in tables for t in RESTORE_TABLES):
                raise ValueError("این فایل بکاپ ربات جذبان نیست.")
            info = {t: chk.execute(f"SELECT COUNT(*) FROM {t}").fetchone()[0]
                    for t in ("admins", "hires", "commissions", "cards")}
        except sqlite3.DatabaseError:
            raise ValueError("فایل دیتابیس قابل خوندن نیست.")
        finally:
            chk.close()
        info["path"] = path
        info["tmpdir"] = tmpdir
        return info
    except Exception:
        _safe_rmtree(tmpdir)
        raise


def restore_apply(db_file: str) -> dict:
    """جایگزینی کامل دیتابیس زنده با فایل بررسی‌شده. قبلش از دیتابیس فعلی یه نسخه کنار فایل اصلی ذخیره میشه.
    فلگ‌های یک‌بار‌مصرفِ ریست تست رو توی دیتابیس بازیابی‌شده روشن میکنه تا بعد از ری‌استارت چیزی پاک نشه."""
    safety = f"{DB_PATH}.pre_restore_{int(time.time())}.bak"
    with _lock:
        dst = sqlite3.connect(safety)
        try:
            CONN.backup(dst)
        finally:
            dst.close()
        src = sqlite3.connect(f"file:{db_file}?mode=ro", uri=True)
        try:
            src.backup(CONN)
        finally:
            src.close()
        CONN.executescript(SCHEMA)
        _migrate()
        CONN.execute("PRAGMA journal_mode=WAL")
        for k in (RESET_FLAG, PURGE_FLAG, "levels_v1"):
            CONN.execute("INSERT INTO settings(key,value) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                         (k, "1"))
        counts = _table_counts(CONN)
    return {"safety": safety, "counts": counts}


async def _file_ok(bot, fid: str) -> bool:
    """False فقط وقتی تلگرام صریحاً بگه شناسه‌ی فایل با این ربات معتبر نیست."""
    try:
        await bot.get_file(fid)
        return True
    except BadRequest as e:
        return "too big" in str(e).lower()  # فایل بالای ۲۰ مگ وجود داره ولی دانلودش برای ربات مجاز نیست
    except Exception:  # noqa
        return True  # خطای شبکه و مشابه: الکی هشدار نده


async def media_problems(bot) -> list:
    """ویدیوها و عکس‌هایی که باید دوباره ثبت بشن (بعد از بازیابی بکاپ، تغییر هاست یا تغییر ربات)."""
    out = []
    fid = get_setting("video_file_id")
    if get_setting("video_enabled") == "1" and not fid:
        out.append("🎬 ویدیوی آموزشی روشنه ولی ثبت نشده\n   ← تنظیمات ← ویدیوی آموزشی ← ثبت یا تعویض ویدیو")
    elif fid and not await _file_ok(bot, fid):
        out.append("🎬 ویدیوی آموزشی با این ربات باز نمیشه\n   ← تنظیمات ← ویدیوی آموزشی ← ثبت یا تعویض ویدیو")
    r = q1("SELECT data FROM auto_media WHERE key='video'")
    if get_setting("auto_vid") == "1" and not (r and r["data"]) and (await saved_pair())[0] is None:
        out.append("🤖 ویدیوی ارسال خودکار ثبت نشده\n   ← تنظیمات ← تنظیمات پیشرفته ← ارسال خودکار ← ویرایش ← "
                   "ثبت یا تعویض ویدیو شروع (اگه دکمه‌ش نیست اول «نمایش دکمه ویدیو»)")
    for _code, (key, title) in PH_ITEMS.items():
        f = get_setting(key)
        if f and not await _file_ok(bot, f):
            out.append(f"🖼️ {title} با این ربات باز نمیشه؛ دوباره ثبتش کن (تنظیمات)")
    return out


async def media_check_job(context: ContextTypes.DEFAULT_TYPE):
    """بعد از هر روشن شدن: اگه ویدیو یا عکسی نبود، یک بار به کارفرما خبر میده (تکراری نمیفرسته)."""
    try:
        probs = await media_problems(context.bot)
        sig = hashlib.sha256("\n".join(probs).encode()).hexdigest()[:16] if probs else ""
        if sig != get_setting("media_warn_sig"):
            set_setting("media_warn_sig", sig)
            if probs:
                await context.bot.send_message(
                    OWNER_ID, "⚠️ این موارد باید دوباره ثبت بشن ⚠️\n\n" + "\n\n".join(probs))
    except Exception as e:  # noqa
        log_err(f"media check: {e!r}")


async def owner_cb(update: Update, context, data: str):
    q = update.callback_query
    chat_id = update.effective_chat.id
    _CUR_KEY.set(data)  # بخش فعلی؛ اموجی نگه‌دارنده از روی همین انتخاب میشه

    if data == "o:noop":
        return None  # دکمه شماره صفحه: هیچ کاری نمی‌کند

    if data == CHEAT_NOTICE_CB:  # «باشه» زیر اعلان ارسال تقلب: پیام پاک میشه
        try:
            ex("DELETE FROM holds WHERE chat_id=? AND message_id=?", (chat_id, q.message.message_id))
            await q.message.delete()
        except TelegramError:
            pass
        return None

    if data == "o:menu":
        clear_state(OWNER_ID)
        await close_glass(update, context)
        return None
    if data == "o:clm":
        clear_state(OWNER_ID)
        await show(update, context, fb(OWNER_CLEAN_TEXT),
                   KB(B("🧹 پاکسازی 🧹", "o:cln", style="danger"), BACK("o:menu")), html_mode=True)
        return None
    if data == "o:cln":
        clear_state(OWNER_ID)
        await clean_texts(context.bot, OWNER_ID, keep_hold=True)
        await send_owner_menu(context, update.effective_chat.id, show_kb=True)
        return None

    # ----- تست اولین ورود ادمین -----
    if data == "o:go":
        if get_setting("owner_go_btn") != "1":
            return "این دکمه پاک شده."
        clear_state(OWNER_ID)
        _preview.pop("code", None)  # هر تست یه کد آزاد تازه نشون میده
        preview_admin()
        drop_contents(context.bot, OWNER_ID)
        await hide_reply_keyboard(context.bot, chat_id, OWNER_ID)
        await send_welcome(context, chat_id, preview_admin())
        return None
    if data == "o:rmgo":
        set_setting("owner_go_btn", "0")
        audit(OWNER_ID, "owner_go_btn_removed")
        await show(update, context, settings_text("✅ دکمه راه‌اندازی از منوی اصلی پاک شد."),
                   settings_kb(), html_mode=True)
        await send_owner_menu(context, chat_id, show_kb=True)  # کیبورد منو بدون دکمه‌ی راه‌اندازی تازه میشه
        return None

    # ----- ارسال خودکار -----
    if data == "o:au":
        clear_state(OWNER_ID)
        text, kb = auto_menu()
        await show(update, context, text, kb, html_mode=True)
        return None
    if data.startswith("o:au:t:"):
        key = data[7:]
        if key in AUTO_FLAGS:
            set_setting(key, "0" if get_setting(key) == "1" else "1")
        text, kb = auto_menu()
        await show(update, context, text, kb, html_mode=True)
        return None
    if data == "o:au:ed":
        clear_state(OWNER_ID)
        text, kb = auto_edit_menu()
        await show(update, context, text, kb, html_mode=True)
        return None
    if data == "o:au:e9":
        set_state(OWNER_ID, "au9", {"items": []})
        await show(update, context,
                   fbox("ویرایش ۹ پیام ✏️ EDIT 9 MESSAGES",
                        "متن‌ها رو به ترتیب بفرست؛ هر پیام یک متن\n(بولد و لینک حفظ میشه)\nوقتی همه رو فرستادی\n"
                        "دکمه‌ی «تمام شد» رو بزن\nبا ثبت، متن‌های قبلی کامل جایگزین میشن."),
                   KB(BACK("o:au:ed")), html_mode=True)
        return None
    if data == "o:au:e9ok":
        st_, d_ = get_state(OWNER_ID)
        items = list(d_.get("items") or []) if st_ == "au9" else []
        if not items:
            return "هنوز متنی نفرستادی."
        set_setting("auto_msgs", json.dumps(items, ensure_ascii=False))
        clear_state(OWNER_ID)
        text, kb = auto_menu()
        await show(update, context, f"✅ {len(items)} متن ذخیره شد.\n\n" + text, kb, html_mode=True)
        return None
    if data == "o:au:er":
        set_state(OWNER_ID, "aur")
        await show(update, context,
                   fbox("✏️ ویرایش متن ثبت نام ✏️",
                        "عکس رو همراه کپشنش بفرست\n(کپشن تا ۱۰۲۴ حرف؛ بولد و لینک\nحفظ میشه). اگه فقط متن بفرستی،\n"
                        "عکس قبلی سر جاش می‌مونه."),
                   KB(BACK("o:au:ed")), html_mode=True)
        return None
    if data == "o:au:ea":
        set_state(OWNER_ID, "aua")
        await show(update, context,
                   fbox("✏️ ویرایش راه جایگزین ✏️",
                        "متنی که بعد از «🔹 راه جایگزین شما:»\nفرستاده میشه رو بفرست\n(بولد و لینک حفظ میشه)."),
                   KB(BACK("o:au:ed")), html_mode=True)
        return None
    if data == "o:au:ev":
        set_state(OWNER_ID, "auv1")
        await show(update, context,
                   fbox("📤 ویدیو شروع 📤",
                        "ویدیو رو بفرست (حداکثر ۲۰ مگابایت).\nمتنش جدا و بلافاصله بعد از ویدیو فرستاده میشه."),
                   KB(BACK("o:au:ed")), html_mode=True)
        return None
    if data == "o:au:vnc":
        set_setting("auto_vid_html", "")
        clear_state(OWNER_ID)
        text, kb = auto_menu()
        await show(update, context, "✅ ویدیو بدون متن ذخیره شد.\n\n" + text, kb, html_mode=True)
        return None
    if data in ("o:au:dv", "o:au:sv"):
        set_setting("auto_vid_btn", "0" if data == "o:au:dv" else "1")
        text, kb = auto_edit_menu()
        await show(update, context, text, kb, html_mode=True)
        return None

    # ----- ریست دیتای یک ادمین -----
    if data == "o:rsd":
        set_state(OWNER_ID, "rsd")
        await show(update, context,
                   f"<b>{SEP10}\n🧹 ریست دیتای ادمین 🧹 ADMIN RESET\n{SEP10}</b>\n"
                   "یوزرنیم یا کد ادمینی که میخوای دیتاش پاک بشه رو بفرست (یا یک پیام ازش فوروارد کن)\n"
                   f"<b>{SEP10}</b>",
                   KB(BACK("o:tsm")), html_mode=True)
        return None
    if data == "o:rsd:y":
        return "این دکمه قدیمیه؛ دوباره از تنظیمات پیشرفته شروع کن."
    if data.startswith("o:rsd:y:"):
        try:
            tid = int(data[8:])
        except ValueError:
            return None
        a = get_admin(tid)
        if a is None:
            return "ادمین پیدا نشد."
        res = reset_one_admin_data(tid)
        if res is None:
            await show(update, context, adv_text("❌ بکاپ ساخته نشد؛ چیزی پاک نشد."),
                       advanced_settings_kb(), html_mode=True)
            return None
        counts, _bk = res
        await release_stale_requests(context.bot)  # درخواست‌های واریزِ پین‌شده‌ی این ادمین از پین درمیان
        await show(update, context,
                   adv_text(f"✅ دیتای ادمین کد「{a['code']}」صفر شد.\n"
                            f"🧲 جذب‌ها:「{counts['hires']}」 💰 پورسانت‌ها:「{counts['commissions']}」 💳 کارت‌ها:「{counts['cards']}」"),
                   advanced_settings_kb(), html_mode=True)
        return None

    # ----- گزارش جذب -----
    if data.startswith("o:rep:"):
        _, _, mode, page = data.split(":")
        await owner_report(update, context, mode, int(page))
        return None

    # ----- مدیریت مالی -----
    if data == "o:fin":
        clear_state(OWNER_ID)
        await show(update, context, fb("💰 مدیریت مالی 💰"),
                   KB(B("✅ واریزی های انجام شده ✅", "o:fd:0", style="success"),
                      B("☑️ واریزی های انجام نشده ☑️", "o:fu:0", style="danger"),
                      BACK("o:menu")))
        return None
    if data.startswith("o:fd:"):
        page = int(data[5:])
        total = q1("SELECT COUNT(*) n FROM commissions WHERE status='paid'")["n"]
        pages = max((total + PAGE_SIZE - 1) // PAGE_SIZE, 1)
        page = min(max(page, 0), pages - 1)
        rows = qa("SELECT * FROM commissions WHERE status='paid' ORDER BY paid_at DESC LIMIT ? OFFSET ?",
                  (PAGE_SIZE, page * PAGE_SIZE))
        if not rows:
            await show(update, context, fb("هنوز واریزی انجام‌شده‌ای ثبت نشده."), KB(BACK("o:fin")))
            return None
        btns = [B(f"💰 واریز {fmt_toman_fa(c['paid_amount'] or c['amount'])} - {jdate_short(c['paid_at'])} 💰",
                  f"o:fr:{c['id']}", style=cyc(i, "success", "primary", "danger")) for i, c in enumerate(rows)]
        nav = nav_row(lambda p: f"o:fd:{p}", page, pages, plain=True)
        if nav:
            btns.append(nav)
        btns.append(B(BTN_BACK, "o:fin"))
        btns.append(MAIN("o:menu"))
        await show(update, context, fbox("✅ واریزی های انجام شده ✅", "برای دیدن فیش، روی هر مورد بزن 👇"), KB(*btns))
        return None
    if data.startswith("o:fr:"):
        c = q1("SELECT * FROM commissions WHERE id=? AND status='paid'", (int(data[5:]),))
        if c is None:
            return "این مورد پیدا نشد."
        a = get_admin(c["admin_id"])
        cap = owner_receipt_caption(a, c)
        await send_receipt_to(context.bot, chat_id, c, cap, html_mode=True)
        return None
    if data.startswith("o:fu:"):
        clear_state(OWNER_ID)
        page = int(data[5:])
        total = q1("SELECT COUNT(*) n FROM commissions WHERE status='requested'")["n"]
        pages = max((total + PAGE_SIZE - 1) // PAGE_SIZE, 1)
        page = min(max(page, 0), pages - 1)
        rows = qa("SELECT * FROM commissions WHERE status='requested' ORDER BY requested_at DESC LIMIT ? OFFSET ?",
                  (PAGE_SIZE, page * PAGE_SIZE))
        if not rows:
            await show(update, context, fb("درخواست واریز پرداخت‌نشده‌ای وجود نداره."), KB(BACK("o:fin")))
            return None
        btns = [B(f"💳 {card_mask(c['card_number'])}", f"o:fi:{c['id']}:{page}", style=cyc(i, "danger", "primary", "success"))
                for i, c in enumerate(rows)]
        nav = nav_row(lambda p: f"o:fu:{p}", page, pages, plain=True)
        if nav:
            btns.append(nav)
        btns.append(B(BTN_BACK, "o:fin"))
        btns.append(MAIN("o:menu"))
        await show(update, context, fbox("☑️ واریزی های انجام نشده ☑️", "برای دیدن جزئیات، روی هر کارت بزن 👇"), KB(*btns))
        return None
    if data.startswith("o:fi:"):
        parts = data.split(":")
        fpage = int(parts[3]) if len(parts) > 3 else 0
        clear_state(OWNER_ID)
        c = q1("SELECT * FROM commissions WHERE id=? AND status='requested'", (int(parts[2]),))
        if c is None:
            return "این درخواست دیگه در لیست پرداخت‌نشده‌ها نیست."
        a = get_admin(c["admin_id"])
        text = fbox("⏳ درخواست واریز پورسانت",
                f"💳 شماره کارت: <code>{c['card_number']}</code>\n\n"
                f"👤 نام صاحب حساب: {FSI}{html.escape(c['card_holder'])}{PDI}\n\n"
                f"🔗 اکانت: {link(a)}\n\n"
                f"📅 تاریخ درخواست: {jdate_plain(c['requested_at'])}\n\n"
                f"🔢 کد اختصاصی:「{a['code']}」\n"
                f"💰 مبلغ:「{fmt_en(c['amount'])}」تومان")
        kb = KB(B("پرداخت", copy=c["card_number"], style="success"),
                B("📩 ارسال فیش واریز 📩", f"o:fs:{c['id']}:{fpage}", style="primary"),
                BACK(f"o:fu:{fpage}"), MAIN("o:menu"))
        await show(update, context, text, kb)
        return None
    if data.startswith("o:fs:"):
        parts = data.split(":")
        fpage = int(parts[3]) if len(parts) > 3 else 0
        c = q1("SELECT * FROM commissions WHERE id=? AND status='requested'", (int(parts[2]),))
        if c is None:
            return "این درخواست قبلا نهایی شده."
        set_state(OWNER_ID, "receipt", {"cid": c["id"]})
        _rq = track_get(OWNER_ID, f"req:{c['id']}")
        _qm = update.callback_query.message if update.callback_query else None
        _on_req = _rq is not None and _qm is not None and _rq["message_id"] == _qm.message_id
        # دکمه روی خود درخواستِ پین‌شده زده شده: اون پیام دست‌نخورده می‌مونه و صفحه‌ی فیش پیام جدید میشه
        _pmsg = await show(update, context, fb(f"{OWNER_NAME} عزیز، لطفا فیش واریزی رو ارسال کن!"),
                           KB(BACK(f"o:fi:{c['id']}:{fpage}"), MAIN("o:menu")), html_mode=True, fresh=_on_req)
        _pm = _pmsg.message_id if _pmsg is not None else (_qm.message_id if _qm is not None else None)
        set_state(OWNER_ID, "receipt", {"cid": c["id"], "pm": _pm})
        return None

    # ----- پیام همگانی -----
    if data == "o:bc":
        set_state(OWNER_ID, "bc")
        await show(update, context,
                   fb(f"{OWNER_NAME} عزیز، لطفا پیامی که میخوای واسه تمام ادمین های ربات ارسال بشه رو ارسال کن!"),
                   KB(BACK("o:menu")), html_mode=True)
        return None
    if data == "o:bcs":
        st, d = get_state(OWNER_ID)
        if st != "bc_confirm":
            return "پیامی برای ارسال آماده نیست."
        clear_state(OWNER_ID)  # جلوگیری از ارسال دوباره
        ids = [r["user_id"] for r in qa("SELECT user_id FROM admins WHERE blocked=0")]
        status_msg = await show(update, context, "⏳", None, html_mode=False)
        ok = fail = 0
        for uid in ids:
            try:
                await deliver_broadcast(context.bot, uid, d)
                ok += 1
            except RetryAfter as e:
                await asyncio.sleep(e.retry_after + 1)
                try:
                    await deliver_broadcast(context.bot, uid, d)
                    ok += 1
                except Exception:  # noqa
                    fail += 1
            except Exception as e:  # noqa
                fail += 1
                if isinstance(e, Forbidden):
                    mark_blocked(uid)
                log_err(f"broadcast to {uid}: {e!r}")
        if d.get("message_id") and not (d.get("is_text") and len(d.get("text", "")) < 3800):
            bg(_safe_delete(context.bot, d["chat_id"], d["message_id"]))  # پیام اصلیِ مدیر بعد از ارسال پاک میشه
            await asyncio.sleep(0.05)
        try:
            if status_msg is not None:
                await context.bot.delete_message(status_msg.chat_id, status_msg.message_id)
            elif q is not None and q.message:
                await q.message.delete()
        except TelegramError:
            pass
        await send(context.bot, chat_id,
                   fbox("✅ ارسال پیام همگانی انجام شد ✅", f"🔹 موفق:「{ok}」\n🔷 ناموفق:「{fail}」"),
                   KB(BACK("o:menu")), html_mode=True)
        return None

    # ----- جست‌وجوی ادمین -----
    if data == "o:sr":
        set_state(OWNER_ID, "search")
        await show(update, context, fb("لطفا یوزرنیم کاربر رو ارسال کن یا یک پیام ازش برام فوروارد کن!"),
                   KB(BACK("o:menu")), html_mode=True)
        return None
    if data.startswith("o:smg:"):
        try:
            uid = int(data[6:])
        except ValueError:
            return None
        set_state(OWNER_ID, "umsg", {"uid": uid})
        await show(update, context, fb("معراج عزیز\nپیام مد نظرت رو ارسال کن:⚡️"),
                   KB(BACK("o:menu")), html_mode=True)
        return None
    if data.startswith("o:chg:"):
        try:
            uid = int(data[6:])
        except ValueError:
            return None
        if get_admin(uid) is None:
            return "ادمین پیدا نشد."
        set_state(OWNER_ID, "chg_p", {"uid": uid})
        await show(update, context, fb("لطفا عدد جذب این دوره رو ارسال کنید!"), KB(BACK("o:menu")), html_mode=True)
        return None
    if data.startswith("o:chy:"):
        try:
            uid = int(data[6:])
        except ValueError:
            return None
        st_c, d_c = get_state(OWNER_ID)
        if st_c != "chg_c" or d_c.get("uid") != uid:
            return "این درخواست منقضی شده؛ دوباره از جستجوی ادمین بزن."
        a = get_admin(uid)
        if a is None:
            clear_state(OWNER_ID)
            return "ادمین پیدا نشد."
        p_new, t_new = int(d_c["p"]), int(d_c["t"])
        if p_new > a["cur_target"]:
            return f"عدد جذب این دوره نباید از {a['cur_target']} بیشتر باشه."
        clear_state(OWNER_ID)
        op, ot = a["period_count"], a["total_count"]
        n = max(p_new - op, 0)
        if n > 0:
            # هر جذبِ اضافه مثل یک جذب واقعی ثبت میشه: نوتیف برای ادمین و برای مدیر، یکی‌یکی
            base_id = int(time.time() * 1000) * 100
            for i in range(n):
                res = record_hire(-(base_id + i), "ثبت دستی", a["code"])
                if res is not None:
                    await notify_hire(context.bot, res)
                await asyncio.sleep(0.3)
            a2 = get_admin(uid)
            if a2 is not None and a2["total_count"] != t_new:
                ex("UPDATE admins SET total_count=? WHERE user_id=?", (t_new, uid))
        else:
            ex("UPDATE admins SET period_count=?,total_count=? WHERE user_id=?", (p_new, t_new, uid))
        audit(OWNER_ID, "change_hires", f"{uid}: {op}/{ot} -> {p_new}/{t_new}")
        a3 = get_admin(uid)
        await show(update, context, search_report_text(a3), search_kb(a3))
        return None
    if data.startswith("o:sts:"):
        clear_state(OWNER_ID)
        try:
            page = int(data[6:])
        except ValueError:
            page = 0
        text, kb = stats_list_menu(page)
        await show(update, context, text, kb, html_mode=True)
        return None
    if data == "o:stl":
        _day = stat_day()
        if _day < stats_baseline():
            return "هنوز آماری ذخیره نشده."
        if get_setting("stats_backfill_done") != stats_baseline():
            if SESSION_CLIENT is None:
                return "سشن اکانت شخصی وصل نیست؛ بازیابی آمار ممکن نیست."
            await stats_backfill(SESSION_CLIENT, context.bot)  # بازیابی از ۶ صبح همین الان انجام میشه
        # آمار ۶ صبح تا همین الان (بازه‌ی در حال گذر)
        _t = stats_text(_day, await asyncio.to_thread(stats_compute, _day, int(time.time())))
        _m = await send(context.bot, chat_id, _t, None, html_mode=True)
        if _m is not None:
            schedule_delete(_m.chat_id, _m.message_id, 30)  # ۳۰ ثانیه بعد خودش پاک میشه
        return None
    if data == "o:stm":
        set_state(OWNER_ID, "stdate")
        await show(update, context, fbox(None, "تاریخ روزی که می‌خوای گزارشش رو ببینی بفرست\nمثلا: 1405/07/13 یا 13 مهر 1405"),
                   KB(BACK("o:sts:0")), html_mode=True)
        return None
    if data.startswith("o:std:"):
        r = stats_row(data[6:])
        if r is None:
            return "برای این تاریخ آمار ثبت نشده."
        await show(update, context, stats_row_text(r), KB(BACK("o:sts:0")))
        return None
    if data.startswith("o:ash:"):
        try:
            uid = int(data[6:])
        except ValueError:
            return None
        a = get_admin(uid)
        if a is None:
            return "ادمین پیدا نشد."
        ex("DELETE FROM shield_auto WHERE admin_id=?", (uid,))  # انتخاب دستی مدیر؛ پایان دوره خاموشش نمیکنه
        if admin_shield_on(uid):
            ex("DELETE FROM shield_admins WHERE admin_id=?", (uid,))
        else:
            ex("INSERT OR IGNORE INTO shield_admins(admin_id) VALUES(?)", (uid,))
        _perf = q is not None and q.message is not None and perf_text_get(q.message.chat_id, q.message.message_id) is not None
        if _perf and await edit_in_place(q, search_report_text(a), search_kb(a, perf=True)):
            return None
        await show(update, context, search_report_text(a), search_kb(a, perf=_perf))
        return None
    if data.startswith("o:perf:"):
        # دکمه‌ی «پنل عملکرد» زیر پیام جذب جدید: همون گزارشِ جستجوی ادمین (با دکمه‌ی سپر) همونجا باز میشه؛ پیام جدید نمیاد
        try:
            uid = int(data[7:])
        except ValueError:
            return None
        a = get_admin(uid)
        if a is None:
            return "ادمین پیدا نشد."
        text = search_report_text(a)
        if q is not None and q.message:
            try:
                perf_text_save(q.message.chat_id, q.message.message_id, q.message.text_html or "")
            except Exception as e:  # noqa
                log_err(f"perf save orig {uid}: {e!r}")
            if await edit_in_place(q, text, search_kb(a, perf=True)):
                return None
        await show(update, context, text, search_kb(a))
        return None
    if data.startswith("o:pbk:"):
        # بازگشت از پنل عملکرد: همون متن نوتیف جذب (با دکمه‌ی «پنل عملکرد») برمیگرده؛ هیچ چیز پاک نمیشه
        try:
            uid = int(data[6:])
        except ValueError:
            return None
        if q is None or q.message is None:
            return None
        orig = perf_text_get(q.message.chat_id, q.message.message_id)
        if not orig:
            a = get_admin(uid)
            if a is None:
                await show(update, context, fb("منوی اصلی"), None)
                return None
            orig = owner_hire_text(a, a["period_count"], a["total_count"])  # پشتیبان: متن ذخیره‌شده نبود
        kb = KB(B("🧬 پنل عملکرد 🧬", f"o:perf:{uid}"))
        if not await edit_in_place(q, orig, kb):
            await show(update, context, orig, kb)
        return None
    if data.startswith("o:srr:"):
        rows = qa("SELECT * FROM commissions WHERE admin_id=? AND status='paid' ORDER BY paid_at DESC",
                  (int(data[6:]),))
        if not rows:
            return "فیشی ثبت نشده."
        async with loading(context.bot, chat_id):
            for c in rows:
                a = get_admin(c["admin_id"])
                await send_receipt_to(context.bot, chat_id, c, owner_receipt_caption(a, c), html_mode=True)
        return None

    # ----- تنظیمات -----
    if data == "o:set":
        clear_state(OWNER_ID)
        # تعداد اعضا (فقط یک پیام) خودش داخل show() قبل از منو میاد
        await show(update, context, settings_text(), settings_kb(), html_mode=True)
        return None
    if data == "o:adv":
        clear_state(OWNER_ID)
        await show(update, context, adv_text(), advanced_settings_kb(), html_mode=True)
        return None
    if data == "o:ck" or data.startswith("o:ck:"):
        return await cheat_owner_cb(update, context, data)
    if data == "o:tsm":
        clear_state(OWNER_ID)
        await show(update, context, test_menu_text(), test_menu_kb(), html_mode=True)
        return None
    if data.startswith("o:bki:"):
        try:
            sec = int(data[6:])
        except ValueError:
            sec = 0
        if sec in {x for x, _ in BACKUP_CHOICES}:
            set_setting("backup_every", str(sec))
            # زمان آخرین بکاپ دست‌نخورده می‌مونه؛ اگه فاصله‌ی جدید گذشته باشه، بکاپ بعدی تا یک دقیقه‌ی دیگه گرفته میشه
        label = dict(BACKUP_CHOICES).get(backup_every(), "")
        await show(update, context,
                   adv_text(f"🗄️ بکاپ خودکار: هر {label}"),
                   advanced_settings_kb(bk_open=True), html_mode=True)
        return None
    if data in ("o:phlevel", "o:phactivity"):
        data = "o:ph:1p" if data == "o:phlevel" else "o:ph:1a"  # دکمه‌های قدیمی هم کار میکنن
    if data.startswith("o:ph:"):
        item = PH_ITEMS.get(data[5:])
        if item is None:
            return None
        set_state(OWNER_ID, "photo_set", {"code": data[5:]})
        await show(update, context, fb(f"{item[1]} رو همینجا به‌صورت عکس بفرست."), KB(BACK("o:set")), html_mode=True)
        return None
    if data in ("o:ac", "o:actg"):
        clear_state(OWNER_ID)
        if data == "o:actg":
            set_setting("ac_on", "0" if ac_enabled() else "1")
        text, kb = ac_page()
        await show(update, context, text, kb)
        return None
    if data == "o:acl":
        clear_state(OWNER_ID)
        text, kb = ac_list()
        await show(update, context, text, kb)
        return None
    if data == "o:aca":
        set_state(OWNER_ID, "ac1")
        await show(update, context, fb("لینک یا یوزرنیم کانال رو بفرست!"),
                   KB(BACK("o:acl")), html_mode=True)
        return None
    if data == "o:act":
        set_state(OWNER_ID, "ac2")
        await show(update, context, fbox(None, "متنی که میخوای ارسال بشه رو بفرست!"),
                   KB(BACK("o:ac")), html_mode=True)
        return None
    if data.startswith("o:acd:"):
        try:
            ex("DELETE FROM ac_channels WHERE chat_id=?", (int(data[6:]),))
        except ValueError:
            return None
        text, kb = ac_list()
        await show(update, context, text, kb)
        return None
    if data in ("o:cy", "o:cyt"):
        clear_state(OWNER_ID)
        if data == "o:cyt":
            set_setting("finder_on", "0" if finder_enabled() else "1")
        text, kb = finder_page()
        await show(update, context, text, kb)
        return None
    if data == "o:rf":  # رفرش: منوی فعلی پاک میشه و منوی تازه میاد
        old_id = q.message.message_id if q and q.message else None
        async with nav_lock():
            await owner_count_swap(context.bot, chat_id)  # عدد اعضای تازه میاد و عدد قبلی (بالای پیام جذب) پاک میشه
            await send(context.bot, chat_id, settings_text(), settings_kb(), html_mode=True)
        if old_id:
            release_cmd(update.effective_user.id, old_id)
            try:
                await context.bot.delete_message(chat_id, old_id)
            except TelegramError:
                pass
        return None
    if data == "o:off":
        _sep = "➖•➖•➖•➖•➖•➖•➖•"
        await show(update, context,
                   f"<b>{_sep}\nدرحال خاموش کردن ربات\nو رفتن به حالت تعمیرات هستیم\nانجام شه؟\n{_sep}</b>",
                   KB(B("بله | OFF 🔘", "o:offy", style="danger"), BACK("o:set")), html_mode=True)
        return None
    if data == "o:offy":
        set_bot_off(True)
        await show(update, context, settings_text("ربات خاموش شد؛ پنل ادمین‌ها غیرفعاله و فقط تو دسترسی داری."),
                   settings_kb(), html_mode=True)
        return None
    if data == "o:on":
        _off_since = get_int_setting("bot_off_since")
        set_bot_off(False)
        _cu = context.application.bot_data.get("catch_up")
        if _cu is not None:  # بعد از روشن شدن: چت‌های وقت خاموشی دوباره چک میشن؛ جذب ثبت‌نشده‌ها ثبت و نوتیف میشن
            bg(_cu(_off_since))
        await show(update, context, settings_text("ربات دوباره روشن شد؛ همه‌ی پنل‌ها و امکانات ادمین‌ها برگشتن."),
                   settings_kb(), html_mode=True)
        return None
    if data == "o:ntf" or data.startswith("o:ntf:"):
        if data.startswith("o:ntf:"):
            for short, key, _label in NTF_KEYS:
                if data == f"o:ntf:{short}":
                    set_setting(key, "0" if get_setting(key) == "1" else "1")
        text, kb = ntf_menu()
        await show(update, context, text, kb, html_mode=True)
        return None
    if data == "o:shm":
        clear_state(OWNER_ID)
        text, kb = shield_menu()
        await show(update, context, text, kb, html_mode=True)
        return None
    if data == "o:shd":
        if shield_on():
            set_setting("shield", "0")
            ex("DELETE FROM shield_admins")  # خاموش شد: هیچ‌کس سپر نداره
            ex("DELETE FROM shield_auto")
            note = "سپر سراسری خاموش شد؛ هیچ‌کس سپر نداره."
        else:
            set_setting("shield", "1")
            note = "سپر سراسری روشن شد؛ همه‌ی ادمین‌ها سپر دارن."
        text, kb = shield_menu(note)
        await show(update, context, text, kb, html_mode=True)
        return None
    if data.startswith("o:shl:"):
        try:
            lv = int(data.split(":")[2])
        except (ValueError, IndexError):
            lv = 0
        if lv not in SHIELD_AT:
            return None
        nm = "سطح " + "⭐️" * lv
        if shield_level_on(lv):
            set_setting(f"shield_l{lv}", "0")
            note = f"سپر {nm} خاموش شد؛ سپر ادمین‌هایی که قبلا فعال شده دست‌نخورده موند."
        else:
            set_setting(f"shield_l{lv}", "1")
            n = await shield22_apply_existing(context.bot, lv)
            note = f"سپر {nm} روشن شد؛ برای {n} ادمینی که الان {SHIELD_AT[lv]} جذب یا بیشتر دارن سپر فعال شد."
        text, kb = shield_menu(note)
        await show(update, context, text, kb, html_mode=True)
        return None
    if data == "o:txt" or data.startswith(("o:txe:", "o:txr:")):
        return "ویرایش متن‌ها از تنظیمات حذف شده."
    if data == "o:vid":
        clear_state(OWNER_ID)
        text, kb = video_menu()
        await show(update, context, text, kb, html_mode=True)
        return None
    if data == "o:vidt":
        if get_setting("video_enabled") != "1" and not get_setting("video_file_id"):
            return "اول ویدیو رو ثبت کن."
        set_setting("video_enabled", "0" if get_setting("video_enabled") == "1" else "1")
        text, kb = video_menu()
        await show(update, context, text, kb, html_mode=True)
        return None
    if data == "o:vids":
        set_state(OWNER_ID, "vid")
        await show(update, context, fb("لطفا ویدیوی آموزشی رو ارسال کن「به‌صورت ویدیو یا فایل」."),
                   KB(BACK("o:vid"), MAIN("o:menu")), html_mode=True)
        return None
    if data == "o:com":
        clear_state(OWNER_ID)
        text, kb = commission_menu()
        await show(update, context, text, kb, html_mode=True)
        return None
    if data == "o:dl":
        return "مهلت پرداخت حذف شده."
    if data in ("o:comamt", "o:comamt2", "o:comamt3", "o:comtgt"):
        prompts = {
            "o:comamt": ("amt", "مبلغ جدید پورسانت سطح یک رو به تومان بفرست「مثلا 200000」:"),
            "o:comamt2": ("amt2", "مبلغ جدید پورسانت سطح دو رو به تومان بفرست「مثلا 250000」:"),
            "o:comamt3": ("amt3", "مبلغ جدید پورسانت سطح سه رو به تومان بفرست「مثلا 300000」:"),
            "o:comtgt": ("tgt", "حدنصاب جدید جذب رو بفرست「مثلا 40」:"),
        }
        key, prompt = prompts[data]
        set_state(OWNER_ID, key)
        await show(update, context, fb(prompt), KB(BACK("o:com"), MAIN("o:menu")), html_mode=True)
        return None
    if data == "o:st":
        await show(update, context, status_text(), KB(BACK("o:adv")))
        return None
    if data == "o:bk":
        await show(update, context, adv_text(), advanced_settings_kb(bk_open=True), html_mode=True)
        return None
    if data == "o:bkn":
        meta = None
        try:
            async with loading(context.bot, chat_id):
                result = await run_backup(context.bot, chat_id)
        except Exception as e:  # noqa
            log.exception("backup failed")
            log_err(f"backup failed: {e!r}")
            await send(context.bot, chat_id,
                       fbox("❌ پشتیبان ناموفق بود ❌",
                            "فایل موقت برای بررسی روی هاست نگه داشته شد و دیتابیس اصلی دست‌نخورده‌ست\n"
                            "جزئیات خطا توی «گزارش خطا» ثبت شد"),
                       KB(BACK("o:adv")), html_mode=True)
            return None
        await send(context.bot, chat_id, fbox(None, result.strip()), KB(BACK("o:adv")))
        return None
    if data == "o:rst":
        set_state(OWNER_ID, "rst")
        await show(update, context,
                   f"<b>{SEP10}\n♻️ بازیابی بکاپ ♻️</b>\n\n"
                   "آخرین فایل بکاپ (.db یا .db.gz) رو همین‌جا به‌صورت فایل بفرست.\n\n"
                   "قبل از جایگزینی، یه نسخه از دیتابیس فعلی کنار فایل اصلی روی هاست ذخیره میشه.\n"
                   "حداکثر حجم فایل ۲۰ مگابایته.\n"
                   f"<b>{SEP10}</b>",
                   KB(BACK("o:adv")), html_mode=True)
        return None
    if data == "o:rst:y":
        st, d = get_state(OWNER_ID)
        path, tmpdir = d.get("path") or "", d.get("tmpdir") or ""
        if st != "rst_ok" or not path or not os.path.isfile(path):
            return "فایل بکاپ منقضی شده؛ از «بازیابی بکاپ» دوباره فایل رو بفرست."
        try:
            async with loading(context.bot, chat_id):
                res = await asyncio.to_thread(restore_apply, path)
        except Exception as e:  # noqa
            log.exception("restore failed")
            log_err(f"restore failed: {e!r}")
            await show(update, context, fbox("❌ بازیابی ناموفق بود ❌",
                                             "دیتابیس فعلی دست‌نخورده‌ست یا از نسخه‌ی کنار فایل قابل برگشته.\n"
                                             "جزئیات توی «گزارش خطا» ثبت شد."), KB(BACK("o:adv")), html_mode=True)
            return None
        finally:
            if tmpdir:
                _safe_rmtree(tmpdir)
        clear_state(OWNER_ID)
        c = res["counts"]
        media_txt = ""
        try:
            probs = await media_problems(context.bot)
            set_setting("media_warn_sig", hashlib.sha256("\n".join(probs).encode()).hexdigest()[:16] if probs else "")
            if probs:
                media_txt = "\n\n⚠️ این موارد باید دوباره ثبت بشن ⚠️\n\n" + "\n\n".join(probs)
        except Exception as e:  # noqa
            log_err(f"media check after restore: {e!r}")
        await show(update, context,
                   fbox("✅ بازیابی انجام شد ✅",
                        html.escape(f"👥 ادمین‌ها:「{fa(c['admins'])}」\n🔷 جذب‌ها:「{fa(c['hires'])}」\n"
                                    f"💰 پورسانت‌ها:「{fa(c['commissions'])}」\n💳 کارت‌ها:「{fa(c['cards'])}」\n\n"
                                    "همین الان اعمال شد و نیازی به ری‌استارت نیست." + media_txt)),
                   KB(BACK("o:adv")), html_mode=True)
        return None
    if data == "o:tst":
        set_state(OWNER_ID, "tst")
        await show(update, context,
                   f"<b>{SEP10}\n🧪 تست پورسانت 🧪 COMMISSION TEST\n{SEP10}</b>\n"
                   "یوزرنیم یا کد ادمینی که میخوای رو بفرست (یا یک پیام ازش فوروارد کن)\n"
                   f"<b>{SEP10}</b>",
                   KB(BACK("o:tsm")), html_mode=True)
        return None
    if data.startswith("o:tst1:") or data.startswith("o:tst2:"):
        a = get_admin(int(data[7:]))
        if a is None:
            return "ادمین پیدا نشد."
        ex("UPDATE admins SET period_count=? WHERE user_id=?", (max(a["cur_target"] - 1, 0), a["user_id"]))
        audit(OWNER_ID, "test_commission", f"{data[:7]} admin={a['user_id']}")
        if data.startswith("o:tst1:"):
            await show(update, context,
                       fb(f"✅ آمار ادمین کد「{a['code']}」روی「{max(a['cur_target'] - 1, 0)}」از「{a['cur_target']}」تنظیم شد.\n\n"
                          f"با یک جذب بعدی (ارسال عدد {a['code']}) پورسانت ثبت میشه."),
                       KB(BACK("o:adv")), html_mode=True)
            return None
        res = record_hire(-int(time.time() * 1000), "تست پورسانت", a["code"])
        if res is None:
            return "ثبت جذب تستی انجام نشد."
        await notify_hire(context.bot, res)
        await show(update, context, fb(f"✅ جذب تستی ثبت شد و اعلان‌ها برای ادمین کد「{a['code']}」ارسال شد."),
                   KB(BACK("o:adv")), html_mode=True)
        return None
    if data == "o:er":
        rows = [r for r in qa("SELECT * FROM errors ORDER BY id DESC LIMIT 60") if not is_noise_error(r["text"])][:10]
        _eh = f"<b>{SEP10}\nگزارش خطا 🐞\n{SEP10}</b>\n"
        if not rows:
            text = _eh + "خطایی ثبت نشده ✅\n" + f"<b>{SEP10}</b>"
        else:
            text = _eh + f"\n{SEP10}\n".join(
                f"{jdate_en(r['ts'])} {dt_of(r['ts']).strftime('%H:%M')}\n{html.escape(r['text'][:300])}" for r in rows
            ) + "\n" + f"<b>{SEP10}</b>"
        kb_rows = [B("🗑️ پاک کردن گزارش 🗑️", "o:erc", style="danger"), BACK_G("o:adv")] if rows else [BACK_G("o:adv")]
        await show(update, context, text[:4000], KB(*kb_rows), holder="🐞")
        return None
    if data == "o:erc":
        ex("DELETE FROM errors")
        await show(update, context, fbox("گزارش خطا 🐞", "خطاها پاک شد ✅"),
                   KB(BACK_G("o:adv")), html_mode=True, holder="🐞")
        return None

    # ----- کانال اجباری -----
    if data == "o:ch":
        clear_state(OWNER_ID)
        text, kb = channel_menu()
        if text is None:
            return await start_channel_add(update, context)
        await show(update, context, text, kb)
        return None
    if data == "o:cha":
        return await start_channel_add(update, context, "o:ch")
    if data == "o:cht":
        set_setting("channel_enabled", "0" if get_setting("channel_enabled") == "1" else "1")
        text, kb = channel_menu()
        await show(update, context, text, kb)
        return None
    if data == "o:chd":
        for k in ("channel_id", "channel_title", "channel_link", "channel_guide", "channel_btn"):
            set_setting(k, "")
        set_setting("channel_enabled", "0")
        await show(update, context, fb("🗑️ کانال اجباری حذف شد."), KB(BACK("o:set")), html_mode=True)
        return None
    return None


async def start_channel_add(update, context, back="o:set"):
    set_state(OWNER_ID, "ch1")
    _sep = "➖•➖•➖•➖•➖•➖•➖•➖•➖•➖•"
    await show(update, context,
               f"<b>{_sep}\nیوزرنیم کانال رو ارسال کن یا یک پیام ازش برام فوروارد کن ⚠️ ربات باید توی کانال ادمین باشه\n{_sep}</b>",
               KB(BACK(back), MAIN("o:menu")), html_mode=True, holder="📢")
    return None


async def deliver_broadcast(bot, uid, d):
    header = "📩 از طرف کارفرما یک پیام جدید داری 📩\n\n🔻متن پیام🔻"
    if d.get("is_text") and len(d.get("text", "")) < 3800:
        await bot.send_message(uid, f"{header}\n\n{d['text']}")
    else:
        await bot.send_message(uid, header)
        await bot.copy_message(chat_id=uid, from_chat_id=d["chat_id"], message_id=d["message_id"])


async def owner_menu_send(context, chat_id, m, text, kb=None, html_mode=True, holder=None):
    """نتیجه‌ی یک ورودیِ مدیر (آیدی، متن، فایل) به‌صورت منوی شیشه‌ای جدید؛ منوی قبلی و پیامی که خودت فرستادی
    همون لحظه پاک میشن تا چیزی از منوهای قبلی توی چت نمونه."""
    async with nav_lock():
        await owner_count_swap(context.bot, chat_id, owner_holder_for(kb, holder))  # اموجی تازه + منوی تازه پایین چت
        msg = await send(context.bot, chat_id, text, kb, html_mode=html_mode)
        cmd_id = None
        if m is not None and getattr(m, "message_id", None):
            INSTANT_CMD.add(m.message_id)
            cmd_id = m.message_id
        await replace_tracked(context.bot, OWNER_ID, "menu", msg, cmd_id=cmd_id)
    return msg


async def owner_message(update: Update, context):
    """هر پیامی که مدیر توی پنل میفرسته بعد از پردازش پاک میشه (/start جداست و ۴ ثانیه بعد پاک میشه)."""
    m = update.effective_message
    try:
        await _owner_message(update, context)
    finally:
        try:
            _st, _d = get_state(OWNER_ID)
            # پیام همگانیِ رسانه‌ای/طولانی تا لحظه‌ی «بفرست» لازمه؛ بعد از ارسال پاک میشه
            _keep = _st == "bc_confirm" and not (_d.get("is_text") and len(_d.get("text", "")) < 3800)
            if m is not None and not _keep:
                bg(_del_msg(m))
        except Exception as e:  # noqa
            log_err(f"owner cmd delete: {e!r}")


async def _owner_message(update: Update, context):
    m = update.effective_message
    chat_id = update.effective_chat.id
    # دکمه‌های کیبورد معمولی منوی اصلی همون عملیات قبلی رو اجرا میکنن (زیرمنوها شیشه‌ای می‌مونن)
    cb = OWNER_KB_MAP.get((m.text or "").strip())
    if cb:
        await del_cmd(m)  # متن دکمه فوری پاک میشه؛ فقط نتیجه میاد
        clear_state(OWNER_ID)
        alert = await owner_cb(update, context, cb)
        if alert:
            await context.bot.send_message(chat_id, fb(alert), parse_mode=H)
        return
    st, d = get_state(OWNER_ID)
    _CUR_KEY.set("st:" + (st or ""))  # بخش فعلی برای اموجی نگه‌دارنده‌ی نتیجه‌ی ورودی متنی

    if st and st.startswith("ck"):  # افزودن/ویرایش تقلب
        await cheat_owner_input(update, context, st, d, m)
        return

    if st == "rst":
        doc = m.document
        if not doc:
            await m.reply_text(fb("فایل بکاپ رو به‌صورت فایل (Document) بفرست."), parse_mode=H, reply_markup=KB(BACK("o:adv")))
            return
        if (doc.file_size or 0) > RESTORE_MAX_BYTES:
            await m.reply_text(fb("حجم فایل بیشتر از ۲۰ مگابایته و ربات نمی‌تونه دانلودش کنه.\n"
                               "فایل رو روی هاست کنار main.py بذار و به‌جای دیتابیس فعلی بنویس (با ربات خاموش)."), parse_mode=H,
                               reply_markup=KB(BACK("o:adv")))
            return
        try:
            async with loading(context.bot, chat_id):
                tgf = await context.bot.get_file(doc.file_id)
                raw = bytes(await tgf.download_as_bytearray())
                info = await asyncio.to_thread(restore_prepare, raw, doc.file_name or "")
        except ValueError as e:
            await m.reply_text(fb(f"❌ {e}"), parse_mode=H, reply_markup=KB(BACK("o:adv")))
            return
        except Exception as e:  # noqa
            log_err(f"restore prepare: {e!r}")
            await m.reply_text(fb("❌ دریافت یا بررسی فایل ناموفق بود. دوباره بفرست."), parse_mode=H, reply_markup=KB(BACK("o:adv")))
            return
        set_state(OWNER_ID, "rst_ok", {"path": info["path"], "tmpdir": info["tmpdir"]})
        await owner_menu_send(context, chat_id, m,
                   fbox("✅ فایل بکاپ سالمه ✅",
                        f"👥 ادمین‌ها:「{fa(info['admins'])}」\n🔷 جذب‌ها:「{fa(info['hires'])}」\n"
                        f"💰 پورسانت‌ها:「{fa(info['commissions'])}」\n💳 کارت‌ها:「{fa(info['cards'])}」\n\n"
                        "با تأیید، همه‌ی دیتای فعلی ربات با این بکاپ جایگزین میشه."),
                   KB(B("✅ بله، جایگزین کن ✅", "o:rst:y", style="danger"), BACK("o:adv")), html_mode=True)
        return

    if st == "au9":
        if not m.text:
            await m.reply_text(fb("فقط متن بفرست."), parse_mode=H)
            return
        items = list(d.get("items") or [])
        if len(items) >= 20:
            await m.reply_text(fb("حداکثر ۲۰ متن میشه ثبت کرد؛ «تمام شد» رو بزن."), parse_mode=H,
                               reply_markup=KB(B("✅ تمام شد ✅", "o:au:e9ok", style="danger"), BACK("o:au:ed")))
            return
        items.append(m.text_html)
        set_state(OWNER_ID, "au9", {"items": items})
        await m.reply_text(fb(f"✅ پیام {len(items)} ثبت شد.\nبعدی رو بفرست یا «تمام شد» رو بزن."), parse_mode=H,
                           reply_markup=KB(B("✅ تمام شد ✅", "o:au:e9ok", style="danger"), BACK("o:au:ed")))
        return

    if st == "aur":
        if m.photo:
            if len(m.caption or "") > 1024:
                await m.reply_text(fb("کپشن بیشتر از ۱۰۲۴ حرفه؛ کوتاه‌ترش کن."), parse_mode=H)
                return
            f = await context.bot.get_file(m.photo[-1].file_id)
            raw = bytes(await f.download_as_bytearray())
            ex("INSERT INTO auto_media(key,data,ext,meta) VALUES('reg_photo',?,'jpg','{}') "
               "ON CONFLICT(key) DO UPDATE SET data=excluded.data, ext='jpg'", (raw,))
            if m.caption:
                set_setting("auto_reg_html", m.caption_html)
        elif m.text:
            set_setting("auto_reg_html", m.text_html)
        else:
            await m.reply_text(fb("عکس همراه کپشن یا فقط متن بفرست."), parse_mode=H)
            return
        clear_state(OWNER_ID)
        text, kb = auto_menu()
        await owner_menu_send(context, chat_id, m, "✅ ذخیره شد.\n\n" + text, kb, html_mode=True)
        return

    if st == "aua":
        if not m.text:
            await m.reply_text(fb("فقط متن بفرست."), parse_mode=H)
            return
        set_setting("auto_alt_html", m.text_html)
        clear_state(OWNER_ID)
        text, kb = auto_menu()
        await owner_menu_send(context, chat_id, m, "✅ ذخیره شد.\n\n" + text, kb, html_mode=True)
        return

    if st == "auv1":
        v = m.video or (m.document if (m.document and (m.document.mime_type or "").startswith("video")) else None)
        if v is None:
            await m.reply_text(fb("لطفا ویدیو رو ارسال کن (به‌صورت ویدیو یا فایل ویدیویی)."), parse_mode=H)
            return
        if (v.file_size or 0) > 20 * 1024 * 1024:
            await m.reply_text(fb("حجم ویدیو بیشتر از ۲۰ مگابایته؛ کوچیک‌ترش کن."), parse_mode=H)
            return
        f = await context.bot.get_file(v.file_id)
        raw = bytes(await f.download_as_bytearray())
        meta = json.dumps({"d": int(getattr(v, "duration", 0) or 0), "w": int(getattr(v, "width", 0) or 0),
                           "h": int(getattr(v, "height", 0) or 0)})
        ex("INSERT INTO auto_media(key,data,ext,meta) VALUES('video',?,'mp4',?) "
           "ON CONFLICT(key) DO UPDATE SET data=excluded.data, ext='mp4', meta=excluded.meta", (raw, meta))
        if m.caption:
            set_setting("auto_vid_html", m.caption_html)
            clear_state(OWNER_ID)
            text, kb = auto_menu()
            await owner_menu_send(context, chat_id, m, "✅ ذخیره شد.\n\n" + text, kb, html_mode=True)
            return
        set_state(OWNER_ID, "auv2")
        await owner_menu_send(context, chat_id, m, fbox("✅ ویدیو ذخیره شد ✅", "حالا متنی که بلافاصله بعد از ویدیو فرستاده میشه رو بفرست."),
                   KB(B("🚫 بدون متن 🚫", "o:au:vnc", style="danger"), BACK("o:au:ed")), html_mode=True)
        return

    if st == "auv2":
        if not m.text:
            await m.reply_text(fb("متن رو به‌صورت متن بفرست."), parse_mode=H)
            return
        set_setting("auto_vid_html", m.text_html)
        clear_state(OWNER_ID)
        text, kb = auto_menu()
        await owner_menu_send(context, chat_id, m, "✅ ذخیره شد.\n\n" + text, kb, html_mode=True)
        return

    if st == "rsd":
        a = None
        origin = getattr(m, "forward_origin", None)
        su = getattr(origin, "sender_user", None) if origin is not None else None
        if su is not None:
            a = get_admin(su.id)
        elif m.text:
            t = normalize(m.text).lstrip("@").lower()
            if t.isdigit():
                a = get_admin(int(t)) or q1("SELECT * FROM admins WHERE code=?", (int(t),))
            else:
                a = q1("SELECT * FROM admins WHERE username=?", (t,))
        if a is None:
            await m.reply_text(fb("ادمینی با این مشخصات پیدا نشد!\nدوباره بفرست..."), parse_mode=H, reply_markup=KB(BACK("o:adv")))
            return
        clear_state(OWNER_ID)
        n_c = q1("SELECT COUNT(*) n FROM commissions WHERE admin_id=?", (a["user_id"],))["n"]
        n_k = q1("SELECT COUNT(*) n FROM cards WHERE admin_id=?", (a["user_id"],))["n"]
        await owner_menu_send(context, chat_id, m,
                   fbox("🧹 ریست دیتای ادمین 🧹",
                        f"🧹 ادمین کد「{a['code']}」: {link(a)}\n"
                        f"🧲 جذب‌ها:「{a['total_count']}」 💰 پورسانت‌ها:「{n_c}」 💳 کارت‌ها:「{n_k}」\n\n"
                        "با تأیید، فقط دیتای همین ادمین پاک میشه و بقیه‌ی ادمین‌ها و تنظیمات دست‌نخورده می‌مونن. "
                        "قبلش یه نسخه‌ی پشتیبان ساخته میشه.\n\nمطمئنی؟"),
                   KB(B("✅ بله، پاک کن ✅", f"o:rsd:y:{a['user_id']}", style="danger"), BACK("o:adv")))
        return

    if st == "tst":
        a = None
        origin = getattr(m, "forward_origin", None)
        su = getattr(origin, "sender_user", None) if origin is not None else None
        if su is not None:
            a = get_admin(su.id)
        elif m.text:
            t = normalize(m.text).lstrip("@").lower()
            if t.isdigit():
                a = get_admin(int(t)) or q1("SELECT * FROM admins WHERE code=?", (int(t),))
            else:
                a = q1("SELECT * FROM admins WHERE username=?", (t,))
        if a is None:
            await m.reply_text(fb("ادمینی با این مشخصات پیدا نشد!\nدوباره بفرست..."), parse_mode=H, reply_markup=KB(BACK("o:adv")))
            return
        clear_state(OWNER_ID)
        await owner_menu_send(context, chat_id, m,
                   fbox("🧪 تست پورسانت 🧪",
                        f"🧪 ادمین کد「{a['code']}」: {link(a)}\n"
                        f"آمار الان:「{a['period_count']}」از「{a['cur_target']}」\n\nکدوم حالت؟"),
                   KB(B("🎯 یک جذب مونده به پورسانت 🎯", f"o:tst1:{a['user_id']}", style="danger"),
                      B("⚡️ تکمیل فوری پورسانت ⚡️", f"o:tst2:{a['user_id']}", style="danger"),
                      BACK("o:adv")))
        return

    if st == "stdate":
        day = parse_jalali_day(m.text or "")
        if day is None:
            await m.reply_text(fb("🚧تاریخ معتبر نیست🚧\nمثل 1405/07/13 یا 13 مهر 1405 بفرست."), parse_mode=H,
                               reply_markup=KB(BACK("o:sts:0")))
            return
        r = stats_row(day)
        if r is None:
            await m.reply_text(fb("برای این تاریخ آمار ثبت نشده؛ تاریخ دیگه‌ای بفرست."), parse_mode=H, reply_markup=KB(BACK("o:sts:0")))
            return
        clear_state(OWNER_ID)
        await owner_menu_send(context, chat_id, m, stats_row_text(r), KB(BACK("o:sts:0")))
        return

    if st == "search":
        a = None
        origin = getattr(m, "forward_origin", None)
        if origin is not None:
            su = getattr(origin, "sender_user", None)
            if su is None:
                await m.reply_text(fb("این پیام فوروارد‌شده هویت فرستنده رو نشون نمیده「پروفایل مخفیه」. "
                                   "لطفا یوزرنیم یا آیدی عددی ادمین رو بفرست."), parse_mode=H)
                return
            a = get_admin(su.id)
        elif m.text:
            t = normalize(m.text).lstrip("@").lower()
            if t.isdigit():
                a = get_admin(int(t)) or q1("SELECT * FROM admins WHERE code=?", (int(t),))
            else:
                a = q1("SELECT * FROM admins WHERE username=?", (t,))
        if a is None:
            await m.reply_text(fb("ادمینی با این مشخصات پیدا نشد!\nدوباره بفرست..."), parse_mode=H,
                               reply_markup=KB(BACK("o:menu")))
            return
        clear_state(OWNER_ID)
        msg = await send(context.bot, chat_id, search_report_text(a), search_kb(a))
        # پیام یوزرنیم/آیدی که فرستادی به این منو وصل میشه؛ با بازگشت و پاک شدن منو همون لحظه اون هم پاک میشه
        INSTANT_CMD.add(m.message_id)
        await replace_tracked(context.bot, OWNER_ID, "menu", msg, cmd_id=m.message_id)
        return

    if st in ("chg_p", "chg_t"):
        a = get_admin(d.get("uid"))
        if a is None:
            clear_state(OWNER_ID)
            await m.reply_text(fb("ادمین پیدا نشد."), parse_mode=H, reply_markup=KB(BACK("o:menu")))
            return
        num = normalize(m.text or "")
        if not num.isdigit():
            await m.reply_text(fb("فقط یک عدد بفرست."), parse_mode=H, reply_markup=KB(BACK("o:menu")))
            return
        val = int(num)
        if st == "chg_p":
            if val > a["cur_target"]:
                await m.reply_text(fb(f"عدد جذب این دوره نباید از {a['cur_target']} بیشتر باشه؛ دوباره بفرست."), parse_mode=H,
                                   reply_markup=KB(BACK("o:menu")))
                return
            set_state(OWNER_ID, "chg_t", {"uid": a["user_id"], "p": val})
            await owner_menu_send(context, chat_id, m, fb("لطفا عدد جذب کلا رو ارسال کنید!"), KB(BACK("o:menu")), html_mode=True)
            return
        if val < int(d.get("p", 0)):
            await m.reply_text(fb("عدد جذب کلا نباید از جذب این دوره کمتر باشه؛ دوباره بفرست."), parse_mode=H,
                               reply_markup=KB(BACK("o:menu")))
            return
        set_state(OWNER_ID, "chg_c", {"uid": a["user_id"], "p": d.get("p", 0), "t": val})
        await owner_menu_send(
            context, chat_id, m,
            fbox("✏️ تغییر جذب ✏️",
                 f"👤 نام: {link(a)}\n"
                 f"🔹 این دوره:「{a['period_count']} ← {d.get('p', 0)}」\n"
                 f"🔷 کلا:「{a['total_count']} ← {val}」\n\n"
                 "تایید میکنی؟"),
            KB(B("✅ تایید ✅", f"o:chy:{a['user_id']}", style="success"),
               B("✏️ ویرایش ✏️", f"o:chg:{a['user_id']}", style="primary"),
               BACK("o:menu")))
        return

    if st == "umsg":
        uid = d.get("uid")
        try:
            await context.bot.copy_message(chat_id=uid, from_chat_id=m.chat_id, message_id=m.message_id)
        except TelegramError as e:
            log_err(f"owner msg to user: {e!r}")
            await m.reply_text(fb("❌ نتونستم پیام رو برسونم؛ ممکنه کاربر ربات رو بلاک کرده باشه."), parse_mode=H,
                               reply_markup=KB(BACK("o:menu")))
            return
        clear_state(OWNER_ID)
        await owner_menu_send(context, chat_id, m, fb("✅ پیامت برای کاربر ارسال شد."), KB(BACK("o:menu")), html_mode=True)
        return

    if st == "bc":
        is_text = bool(m.text)
        set_state(OWNER_ID, "bc_confirm", {"chat_id": m.chat_id, "message_id": m.message_id,
                                           "is_text": is_text, "text": m.text or ""})
        await m.reply_text(fb("👇 پیش‌نمایش پیامی که برای ادمین‌ها ارسال میشه:"), parse_mode=H)
        try:
            await deliver_broadcast(context.bot, chat_id, get_state(OWNER_ID)[1])
        except Exception as e:  # noqa
            log_err(f"broadcast preview: {e!r}")
            await m.reply_text(fb("نتونستم پیش‌نمایش رو بسازم؛ این نوع پیام پشتیبانی نمیشه."), parse_mode=H)
            clear_state(OWNER_ID)
            return
        await owner_menu_send(context, chat_id, m, fb("با زدن دکمه زیر، پیام برای تمام ادمین‌ها ارسال میشه."),
                   KB(B("📤 بفرست 📤", "o:bcs", style="success"), BACK("o:menu")), html_mode=True)
        return

    if st == "receipt":
        kind = fid = None
        if m.photo:
            kind, fid = "photo", m.photo[-1].file_id
        elif m.document:
            kind, fid = "document", m.document.file_id
        if not fid:
            await m.reply_text(fb("لطفا فیش رو به‌صورت عکس یا فایل ارسال کن."), parse_mode=H)
            return
        await finalize_payment(context, m, d["cid"], fid, kind)
        return

    if st in ("photo_level", "photo_activity", "photo_set"):
        if not m.photo:
            await m.reply_text(fb("لطفاً عکس را به‌صورت Photo ارسال کن، نه فایل."), parse_mode=H)
            return
        code = d.get("code") if st == "photo_set" else ("1p" if st == "photo_level" else "1a")
        item = PH_ITEMS.get(code)
        if item is None:
            clear_state(OWNER_ID)
            return
        set_setting(item[0], m.photo[-1].file_id)
        clear_state(OWNER_ID)
        if code == "ad" and d.get("cid") and cheat_get(d["cid"]) is not None:
            _t, _k = cheat_detail(int(d["cid"]), "✅ عکس آگهی ذخیره شد.")
            await owner_menu_send(context, chat_id, m, _t, _k, html_mode=True)
            return
        await owner_menu_send(context, chat_id, m, fb(f"✅ {item[1]} ذخیره شد."), settings_kb(), html_mode=True)
        return

    if st == "vid":
        v = m.video or (m.document if (m.document and (m.document.mime_type or "").startswith("video")) else None)
        if v is None:
            await m.reply_text(fb("لطفا ویدیو رو ارسال کن (به‌صورت ویدیو یا فایل ویدیویی)."), parse_mode=H)
            return
        set_setting("video_file_id", v.file_id)
        set_setting("video_kind", "video" if m.video else "document")
        clear_state(OWNER_ID)
        text, kb = video_menu()
        await owner_menu_send(context, chat_id, m, fb("✅ ویدیو ذخیره شد.") + "\n" + text, kb, html_mode=True)
        return

    if st == "txt":
        clear_state(OWNER_ID)
        await owner_menu_send(context, chat_id, m, fb("ویرایش متن‌ها از تنظیمات حذف شده."), settings_kb(), html_mode=True)
        return


    if st in ("amt", "amt2", "amt3", "tgt"):
        raw = normalize(m.text or "").replace(",", "").replace("٬", "")
        if not raw.isdigit():
            await m.reply_text(fb("لطفا فقط عدد بفرست."), parse_mode=H)
            return
        v = int(raw)
        if st in ("amt", "amt2", "amt3"):
            if v < 1000:
                await m.reply_text(fb("مبلغ باید به تومان و حداقل 1000 باشه."), parse_mode=H)
                return
            set_setting({"amt": "pay_amount", "amt2": "pay_amount_2", "amt3": "pay_amount_3"}[st], v)
        else:
            if not 1 <= v <= 100000:
                await m.reply_text(fb("حدنصاب باید بین 1 تا 100000 باشه."), parse_mode=H)
                return
            set_setting("pay_target", v)
        clear_state(OWNER_ID)
        text, kb = commission_menu()
        await owner_menu_send(context, chat_id, m, "✅ ذخیره شد.\n\n" + text, kb, html_mode=True)
        return

    if st == "ac1":
        if not m.text:
            await m.reply_text(fb("لینک یا یوزرنیم کانال رو به‌صورت متن بفرست."), parse_mode=H)
            return
        client = SESSION_CLIENT
        if client is None:
            await m.reply_text(fb("اکانت شخصی وصل نیست؛ بعد از وصل شدن دوباره امتحان کن."), parse_mode=H)
            return
        try:
            ent, err = await ac_resolve_and_join(client, m.text)
        except Exception as e:  # noqa
            log_err(f"autocomment add: {e!r}")
            await m.reply_text(fb("نتونستم کانال رو پیدا کنم یا عضوش بشم. لینک رو چک کن و دوباره بفرست."), parse_mode=H)
            return
        if err:
            await m.reply_text(fb(err), parse_mode=H)
            return
        from telethon import utils as tl_utils
        ac_tables()
        ch_link = f"https://t.me/{ent.username}" if getattr(ent, "username", None) else m.text.strip()
        ex("INSERT OR REPLACE INTO ac_channels(chat_id,title,link,added_at) VALUES(?,?,?,?)",
           (tl_utils.get_peer_id(ent), getattr(ent, "title", "") or ch_link, ch_link, int(time.time())))
        clear_state(OWNER_ID)
        text, kb = ac_list()
        await owner_menu_send(context, chat_id, m, "✅ کانال اضافه شد.\n\n" + text, kb)
        return

    if st == "ac2":
        if not m.text:
            await m.reply_text(fb("متن کامنت رو به‌صورت متن بفرست."), parse_mode=H)
            return
        set_setting("ac_text", m.text.strip()[:1000])
        clear_state(OWNER_ID)
        text, kb = ac_page()
        await owner_menu_send(context, chat_id, m, "✅ متن ذخیره شد.\n\n" + text, kb)
        return

    if st == "ch1":
        ref = None
        origin = getattr(m, "forward_origin", None)
        if origin is not None and getattr(origin, "chat", None) is not None:
            ref = origin.chat.id
        elif m.text:
            t = m.text.strip()
            ref = int(t) if re.fullmatch(r"-?\d+", t) else ("@" + t.lstrip("@"))
        if ref is None:
            await m.reply_text(fb("یوزرنیم کانال، آیدی عددی یا یک پیام فوروارد‌شده از کانال بفرست."), parse_mode=H)
            return
        try:
            chat = await context.bot.get_chat(ref)
            me = await context.bot.get_me()
            mem = await context.bot.get_chat_member(chat.id, me.id)
            if mem.status not in ("administrator", "creator"):
                raise ValueError("bot-not-admin")
            invite = f"https://t.me/{chat.username}" if chat.username else None
            if invite is None:
                invite = getattr(chat, "invite_link", None) or await context.bot.export_chat_invite_link(chat.id)
        except Exception as e:  # noqa
            log_err(f"channel add failed: {e!r}")
            await m.reply_text(fb("نتونستم کانال رو تایید کنم. مطمئن شو ربات توی کانال ادمینه「برای کانال خصوصی "
                               "اجازه ساخت لینک دعوت هم لازمه」و دوباره بفرست."), parse_mode=H)
            return
        set_state(OWNER_ID, "ch2", {"id": chat.id, "title": chat.title or str(chat.id), "link": invite})
        await m.reply_text(fb("متن پیام عضویت اجباری چی باشه؟「همون متنی که قبل از ادامه به کاربر نشون داده میشه」"), parse_mode=H)
        return
    if st == "ch2":
        if not m.text:
            await m.reply_text(fb("لطفا متن پیام رو به‌صورت متن بفرست."), parse_mode=H)
            return
        d["guide"] = m.text
        set_state(OWNER_ID, "ch3", d)
        await m.reply_text(fb("اسم دکمه ورود به کانال چی باشه؟"), parse_mode=H)
        return
    if st == "ch3":
        if not m.text or len(m.text) > 60:
            await m.reply_text(fb("اسم دکمه باید متن و حداکثر 60 کاراکتر باشه."), parse_mode=H)
            return
        set_setting("channel_id", d["id"])
        set_setting("channel_title", d["title"])
        set_setting("channel_link", d["link"])
        set_setting("channel_guide", d["guide"])
        set_setting("channel_btn", m.text)
        set_setting("channel_enabled", "1")
        clear_state(OWNER_ID)
        text, kb = channel_menu()
        await owner_menu_send(context, chat_id, m, "✅ کانال اجباری فعال شد.\n\n" + text, kb)
        return

    # پیام متفرقه: بعد از ۱۰ دقیقه پاک میشه و منوی اصلی حداکثر هر ۱۰ دقیقه یک بار میاد
    schedule_delete(chat_id, m.message_id)
    if menu_due(OWNER_ID):
        await send_owner_menu(context, chat_id)


_pay_lock = asyncio.Lock()


def parse_amount(text, default: int) -> int:
    if not text:
        return default
    mm = re.search(r"\d[\d,٬]*", normalize(text))
    if not mm:
        return default
    v = int(re.sub(r"[,٬]", "", mm.group(0)))
    if v <= 0:
        return default
    return v * 1000 if v < 10000 else v  # عدد کوچک = هزار تومان


async def finalize_payment(context, m, cid: int, file_id: str, kind: str):
    """پرداخت فقط وقتی نهایی می‌شود که فیش واقعا به ادمین ارسال شده باشد."""
    async with _pay_lock:
        c = q1("SELECT * FROM commissions WHERE id=?", (cid,))
        if c is None or c["status"] != "requested":
            clear_state(OWNER_ID)
            await m.reply_text(fb("این درخواست قبلا نهایی شده یا پیدا نشد."), parse_mode=H, reply_markup=KB(BACK("o:fin")))
            return
        a = get_admin(c["admin_id"])
        _st0, _sd0 = get_state(OWNER_ID)
        _pm = _sd0.get("pm") if (_st0 == "receipt" and isinstance(_sd0, dict) and _sd0.get("cid") == cid) else None
        ts = int(time.time())
        amount = parse_amount(m.caption, c["amount"])
        tmp = dict(c)
        tmp.update(paid_at=ts, paid_amount=amount)
        try:
            async with loading(context.bot, m.chat_id):
                _rm = await send_media(context.bot, a["user_id"], kind, file_id, caption=receipt_caption_for_admin(tmp), kb=ADMIN_RECEIPT_KB(), html_mode=True)
                await hold_receipt(context.bot, a["user_id"], cid, _rm)
        except Exception as e:  # noqa
            if isinstance(e, Forbidden):
                mark_blocked(a["user_id"])
            log_err(f"receipt to admin {a['user_id']} failed: {e!r}")
            await m.reply_text(fb("ارسال فیش به ادمین ناموفق بود「احتمالا ربات رو بلاک کرده」؛ پرداخت ثبت نشد."), parse_mode=H,
                               reply_markup=KB(BACK("o:fin")))
            return
        mark_paid(cid, ts, file_id, kind, amount)
        clear_state(OWNER_ID)
    _okm = await send(context.bot, m.chat_id,
                      f"💸 پرداخت پورسانت: {link(a)}\n با موفقیت انجام شد ✅\n\n💰 مبلغ ثبت‌شده:「{fmt_en(amount)}」تومان",
                      KB(B("☑️ واریزی های انجام نشده ☑️", "o:fu:0", style="primary"), BACK("o:fin")))
    # از پین درمیاد؛ ۳ ثانیه بعد درخواست، صفحه‌ی فیش، عکس فیش و همین پیام پاک میشن
    await finish_request(context.bot, cid, extra=[m.message_id, _pm, getattr(_okm, "message_id", None)], delay=3)


# ----------------------------------------------------------------------------
# روتر کلی
# ----------------------------------------------------------------------------
async def on_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    data = q.data or ""
    uid = q.from_user.id
    alert = None
    answered = False
    try:
        if data.startswith("o:"):
            if uid != OWNER_ID:
                await q.answer("دسترسی نداری.", show_alert=True)
                return
            alert = await owner_cb(update, context, data)
        else:
            if uid != OWNER_ID and bot_off() and data not in MAINT_OK_CB:
                # حالت تعمیرات: حتی دکمه‌های قدیمی هم فقط پیام تعمیرات نشون میدن
                try:
                    await q.answer()
                except TelegramError:
                    pass
                await maintenance_reply(context.bot, q.message.chat_id if q.message else uid, uid)
                return
            if throttled(uid, data):
                await q.answer()  # ضداسپم: فاصله ۲ ثانیه بین زدن پشت‌سرهم یک دکمه
                return
            ex("UPDATE admins SET blocked=0 WHERE user_id=? AND blocked=1", (uid,))
            if data in ("t:start", "t:seen", "t:rsp", "t:gr") and (get_admin(uid) is not None or uid == OWNER_ID):
                try:
                    await q.answer()
                except TelegramError:
                    pass
                answered = True
            alert = await admin_cb(update, context, data)
    except Exception as e:  # noqa
        log.exception("callback error")
        log_err(f"callback {data}: {e!r}")
        alert = ERROR_TEXT
    if answered:
        return
    try:
        await q.answer(alert, show_alert=bool(alert)) if alert else await q.answer()
    except TelegramError:
        pass


async def on_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    if user is None or user.is_bot:
        return
    _fut = _sv_wait["fut"]
    if _fut is not None and not _fut.done() and user.id == OWNER_ID:
        _sm = update.effective_message
        _sd = _sm.document if (_sm is not None and _sm.document and (_sm.document.mime_type or "").startswith("video")) else None
        _sv = (_sm.video if _sm is not None else None) or _sd
        if _sv is not None:  # ویدیوی آموزشی که اکانت شخصی از Saved Messages فرستاد (همگام‌سازی خودکار)
            _fut.set_result((_sv.file_id, "video" if _sm.video else "document", _sm.message_id))
            return
    try:
        if user.id == OWNER_ID:
            await owner_message(update, context)
        else:
            _a = get_admin(user.id) if bot_off() else None
            if _a is not None and _a["training_done"]:
                _m = update.effective_message
                _t = (_m.text or _m.caption or "") if _m else ""
                _suggest = get_state(user.id)[0] == "suggest" and not is_kb_text(_t)
                if not (_t in RBTN_ALIASES["contact"] or _suggest):
                    if is_kb_text(_t):
                        await del_cmd(_m)
                    await maintenance_reply(context.bot, update.effective_chat.id, user.id)
                    return
            await admin_message(update, context)
    except Exception as e:  # noqa
        log.exception("message error")
        log_err(f"message from {user.id}: {e!r}")
        try:
            await update.effective_message.reply_text(ERROR_TEXT)
        except Exception:  # noqa
            pass


async def on_error(update, context: ContextTypes.DEFAULT_TYPE):
    log.error("Unhandled error", exc_info=context.error)
    log_err(f"unhandled: {context.error!r}")


async def housekeeping_job(context: ContextTypes.DEFAULT_TYPE):
    """پاک‌سازی پیام‌های متفرقه، پاک شدن وضعیت موقت ثبت کارت بعد از ۳۰ دقیقه، و تمیزکاری حافظه."""
    now = int(time.time())
    for r in qa("SELECT * FROM cleanup WHERE due<=? ORDER BY due LIMIT 200", (now,)):
        ok = await _safe_delete(context.bot, r["chat_id"], r["message_id"])
        if ok:
            ex("DELETE FROM cleanup WHERE id=?", (r["id"],))
        else:
            # خطاهای موقت گم نمی‌شوند؛ یک بار دیگر بعداً تلاش می‌کنیم.
            ex("UPDATE cleanup SET due=? WHERE id=?", (now + 300, r["id"]))
    # فقط وضعیت موقت پاک میشه؛ کارت‌های ذخیره‌شده و اطلاعات ادمین دست‌نخورده می‌مونن
    ex("DELETE FROM state WHERE state IN ('card_input','pay','suggest') AND COALESCE(ts,0)<?", (now - STATE_TTL,))
    ex("DELETE FROM sent_log WHERE ts<?", (now - SENT_KEEP,))
    ex("DELETE FROM holds WHERE until<?", (now - 120,))
    await release_stale_requests(context.bot)
    cut = time.time() - 3600
    for k in [k for k, v in _tut_seen.items() if v < cut]:
        _tut_seen.pop(k, None)


def WEEKLY_KB():
    # همون عملیات دکمه‌ی «راه‌اندازی مجدد» (callback ی a:rst)
    return KB(B("🔥 شروع دوباره 🔥", "a:rst", style="success"))


WEEKLY_HOUR = 21  # ساعت ارسال پیام هفتگی (شنبه‌ها، به وقت TZ)


async def weekly_levels_job(context: ContextTypes.DEFAULT_TYPE):
    """هر شنبه ساعت ۲۱ (شب): پیام سطح‌بندی فقط برای ادمین‌هایی که هفته‌ی گذشته (شنبه تا جمعه) کمتر از حدنصاب دوره جذب داشتن.
    اجرای اول فقط شروع رو ثبت میکنه (پیام ناخواسته نمیره) و ارسال از شنبه‌ی بعد شروع میشه."""
    if bot_off():
        return
    now = int(time.time())
    d = dt_of(now)
    start = (d - timedelta(days=(d.weekday() - 5) % 7)).replace(hour=0, minute=0, second=0, microsecond=0)
    key = start.strftime("%Y%m%d")
    last = get_setting("weekly_last")
    if last == key:
        return
    if not last:
        set_setting("weekly_last", key)
        return
    if d.hour < WEEKLY_HOUR:
        return
    set_setting("weekly_last", key)  # قبل از ارسال ثبت میشه تا با ریستارت دوباره نره
    w_from = int((start - timedelta(days=7)).timestamp())
    w_to = int(start.timestamp())
    rows = qa("SELECT a.user_id, a.cur_target, "
              "(SELECT COUNT(*) FROM hires h WHERE h.admin_id=a.user_id AND h.ts>=? AND h.ts<?) wk "
              "FROM admins a WHERE a.training_done=1 AND a.blocked=0 AND a.user_id<>? "
              "AND COALESCE(a.training_done_at,0)<?", (w_from, w_to, OWNER_ID, now - 86400))
    text = weekly_text()
    sent = 0
    for r in rows:
        if r["wk"] >= r["cur_target"]:
            continue
        if await safe_send(context.bot, r["user_id"], text, WEEKLY_KB()) is not None:
            sent += 1
        await asyncio.sleep(0.05)
    audit(0, "weekly_levels", f"sent={sent}")


NOACT_EVERY = 2 * 86400   # ادمینی که ۲ روز جذب نکرده؛ تا جذب جدید ثبت کنه هر ۲ روز تکرار میشه
NOACT_AFTER_STALL = 3 * 3600  # اطلاعیه‌ی ۲ روز بدون جذب و یادآوریِ «N جذب دیگه تا پورسانت» اگه همزمان برسن، دومی ۳ ساعت بعد میره (همون روز؛ اگه از ۲۳ رد بشه صبح ۹)
NOACT_TTL = 86400         # اطلاعیه ۲۴ ساعت می‌مونه و دکمه‌ی پاک‌کردن نداره
NOACT_CK_CB = "a:ckopen"  # دکمه‌ی «مشاهده تقلب‌ها»: بخش تقلب‌ها براش باز میشه
_NA_SEP = "➖•➖•➖•➖"
NOACT_TEXT = rl(
    f"{_NA_SEP}\n"
    "<b>🚀 می‌خوای جذبت رو چند برابر کنی؟</b>\n"
    f"{_NA_SEP}\n"
    "اگه هنوز نتونستی جذب‌هات رو شروع کنی یا دنبال روش‌های جدید برای جذب بیشتر هستی، "
    "بخش تقلب‌ها دقیقا برای تو ساخته شده❕🃏\n\n"
    "چند روش کاربردی و متفاوت آماده کردیم که می‌تونی با استفاده ازشون افراد بیشتری رو جذب کنی "
    "و سریع‌تر به پورسانت برسی. 💸\n"
    f"{_NA_SEP}\n"
    "همین الان دکمه زیر رو بزن:\n"
    "<b>🔻و روش‌های جدید جذب رو ببین!🔻</b>\n"
    f"{_NA_SEP}"
)


# نسخه‌ی مخصوص ادمینی که هنوز هیچ جذبی نداره
NOACT_ZERO_TEXT = rl(
    f"{_NA_SEP}\n"
    "<b>🚀 می‌خوای یه عالمه جذب بدست بیاری❔</b>\n"
    f"{_NA_SEP}\n\n"
    "اگه هنوز نتونستی جذب‌هات رو شروع کنی یا دنبال روش‌های جدید برای جذب بیشتر هستی "
    "بخش تقلب‌ها دقیقا برای تو ساخته شده❕🃏\n\n"
    "چند روش کاربردی و متفاوت آماده کردیم که می‌تونی با استفاده ازشون افراد بیشتری رو جذب کنی "
    "و سریع‌تر به پورسانت برسی. 💸\n\n"
    f"{_NA_SEP}\n"
    "همین الان دکمه زیر رو بزن:\n"
    "<b>🔻و روش‌های جدید جذب رو ببین!🔻</b>\n"
    f"{_NA_SEP}"
)


def NOACT_KB():
    return KB(B("🃏 مشاهده تقلب‌ها 🃏", NOACT_CK_CB, style="primary"))


def WARN_KB():
    return KB(B("🃏 دریافت تقلب 🃏", NOACT_CK_CB, style="danger"))  # بخش تقلب‌ها رو باز میکنه


NOACT_STOP_BEFORE_WARN = 86400  # ادمین بدون جذب: پیام تقلب از ۱ روز قبل از هشدار دیگه نمیره (فقط روز ۲ و ۴)


def in_notice_hours(now: int) -> bool:
    """پیام تقلب و هشدار حذف فقط بین ۹ تا ۲۳ (وقت تهران) ارسال میشن."""
    return STALL_HOURS[0] <= datetime.fromtimestamp(now, TZ).hour < STALL_HOURS[1]


async def no_recruit_notice_job(context: ContextTypes.DEFAULT_TYPE):
    """هر ادمین فعال که ۲ روز جذب نداشته اطلاعیه میگیره؛ اگه جذب نکنه هر ۲ روز دوباره (قبلی پاک میشه).
    با ثبت جذب جدید شمارش از همون جذب دوباره شروع میشه. مبنا: آخرین جذب، یا پایان آموزش اگه هنوز جذبی نداشته.
    فقط بین ۹ تا ۲۳؛ زمان ارسال فقط بعد از ارسال موفق ثبت میشه (ارسال ناموفق ۱ ساعت بعد دوباره تلاش میشه)."""
    if bot_off():
        return
    now = int(time.time())
    if not in_notice_hours(now):
        return
    rows = qa("SELECT user_id, last_hire_at, training_done_at, total_count, noact_sent_at, noact_msg, stall_sent_at "
              "FROM admins WHERE training_done=1 AND blocked=0 AND user_id<>?", (OWNER_ID,))
    for a in rows:
        uid = a["user_id"]
        ref = int(a["last_hire_at"] or a["training_done_at"] or 0)
        if not ref:
            continue
        _zero = not a["last_hire_at"] and not a["total_count"]  # بدون هیچ جذبی: متن مخصوص خودش
        if now < max(ref, int(a["noact_sent_at"] or 0)) + NOACT_EVERY:
            continue
        if not _zero:
            _st = int(a["stall_sent_at"] or 0)
            _due = max(ref, int(a["noact_sent_at"] or 0)) + NOACT_EVERY
            if _st >= _due and now < _st + NOACT_AFTER_STALL:
                continue  # «N جذب دیگه تا پورسانت» همین الان رفته؛ این اطلاعیه ۳ ساعت بعد از اون میره
        if _zero:
            # بدون هیچ جذبی: از ۱ روز قبل از هشدار حذف دیگه پیام تقلب نمیره
            has_card = q1("SELECT 1 FROM cards WHERE admin_id=?", (uid,)) is not None
            if now - ref >= (INACTIVE_CARD if has_card else INACTIVE_NO_CARD) - WARN_BEFORE - NOACT_STOP_BEFORE_WARN:
                continue
        m = await safe_send(context.bot, uid, NOACT_ZERO_TEXT if _zero else NOACT_TEXT, NOACT_KB(), html_mode=True)
        if m is None:
            # ارسال نشد: ۱ ساعت بعد دوباره تلاش میشه (نه ۲ روز بعد)
            ex("UPDATE admins SET noact_sent_at=? WHERE user_id=?", (now + 3600 - NOACT_EVERY, uid))
        else:
            ex("UPDATE admins SET noact_sent_at=? WHERE user_id=?", (now, uid))
            hold_notice(m, secs=NOACT_TTL)
            prev = int(a["noact_msg"] or 0)
            if prev:
                bg(_safe_delete(context.bot, uid, prev))
            ex("UPDATE admins SET noact_msg=? WHERE user_id=?", (m.message_id, uid))
        await asyncio.sleep(0.05)


def comeback_returned(uid: int) -> bool:
    """ادمینِ خودکار-حذف‌شده دوباره برگشته؟ فقط یک بار True میده (برای پیام «خوش برگشتی»)."""
    if q1("SELECT 1 FROM comeback WHERE user_id=? AND back=0", (uid,)) is None:
        return False
    ex("UPDATE comeback SET back=1, sent=1 WHERE user_id=?", (uid,))
    return True


async def comeback_job(context: ContextTypes.DEFAULT_TYPE):
    """یک روز بعد از حذف خودکار، یک بار پیام «هنوز دیر نشده» با دکمه‌ی شروع دوباره (فقط بین ۹ تا ۲۳)."""
    if bot_off():
        return
    now = int(time.time())
    if not in_notice_hours(now):
        return
    rows = qa("SELECT user_id FROM comeback WHERE sent=0 AND back=0 AND removed_at<=?", (now - COMEBACK_AFTER,))
    for r in rows:
        uid = r["user_id"]
        ex("UPDATE comeback SET sent=1 WHERE user_id=?", (uid,))
        if get_admin(uid) is not None:  # خودش قبلاً برگشته
            continue
        m = await safe_send(context.bot, uid, COMEBACK_TEXT, KB(B(COMEBACK_BTN, COMEBACK_CB, style="danger")), html_mode=True)
        hold_notice(m, chat_id=uid, secs=COMEBACK_HOLD)
        if m is not None:
            ex("UPDATE comeback SET msg_id=?, sent_at=? WHERE user_id=?", (m.message_id, now, uid))
        await asyncio.sleep(0.05)


async def tut_nudge_job(context: ContextTypes.DEFAULT_TYPE):
    """ادمینی که ۳۰ دقیقه از /start گذشته و هنوز آموزشش تموم نشده، یک بار یادآوری میگیره (فقط بین ۹ تا ۲۳)."""
    if bot_off():
        return
    now = int(time.time())
    if not in_notice_hours(now):
        return
    rows = qa("SELECT user_id FROM admins WHERE training_done=0 AND tut_nudge_sent=0 AND blocked=0 "
              "AND user_id<>? AND created_at<=?", (OWNER_ID, now - TUT_NUDGE_AFTER))
    for r in rows:
        uid = r["user_id"]
        ex("UPDATE admins SET tut_nudge_sent=1 WHERE user_id=?", (uid,))
        m = await safe_send(context.bot, uid, tut_nudge_text(uid), html_mode=True)
        if m is not None:
            ex("UPDATE admins SET tut_nudge_msg=? WHERE user_id=?", (m.message_id, uid))
        await asyncio.sleep(0.05)


async def inactive_admins_job(context: ContextTypes.DEFAULT_TYPE):
    """حذف ادمین‌های بدون جذب: ۸ روز بعد از پایان آموزش و هشدار یک روز قبلش (یعنی هشدار بعد از ۷ روز)."""
    if bot_off():
        return  # وقت تعمیرات هشدار و حذفی در کار نیست
    now = int(time.time())
    rows = qa("SELECT * FROM admins WHERE training_done=1 AND total_count=0 AND user_id<>? "
              "AND NOT EXISTS (SELECT 1 FROM hires h WHERE h.admin_id=admins.user_id)", (OWNER_ID,))
    for a in rows:
        uid = a["user_id"]
        has_card = q1("SELECT 1 FROM cards WHERE admin_id=?", (uid,)) is not None
        t0 = a["training_done_at"]
        if t0 is None:  # ادمین‌های قدیمی که قبل از این قابلیت آموزش رو تموم کرده بودن
            if has_card:
                ex("UPDATE admins SET training_done_at=? WHERE user_id=?", (now, uid))
                continue
            t0 = 0
        limit = INACTIVE_CARD if has_card else INACTIVE_NO_CARD
        age = now - t0
        warned_at = int(a["warn_at"] or 0)
        if age >= limit - WARN_BEFORE and not warned_at:
            # هشدار حذف (فقط بین ۹ تا ۲۳)؛ حذف همیشه بعد از هشدار و حداقل ۲۴ ساعت فاصله انجام میشه
            if not in_notice_hours(now):
                continue
            ex("UPDATE admins SET warn_sent=1, warn_at=? WHERE user_id=?", (now, uid))
            m = await send_alert(context.bot, uid, WARN_TEXT, WARN_KB(), html_mode=True, secs=WARN_BEFORE)  # 🚨 + متن؛ تا زمان حذف از پاکسازی خودکار در امانن تا دکمه‌ش بمونه
            if m is None:
                _a2 = get_admin(uid)
                if _a2 is not None and not _a2["blocked"]:
                    ex("UPDATE admins SET warn_sent=0, warn_at=0 WHERE user_id=?", (uid,))  # ارسال نشد؛ دفعه‌ی بعد دوباره
        elif warned_at and age >= limit and now >= warned_at + WARN_BEFORE:
            if not remove_admin(uid):
                continue
            ex("INSERT OR REPLACE INTO comeback(user_id, removed_at, sent, back) VALUES(?,?,0,0)", (uid, now))
            await safe_send(context.bot, uid, REMOVED_TEXT, ReplyKeyboardRemove(), html_mode=False)
        elif age >= NUDGE_AFTER and not a["nudge_sent"] and a["training_done_at"] is not None and in_notice_hours(now):
            ex("UPDATE admins SET nudge_sent=1 WHERE user_id=?", (uid,))
            _nm = await safe_send(context.bot, uid, NUDGE_TEXT, NUDGE_KB(), html_mode=True)
            if _nm is None:
                _a2 = get_admin(uid)
                if _a2 is not None and not _a2["blocked"]:
                    ex("UPDATE admins SET nudge_sent=0 WHERE user_id=?", (uid,))  # ارسال نشد؛ دفعه‌ی بعد دوباره (مثل هشدار حذف)
            else:
                ex("UPDATE admins SET why_sent=1 WHERE user_id=?", (uid,))
                hold_notice(_nm, chat_id=uid, secs=86400)  # تا ۲۴ ساعت از پاکسازی خودکار در امانه تا دکمه‌ها بمونن
        elif (FIRST_AFTER <= age < NUDGE_AFTER and not a["first_sent"]
              and a["training_done_at"] is not None):
            ex("UPDATE admins SET first_sent=1 WHERE user_id=?", (uid,))
            await safe_send(context.bot, uid, FIRST_TEXT, html_mode=True)
    await stalled_admins_remind(context.bot, now)


async def nudge_why_catchup_job(context: ContextTypes.DEFAULT_TYPE):
    """یک بار برای ادمین‌های بدون جذبی که پیام ۲۴ ساعته رو بدون دکمه‌ها گرفته بودن، همون پیام با دکمه‌ها (فقط بین ۹ تا ۲۳)."""
    if bot_off():
        return
    now = int(time.time())
    if not in_notice_hours(now):
        return
    rows = qa("SELECT user_id FROM admins WHERE training_done=1 AND total_count=0 AND blocked=0 AND user_id<>? "
              "AND nudge_sent=1 AND why_sent=0 AND warn_at=0 "
              "AND NOT EXISTS (SELECT 1 FROM hires h WHERE h.admin_id=admins.user_id) "
              "AND NOT EXISTS (SELECT 1 FROM nudge_why w WHERE w.user_id=admins.user_id)", (OWNER_ID,))
    for r in rows:
        uid = r["user_id"]
        ex("UPDATE admins SET why_sent=1 WHERE user_id=?", (uid,))
        m = await safe_send(context.bot, uid, NUDGE_TEXT, NUDGE_KB(), html_mode=True)
        if m is None:
            _a2 = get_admin(uid)
            if _a2 is not None and not _a2["blocked"]:
                ex("UPDATE admins SET why_sent=0 WHERE user_id=?", (uid,))  # ارسال نشد؛ دفعه‌ی بعد دوباره
        else:
            hold_notice(m, chat_id=uid, secs=86400)
        await asyncio.sleep(0.05)


LEVEL_DROP_AFTER = 7 * 86400  # ادمین سطح‌دار (سطح ۲ و ۳) که ۷ روزه جذب نکرده


def _drop_amt(a: int) -> str:
    return f"{a // 1000} هزارتومان" if a % 1000 == 0 else f"{a:,} تومان"


_DROP_NAMES = {2: ("ادمین دو‌ستاره ⭐️⭐️", "ادمین تک‌ستاره ⭐️"),
               3: ("ادمین سه‌ستاره ⭐️⭐️⭐️", "ادمین دوستاره ⭐️⭐️")}


def level_drop_text(level: int) -> str:
    cur, low = _DROP_NAMES[min(max(level, 2), 3)]
    lv = min(max(level, 2), 3)
    head = ("•➖•➖•➖•➖•➖•➖•➖•➖\n"
            "<b>🚨 هشدار افت سطح ⚠️</b>\n"
            "➖•➖•➖•➖\n")
    if lv == 3:
        head += ("\n<b>همکار گرامی،</b>\n"
                 "۷ روزه که هیچ جذب جدیدی ثبت نکردی❗️\n\n")
    else:
        head += ("<b>همکار گرامی،</b>\n"
                 "۷ روزه که هیچ جذب جدیدی نداشتی❗️\n\n")
    return rl(
        head +
        f"⏳ اگه تا ۲۴ ساعت آینده جذب جدیدی ثبت نکنی، از سطح «{cur}»\n"
        f"به سطح «{low}» برمی‌گردی.\n\n"
        f"💰 درآمد هر دوره‌ت هم از {_drop_amt(level_amount(lv))} به {_drop_amt(level_amount(lv - 1))} کاهش پیدا میکنه❗️\n\n"
        "🃏 برای جذب سریع‌تر، از روش‌های بخش «تقلب‌ها» استفاده کن و سطحت رو حفظ کن.\n\n"
        "<b>سطحت رو از دست نده!</b> 🚀❤️\n"
        "➖•➖•➖•➖•➖•➖•➖•➖•➖"
    )


async def level_drop_warn_job(context: ContextTypes.DEFAULT_TYPE):
    """ادمین سطح‌دار (سطح ۲ به بالا) که ۷ روز از آخرین جذبش گذشته: یک‌بار «هشدار افت سطح» (فقط ۹ تا ۲۳).
    اگه بعد از افت هم جذب نکنه، ۷ روز بعد از افت دوباره هشدار میگیره و یک سطح دیگه افت میکنه (تا سطح ۱)."""
    if bot_off():
        return
    now = int(time.time())
    # افت واقعی سطح: ۲۴ ساعت از هشدار گذشته و از اون موقع جذب جدیدی ثبت نشده (ساعت‌محدودیت نداره؛ چیزی ارسال نمیشه)
    for a in qa("SELECT * FROM admins WHERE training_done=1 AND blocked=0 AND user_id<>? AND drop_warn_at>0 "
                "AND drop_warn_at>=COALESCE(last_hire_at,0) AND drop_done_at<drop_warn_at AND drop_warn_at<=?",
                (OWNER_ID, now - 86400)):
        old = level_of(a)
        if old < 2:
            ex("UPDATE admins SET drop_done_at=? WHERE user_id=?", (now, a["user_id"]))
            continue
        ex("UPDATE admins SET level_pen=level_pen+1, cur_amount=?, drop_done_at=? WHERE user_id=?",
           (level_amount(old - 1), now, a["user_id"]))
        audit(a["user_id"], "level_drop", f"{old}->{old - 1}")
    if not in_notice_hours(now):
        return
    rows = qa("SELECT user_id, period_no, level_pen FROM admins WHERE training_done=1 AND blocked=0 AND user_id<>? "
              "AND (MIN(period_no,3)-level_pen)>=2 AND last_hire_at IS NOT NULL "
              "AND MAX(last_hire_at,drop_done_at)<=? AND drop_warn_at<MAX(last_hire_at,drop_done_at)",
              (OWNER_ID, now - LEVEL_DROP_AFTER))  # مبنا: آخرین جذب یا آخرین افت (هرکدوم دیرتر)؛ بعد از افت دوباره ۷ روز
    for r in rows:
        uid = r["user_id"]
        ex("UPDATE admins SET drop_warn_at=? WHERE user_id=?", (now, uid))  # قبل از ارسال؛ با ریستارت دوباره نره
        m = await send_alert(context.bot, uid, level_drop_text(level_of(r)), WARN_KB(),
                             html_mode=True, secs=86400)
        if m is None:
            _a2 = get_admin(uid)
            if _a2 is not None and not _a2["blocked"]:
                ex("UPDATE admins SET drop_warn_at=0 WHERE user_id=?", (uid,))  # ارسال نشد؛ دفعه‌ی بعد دوباره
        await asyncio.sleep(0.05)


async def stalled_admins_remind(bot, now: int) -> None:
    """ادمینی که جذب داشته و دوره‌ش تموم نشده ولی ۲ روزه جذب نکرده: «N جذب دیگه تا پورسانت» (هفته‌ای یک بار، فقط روزها)."""
    hour = datetime.fromtimestamp(now, TZ).hour
    if not (STALL_HOURS[0] <= hour < STALL_HOURS[1]):
        return
    rows = qa("SELECT user_id, period_count, cur_target FROM admins "
              "WHERE training_done=1 AND blocked=0 AND user_id<>? AND period_count>=1 AND period_count<cur_target "
              "AND COALESCE(last_hire_at,0)<=? AND stall_sent_at<=? AND COALESCE(noact_sent_at,0)<=?",
              (OWNER_ID, now - STALL_AFTER, now - STALL_EVERY, now - NOACT_AFTER_STALL))  # اطلاعیه‌ی ۲ روز بدون جذب تازه رفته؟ ۳ ساعت بعدش میاد
    for r in rows:
        ex("UPDATE admins SET stall_sent_at=? WHERE user_id=?", (now, r["user_id"]))
        text = STALL_TEXT.format(left=r["cur_target"] - r["period_count"], period=r["period_count"],
                                 target=r["cur_target"])
        await safe_send(bot, r["user_id"], text, html_mode=True)
        await asyncio.sleep(0.05)


async def on_business_update(update: Update, context):
    if update.business_message is not None:
        try:
            await on_business(update, context)
        except Exception as e:  # noqa
            log_err(f"business: {e!r}")


async def del_pin_service(update: Update, context):
    """پیام سرویس تلگرام «... پیام را پین کرد» همون لحظه پاک میشه."""
    m = update.effective_message
    if m is not None:
        try:
            await m.delete()
        except TelegramError as e:
            log_err(f"delete pin service msg failed: {e!r}")


def build_app() -> Application:
    patch_send_tracking()
    app = (Application.builder().token(BOT_TOKEN).post_init(start_user_session)
           .concurrent_updates(True).build())
    BOT_REF["bot"] = app.bot
    app.add_handler(TypeHandler(Update, track_activity), group=-1)
    app.add_handler(CommandHandler("start", cmd_start, filters=filters.ChatType.PRIVATE))
    app.add_handler(CallbackQueryHandler(on_callback))
    app.add_handler(MessageHandler(filters.ChatType.PRIVATE & filters.StatusUpdate.PINNED_MESSAGE, del_pin_service))
    app.add_handler(MessageHandler(filters.UpdateType.CHANNEL_POST & filters.Document.ALL, finder_file_post))
    app.add_handler(MessageHandler(filters.ChatType.PRIVATE & filters.UpdateType.MESSAGE, on_message))
    app.add_handler(TypeHandler(Update, on_business_update), group=1)
    app.add_error_handler(on_error)
    if app.job_queue is not None:
        app.job_queue.run_repeating(housekeeping_job, interval=10, first=10)
        app.job_queue.run_repeating(auto_clean_job, interval=10, first=15)
        app.job_queue.run_repeating(inactive_admins_job, interval=300, first=45)
        app.job_queue.run_repeating(tut_nudge_job, interval=300, first=60)
        app.job_queue.run_repeating(nudge_why_catchup_job, interval=300, first=90)
        app.job_queue.run_repeating(comeback_job, interval=300, first=75)
        app.job_queue.run_repeating(no_recruit_notice_job, interval=300, first=75)
        app.job_queue.run_repeating(level_drop_warn_job, interval=300, first=105)
        app.job_queue.run_repeating(weekly_levels_job, interval=1800, first=90)
        app.job_queue.run_repeating(daily_backup_job, interval=60, first=120)
        app.job_queue.run_repeating(stats_job, interval=60, first=100)
        app.job_queue.run_repeating(questions_export_job, interval=3600, first=180)
        app.job_queue.run_repeating(cheat_job, interval=30, first=35)
        app.job_queue.run_once(purge_notice_job, 15)
        app.job_queue.run_once(reset_notice_job, 20)
        app.job_queue.run_once(media_check_job, 30)
    else:
        log.warning("JobQueue فعال نیست (pip install 'python-telegram-bot[job-queue]'); اعلان مهلت پرداخت کار نمی‌کند.")
    return app

# ---------------------- ارسال خودکار از اکانت شخصی ----------------------
AUTO_DELAY_MIN = 60        # همه‌ی پاسخ‌های خودکار (۹ پیام، ثبت‌نام، ویدیو) بین ۱ تا ۳ دقیقه‌ی رندوم بعد میرن
AUTO_DELAY_MAX = 180
AUTO_HOURLY_CAP = 40       # حداکثر تعداد آدم‌هایی که توی هر ساعت «۹ پیام» می‌گیرن؛ بقیه توی صف می‌مونن و به‌ترتیب نوبتشون میرسه


def auto_delay() -> int:
    return random.randint(AUTO_DELAY_MIN, AUTO_DELAY_MAX)
AUTO_CONF_DELAY_MIN = 10   # ویدیوی شروع بعد از «تایید شرایط» (راه جایگزین): بین ۱۰ تا ۶۰ ثانیه‌ی رندوم
AUTO_CONF_DELAY_MAX = 60


def auto_conf_delay() -> int:
    return random.randint(AUTO_CONF_DELAY_MIN, AUTO_CONF_DELAY_MAX)
CATCHUP_MAX = 48 * 3600  # بعد از خاموشی، پیام‌های حداکثر ۴۸ ساعت اخیر بررسی میشن
AUTO_MAX_AGE = 7 * 86400   # فقط چت‌هایی که اولین پیامشون تازه‌ست
AUTO_ALT_TRIGGER = "🔹 راه جایگزین شما:"
AUTO_VIDEO_TRIGGER = "تایید استخدام"
AUTO_FLAGS = ("auto_9", "auto_reg", "auto_alt", "auto_vid")
_auto_task = None


def _aw(t: str) -> str:
    """نرمال‌سازی کلمه‌های کلیدی: بدون فاصله، نیم‌فاصله، علامت و ایموجی؛ ی و ک فارسی؛ همزه حذف."""
    t = unicodedata.normalize("NFKD", t or "").replace("ي", "ی").replace("ك", "ک")
    return "".join(ch for ch in t if ch.isalnum()).lower()


def _auto_json(key: str) -> list:
    try:
        v = json.loads(get_setting(key) or "[]")
    except ValueError:
        return []
    return [x for x in v if isinstance(x, str) and x.strip()] if isinstance(v, list) else []


def _auto_row(uid: int):
    return q1("SELECT * FROM auto_chat WHERE user_id=?", (uid,))


def _auto_claim(col: str, uid: int, val: int = 1) -> bool:
    """فقط یک بار موفق میشه (جلوی ارسال دوباره‌ی یک مرحله رو میگیره)."""
    with tx() as c:
        return c.execute(f"UPDATE auto_chat SET {col}=? WHERE user_id=? AND {col}=0", (val, uid)).rowcount > 0


def _auto_peer(uid: int):
    r = _auto_row(uid)
    if r is not None and r["access_hash"]:
        return InputPeerUser(uid, r["access_hash"])
    return uid


def _auto_touch(uid: int, peer=None) -> None:
    """برای چتی که ردیفی نداره (مثلاً با کلمه‌ی خودت شروع شد) ردیف می‌سازه؛ مراحل قبلی انجام‌شده حساب میشن."""
    ex("INSERT OR IGNORE INTO auto_chat(user_id,first_ts,access_hash,nine_sent) VALUES(?,?,?,1)",
       (uid, int(time.time()), int(getattr(peer, "access_hash", 0) or 0)))


async def _auto_try(make):
    for _ in range(3):
        try:
            return await make()
        except FloodWaitError as e:
            await asyncio.sleep(min(e.seconds + 1, 60))
    return await make()


async def _auto_ack(peer, upto: int = 0, everything: bool = False) -> None:
    """everything=True: کل چت خونده میشه (مرحله‌ی ۹ پیام؛ پیام اول طرف حتی اگه سوال باشه آنرید نمی‌مونه).
    وگرنه فقط تا پیامِ محرک (مثلاً «شروع») خونده میشه و هر پیام بعدیِ طرف (مثل سوال) آنرید می‌مونه.
    اگه شناسه‌ای نباشه (upto=0) و everything هم نباشه، هیچ چیزی خونده نمیشه."""
    if not upto and not everything:
        return
    try:
        if everything:
            await _auto_try(lambda: SESSION_CLIENT.send_read_acknowledge(peer))
        else:
            await _auto_try(lambda: SESSION_CLIENT.send_read_acknowledge(peer, max_id=int(upto)))
    except Exception as e:  # noqa
        log_err(f"auto ack: {e!r}")


def _bio(data: bytes, name: str):
    f = io.BytesIO(bytes(data))
    f.name = name
    return f


async def auto_send_texts(uid: int) -> int:
    items = _auto_json("auto_msgs")
    peer = _auto_peer(uid)
    for t in items:
        await _auto_try(lambda t=t: SESSION_CLIENT.send_message(peer, t, parse_mode="html"))
    await _auto_ack(peer, everything=True)  # سیستم آنرید برای پیام اول نیست: چت کامل خونده میشه
    shield_owner_replied(uid)  # سپر: ۹ پیام خودکار هم «جواب کارفرما» حساب میشه (به رویداد پیام خروجی وابسته نیست)
    return len(items)


async def auto_send_reg(uid: int) -> None:
    peer = _auto_peer(uid)
    _r = _auto_row(uid)
    upto = int(_r["ack_shoro"] or 0) if _r is not None else 0
    cap = get_setting("auto_reg_html")
    m = q1("SELECT data, ext FROM auto_media WHERE key='reg_photo'")
    if m is not None and m["data"]:
        await _auto_try(lambda: SESSION_CLIENT.send_file(peer, _bio(m["data"], f"photo.{m['ext'] or 'jpg'}"),
                                                         caption=cap, parse_mode="html"))
    else:
        await _auto_try(lambda: SESSION_CLIENT.send_message(peer, cap, parse_mode="html"))
    await _auto_ack(peer, upto)
    shield_owner_replied(uid)


async def auto_send_alt(peer) -> bool:
    alt = get_setting("auto_alt_html")
    if not alt:
        return False
    await _auto_try(lambda: SESSION_CLIENT.send_message(peer, alt, parse_mode="html"))  # تو خودت تو چتی؛ چیزی خونده نمیشه
    return True


SAVED_TTL = 30  # ثانیه؛ تغییر توی Saved Messages حداکثر تا نیم دقیقه بعد اعمال میشه
_saved_cache = {"ts": 0.0, "video": None, "text": None}
_SAVED_VID = {"ok": False}
_saved_lock = asyncio.Lock()


def _is_video_msg(m) -> bool:
    if m is None or getattr(m, "media", None) is None:
        return False
    d = getattr(m, "document", None)
    return bool(getattr(m, "video", None) or (d is not None and (d.mime_type or "").startswith("video")))


async def saved_pair():
    """آخرین ویدیوی Saved Messages = ویدیو، و پیامِ متنیِ بلافاصله بعدش = کپشن.
    (پیام جدید همیشه ته چت میاد؛ پس ویدیو رو بذار و بعدش فوراً متنش رو بفرست.)
    نتیجه ۳۰ ثانیه کش میشه تا با چند نفر همزمان، تلگرام یک بار پرسیده بشه."""
    if time.monotonic() - _saved_cache["ts"] < SAVED_TTL:
        return _saved_cache["video"], _saved_cache["text"]
    async with _saved_lock:
        if time.monotonic() - _saved_cache["ts"] < SAVED_TTL:
            return _saved_cache["video"], _saved_cache["text"]
        if SESSION_CLIENT is None or not SESSION_CLIENT.is_connected():
            return None, None
        try:
            v = None
            found = await SESSION_CLIENT.get_messages("me", limit=1, filter=InputMessagesFilterVideo)
            if found and _is_video_msg(found[0]):
                v = found[0]
            else:  # ویدیویی که به‌صورت فایل فرستاده شده
                async for m in SESSION_CLIENT.iter_messages("me", limit=300):
                    if _is_video_msg(m):
                        v = m
                        break
            t = None
            if v is not None:
                nxt = await SESSION_CLIENT.get_messages("me", limit=1, min_id=v.id, reverse=True)
                if nxt and nxt[0].media is None and (nxt[0].message or "").strip():
                    t = nxt[0]
        except Exception as e:  # noqa
            log_err(f"saved_pair: {e!r}")
            return _saved_cache["video"], _saved_cache["text"]
        _saved_cache.update(ts=time.monotonic(), video=v, text=t)
        _SAVED_VID["ok"] = v is not None
        return v, t


_sv_wait = {"fut": None}
_sv_task = None


async def saved_video_sync_loop(bot) -> None:
    """ویدیوی آموزشی (دکمه‌ی «دریافت ویدیو آموزشی» و مسیر آموزش) از همون ویدیوی اولِ Saved Messages ساخته میشه:
    اکانت شخصی ویدیو رو یک بار برای ربات میفرسته، ربات شناسه‌ی فایل رو ذخیره میکنه و پیام رو پاک میکنه.
    فقط وقتی ویدیوی Saved Messages عوض بشه دوباره انجام میشه؛ ارسال به ادمین‌ها بعدش بدون آپلود و بدون سقف ۲۰ مگ."""
    me_ok = None
    retry_at = 0.0
    while True:
        try:
            await asyncio.sleep(20)
            if SESSION_CLIENT is None or not SESSION_CLIENT.is_connected() or time.monotonic() < retry_at:
                continue
            if me_ok is None:
                me = await SESSION_CLIENT.get_me()
                me_ok = bool(me and me.id == OWNER_ID)
                if not me_ok:
                    log_err("saved_video_sync: اکانت شخصی همون OWNER_ID نیست؛ همگام‌سازی ویدیوی آموزشی خاموش شد")
            if not me_ok:
                return
            sv, _t = await saved_pair()
            if sv is None:
                continue
            key = f"{sv.id}:{getattr(getattr(sv, 'document', None), 'id', 0)}"
            if get_setting("saved_vid_key") == key and get_setting("video_file_id"):
                continue
            fut = asyncio.get_running_loop().create_future()
            _sv_wait["fut"] = fut
            try:
                uname = (await bot.get_me()).username
                sent = await SESSION_CLIENT.send_file(uname, sv.media)
                fid, kind, mid = await asyncio.wait_for(fut, 90)
            finally:
                _sv_wait["fut"] = None
            set_setting("video_file_id", fid)
            set_setting("video_kind", kind)
            set_setting("saved_vid_key", key)
            for _d in (lambda: bot.delete_message(OWNER_ID, mid), lambda: sent.delete()):
                try:
                    await _d()
                except Exception:  # noqa
                    pass
        except asyncio.CancelledError:
            raise
        except Exception as e:  # noqa
            log_err(f"saved_video_sync: {e!r}")
            retry_at = time.monotonic() + 300  # اگه نشد، ۵ دقیقه بعد دوباره


AUTO_SHORO_TEXT = (
    "این ویدیو، آموزش صفر تا صد ادمینی\n"
    "در تیم جذبان هست دوست عزیز!\n\n"
    "لطفا ویدیو رو به‌طور کامل و با دقت تماشا کنید. سپس، طبق آموزش‌های ارائه‌شده، "
    "در صورت تمایل می‌تونید فعالیت خودتون رو از همین امروز در تیم جذبان شروع کنید.\n\n"
    "آیدی ربات 👈 @JAZBANBOT 👉\n\n"
    "به امید یک همکاری خوب و درخشان! 🌱"
)  # متنِ پشت ویدیو وقتی «متن ثبت‌نام» خاموشه و مشتری «شروع» گفته


async def auto_send_video(peer, text_html: str = None, upto: int = 0) -> bool:
    ok = await _auto_send_video(peer, text_html)
    if ok:
        await _auto_ack(peer, upto)
    return ok


async def _auto_send_video(peer, text_html: str = None) -> bool:
    """ویدیوی شروع + متن پشتش. اگه text_html داده بشه، به‌جای متن همراه ویدیو همون میره."""
    try:
        sv, st = await saved_pair()
    except Exception as e:  # noqa
        log_err(f"auto saved video: {e!r}")
        sv = st = None
    if sv is not None:  # ویدیو و متن از Saved Messages؛ بدون دانلود و آپلود دوباره (فایل بزرگ هم مشکلی نداره)
        ok = False
        try:
            await _auto_try(lambda: SESSION_CLIENT.send_file(peer, sv.media, supports_streaming=True))
            ok = True
        except Exception as e:  # noqa
            log_err(f"auto send saved video: {e!r}")
        if ok:
            if text_html is not None:
                try:
                    await _auto_try(lambda: SESSION_CLIENT.send_message(peer, text_html, parse_mode="html"))
                except Exception as e:  # noqa
                    log_err(f"auto send custom text: {e!r}")
            elif st is not None:
                try:
                    await _auto_try(lambda: SESSION_CLIENT.send_message(peer, st.message,
                                                                        formatting_entities=st.entities))
                except Exception as e:  # noqa
                    log_err(f"auto send saved text: {e!r}")
            return True
    m = q1("SELECT data, ext, meta FROM auto_media WHERE key='video'")
    if m is None or not m["data"]:
        return False
    try:
        meta = json.loads(m["meta"] or "{}")
    except ValueError:
        meta = {}
    attrs = [DocumentAttributeVideo(duration=int(meta.get("d") or 0), w=int(meta.get("w") or 0),
                                    h=int(meta.get("h") or 0), supports_streaming=True)]
    cap = text_html if text_html is not None else get_setting("auto_vid_html")
    await _auto_try(lambda: SESSION_CLIENT.send_file(peer, _bio(m["data"], f"video.{m['ext'] or 'mp4'}"),
                                                     attributes=attrs, supports_streaming=True))
    if cap:  # متن، جدا و پشت‌بندِ ویدیو
        await _auto_try(lambda: SESSION_CLIENT.send_message(peer, cap, parse_mode="html"))
    return True


def auto_apply_cut(uid: int) -> bool:
    """کسی که «تایید» گفته و ادمین شده (هنوز توی دوره‌ی اول): پورسانت این دوره‌ش ۱۰۰ هزار کمتر میشه."""
    with tx() as c:
        ac = c.execute("SELECT confirmed, cut FROM auto_chat WHERE user_id=?", (uid,)).fetchone()
        if ac is None or not ac["confirmed"] or ac["cut"]:
            return False
        a = c.execute("SELECT * FROM admins WHERE user_id=?", (uid,)).fetchone()
        if a is None or a["period_no"] != 1:
            return False
        c.execute("UPDATE admins SET cur_amount=? WHERE user_id=?", (max(a["cur_amount"] - AUTO_CUT, 0), uid))
        c.execute("UPDATE auto_chat SET cut=1, cut_from=? WHERE user_id=?", (a["cur_amount"], uid))
    audit(OWNER_ID, "auto_cut", json.dumps({"user_id": uid}))
    return True


def auto_notice_text(old: int, new: int) -> str:
    return ("<b>📌 یه نکته‌ی کوچیک 📌</b>\n\n"
            "چون در ابتدا شما انتخاب کردید که در سایت ثبت‌نام نکنید و به‌جاش اون مبلغ از اولین حقوقتون کم بشه، "
            "این دوره به‌جای:\n\n"
            f"<b>({fmt_en(old)} تومان) ← ({fmt_en(new)} تومان)</b> پورسانت دریافت می‌کنید!\n\n"
            "اما از دوره‌های بعدی، پورسانت شما طبق سطحی که داخلش هستید، <b>کامل پرداخت می‌شه</b> 🌷")


async def _auto_is_new_ex(sender):
    """مثل _auto_is_new ولی سه‌حالته: True/False؛ و None یعنی خطای موقت موقع خوندن تاریخچه (نباید برچسب دائمی بخوره)."""
    if getattr(sender, "bot", False) or sender.id == OWNER_ID:
        return False
    if getattr(sender, "contact", False) or getattr(sender, "mutual_contact", False):
        return False
    if q1("SELECT 1 FROM admins WHERE user_id=?", (sender.id,)):
        return False
    hist = None
    for _try in range(2):  # یک بار تلاش دوباره برای خطای لحظه‌ای
        try:
            hist = await SESSION_CLIENT.get_messages(sender, limit=50)
            break
        except FloodWaitError as e:
            log_err(f"auto history flood: {e!r}")
            return None
        except Exception as e:  # noqa
            log_err(f"auto history: {e!r}")
            if _try == 0:
                await asyncio.sleep(1)
    if hist is None:
        return None
    if len(hist) >= 50 or any(getattr(h, "out", False) for h in hist):
        return False
    old = min((h.date for h in hist), default=None)
    return old is None or time.time() - old.timestamp() <= AUTO_MAX_AGE


async def _auto_is_new(sender) -> bool:
    """اولین پیامِ یک آدم تازه: ربات/خودت/مخاطب/ادمین نباشه و تو قبلاً توی اون چت چیزی نفرستاده باشی."""
    return bool(await _auto_is_new_ex(sender))


async def auto_on_incoming(sender, text: str, bot=None, msg_id: int = 0, catchup: bool = False) -> None:
    if not any(get_setting(k) == "1" for k in AUTO_FLAGS):
        return
    uid = sender.id
    now = int(time.time())
    row = _auto_row(uid)
    if row is None:
        if not await _auto_is_new(sender):
            return
        nine_on = get_setting("auto_9") == "1"
        ex("INSERT OR IGNORE INTO auto_chat(user_id,first_ts,access_hash,nine_at,nine_sent,ack_nine) VALUES(?,?,?,?,?,?)",
           (uid, now, int(getattr(sender, "access_hash", 0) or 0),
            now + auto_delay() if nine_on else None, 0 if nine_on else 1, int(msg_id or 0)))
        return
    w = _aw(text)
    if not w:
        return
    # بعد از خاموشی: اگه «شروع» اومده ولی ۹ پیام هنوز نرفته، بعد از ۹ پیام جواب میره (نه قبلش)
    _nine_ok = bool(row["nine_sent"]) or (catchup and row["nine_at"] is not None and get_setting("auto_9") == "1")
    if (_nine_ok and not row["reg_sent"] and row["shoro_at"] is None and w.startswith("شروع")
            and len(w) <= 12 and (get_setting("auto_reg") == "1" or get_setting("auto_vid") == "1")):
        _at = now + auto_delay()
        if not row["nine_sent"] and row["nine_at"]:
            _at = max(_at, int(row["nine_at"]) + auto_delay())
        ex("UPDATE auto_chat SET shoro_at=?, ack_shoro=? WHERE user_id=?", (_at, int(msg_id or 0), uid))
        return
    if row["alt_sent"] and not row["confirmed"] and (w == "تایید" or w.startswith("تاییدشرایط")):
        ex("UPDATE auto_chat SET confirmed=1, ack_conf=? WHERE user_id=?", (int(msg_id or 0), uid))
        auto_apply_cut(uid)
        # «تایید شرایط» خودش موافقت صریحه؛ ویدیوی شروع بین ۱۰ تا ۶۰ ثانیه بعد خودکار میره (فقط یک بار برای هر آدم)
        # (اگه تو خودت «تایید استخدام» رو بفرستی، همون موقع درجا میره و این ارسال دیگه تکرار نمیشه)
        if get_setting("auto_vid") == "1":
            ex("UPDATE auto_chat SET vid_at=? WHERE user_id=? AND video_sent=0", (now + auto_conf_delay(), uid))


async def auto_on_outgoing(event, bot) -> None:
    """کلمه‌های ثابتِ خودت توی چت: «🔹 راه جایگزین شما:» و «تایید استخدام»."""
    # اگه خودت قبل از رسیدن ۲ دقیقه به اون آدم پیام دادی، ۹ متنِ خودکار دیگه نمیره
    ex("UPDATE auto_chat SET nine_sent=2 WHERE user_id=? AND nine_sent=0", (event.chat_id,))
    w = _aw(event.raw_text or "")
    if not w:
        return
    if w == _aw(AUTO_ALT_TRIGGER):
        if get_setting("auto_alt") != "1":
            return
        peer = await event.get_input_chat()
        _auto_touch(event.chat_id, peer)
        await asyncio.sleep(0.7)
        if await auto_send_alt(peer):
            ex("UPDATE auto_chat SET alt_sent=1 WHERE user_id=?", (event.chat_id,))
    elif w == _aw(AUTO_VIDEO_TRIGGER):
        if get_setting("auto_vid") != "1":
            return
        if q1("SELECT 1 FROM auto_media WHERE key='video'") is None and (await saved_pair())[0] is None:
            try:
                await bot.send_message(OWNER_ID, fb("⚠️ ویدیوی شروع ثبت نشده؛ از تنظیمات پیشرفته ← ارسال خودکار ثبتش کن."), parse_mode=H)
            except Exception:  # noqa
                pass
            return
        peer = await event.get_input_chat()
        _auto_touch(event.chat_id, peer)
        try:
            await event.delete()
        except Exception as e:  # noqa
            log_err(f"auto delete trigger: {e!r}")
        if await auto_send_video(peer):
            ex("UPDATE auto_chat SET video_sent=1 WHERE user_id=?", (event.chat_id,))


async def auto_loop(bot=None) -> None:
    """هر ۱۰ ثانیه ارسال‌های زمان‌دار (هر دو ۲ دقیقه) رو چک میکنه؛ زمان‌بندی توی دیتابیسه و با ریستارت از بین نمیره."""
    last_beat = 0
    while True:
        try:
            await asyncio.sleep(10)
            if SESSION_CLIENT is None or not SESSION_CLIENT.is_connected():
                continue
            now = int(time.time())
            if now - last_beat >= 30:
                set_setting("auto_alive", now)
                last_beat = now
            try:
                await saved_pair()  # وضعیت ویدیوی Saved Messages برای منوی ارسال خودکار؛ خطاش هیچ‌وقت ارسال‌ها رو متوقف نمیکنه
            except Exception as e:  # noqa
                log_err(f"auto loop saved_pair: {e!r}")
            _cap_left = AUTO_HOURLY_CAP - q1("SELECT COUNT(*) n FROM auto_chat WHERE nine_sent=1 AND nine_at>?",
                                             (now - 3600,))["n"]
            for r in qa("SELECT user_id, nine_at FROM auto_chat WHERE nine_sent=0 AND nine_at IS NOT NULL "
                        "AND nine_at<=? ORDER BY nine_at", (now,)):
                if get_setting("auto_9") != "1":
                    if now - r["nine_at"] > 3600:
                        _auto_claim("nine_sent", r["user_id"], 2)  # خاموش بود؛ دیگه کهنه شده
                    continue
                if _cap_left <= 0:
                    break  # سقف ساعتی پر شده؛ بقیه توی صف می‌مونن
                if _auto_claim("nine_sent", r["user_id"]):
                    _cap_left -= 1
                    ex("UPDATE auto_chat SET nine_at=? WHERE user_id=?", (int(time.time()), r["user_id"]))  # زمان واقعی ارسال
                    try:
                        await auto_send_texts(r["user_id"])
                    except Exception as e:  # noqa
                        log_err(f"auto nine {r['user_id']}: {e!r}")
            for r in qa("SELECT user_id, vid_at FROM auto_chat WHERE video_sent=0 AND vid_at IS NOT NULL "
                        "AND vid_at<=?", (now,)):
                if get_setting("auto_vid") != "1":
                    if now - r["vid_at"] > 3600:
                        ex("UPDATE auto_chat SET vid_at=NULL WHERE user_id=?", (r["user_id"],))  # خاموش بود؛ کهنه شد
                    continue
                if _auto_claim("video_sent", r["user_id"]):
                    ex("UPDATE auto_chat SET vid_at=NULL WHERE user_id=?", (r["user_id"],))
                    try:
                        _r = _auto_row(r["user_id"])
                        ok = await auto_send_video(_auto_peer(r["user_id"]), None, int(_r["ack_conf"] or 0) if _r is not None else 0)
                    except Exception as e:  # noqa
                        log_err(f"auto video {r['user_id']}: {e!r}")
                        ok = False
                    if not ok:
                        ex("UPDATE auto_chat SET video_sent=0 WHERE user_id=?", (r["user_id"],))
                        try:
                            if bot is not None:
                                await bot.send_message(OWNER_ID, fb("⚠️ یه نفر «تایید شرایط» رو فرستاد ولی ویدیوی شروع ارسال نشد (ثبت نشده یا خطا)؛ "
                                                                 "از تنظیمات پیشرفته ← ارسال خودکار ثبتش کن و بعد `تایید استخدام` رو براش بفرست."), parse_mode=H)
                        except Exception:  # noqa
                            pass
            for r in qa("SELECT user_id, shoro_at FROM auto_chat WHERE reg_sent=0 AND shoro_at IS NOT NULL "
                        "AND shoro_at<=?", (now,)):
                reg_on = get_setting("auto_reg") == "1"
                vid_on = get_setting("auto_vid") == "1"
                if not reg_on and not vid_on:
                    if now - r["shoro_at"] > 3600:
                        _auto_claim("reg_sent", r["user_id"], 2)
                    continue
                if _auto_claim("reg_sent", r["user_id"]):
                    if reg_on:
                        try:
                            await auto_send_reg(r["user_id"])
                        except Exception as e:  # noqa
                            log_err(f"auto reg {r['user_id']}: {e!r}")
                    elif _auto_claim("video_sent", r["user_id"]):
                        # متن ثبت‌نام خاموشه: بعد از «شروع»، ویدیوی شروع (با متن زیرش) میره
                        try:
                            _r = _auto_row(r["user_id"])
                            ok = await auto_send_video(_auto_peer(r["user_id"]), AUTO_SHORO_TEXT,
                                                       int(_r["ack_shoro"] or 0) if _r is not None else 0)
                        except Exception as e:  # noqa
                            log_err(f"auto video(shoro) {r['user_id']}: {e!r}")
                            ok = False
                        if not ok:
                            ex("UPDATE auto_chat SET video_sent=0 WHERE user_id=?", (r["user_id"],))
                            try:
                                if bot is not None:
                                    await bot.send_message(OWNER_ID, fb("⚠️ یه نفر «شروع» رو فرستاد ولی ویدیوی شروع ارسال نشد (ثبت نشده یا خطا)؛ "
                                                                     "از تنظیمات پیشرفته ← ارسال خودکار ثبتش کن."), parse_mode=H)
                            except Exception:  # noqa
                                pass
        except asyncio.CancelledError:
            raise
        except Exception as e:  # noqa
            log_err(f"auto loop: {e!r}")


def auto_menu():
    n9 = len(_auto_json("auto_msgs"))
    reg_photo = q1("SELECT 1 FROM auto_media WHERE key='reg_photo'") is not None
    vid = q1("SELECT 1 FROM auto_media WHERE key='video'") is not None or _SAVED_VID["ok"]

    def tg(key: str, label: str):
        return onoff_btn(label, get_setting(key) == "1", f"o:au:t:{key}")

    def row(ok: bool, label: str) -> str:
        return f"{'✅' if ok else '❎'} |{label}: {'ثبت شده' if ok else 'ثبت نشده'}"

    sep = "➖•➖•➖•➖•➖•➖•➖•➖"
    text = (f"<b>{sep}\nAUTO SEND 🤖 | ارسال خودکار\n{sep}</b>\n"
            f"{row(bool(n9), '۹ پیام شروع')}\n"
            f"{row(bool(get_setting('auto_reg_html')), 'متن ثبت‌نام')}\n"
            f"{row(bool(get_setting('auto_alt_html')), 'راه جایگزین')}\n"
            f"{row(bool(vid), 'ویدیو شروع')}\n"
            f"<b>{sep}</b>")
    kb = KB(
        tg("auto_9", "ارسال ۹ پیام"),
        tg("auto_reg", "ارسال متن ثبت نام"),
        tg("auto_alt", "ارسال راه جایگزین"),
        tg("auto_vid", "ارسال ویدیو شروع"),
        B("✏️ ویرایش ✏️", "o:au:ed", style="primary"),
        BACK("o:adv"),
    )
    return text, kb


def auto_edit_menu():
    show_vid_btn = get_setting("auto_vid_btn") == "1"
    kb = KB(
        B("✏️ ویرایش ۹ پیام ✏️", "o:au:e9", style="primary"),
        B("✏️ ویرایش متن ثبت نام ✏️", "o:au:er", style="primary"),
        B("✏️ ویرایش راه جایگزین ✏️", "o:au:ea", style="primary"),
        *([B("📤 ثبت یا تعویض ویدیو شروع 📤", "o:au:ev", style="danger"),
           B("🗑️ حذف دکمه ویدیو 🗑️", "o:au:dv", style="danger")] if show_vid_btn
          else [B("➕ نمایش دکمه ویدیو ➕", "o:au:sv", style="danger")]),
        BACK("o:au"),
    )
    return fbox("ویرایش ✏️ EDIT", "کدوم رو می‌خوای ویرایش کنی؟"), kb


# ---------------------- کانال‌یاب (پیدا کردن کانال‌های پرکامنت) ----------------------
FINDER_BOT = "SemagramBot"
FINDER_MIN_POSTS = 8          # حداقل پست در ۲۴ ساعت اخیر (تقریبا هر ۳ ساعت یک پست)
FINDER_MAX_GAP = 6 * 3600     # بیشترین فاصله‌ی مجاز بین دو پست پشت‌سرهم (ثانیه)
FINDER_MIN_COMMENTS = 200     # حداقل کامنت در یک ساعت اولِ هر پست
FINDER_VERIFY_POSTS = 3       # چند پست اخیر دونه‌دونه بررسی میشن (همه باید رد بشن)
FINDER_HOURS = (8, 24)        # فقط توی این ساعت‌ها (به وقت TZ_NAME) جستجو میکنه
FINDER_WORD_GAP = (40, 90)    # فاصله‌ی رندوم بین دو کلمه (ثانیه)
FINDER_CH_GAP = (4, 9)        # فاصله‌ی رندوم بین بررسی دو کانال (ثانیه)
FINDER_IGNORE_CHATS = set()   # چت ربات جستجو؛ ارسال خودکار و سپر اون رو نادیده میگیرن
_finder_task = None
_finder_ent = None
_finder_fail = {}
_FD_USER = re.compile(r"@([A-Za-z][A-Za-z0-9_]{3,31})")
_FD_SUBS = re.compile(r"\(([\d\s,.\u202f\u00a0]+?)\s*subscribers", re.I)


def finder_tables():
    ex("CREATE TABLE IF NOT EXISTS finder_words(id INTEGER PRIMARY KEY AUTOINCREMENT, word TEXT UNIQUE, "
       "done INTEGER NOT NULL DEFAULT 0, found INTEGER NOT NULL DEFAULT 0, done_at INTEGER)")
    ex("CREATE TABLE IF NOT EXISTS finder_seen(username TEXT PRIMARY KEY, ok INTEGER NOT NULL DEFAULT 0, "
       "checked_at INTEGER)")


def finder_enabled() -> bool:
    return get_setting("finder_on") != "0"


def finder_parse(text: str):
    """خروجی ربات جستجو: فقط خط‌هایی که [channel] دارن؛ (یوزرنیم، عنوان، تعداد عضو)."""
    out = []
    for line in (text or "").splitlines():
        if "[channel]" not in line.lower():
            continue
        m = _FD_USER.search(line)
        if not m:
            continue
        subs = _FD_SUBS.search(line)
        n = int(re.sub(r"\D", "", subs.group(1)) or 0) if subs else 0
        title = re.split(r"\[channel\]", line, flags=re.I)[0][m.end():].lstrip(": ").strip()
        out.append((m.group(1), title, n))
    return out


async def finder_ask(client, word: str):
    global _finder_ent
    if _finder_ent is None:
        _finder_ent = await client.get_entity(FINDER_BOT)
        FINDER_IGNORE_CHATS.add(_finder_ent.id)
    ent = _finder_ent
    sent = await client.send_message(ent, word)
    deadline = time.time() + 45

    async def read():
        msgs = await client.get_messages(ent, limit=6, min_id=sent.id)
        return finder_parse("\n".join((x.raw_text or "") for x in reversed(msgs) if not x.out))

    while time.time() < deadline:
        await asyncio.sleep(3)
        items = await read()
        if items:
            await asyncio.sleep(3)  # اگه ربات پیامش رو ادیت کرد
            return (await read()) or items
    return []


async def finder_hour_count(client, ent, post) -> int:
    limit = post.date + timedelta(hours=1)
    n = 0
    async for c in client.iter_messages(ent, reply_to=post.id, reverse=True, limit=FINDER_MIN_COMMENTS):
        if c.date > limit:
            break
        n += 1
    return n


async def finder_check(client, uname: str):
    """(قبول شد؟، عنوان کانال)"""
    ent = await client.get_entity(uname)
    title = getattr(ent, "title", "") or uname
    if not getattr(ent, "broadcast", False):
        return False, title
    now = datetime.now(TZ)
    start = now - timedelta(hours=24)
    posts = []
    async for m in client.iter_messages(ent, limit=80):
        if m.date < start:
            break
        if getattr(m, "action", None) is not None:
            continue
        posts.append(m)
    if len(posts) < FINDER_MIN_POSTS:
        return False, title
    ds = [start] + sorted(p.date for p in posts) + [now]
    if max((b - a).total_seconds() for a, b in zip(ds, ds[1:])) > FINDER_MAX_GAP:
        return False, title

    def rc(p):
        r = getattr(p, "replies", None)
        return (r.replies or 0) if r is not None else 0

    elig = [p for p in posts if p.date <= now - timedelta(minutes=70)]  # بیشترین ساعت اول کامل شده
    if len(elig) < FINDER_VERIFY_POSTS:
        return False, title
    if sum(1 for p in elig if rc(p) >= FINDER_MIN_COMMENTS) * 10 < len(elig) * 6:
        return False, title
    for p in elig[:FINDER_VERIFY_POSTS]:
        if rc(p) < FINDER_MIN_COMMENTS:
            return False, title
        await asyncio.sleep(random.uniform(2, 4))
        if await finder_hour_count(client, ent, p) < FINDER_MIN_COMMENTS:
            return False, title
    return True, title


async def finder_loop(app):
    errs = 0
    while True:
        try:
            finder_tables()
            chat = get_setting("finder_chat")
            hour = datetime.now(TZ).hour
            if (not finder_enabled() or not chat or SESSION_CLIENT is None
                    or not (FINDER_HOURS[0] <= hour < FINDER_HOURS[1])):
                await asyncio.sleep(120)
                continue
            client = SESSION_CLIENT
            r = q1("SELECT id, word FROM finder_words WHERE done=0 ORDER BY id LIMIT 1")
            if r is None:
                await asyncio.sleep(900)
                continue
            items = await finder_ask(client, r["word"])
            hits = 0
            for uname, _t, subs in items:
                key = uname.lower()
                if q1("SELECT 1 FROM finder_seen WHERE username=?", (key,)):
                    continue
                await asyncio.sleep(random.uniform(*FINDER_CH_GAP))
                try:
                    ok, title = await finder_check(client, uname)
                except (FloodWaitError, ConnectionError, OSError, asyncio.TimeoutError):
                    raise
                except Exception:  # noqa  # کانال خصوصی/حذف‌شده/بدون کامنت و ...
                    ok, title = False, uname
                ex("INSERT OR REPLACE INTO finder_seen(username,ok,checked_at) VALUES(?,?,?)",
                   (key, 1 if ok else 0, int(time.time())))
                if ok:
                    hits += 1
                    txt = f"📣 <b>{html.escape(title)}</b>\n"
                    if subs:
                        txt += f"👥 {fmt_en(subs)} عضو\n"
                    txt += f"🔗 https://t.me/{uname}"
                    try:
                        await app.bot.send_message(int(chat), txt, parse_mode=H)
                    except TelegramError as e:
                        log_err(f"finder send: {e!r}")
            ex("UPDATE finder_words SET done=1, found=?, done_at=? WHERE id=?", (hits, int(time.time()), r["id"]))
            _finder_fail.pop(r["id"], None)
            errs = 0
            await asyncio.sleep(random.uniform(*FINDER_WORD_GAP))
        except asyncio.CancelledError:
            raise
        except FloodWaitError as e:
            log_err(f"finder floodwait {e.seconds}s")
            await asyncio.sleep(e.seconds + 10)
        except Exception as e:  # noqa
            errs += 1
            log_err(f"finder: {e!r}")
            try:
                wid = q1("SELECT id FROM finder_words WHERE done=0 ORDER BY id LIMIT 1")
                if wid is not None:
                    _finder_fail[wid["id"]] = _finder_fail.get(wid["id"], 0) + 1
                    if _finder_fail[wid["id"]] >= 3:  # کلمه‌ی مشکل‌دار تا ابد گیر نمیندازه
                        ex("UPDATE finder_words SET done=1, done_at=? WHERE id=?", (int(time.time()), wid["id"]))
            except Exception:  # noqa
                pass
            if errs >= 5:
                errs = 0
                await asyncio.sleep(3 * 3600)  # چند خطای پشت‌سرهم: چند ساعت استراحت
            else:
                await asyncio.sleep(60)


async def finder_file_post(update: Update, context):
    """فایل txt کلمه‌ها داخل کانال: خونده میشه، ثبت میشه و پیام فایل همون لحظه پاک میشه."""
    m = update.channel_post
    if m is None or m.document is None:
        return
    log.info("finder: فایل داخل کانال %s رسید", m.chat_id)
    try:
        mem = await context.bot.get_chat_member(m.chat_id, OWNER_ID)
    except TelegramError as e:
        log_err(f"finder member check: {e!r}")
        try:
            await context.bot.send_message(OWNER_ID, fb("❌ کانال‌یاب: نتونستم ادمین بودنت رو توی کانال چک کنم؛ "
                                                     "مطمئن شو ربات توی کانال ادمینه و دسترسی‌ها کامله."), parse_mode=H)
        except TelegramError:
            pass
        return
    if mem.status not in ("creator", "administrator"):
        return  # فقط کانالی که خودت توش ادمینی
    name = (m.document.file_name or "").lower()
    if not (name.endswith(".txt") or (m.document.mime_type or "").startswith("text/")):
        await context.bot.send_message(OWNER_ID, fb("❌ کانال‌یاب: فایل باید txt باشه."), parse_mode=H)
        return
    try:
        tgf = await context.bot.get_file(m.document.file_id)
        raw = bytes(await tgf.download_as_bytearray())
    except TelegramError as e:
        log_err(f"finder file: {e!r}")
        await context.bot.send_message(OWNER_ID, fb("❌ فایل کلمه‌ها رو نتونستم بخونم؛ دوباره بفرست."), parse_mode=H)
        return
    if raw[:2] in (b"\xff\xfe", b"\xfe\xff") or b"\x00" in raw[:200]:
        txt = raw.decode("utf-16", errors="ignore")
    else:
        try:
            txt = raw.decode("utf-8-sig")
        except UnicodeDecodeError:
            txt = raw.decode("cp1256", errors="ignore")
    words, seen = [], set()
    for line in re.split(r"[\r\n,،;؛]+", txt):
        w = re.sub(r"^\s*(?:\d+\s*[\.\)\-:]\s*|[-*•]\s*)", "", line).replace("\u200f", "").strip()
        if w and len(w) <= 40 and w.lower() not in seen:
            seen.add(w.lower())
            words.append(w)
    if not words:  # فایل پاک نمیشه تا بتونی ببینی چیه
        await context.bot.send_message(OWNER_ID, fb("❌ کانال‌یاب: توی فایل هیچ کلمه‌ای پیدا نشد. هر کلمه باید توی یه خط باشه "
                                                 "(حداکثر ۴۰ حرف). فایل رو چک کن و دوباره بفرست."), parse_mode=H)
        return
    finder_tables()
    new = 0
    for w in words:
        new += ex("INSERT OR IGNORE INTO finder_words(word) VALUES(?)", (w,)).rowcount
    set_setting("finder_chat", str(m.chat_id))
    try:
        await m.delete()
    except TelegramError:
        pass
    left = q1("SELECT COUNT(*) n FROM finder_words WHERE done=0")["n"]
    await context.bot.send_message(OWNER_ID, fb(f"✅ کانال‌یاب: {len(words)} کلمه توی فایل بود، {new} تاشون جدید ثبت شد. مونده برای جستجو: {left}\n"
                                             f"جستجو هر روز از ساعت {FINDER_HOURS[0]} صبح تا نیمه‌شب انجام میشه."), parse_mode=H)


def finder_page():
    finder_tables()
    n = lambda sql: q1(sql)["n"]  # noqa
    on = finder_enabled()
    sep = "➖•➖•➖•➖•➖•➖•➖"
    text = (f"<b>{sep}\nChannelYAB 📺 کانال یاب\n{sep}</b>\n"
            f"<b>وضعیت</b>: {'🟢 روشن' if on else '🔴 خاموش'}\n"
            f"<b>کلمه‌ی باقی‌مونده</b>:「{fmt_en(n('SELECT COUNT(*) n FROM finder_words WHERE done=0'))}」\n"
            f"<b>کلمه‌ی انجام‌شده</b>:「{fmt_en(n('SELECT COUNT(*) n FROM finder_words WHERE done=1'))}」\n"
            f"<b>کانال بررسی‌شده</b>:「{fmt_en(n('SELECT COUNT(*) n FROM finder_seen'))}」\n"
            f"<b>کانال پیداشده</b>:「{fmt_en(n('SELECT COUNT(*) n FROM finder_seen WHERE ok=1'))}」\n"
            f"<b>{sep}</b>")
    kb = KB(onoff_btn("روشن" if on else "خاموش", on, "o:cyt"), BACK("o:adv"))
    return text, kb


# ---------------------- تقلب هفتگی ----------------------
CHEAT_TZ = ZoneInfo("Asia/Tehran")                              # زمان‌بندی تقلب‌ها همیشه به وقت ایران
CHEAT_ONCE_AD = datetime(2026, 10, 30, 19, 0, tzinfo=CHEAT_TZ)  # جمعه ۸ آبان ۱۴۰۵ ساعت ۱۹:۰۰ (ارسال اولیه‌ی تقلب با آگهی)
CHEAT_GRACE = 1800         # اگه ربات سر ساعت خاموش بود، تا ۳۰ دقیقه بعدش هنوز ارسال میشه
CHEAT_DUP_WINDOW = 120     # همون تقلب برای همون نفر توی این فاصله (ثانیه) دوباره نمیره
CHEAT_RESUME_MAX = 86400   # ارسال نیمه‌تموم (مثلا ری‌استارت وسط ارسال) تا ۲۴ ساعت ادامه پیدا میکنه
CHEAT_PAGE = 20            # تعداد دکمه‌ی تقلب توی هر صفحه
CHEAT_MAX_TIMES = 24
CHEAT_NAME_MAX = 40
CHEAT_AUTO_TTL = 86400   # تقلب‌های ارسال خودکارِ هفتگی: ۲۴ ساعت می‌مونن (دکمه‌ای براشون پاک‌کردن نداره)
CHEAT_TEXT_MAX = 3500
CHEAT_SEP = "➖•➖•➖•➖•➖•➖•➖"

AD_CHEAT_NAME = "تقلب با آگهی"
AD_CHEAT_HEAD = (
    "یه تقلب بهت برسونم؟! 🃏🤫\n"
    "➖•➖\n"
    "میدونستی با آگهی گذاشتن داخل دیوار\n"
    "می\u200cتونی یهو کلی جذب بدست بیاری!؟\n\n"
    "کافیه برنامه دیوار شی و بری به دسته\u200cبندی استخدام ← رایانه و فناوری اطلاعات\n\n"
    "🔻عنوان آگهی🔻"
)
AD_TITLES = (
    "استخدام اپراتور کامنت\u200cگذار",
    "جذب نیروی کامنت\u200cگذار",
    "نیازمند ادمین کامنت\u200cگذار",
    "استخدام نیروی دورکار",
    "دعوت به همکاری اپراتور اینستاگرام",
    "استخدام نیروی فعالیت در اینستاگرام",
    "جذب همکار برای کامنت\u200cگذاری",
    "استخدام اپراتور شبکه\u200cهای اجتماعی",
    "نیازمند نیروی فعال در اینستاگرام",
    "فرصت همکاری به\u200cعنوان کامنت\u200cگذار",
)
AD_BTN_TEXT = "♨️ دریافت متن آگهی ♨️"  # قرمز؛ دکمه‌ی عکس آبی
AD_BTN_CB = "ck:ad"
AD_PHOTO_BTN_TEXT = "🖼️ دریافت عکس آگهی 🖼️"
AD_PHOTO_BTN_CB = "ck:adp"
AD_BACK_CB = "ck:adx"      # «بازگشت» زیر متن و عکس آگهی: همون پیام پاک میشه
AD_MEDIA_TTL_ADMIN = 86400  # ادمین‌ها: ۲۴ ساعت
AD_MEDIA_TTL_OWNER = 60     # پیش‌نمایش کارفرما: ۱ دقیقه
AD_BODY_TEXT = (
    "به تعدادی نیروی فعال جهت همکاری در زمینه کامنت\u200cگذاری اینستاگرام نیازمندیم.\n\n"
    "کاملا رایگان\n"
    "درآمد روزانه ۲۰۰ تا ۹۰۰ هزار تومان\n"
    "قابل انجام با موبایل\n"
    "همراه آموزش اولیه\n"
    "بدون هزینه استخدام\n\n"
    "برای دریافت شرایط همکاری و شروع فعالیت داخل چت دیوار پیام بدید."
)


def _src_has_back(q) -> bool:
    """پیامی که دکمه‌ی آگهی ازش زده شد از منوی تقلبِ خودِ ادمین (یا پیش‌نمایش مدیر) اومده؟ یعنی بازگشت داره.
    تقلبِ خودکارِ هفتگی بازگشت نداره؛ متن و عکسی که ازش گرفته میشه هم دکمه‌ی پاک‌کردن نداره و ۲۴ ساعت می‌مونه."""
    try:
        for row in q.message.reply_markup.inline_keyboard:
            for b in row:
                if b.callback_data in (AD_BACK_CB, "o:ck:pb"):
                    return True
    except Exception:  # noqa
        pass
    return False


async def send_ad_body(bot, uid, chat_id, back: bool = True):
    msg = await bot.send_message(chat_id, AD_BODY_TEXT, reply_markup=KB(BACK_PLAIN(AD_BACK_CB)) if back else None)
    await replace_tracked(bot, uid, "reply", msg)
    _ad_expire(msg, uid)
    return msg


def _ad_expire(msg, uid: int):
    """پاک شدن خودکار متن/عکس آگهی: کارفرما ۱ دقیقه، ادمین‌ها ۲۴ ساعت (تو پاکسازی ۳۰ ثانیه‌ای هم نگه داشته میشه)."""
    if msg is None:
        return
    if uid == OWNER_ID:
        schedule_delete(msg.chat_id, msg.message_id, AD_MEDIA_TTL_OWNER)
    else:
        hold_notice(msg, secs=AD_MEDIA_TTL_ADMIN)


async def send_ad_photo(bot, uid, chat_id, back: bool = True):
    fid = get_setting("ad_photo_id")
    if not fid:
        return None
    msg = await bot.send_photo(chat_id, fid, reply_markup=KB(BACK_PLAIN(AD_BACK_CB)) if back else None)
    await replace_tracked(bot, uid, "adphoto", msg)
    _ad_expire(msg, uid)
    return msg


def ad_buttons():
    """دکمه‌های زیر پیام تقلب آگهی: اول متن آگهی (قرمز)، بعد عکس آگهی (آبی؛ فقط اگه عکس ثبت شده باشه)."""
    btns = [B(AD_BTN_TEXT, AD_BTN_CB, style="danger")]
    if get_setting("ad_photo_id"):
        btns.append(B(AD_PHOTO_BTN_TEXT, AD_PHOTO_BTN_CB, style="primary"))
    return btns


_ck_preview_ads = {}  # شناسه‌ی پیام پیش‌نمایش -> شناسه‌ی متن آگهی‌ای که از روش گرفته شده (با بازگشت هر دو پاک میشن)

CHEAT_PROMPT_NAME = fbox(None, "لطفا اسم دکمه تقلب رو وارد کنید✔️")
CHEAT_PROMPT_DAYS = fbox(None, "چه روز یا روزهایی ارسال شه؟ ✔️")
CHEAT_PROMPT_TIME = fbox(None, "چه ساعتی ارسال کنم؟✔️")
CHEAT_PROMPT_TEXT = fbox(None, "حالا متن تقلب رو بفرست✔️")
CHEAT_PROMPT_PHOTO = fbox(None, "حالا عکس تقلب رو بفرست✔️")
CHEAT_CAPTION_MAX = 1024  # سقف کپشن عکس توی تلگرام؛ متن تقلب‌های عکس‌دار باید توی همین حد باشه


def cheat_caption_len(text) -> int:
    return len(_strip_html(text or ""))


async def safe_send_photo(bot, chat_id, fid, caption=None, kb=None):
    """عکس با کپشن (HTML)؛ مثل safe_send خطا لاگ میشه و None برمیگرده."""
    async def _go():
        try:
            return await bot.send_photo(chat_id=chat_id, photo=fid, caption=caption, reply_markup=kb,
                                        parse_mode=H if caption else None)
        except BadRequest as e:
            if caption and "parse entities" in str(e).lower():
                return await bot.send_photo(chat_id=chat_id, photo=fid, caption=_strip_html(caption), reply_markup=kb)
            raise
    try:
        return await _go()
    except RetryAfter as e:
        await asyncio.sleep(e.retry_after + 1)
        try:
            return await _go()
        except Exception as e2:  # noqa
            log_err(f"send photo retry to {chat_id}: {e2!r}")
    except Forbidden as e:
        mark_blocked(chat_id)
        log_err(f"send photo to {chat_id}: blocked ({e!r})")
    except Exception as e:  # noqa
        log_err(f"send photo to {chat_id}: {e!r}")
    return None


async def send_cheat_msg(bot, chat_id, text, kb=None, photo=None, no_preview=False):
    """متن تقلب؛ اگه عکس داره عکس میره و متن کپشنشه (یک پیام). اگه عکس ارسال نشد، متن تنها میره تا تقلب گم نشه."""
    if photo:
        m = await safe_send_photo(bot, chat_id, photo, text, kb)
        if m is not None:
            return m
    return await safe_send(bot, chat_id, text, kb, html_mode=True, preview=(False if no_preview else None))

# هفته‌ی ایرانی: شنبه تا جمعه؛ مقدار هر روز = weekday() پایتون (دوشنبه=0)
CH_WEEK = ((5, "شنبه"), (6, "یکشنبه"), (0, "دوشنبه"), (1, "سه\u200cشنبه"), (2, "چهارشنبه"), (3, "پنجشنبه"), (4, "جمعه"))
CH_WEEK_NAME = dict(CH_WEEK)
CH_WEEK_ORDER = [d for d, _ in CH_WEEK]

# ---------- تشخیص روز و ساعت از متن فارسی ----------
_CH_ALL_DAYS = re.compile(
    r"(?<![آ-ی])(?:هر\s?روز(?:ه)?|روزانه|همه\s?(?:ی\s?)?روز(?:ها)?(?:\s?(?:ی\s?)?هفته)?|"
    r"تمام\s?(?:ی\s?)?روز(?:ها)?(?:\s?(?:ی\s?)?هفته)?)(?![آ-ی])")
_CH_DAY_RX = re.compile(
    r"(?<![آ-ی])(?:(?P<d2>چه?ار\s?شنبه)|(?P<d3>پنج\s?شنبه)|(?P<d1>سه\s?شنبه)|(?P<d0>دو\s?شنبه)|"
    r"(?P<d6>یک\s?شنبه)|(?P<d4>جمعه)|(?P<d5>شنبه))(?:\s?ها)?(?![آ-ی])")
_CH_DAY_KEYS = {"d2": 2, "d3": 3, "d1": 1, "d0": 0, "d6": 6, "d4": 4, "d5": 5}
_CH_RANGE_BETWEEN = re.compile(r"^\s*(?:تا|الی|[-–—])\s*$")

_CH_NUM_WORDS = (("چهارده", 14), ("چهار", 4), ("پانزده", 15), ("پنج", 5), ("شانزده", 16), ("سیزده", 13), ("دوازده", 12),
                 ("یازده", 11), ("هفده", 17), ("هفت", 7), ("هجده", 18), ("نوزده", 19), ("بیست", 20), ("شیش", 6), ("شش", 6),
                 ("هشت", 8), ("صفر", 0), ("یک", 1), ("یه", 1), ("دو", 2), ("سه", 3), ("نه", 9), ("ده", 10))
_CH_PERIOD = r"(?:صبح|بامداد|نیمه\s?شب|بعد\s?از\s?ظهر|بعدازظهر|ظهر|عصر|غروب|شب)"
_CH_TIME_RX = re.compile(
    r"(?:(?P<p0>" + _CH_PERIOD + r")\s*)?(?:ساعت\s*)?"
    r"(?<!\d)(?P<h>\d{1,2})(?!\d)(?:\s*[:٫.]\s*(?P<m>\d{2})(?!\d))?"
    r"(?:\s*و\s*(?:(?P<half>نیم)|(?P<qtr>ربع)|(?P<mm>\d{1,2})\s*دقیقه(?:\s*ای)?|(?P<mm2>[3-5]\d)(?!\d)))?"
    r"(?:\s*(?P<p1>" + _CH_PERIOD + r"))?")


def _ch_norm(text: str) -> str:
    t = normalize(text or "")
    return re.sub(r"[،,؛;]+", " ، ", t)


def parse_cheat_days(text: str):
    """«شنبه و دوشنبه»، «دو شنبه»، «هر روز»، «شنبه تا چهارشنبه» -> لیست weekday() پایتون؛ تشخیص ندادن = []."""
    t = _ch_norm(text)
    if _CH_ALL_DAYS.search(t):
        return list(CH_WEEK_ORDER)
    found = [(next(_CH_DAY_KEYS[k] for k, v in m.groupdict().items() if v and k in _CH_DAY_KEYS), m.start(), m.end())
             for m in _CH_DAY_RX.finditer(t)]
    days = []
    i = 0
    while i < len(found):
        d, s, e = found[i]
        if i + 1 < len(found) and _CH_RANGE_BETWEEN.match(t[e:found[i + 1][1]]):
            a, b = CH_WEEK_ORDER.index(d), CH_WEEK_ORDER.index(found[i + 1][0])
            k = a
            while True:
                days.append(CH_WEEK_ORDER[k])
                if k == b:
                    break
                k = (k + 1) % 7
            i += 2
            continue
        days.append(d)
        i += 1
    out = []
    for d in days:
        if d not in out:
            out.append(d)
    return sorted(out, key=CH_WEEK_ORDER.index)


def _ch_words_to_digits(t: str) -> str:
    t = re.sub(r"(?<![آ-ی])بیست\s?و\s?(یک|دو|سه|چهار)(?![آ-ی])",
               lambda m: str(20 + {"یک": 1, "دو": 2, "سه": 3, "چهار": 4}[m.group(1)]), t)
    for w, n in _CH_NUM_WORDS:
        t = re.sub(r"(?<![آ-ی])" + w + r"(?![آ-ی])", str(n), t)
    return t


def _ch_to24(h: int, p: str) -> int:
    p = re.sub(r"\s", "", p or "")
    if p == "بامداد":
        h = 0 if h == 12 else h
    elif p == "ظهر":
        h = h + 12 if 1 <= h <= 5 else h
    elif p in ("عصر", "بعدازظهر", "غروب"):
        h = h + 12 if h < 12 else h
    elif p == "شب":
        h = 0 if h == 12 else (h + 12 if 6 <= h <= 11 else h)
    elif p == "نیمهشب":
        h = 0 if h == 12 else h
    return h % 24


def parse_cheat_times(text: str):
    """«ساعت ۳ ظهر»، «۱۹:۳۰»، «۸ و نیم شب»، «ده صبح و ۸ شب» -> لیست «HH:MM» مرتب؛ تشخیص ندادن = []."""
    t = _ch_norm(text)
    t = _CH_ALL_DAYS.sub(" ، ", t)
    t = _CH_DAY_RX.sub(" ، ", t)  # اسم روزها (مثل «سه شنبه») با ساعت قاطی نشه
    t = _ch_words_to_digits(t)
    out = []
    for m in _CH_TIME_RX.finditer(t):
        h = int(m.group("h"))
        if h > 24:
            continue
        if m.group("m") is not None:
            mi = int(m.group("m"))
        elif m.group("half"):
            mi = 30
        elif m.group("qtr"):
            mi = 15
        elif m.group("mm") is not None:
            mi = int(m.group("mm"))
        elif m.group("mm2") is not None:
            mi = int(m.group("mm2"))
        else:
            mi = 0
        if mi > 59:
            continue
        hh = _ch_to24(h, m.group("p1") or m.group("p0"))
        s = f"{hh:02d}:{mi:02d}"
        if s not in out:
            out.append(s)
    if not out:
        if re.search(r"نیمه\s?شب", t):
            out = ["00:00"]
        elif re.search(r"(?<![آ-ی])ظهر(?![آ-ی])", t):
            out = ["12:00"]
    return sorted(out)


def cheat_days_label(days) -> str:
    days = [d for d in CH_WEEK_ORDER if d in (days or [])]
    if not days:
        return "تنظیم نشده"
    if len(days) == 7:
        return "هر روز"
    return "، ".join(CH_WEEK_NAME[d] for d in days)


def cheat_times_label(times) -> str:
    return "، ".join(times) if times else "تنظیم نشده"


def cheat_ts_label(ts: int) -> str:
    d = datetime.fromtimestamp(ts, CHEAT_TZ)
    jy, jm, jd = to_jalali(d.year, d.month, d.day)
    return f"{J_WEEKDAYS[d.weekday()]} {jd} {J_MONTHS[jm - 1]} {jy} ساعت {d:%H:%M}"


# ---------- دیتابیس ----------
def cheat_get(cid):
    try:
        return q1("SELECT * FROM cheats WHERE id=?", (int(cid),))
    except (TypeError, ValueError):
        return None


def cheat_list():
    return qa("SELECT * FROM cheats ORDER BY id")


def _cj(raw, default):
    try:
        v = json.loads(raw or "")
        return v if isinstance(v, list) else default
    except ValueError:
        return default


def cheat_days_of(c):
    return [d for d in _cj(c["days"], []) if isinstance(d, int) and 0 <= d <= 6]


def cheat_times_of(c):
    return [t for t in _cj(c["times"], []) if isinstance(t, str) and re.fullmatch(r"\d{2}:\d{2}", t)]


# ---------- تقلب «کامنت زیر استوری پیج‌ها» (یک‌باره، همه‌ی اعضا، دکمه‌ی لینک برای هر پیج) ----------
STORY_CHEAT_TEXT = "<b>" + (
    "یه تقلب دیگه بهت برسونم؟! 🃏🤫\n"
    "➖•➖\n"
    "میدونستی می\u200cتونی زیر استوری افرادی که امکان ارسال کامنت براشون فعاله کامنت بذاری❕👀\n"
    "➖•➖\n"
    "این روش میتونه نسبت به کامنت\u200cگذاری زیر ریلز، جذب خیلی بیشتری برات داشته باشه! 🚀\n"
    "➖•➖\n"
    "برای شروع، وارد پیج\u200cهای زیر بشید و متن کامنت رو زیر تمام استوری\u200cهای فعال ارسال کنید تا شاهد جذب فوق\u200cالعاده\u200cای باشید! 🔻\n"
    "➖•➖"
) + "</b>"  # کل متن بولد
STORY_PAGES = (
    "arta", "erfanpaydar", "parsalip", "sinavaliollah", "farid__kenzo8", "ehsan.mirzad", "ft360_ir",
    "vahidreza_sadeghpour", "ehsanalikhani",
)


def is_story_cheat(c) -> bool:
    """تقلبِ استوریِ منوی تقلب‌ها: هر تقلب معمولی که اسمش «استوری» داره؛ دکمه‌ی پیج‌ها زیرش میاد."""
    try:
        return c["kind"] != "ad" and "استوری" in str(c["name"] or "")
    except Exception:  # noqa
        return False


def story_cheat_kb(back=None):
    """هر پیج یک دکمه‌ی لینک (اسم دکمه = اسم پیج)؛ یکی در میون قرمز و آبی؛ back (اختیاری) = بازگشت زیرش."""
    rows = [B(pg, url=f"https://www.instagram.com/{pg}/", style=("danger" if i % 2 == 0 else "primary"))
            for i, pg in enumerate(STORY_PAGES)]
    if back is not None:
        rows.append(back)
    return KB(*rows)


def cheat_seed() -> None:
    """یک بار «تقلب با آگهی» ساخته میشه؛ اگه مدیر پاکش کنه دوباره نمیاد."""
    if get_setting("story_text_v3") != "1":  # یک بار: متن تقلب استوری با متن جدید جایگزین میشه (بعدش ویرایش مدیر دست‌نخورده می‌مونه)
        ex("UPDATE cheats SET text=? WHERE kind<>'ad' AND name LIKE ?", (STORY_CHEAT_TEXT, "%استوری%"))
        set_setting("story_text_v3", "1")
    if get_setting("cheat_seed_ad") == "1":
        return
    if q1("SELECT id FROM cheats WHERE kind='ad'") is None:
        ex("INSERT INTO cheats(name,kind,text,days,times,enabled,once_ts,once_done,created_at) VALUES(?,?,?,?,?,?,?,?,?)",
           (AD_CHEAT_NAME, "ad", None, "[]", "[]", 1, int(CHEAT_ONCE_AD.timestamp()), 0, int(time.time())))
    set_setting("cheat_seed_ad", "1")


def cheat_recipients():
    """تمام اعضای ربات (ادمین‌های ثبت‌شده)؛ بلاک‌کرده‌ها و مدیر کنار میرن."""
    return [r["user_id"] for r in qa("SELECT user_id FROM admins WHERE blocked=0 AND user_id<>? ORDER BY user_id", (OWNER_ID,))]


def ad_pick_title(uid: int):
    """عنوان آگهی برای این نفر: تا همه‌ی عنوان‌ها رو نگرفته تکراری نمیگیره؛ بعدش دوره از اول شروع میشه.
    بین عنوان‌های نگرفته، اونی که کمتر بین بقیه پخش شده انتخاب میشه تا عنوان‌ها بین آدم‌ها فرق کنن."""
    n = len(AD_TITLES)
    r = q1("SELECT MAX(cycle) c FROM cheat_ad_titles WHERE user_id=?", (uid,))
    cyc = int(r["c"]) if r is not None and r["c"] else 1
    used = {x["title_idx"] for x in qa("SELECT title_idx FROM cheat_ad_titles WHERE user_id=? AND cycle=?", (uid, cyc))}
    if len(used) >= n:
        cyc += 1
        used = set()
    counts = {x["title_idx"]: x["n"] for x in qa("SELECT title_idx, COUNT(*) n FROM cheat_ad_titles GROUP BY title_idx")}
    free = [i for i in range(n) if i not in used]
    low = min(counts.get(i, 0) for i in free)
    return random.choice([i for i in free if counts.get(i, 0) == low]), cyc


def ad_head_html() -> str:
    """جمله‌ی بالای پیام آگهی: بولد؛ اگه مدیر از ویرایش متن اصلی گذاشته باشه همون، وگرنه متن پیش‌فرض."""
    r = q1("SELECT text FROM cheats WHERE kind='ad' ORDER BY id LIMIT 1")
    custom = ((r["text"] or "").strip() if r is not None else "")
    return f"<b>{custom}</b>" if custom else f"<b>{html.escape(AD_CHEAT_HEAD)}</b>"


def ad_cheat_message(idx: int):
    text = ad_head_html() + "\n" + f"<code>{html.escape(AD_TITLES[idx])}</code>"
    return text, KB(*ad_buttons())


# ---------- ارسال ----------
_cheat_lock_obj = None
_cheat_active = set()      # شناسه‌ی ارسال‌هایی که همین الان توی همین پروسه در حال اجرا یا توی صف اجرا هستن
_cheat_pruned_at = 0.0


def _cheat_lock():
    """ارسال‌ها یکی‌یکی انجام میشن؛ دو تقلبِ هم‌ساعت پشت‌سرهم میرن، نه قاطی هم."""
    global _cheat_lock_obj
    if _cheat_lock_obj is None:
        _cheat_lock_obj = asyncio.Lock()
    return _cheat_lock_obj


def _cheat_claim(cid: int, kind: str, slot_key: str):
    """هر (تقلب، اسلات) فقط یک بار ثبت میشه؛ دومی None برمیگردونه و ارسال تکراری نمیشه."""
    try:
        cur = ex("INSERT OR IGNORE INTO cheat_runs(cheat_id,kind,slot_key,started_at) VALUES(?,?,?,?)",
                 (cid, kind, slot_key, int(time.time())))
        return cur.lastrowid if cur.rowcount == 1 else None
    except Exception as e:  # noqa
        log_err(f"cheat claim {cid}: {e!r}")
        return None


async def _cheat_send_one(bot, c, uid: int, run_id: int) -> bool:
    now = int(time.time())
    if c["kind"] == "ad":
        idx, cyc = ad_pick_title(uid)
        text, kb = ad_cheat_message(idx)
        msg = await safe_send(bot, uid, text, kb, html_mode=True)
        if msg is None:
            return False
        hold_notice(msg, secs=CHEAT_AUTO_TTL)  # تقلب خودکار ۲۴ ساعت می‌مونه و بعدش خودش پاک میشه
        await pin_quiet(bot, uid, msg)  # تقلب آگهی هم مثل بقیه‌ی تقلب‌های هفتگی بی‌صدا پین میشه
        with tx() as conn:
            conn.execute("INSERT OR IGNORE INTO cheat_ad_titles(user_id,title_idx,cycle,ts) VALUES(?,?,?,?)", (uid, idx, cyc, now))
            conn.execute("INSERT OR IGNORE INTO cheat_delivered(run_id,user_id,cheat_id,ts) VALUES(?,?,?,?)", (run_id, uid, c["id"], now))
        return True
    if not (c["text"] or "").strip():
        return False
    msg = await send_cheat_msg(bot, uid, c["text"], (story_cheat_kb() if is_story_cheat(c) else None),
                               photo=c["photo"], no_preview=bool(c["no_preview"]))
    if msg is None:
        return False
    hold_notice(msg, secs=CHEAT_AUTO_TTL)  # تقلب خودکار ۲۴ ساعت می‌مونه و بعدش خودش پاک میشه
    await pin_quiet(bot, uid, msg)  # تقلب هفتگی بی‌صدا پین میشه؛ با پاک شدن پیام، پینش هم خودبه‌خود میره
    ex("INSERT OR IGNORE INTO cheat_delivered(run_id,user_id,cheat_id,ts) VALUES(?,?,?,?)", (run_id, uid, c["id"], now))
    return True


def cheat_notice_name(c) -> str:
    """اسم تقلب توی اعلان: آگهی = «تقلب آگهی»؛ بقیه همون اسم دکمه (اگه با «تقلب» شروع نشه، «تقلب » جلوش میاد)."""
    if c["kind"] == "ad":
        return "تقلب آگهی"
    name = str(c["name"] or "").strip()
    return name if "تقلب" in name else f"تقلب {name}"  # اگه «تقلب» جایی توی اسم دکمه هست (مثلا بین اموجی‌ها) دوباره جلوش نمیاد


async def cheat_notice_owner(bot, c) -> None:
    """بعد از تموم شدن ارسال تقلب برای اعضا، به کارفرما اعلان میره؛ تا زدن «باشه» پاک نمیشه."""
    try:
        m = await safe_send(bot, OWNER_ID,
                            f"<b>{_ACT_SEP}\n{html.escape(cheat_notice_name(c))}\nبرای این هفته ارسال شد ✅\n{_ACT_SEP}</b>",
                            KB(B("🆗", CHEAT_NOTICE_CB, style="success")), html_mode=True)
        if m is not None:  # از پاکسازی خودکار در امانه (سال‌ها دور) تا خودش دکمه رو بزنه
            ex("INSERT OR REPLACE INTO holds(chat_id,message_id,until) VALUES(?,?,?)",
               (OWNER_ID, m.message_id, int(time.time()) + 10 * 365 * 86400))
    except Exception as e:  # noqa
        log_err(f"cheat notice: {e!r}")


async def cheat_run_exec(bot, run_id: int) -> None:
    _cheat_active.add(run_id)
    try:
        async with _cheat_lock():
            run = q1("SELECT * FROM cheat_runs WHERE id=?", (run_id,))
            if run is None or run["finished_at"]:
                return
            c = cheat_get(run["cheat_id"])
            if c is None:
                ex("UPDATE cheat_runs SET finished_at=? WHERE id=?", (int(time.time()), run_id))
                return
            sent, failed = int(run["sent"] or 0), int(run["failed"] or 0)
            done = {r["user_id"] for r in qa("SELECT user_id FROM cheat_delivered WHERE run_id=?", (run_id,))}
            recent = {r["user_id"] for r in qa(
                "SELECT DISTINCT user_id FROM cheat_delivered WHERE cheat_id=? AND run_id<>? AND ts>?",
                (c["id"], run_id, int(time.time()) - CHEAT_DUP_WINDOW))}
            aborted = False
            for n, uid in enumerate(cheat_recipients(), 1):
                if uid in done or uid in recent:
                    continue
                cur = cheat_get(c["id"])
                if cur is None or (run["kind"] != "now" and not cur["enabled"]):
                    aborted = True  # پاک یا خاموش شد: ادامه‌ی ارسال متوقف میشه
                    break
                if bot_off():
                    return  # وقت تعمیرات: ارسال نیمه‌تموم می‌مونه و بعد از روشن شدن ادامه پیدا میکنه
                try:
                    ok = await _cheat_send_one(bot, cur, uid, run_id)
                except Exception as e:  # noqa
                    log_err(f"cheat send {c['id']}->{uid}: {e!r}")
                    ok = False
                if ok:
                    sent += 1
                else:
                    failed += 1
                if n % 20 == 0:
                    ex("UPDATE cheat_runs SET sent=?, failed=? WHERE id=?", (sent, failed, run_id))
                await asyncio.sleep(0.05)
            ex("UPDATE cheat_runs SET sent=?, failed=?, finished_at=? WHERE id=?", (sent, failed, int(time.time()), run_id))
            audit(0, "cheat_run", f"cheat={c['id']} kind={run['kind']} sent={sent} failed={failed}{' aborted' if aborted else ''}")
            _dl = q1("SELECT COUNT(*) n FROM cheat_delivered WHERE run_id=?", (run_id,))
            if not aborted and (sent > 0 or (_dl is not None and int(_dl["n"] or 0) > 0)):
                await cheat_notice_owner(bot, c)
    except Exception as e:  # noqa
        log_err(f"cheat run {run_id}: {e!r}")
    finally:
        _cheat_active.discard(run_id)


def _cheat_spawn(bot, rid: int) -> None:
    _cheat_active.add(rid)  # همین‌جا ثبت میشه تا همون تیک یه بار دیگه برای همین ارسال شروع نشه
    bg(cheat_run_exec(bot, rid))


def cheat_busy(cid: int) -> bool:
    return q1("SELECT 1 FROM cheat_runs WHERE cheat_id=? AND finished_at IS NULL", (cid,)) is not None


def cheat_now_start(bot, cid: int):
    """ارسال فوری: برنامه‌ی زمان‌بندی دست‌نخورده می‌مونه؛ (ok، پیام)."""
    c = cheat_get(cid)
    if c is None:
        return False, "این تقلب پیدا نشد."
    if bot_off():
        return False, "ربات خاموشه؛ اول روشنش کن."
    if c["kind"] != "ad" and not (c["text"] or "").strip():
        return False, "این تقلب متن نداره؛ اول متنش رو از ویرایش ثبت کن."
    if cheat_busy(cid):
        return False, "همین تقلب الان در حال ارساله؛ صبر کن تموم شه."
    r = q1("SELECT MAX(ts) t FROM cheat_delivered WHERE cheat_id=?", (cid,))
    if r is not None and r["t"] and int(time.time()) - int(r["t"]) < CHEAT_DUP_WINDOW:
        return False, "همین الان برای اعضا ارسال شد؛ ۲ دقیقه صبر کن."
    rid = _cheat_claim(cid, "now", f"now{time.time_ns()}")
    if rid is None:
        return False, ERROR_TEXT
    _cheat_spawn(bot, rid)
    return True, ""


async def cheat_job(context: ContextTypes.DEFAULT_TYPE):
    """هر ۳۰ ثانیه: تقلب‌هایی که ساعتشون رسیده ثبت و ارسال میشن (یک‌باره‌ها + برنامه‌ی هفتگی)، ارسال‌های نیمه‌تموم ادامه پیدا میکنن."""
    global _cheat_pruned_at
    try:
        cheat_seed()
        now_ts = time.time()
        if now_ts - _cheat_pruned_at > 3600:
            _cheat_pruned_at = now_ts
            ex("DELETE FROM cheat_delivered WHERE ts<?", (int(now_ts) - 40 * 86400,))
            ex("DELETE FROM cheat_runs WHERE finished_at IS NOT NULL AND finished_at<?", (int(now_ts) - 40 * 86400,))
        ex("UPDATE cheat_runs SET finished_at=? WHERE finished_at IS NULL AND started_at<?",
           (int(now_ts), int(now_ts) - CHEAT_RESUME_MAX))
        if bot_off():
            return
        now = datetime.now(CHEAT_TZ)
        for c in cheat_list():
            if not c["enabled"]:
                continue
            if c["once_ts"] and not c["once_done"] and now.timestamp() >= c["once_ts"]:
                ex("UPDATE cheats SET once_done=1 WHERE id=?", (c["id"],))
                rid = _cheat_claim(c["id"], "once", "once")
                if rid:
                    _cheat_spawn(context.bot, rid)
            days, times = cheat_days_of(c), cheat_times_of(c)
            if not days or not times:
                continue
            for back in (0, 1):
                d = (now - timedelta(days=back)).date()
                if d.weekday() not in days:
                    continue
                for t in times:
                    hh, mm = int(t[:2]), int(t[3:])
                    slot = datetime(d.year, d.month, d.day, hh, mm, tzinfo=CHEAT_TZ)
                    if 0 <= (now - slot).total_seconds() <= CHEAT_GRACE:
                        rid = _cheat_claim(c["id"], "slot", slot.strftime("%Y%m%d%H%M"))
                        if rid:
                            _cheat_spawn(context.bot, rid)
        for r in qa("SELECT id FROM cheat_runs WHERE finished_at IS NULL"):
            if r["id"] not in _cheat_active:
                _cheat_spawn(context.bot, r["id"])  # ری‌استارت وسط ارسال: فقط به کسایی که نرسیده بود میره
    except Exception as e:  # noqa
        log_err(f"cheat job: {e!r}")


# ---------- منوی مدیر ----------
def cheat_menu(page: int = 0, extra: str = ""):
    rows = cheat_list()
    pages = max(1, (len(rows) + CHEAT_PAGE - 1) // CHEAT_PAGE)
    page = max(0, min(page, pages - 1))
    body = (f"<b>{SEP10}\nWEEKLY CHEAT 🃏 تقلب هفتگی\n{SEP10}</b>\n"
            f"<b>تعداد تقلب‌ها</b>:「{len(rows)}」\n"
            f"<b>{SEP10}</b>")
    if extra:
        body += "\n\n" + html.escape(extra)
    btns = [B(str(c["name"])[:CHEAT_NAME_MAX], f"o:ck:v:{c['id']}") for c in rows[page * CHEAT_PAGE:(page + 1) * CHEAT_PAGE]]
    nav = nav_row(lambda p: f"o:ck:p:{p}", page, pages, plain=True)
    kb = KB(*btns, *([nav] if nav else []),
            B("➕ اضافه کردن تقلب ➕", "o:ck:a", style="danger"),
            B(BTN_BACK, "o:adv", style="primary"))
    return body, kb


CHEAT_SEP8 = "➖•➖•➖•➖•➖•➖•➖•➖"


def cheat_head(name, kind: str = "custom") -> str:
    """سرتیتر یکسان برای صفحه‌ی هر تقلب و خلاصه‌ی تقلب جدید."""
    return f"<b>{CHEAT_SEP8}\n{html.escape(str(name))} 🃏 {'AD ' if kind == 'ad' else ''}CHEATING\n{CHEAT_SEP8}</b>"


def cheat_status_label(on: bool) -> str:
    return "ON | 🟡" if on else "OFF | 🔘"


def cheat_detail(cid: int, extra: str = ""):
    c = cheat_get(cid)
    if c is None:
        return None, None
    on = bool(c["enabled"])
    lines = [cheat_head(c["name"], c["kind"]),
             f"<b>وضعیت</b>: {cheat_status_label(on)}",
             f"<b>روزها</b>: {html.escape(cheat_days_label(cheat_days_of(c)))}",
             f"<b>ساعت</b>: {html.escape(cheat_times_label(cheat_times_of(c)))}"]
    last = q1("SELECT started_at FROM cheat_runs WHERE cheat_id=? AND finished_at IS NOT NULL ORDER BY id DESC LIMIT 1", (cid,))
    if last is not None:
        lines.append(f"<b>آخرین ارسال</b>: {cheat_ts_label(int(last['started_at']))}")
    lines.append(f"<b>{CHEAT_SEP8}</b>")
    text = "\n".join(lines) + (("\n\n" + html.escape(extra)) if extra else "")
    kb = KB(B(cheat_status_label(on), f"o:ck:t:{cid}", style="success" if on else "danger"),
            B("👁️ پیش‌نمایش 👁️", f"o:ck:pv:{cid}", style="primary"),
            B("🚀 ارسال فوری 🚀", f"o:ck:s:{cid}", style="primary"),
            B("✏️ ویرایش ✏️", f"o:ck:e:{cid}", style="primary"),
            B("🗑️ حذف 🗑️", f"o:ck:d:{cid}", style="danger"),
            B(BTN_BACK, "o:ck"))
    return text, kb


def cheat_summary_text(dr: dict, title: str = "") -> str:
    """خلاصه‌ی تقلب جدید: همون قالب صفحه‌ی تقلب؛ متن نمیاد چون پیش‌نمایش داره."""
    return "\n".join([cheat_head(dr.get("name") or ""),
                      f"<b>وضعیت</b>: {cheat_status_label(True)}",
                      f"<b>روزها</b>: {html.escape(cheat_days_label(dr.get('days')))}",
                      f"<b>ساعت</b>: {html.escape(cheat_times_label(dr.get('times')))}",
                      f"<b>{CHEAT_SEP8}</b>"])


def cheat_summary_kb():
    return KB(B("👁️ پیش‌نمایش 👁️", "o:ck:dpv", style="primary"),
              B("✅ تایید ✅", "o:ck:ok", style="success"),
              B("✏️ ویرایش ✏️", "o:ck:de", style="primary"),
              BACK("o:ck"))


def cheat_edit_kb(cid=None, draft: bool = False, with_text: bool = True, photo: bool = False, cphoto=None):
    p = "o:ck:d" if draft else "o:ck:e"
    sfx = "" if draft else f":{cid}"
    rows = [B("🏷️ تغییر اسم دکمه 🏷️", f"{p}n{sfx}", style="primary"),
            B("📅 تغییر روزها 📅", f"{p}d{sfx}", style="primary"),
            B("🕒 تغییر ساعت 🕒", f"{p}h{sfx}", style="primary")]
    if with_text:
        rows.append(B("📝 تغییر متن 📝", f"{p}x{sfx}", style="primary"))
    if photo and not draft:
        rows.append(B("🖼️ تغییر عکس آگهی 🖼️", f"o:ck:ph:{cid}", style="primary"))
    if cphoto is not None:  # تقلب معمولی: عکس بفرست تا متن تقلب کپشنش بشه؛ cphoto یعنی الان عکس داره یا نه
        rows.append(B("🖼️ تغییر عکس 🖼️", f"{p}p{sfx}", style="primary"))
        if cphoto:
            rows.append(B("🗑️ حذف عکس 🗑️", f"{p}pd{sfx}", style="danger"))
    rows.append(BACK("o:ck:ds" if draft else f"o:ck:v:{cid}"))
    return KB(*rows)


def _cheat_edit_head(title: str) -> str:
    return fbox(title, "کدوم رو می‌خوای ویرایش کنی؟")


_CHEAT_PROMPTS = {"name": CHEAT_PROMPT_NAME, "days": CHEAT_PROMPT_DAYS, "time": CHEAT_PROMPT_TIME, "text": CHEAT_PROMPT_TEXT,
                  "photo": CHEAT_PROMPT_PHOTO}
_CHEAT_FIELD = {"n": "name", "d": "days", "h": "time", "x": "text", "p": "photo"}
CHEAT_CAPTION_ERR = f"متن تقلب برای کپشن عکس خیلی بلنده؛ حداکثر {CHEAT_CAPTION_MAX} حرف."


async def cheat_owner_cb(update: Update, context, data: str):
    chat_id = update.effective_chat.id
    parts = data.split(":")
    act = parts[2] if len(parts) > 2 else ""
    arg = parts[3] if len(parts) > 3 else ""

    async def detail(cid, extra=""):
        text, kb = cheat_detail(cid, extra)
        if text is None:
            return "این تقلب پیدا نشد."
        await show(update, context, text, kb, html_mode=True)
        return None

    if act == "":
        clear_state(OWNER_ID)
        text, kb = cheat_menu(0)
        await show(update, context, text, kb, html_mode=True)
        return None
    if act == "p":
        clear_state(OWNER_ID)
        text, kb = cheat_menu(int(arg) if arg.isdigit() else 0)
        await show(update, context, text, kb, html_mode=True)
        return None
    if act == "a":  # شروع افزودن
        set_state(OWNER_ID, "ckA_name", {"dr": {}, "sum": False})
        await show(update, context, CHEAT_PROMPT_NAME, KB(BACK("o:ck")), html_mode=True)
        return None
    if act == "ds":  # برگشت به خلاصه (از منوی ویرایش پیش‌نویس)
        st, d = get_state(OWNER_ID)
        if st is None or not st.startswith("ckA"):
            return "اطلاعات تقلب پیدا نشد؛ دوباره اضافه کن."
        set_state(OWNER_ID, "ckA_sum", {"dr": d.get("dr", {}), "sum": True})
        await show(update, context, cheat_summary_text(d.get("dr", {})), cheat_summary_kb(), html_mode=True)
        return None
    if act == "de":
        st, d = get_state(OWNER_ID)
        if st is None or not st.startswith("ckA"):
            return "اطلاعات تقلب پیدا نشد؛ دوباره اضافه کن."
        set_state(OWNER_ID, "ckA_sum", {"dr": d.get("dr", {}), "sum": True})
        await show(update, context, _cheat_edit_head("ویرایش ✏️ EDIT"),
                   cheat_edit_kb(draft=True, cphoto=bool((d.get("dr") or {}).get("photo"))), html_mode=True)
        return None
    if act == "dpd":  # حذف عکسِ تقلبِ جدید (قبل از تایید)
        st, d = get_state(OWNER_ID)
        if st is None or not st.startswith("ckA"):
            return "اطلاعات تقلب پیدا نشد؛ دوباره اضافه کن."
        dr = dict(d.get("dr") or {})
        dr.pop("photo", None)
        set_state(OWNER_ID, "ckA_sum", {"dr": dr, "sum": True})
        await show(update, context, _cheat_edit_head("ویرایش ✏️ EDIT"), cheat_edit_kb(draft=True, cphoto=False), html_mode=True)
        return None
    if act in ("dn", "dd", "dh", "dx", "dp"):
        st, d = get_state(OWNER_ID)
        if st is None or not st.startswith("ckA"):
            return "اطلاعات تقلب پیدا نشد؛ دوباره اضافه کن."
        if act == "dp" and cheat_caption_len((d.get("dr") or {}).get("text")) > CHEAT_CAPTION_MAX:
            return CHEAT_CAPTION_ERR
        fld = _CHEAT_FIELD[act[1]]
        set_state(OWNER_ID, f"ckA_{fld}", {"dr": d.get("dr", {}), "sum": True})
        await show(update, context, _CHEAT_PROMPTS[fld], KB(BACK("o:ck:de")), html_mode=True)
        return None
    if act == "ok":
        st, d = get_state(OWNER_ID)
        dr = d.get("dr") if st is not None and st.startswith("ckA") else None
        if not dr or not dr.get("name") or not dr.get("days") or not dr.get("times") or not (dr.get("text") or "").strip():
            return "اطلاعات تقلب کامل نیست؛ دوباره اضافه کن."
        cur = ex("INSERT INTO cheats(name,kind,text,days,times,enabled,once_ts,once_done,created_at,photo,no_preview) VALUES(?,?,?,?,?,?,?,?,?,?,?)",
                 (dr["name"], "custom", dr["text"], json.dumps(dr["days"]), json.dumps(dr["times"]), 1, None, 0, int(time.time()),
                  dr.get("photo"), int(dr.get("no_preview") or 0)))
        clear_state(OWNER_ID)
        audit(OWNER_ID, "cheat_add", f"id={cur.lastrowid}")
        return await detail(cur.lastrowid, "✅ تقلب ثبت شد.")

    if act == "dpv":  # پیش‌نمایش تقلبِ جدید (قبل از تایید)
        st, d = get_state(OWNER_ID)
        dr = d.get("dr") if st is not None and st.startswith("ckA") else None
        if not dr or not (dr.get("text") or "").strip():
            return "متن تقلب هنوز ثبت نشده."
        _pmsg = await send_cheat_msg(context.bot, chat_id, dr["text"], KB(BACK("o:ck:pb")), photo=dr.get("photo"),
                                     no_preview=bool(dr.get("no_preview")))
        if _pmsg is not None:
            schedule_delete(chat_id, _pmsg.message_id, AD_MEDIA_TTL_OWNER)
        return None
    if act == "pb":  # برگشت از پیش‌نمایش: پیش‌نمایش (و متن آگهیِ گرفته‌شده از روش) پاک میشن؛ صفحه‌ی تقلب سر جاش می‌مونه
        _pm = update.callback_query.message
        _ad_mids = _ck_preview_ads.pop(_pm.message_id, []) if _pm is not None else []
        for _mid in (*_ad_mids, _pm.message_id if _pm is not None else None):
            if _mid:
                try:
                    await context.bot.delete_message(chat_id, _mid)
                except Exception:  # noqa
                    pass
        return None

    # ---- از اینجا به بعد روی یک تقلبِ مشخص ----
    if not arg.isdigit():
        return None
    cid = int(arg)
    if cheat_get(cid) is None:
        return "این تقلب پیدا نشد."
    if act == "v":
        clear_state(OWNER_ID)
        return await detail(cid)
    if act == "t":
        ex("UPDATE cheats SET enabled=1-enabled WHERE id=?", (cid,))
        return await detail(cid)
    if act == "d":
        await show(update, context,
                   f"<b>{CHEAT_SEP}\nآیا از حذف این تقلب مطمئنی؟\n{CHEAT_SEP}</b>",
                   KB(B("✅ بله، حذف کن ✅", f"o:ck:dy:{cid}", style="danger"), BACK(f"o:ck:v:{cid}")), html_mode=True)
        return None
    if act == "dy":
        ex("DELETE FROM cheats WHERE id=?", (cid,))
        ex("DELETE FROM cheat_runs WHERE cheat_id=?", (cid,))
        ex("DELETE FROM cheat_delivered WHERE cheat_id=?", (cid,))
        audit(OWNER_ID, "cheat_del", f"id={cid}")
        text, kb = cheat_menu(0, "✅ تقلب حذف شد.")
        await show(update, context, text, kb, html_mode=True)
        return None
    if act == "e":
        c = cheat_get(cid)
        clear_state(OWNER_ID)
        await show(update, context, _cheat_edit_head("ویرایش ✏️ EDIT"),
                   cheat_edit_kb(cid, with_text=True, photo=(c["kind"] == "ad"),
                                 cphoto=(None if c["kind"] == "ad" else bool(c["photo"]))), html_mode=True)
        return None
    if act == "epd":  # حذف عکس تقلب
        c = cheat_get(cid)
        if c["kind"] != "ad":
            ex("UPDATE cheats SET photo=NULL WHERE id=?", (cid,))
        clear_state(OWNER_ID)
        await show(update, context, _cheat_edit_head("ویرایش ✏️ EDIT"),
                   cheat_edit_kb(cid, with_text=True, photo=(c["kind"] == "ad"),
                                 cphoto=(None if c["kind"] == "ad" else False)), html_mode=True)
        return None
    if act == "ph":  # ثبت یا تعویض عکس آگهی
        if cheat_get(cid)["kind"] != "ad":
            return None
        set_state(OWNER_ID, "photo_set", {"code": "ad", "cid": cid})
        await show(update, context, fb("عکس آگهی رو همینجا به‌صورت عکس بفرست."),
                   KB(BACK(f"o:ck:e:{cid}")), html_mode=True)
        return None
    if act in ("en", "ed", "eh", "ex", "ep"):
        if act == "ep":
            _c1 = cheat_get(cid)
            if _c1["kind"] == "ad":
                return None
            if cheat_caption_len(_c1["text"]) > CHEAT_CAPTION_MAX:
                return CHEAT_CAPTION_ERR
        fld = _CHEAT_FIELD[act[1]]
        set_state(OWNER_ID, f"ckE_{fld}", {"id": cid})
        await show(update, context, _CHEAT_PROMPTS[fld], KB(BACK(f"o:ck:e:{cid}")), html_mode=True)
        return None
    if act == "pv":  # پیش‌نمایش: همون پیامی که اعضا میگیرن، جدا برای مدیر میاد و منو عوض نمیشه
        c = cheat_get(cid)
        if c["kind"] == "ad":
            ptext, _ = ad_cheat_message(random.randrange(len(AD_TITLES)))
            pkb = KB(*ad_buttons(), BACK("o:ck:pb"))
        elif (c["text"] or "").strip():
            ptext, pkb = c["text"], (story_cheat_kb(BACK("o:ck:pb")) if is_story_cheat(c) else KB(BACK("o:ck:pb")))
        else:
            return "این تقلب متن نداره؛ اول متنش رو از ویرایش ثبت کن."
        _pmsg = await send_cheat_msg(context.bot, chat_id, ptext, pkb, photo=(c["photo"] if c["kind"] != "ad" else None),
                                     no_preview=(bool(c["no_preview"]) if c["kind"] != "ad" else False))
        if _pmsg is not None:
            schedule_delete(chat_id, _pmsg.message_id, AD_MEDIA_TTL_OWNER)  # پیش‌نمایش بعد از ۱ دقیقه خودش پاک میشه
        return None
    if act == "s":
        ok, msg = cheat_now_start(context.bot, cid)
        if not ok:
            return msg
        return await detail(cid, "✅ ارسال فوری برای اعضا شروع شد.")
    return None


async def cheat_owner_input(update: Update, context, st: str, d: dict, m):
    """ورودی متنی مدیر برای افزودن/ویرایش تقلب؛ خروجی True یعنی پیام مدیریت شد."""
    chat_id = update.effective_chat.id
    kind, fld = st[2], st[4:]  # ckA_name -> ('A','name') ؛ ckE_days -> ('E','days')
    if fld == "sum":
        return  # روی صفحه‌ی خلاصه هستیم؛ پیام اضافه نادیده گرفته میشه و پیش‌نویس سر جاش می‌مونه
    if fld == "photo":
        if not m.photo:
            await m.reply_text(fb("لطفاً عکس را به‌صورت Photo ارسال کن، نه فایل."), parse_mode=H)
            return
        _c1 = cheat_get(d.get("id")) if kind == "E" else None
        if kind == "E" and (_c1 is None or _c1["kind"] == "ad"):
            clear_state(OWNER_ID)
            return
        _txt1 = _c1["text"] if _c1 is not None else (d.get("dr") or {}).get("text")
        if cheat_caption_len(_txt1) > CHEAT_CAPTION_MAX:
            await m.reply_text(fb(CHEAT_CAPTION_ERR), parse_mode=H)
            return
        val = m.photo[-1].file_id
        raw = ""
    elif not m.text:
        await m.reply_text(fb(f"لطفا {'متن تقلب رو' if fld == 'text' else 'پیامت رو'} به‌صورت متن بفرست."), parse_mode=H)
        return
    else:
        raw = m.text.strip()
    if fld == "photo":
        pass
    elif fld == "name":
        val = raw[:CHEAT_NAME_MAX]
        if not val:
            await m.reply_text(fb("اسم دکمه نباید خالی باشه."), parse_mode=H)
            return
    elif fld == "days":
        val = parse_cheat_days(raw)
        if not val:
            await m.reply_text(fb("روز رو متوجه نشدم؛ مثلا بنویس «شنبه و دوشنبه» یا «هر روز»."), parse_mode=H)
            return
    elif fld == "time":
        val = parse_cheat_times(raw)
        if not val:
            await m.reply_text(fb("ساعت رو متوجه نشدم؛ مثلا بنویس «ساعت ۳ ظهر» یا «19:30»."), parse_mode=H)
            return
        if len(val) > CHEAT_MAX_TIMES:
            await m.reply_text(fb(f"حداکثر {CHEAT_MAX_TIMES} ساعت برای هر تقلب ممکنه."), parse_mode=H)
            return
    elif fld == "text":
        _lp = getattr(m, "link_preview_options", None)
        np_flag = 1 if (_lp is not None and getattr(_lp, "is_disabled", False)) else 0  # مدیر پریویو رو بسته؛ همون‌طور میره
        _c0 = cheat_get(d.get("id")) if kind == "E" else None
        val = html.escape(raw) if (_c0 is not None and _c0["kind"] == "ad") else (m.text_html or raw).strip()
        if len(m.text) > CHEAT_TEXT_MAX:
            await m.reply_text(fb(f"متن خیلی بلنده؛ حداکثر {CHEAT_TEXT_MAX} حرف."), parse_mode=H)
            return
        _has_ph = bool(_c0["photo"]) if (_c0 is not None and _c0["kind"] != "ad") else (kind == "A" and bool((d.get("dr") or {}).get("photo")))
        if _has_ph and cheat_caption_len(val) > CHEAT_CAPTION_MAX:  # عکس‌دار: متن کپشنه و تلگرام بیشتر از این قبول نمیکنه
            await m.reply_text(fb(CHEAT_CAPTION_ERR), parse_mode=H)
            return
    else:
        clear_state(OWNER_ID)
        return
    key = {"time": "times"}.get(fld, fld)

    if kind == "E":
        cid = d.get("id")
        if cheat_get(cid) is None:
            clear_state(OWNER_ID)
            await m.reply_text(fb("این تقلب پیدا نشد."), parse_mode=H)
            return
        ex(f"UPDATE cheats SET {key}=? WHERE id=?", (json.dumps(val) if key in ("days", "times") else val, cid))
        if fld == "text":
            ex("UPDATE cheats SET no_preview=? WHERE id=?", (np_flag, cid))
        clear_state(OWNER_ID)
        text, kb = cheat_detail(cid, "ذخیره شد ✅")
        await owner_menu_send(context, chat_id, m, text, kb, html_mode=True)
        return

    dr = dict(d.get("dr") or {})
    dr[key] = val
    if fld == "text":
        dr["no_preview"] = np_flag
    if d.get("sum"):  # از منوی ویرایشِ خلاصه اومده؛ برمیگرده خلاصه
        set_state(OWNER_ID, "ckA_sum", {"dr": dr, "sum": True})
        await owner_menu_send(context, chat_id, m, cheat_summary_text(dr), cheat_summary_kb(), html_mode=True)
        return
    nxt = {"name": "days", "days": "time", "time": "text"}.get(fld)
    if nxt is None:  # آخرین مرحله: خلاصه
        set_state(OWNER_ID, "ckA_sum", {"dr": dr, "sum": True})
        await owner_menu_send(context, chat_id, m, cheat_summary_text(dr), cheat_summary_kb(), html_mode=True)
        return
    set_state(OWNER_ID, f"ckA_{nxt}", {"dr": dr, "sum": False})
    await owner_menu_send(context, chat_id, m, _CHEAT_PROMPTS[nxt], KB(BACK("o:ck")), html_mode=True)


# ---------------------- کامنت خودکار ----------------------
_ac_lock = None
_ac_last = {}


def ac_tables():
    ex("CREATE TABLE IF NOT EXISTS ac_channels(chat_id INTEGER PRIMARY KEY, title TEXT, link TEXT, added_at INTEGER)")


def ac_enabled() -> bool:
    return get_setting("ac_on") == "1"


def ac_page():
    ac_tables()
    n = q1("SELECT COUNT(*) n FROM ac_channels")["n"]
    on = ac_enabled()
    sep = "➖•➖•➖•➖•➖•"
    text = (f"<b>{sep}\n💭 کامنت خودکار 💭\n{sep}</b>\n"
            f"<b>وضعیت</b> | {'🟢 ON' if on else '🔴 OFF'}\n"
            f"<b>تعداد کانال</b>:「{n}」\n"
            f"<b>{sep}</b>")
    kb = KB(onoff_btn("روشن" if on else "خاموش", on, "o:actg"),
            B("لیست کانال‌ها 📢", "o:acl", style="danger"),
            B("متن ارسال 🗯️", "o:act", style="danger"),
            BACK("o:adv"))
    return text, kb


def ac_list():
    ac_tables()
    rows = qa("SELECT * FROM ac_channels ORDER BY added_at")
    lines = [f"{i}. {html.escape(r['title'] or str(r['chat_id']))}" for i, r in enumerate(rows, 1)]
    text = (f"<b>{SEP10}\nلیست کانال‌ها 📋 CHANNEL\n{SEP10}</b>\n"
            + ("\n".join(lines) if lines else "هنوز کانالی اضافه نشده.")
            + f"\n<b>{SEP10}\nبرای حذف، روی اسم کانال بزن 👇</b>")
    btns = [B(f"🗑️ {(r['title'] or str(r['chat_id']))[:30]}", f"o:acd:{r['chat_id']}", style="danger") for r in rows]
    kb = KB(*btns, B("➕ اضافه کردن کانال ➕", "o:aca", style="danger"), BACK("o:ac"))
    return text, kb


async def ac_resolve_and_join(client, raw: str):
    """کانال رو پیدا میکنه، عضوش میشه و عضو گروه کامنتش هم میشه. (کانال، پیام خطا)"""
    from telethon.tl.functions.channels import JoinChannelRequest, GetFullChannelRequest
    from telethon.tl.functions.messages import ImportChatInviteRequest, CheckChatInviteRequest
    from telethon.errors import UserAlreadyParticipantError
    t = re.sub(r"^(?:https?://)?(?:t\.me|telegram\.me)/", "", raw.strip()).strip("/ ")
    inv = t[1:] if t.startswith("+") else (t.split("/", 1)[1] if t.lower().startswith("joinchat/") else None)
    if inv:
        try:
            ent = (await client(ImportChatInviteRequest(inv))).chats[0]
        except UserAlreadyParticipantError:
            ent = getattr(await client(CheckChatInviteRequest(inv)), "chat", None)
    else:
        key = int(t) if re.fullmatch(r"-?\d+", t) else t.lstrip("@").split("?")[0].split("/")[0]
        ent = await client.get_entity(key)
        try:
            await client(JoinChannelRequest(ent))
        except UserAlreadyParticipantError:
            pass
    if ent is None or not getattr(ent, "broadcast", False):
        return None, "این یه کانال نیست؛ لینک یا یوزرنیم یه کانال رو بفرست."
    full = await client(GetFullChannelRequest(ent))
    linked = getattr(full.full_chat, "linked_chat_id", None)
    if not linked:
        return None, "این کانال بخش کامنت نداره و نمیشه توش کامنت گذاشت."
    grp = next((c for c in full.chats if c.id == linked), None)
    if grp is not None:
        try:
            await client(JoinChannelRequest(grp))
        except Exception:  # noqa
            pass
    return ent, None


async def _ac_send(event, text: str):
    client = event.client
    try:
        await client.send_message(event.chat_id, text, comment_to=event.id, parse_mode=None)
        return
    except FloodWaitError as e:
        log_err(f"autocomment floodwait {e.seconds}s")
        return
    except Exception as e:  # noqa  # شاید عضو گروه کامنت نیست؛ یک بار عضو میشه و دوباره تلاش میکنه
        first = repr(e)
    try:
        from telethon.tl.functions.channels import JoinChannelRequest, GetFullChannelRequest
        full = await client(GetFullChannelRequest(await event.get_chat()))
        grp = next((c for c in full.chats if c.id == full.full_chat.linked_chat_id), None)
        if grp is None:
            raise RuntimeError(first)
        await client(JoinChannelRequest(grp))
        await client.send_message(event.chat_id, text, comment_to=event.id, parse_mode=None)
    except Exception as e2:  # noqa
        log_err(f"autocomment failed: {first} / {e2!r}")


async def autocomment_on_post(event):
    """پست جدید یکی از کانال‌های لیست: وقتی روشنه، کامنتِ تنظیم‌شده سریع گذاشته میشه."""
    global _ac_lock
    try:
        if not ac_enabled() or event.out or not event.is_channel or event.is_group:
            return
        text = get_setting("ac_text")
        if not text:
            return
        ac_tables()
        cid = event.chat_id
        if not q1("SELECT 1 FROM ac_channels WHERE chat_id=?", (cid,)):
            return
        gid = getattr(event.message, "grouped_id", None)
        if gid and _ac_last.get(cid) == gid:  # آلبوم فقط یک کامنت
            return
        _ac_last[cid] = gid
        if _ac_lock is None:
            _ac_lock = asyncio.Lock()
        async with _ac_lock:
            await asyncio.sleep(random.uniform(1.5, 4))
            await _ac_send(event, text)
    except Exception:  # noqa
        log.exception("autocomment")


# ---------------------- خواندن خودکار چت‌های آرشیو (گروه‌ها و ربات‌ها) ----------------------
ARCHIVE_REFRESH = 30   # هر ۳۰ ثانیه فهرست چت‌های آرشیو تازه میشه و هر کدوم خوانده‌نشده داشت خونده میشه
ARCHIVE_READ_GAP = 1   # پیام تازه توی چت آرشیو، ۱ ثانیه بعد «خونده» میشه
_arch_ids: set = set()
_arch_pending: set = set()
_arch_task = None
_ecl_task = None
EMPTY_CLEAN_EVERY = 180   # هر ۳ دقیقه یک بررسی کامل؛ پاک شدن چت از طرف مقابل همون لحظه هم بیدارش میکنه چت‌های خالی (پیام‌پاک‌شده از دو طرف) پیدا و از لیست چت‌ها حذف میشن
EMPTY_CLEAN_MAX = 15      # در هر دور حداکثر این تعداد (بدون فشار به تلگرام)


def _dialog_is_empty(d) -> bool:
    m = d.message
    if m is None or getattr(m, "id", 0) == 0 or type(m).__name__ == "MessageEmpty":
        return True
    act = getattr(m, "action", None)
    # وقتی طرف مقابل چت رو دوطرفه پاک میکنه، تلگرام یه پیام سرویسی «تاریخچه پاک شد» میذاره که توی لیست خالی دیده میشه
    if type(act).__name__ == "MessageActionHistoryClear":
        return True
    # پیامی که نه متن داره نه رسانه نه رویداد هم خالی دیده میشه
    return not getattr(m, "message", None) and not getattr(m, "media", None) and act is None


async def _drop_empty_dialog(client, ent) -> None:
    """حذف چت خالی از لیست: اول مثل اپ رسمی با max_id بزرگ، بعد روش دوم."""
    from telethon.tl.functions.messages import DeleteHistoryRequest
    try:
        for _ in range(5):
            r = await client(DeleteHistoryRequest(peer=ent, max_id=2147483647, just_clear=False, revoke=False))
            if not getattr(r, "offset", 0):
                break
    except FloodWaitError:
        raise
    except Exception as e:  # noqa
        log_err(f"empty chat DeleteHistory {getattr(ent, 'id', '?')}: {e!r}")
    await client.delete_dialog(ent)


async def empty_chat_clean(client, limit: int = 500) -> dict:
    """چت خصوصیِ کاملاً خالی (طرف مقابل چت رو دوطرفه پاک کرده): از لیست چت‌های اکانت شخصی حذف میشه.
    ربات‌ها، Saved Messages، چت‌های پین‌شده و چت‌های دارای پیام دست‌نخورده می‌مونن. بی‌صدا و بدون پیام به مدیر."""
    st = {"scanned": 0, "found": 0, "deleted": 0, "failed": 0}
    async for d in client.iter_dialogs(limit=limit):
        ent = d.entity
        if not d.is_user or getattr(ent, "bot", False) or getattr(ent, "is_self", False):
            continue
        st["scanned"] += 1
        if getattr(d, "pinned", False) or d.id in FINDER_IGNORE_CHATS or not _dialog_is_empty(d):
            continue
        st["found"] += 1
        if st["deleted"] + st["failed"] >= EMPTY_CLEAN_MAX:
            continue
        try:
            await _drop_empty_dialog(client, ent)
            st["deleted"] += 1
            stat_log("delchat", ent.id)  # آمار: چتِ دوطرفه پاک‌شده
        except FloodWaitError as e:
            await asyncio.sleep(min(e.seconds + 1, 120))
            break
        except Exception as e:  # noqa
            st["failed"] += 1
            log_err(f"empty chat delete {getattr(ent, 'id', '?')}: {e!r}")
        await asyncio.sleep(1.0)
    if st["found"]:
        log.info("empty chats: %s", st)
    return st


_ecl_state = {"ev": None}


def ecl_kick() -> None:
    """وقتی تلگرام خبر پاک شدن پیام/تاریخچه رو میده، پاکسازی همون لحظه بیدار میشه."""
    ev = _ecl_state.get("ev")
    if ev is not None:
        ev.set()


async def empty_clean_loop(client) -> None:
    ev = asyncio.Event()
    _ecl_state["ev"] = ev
    await asyncio.sleep(10)
    full = True
    while True:
        try:
            if client.is_connected():
                await empty_chat_clean(client, 500 if full else 100)
            full = False
            try:
                await asyncio.wait_for(ev.wait(), timeout=EMPTY_CLEAN_EVERY)
                await asyncio.sleep(2)  # بذار تلگرام وضعیت چت رو کامل به‌روز کنه
            except asyncio.TimeoutError:
                full = True  # هر چند دقیقه یک بررسی کامل
            ev.clear()
        except asyncio.CancelledError:
            raise
        except FloodWaitError as e:
            await asyncio.sleep(min(e.seconds + 1, 300))
        except Exception as e:  # noqa
            log_err(f"empty clean loop: {e!r}")
            await asyncio.sleep(30)


async def archive_refresh(client) -> None:
    """چت‌های آرشیو که گروه، کانال یا ربات‌ان رو پیدا می‌کنه و خوانده‌نشده‌هاشون رو می‌خونه.
    چت آدم‌ها (متقاضی‌ها) هیچ‌وقت لمس نمیشه تا تأخیر «خوانده شدن» سر جاش بمونه."""
    ids = set()
    async for d in client.iter_dialogs(folder=1, limit=200):
        ent = d.entity
        if d.is_user and not getattr(ent, "bot", False):
            continue
        if str(d.id) == str(BOT_TOKEN).split(":")[0]:
            continue  # چت خودِ این ربات (اعلان جذب و پنل) هیچ‌وقت خودکار خونده نمیشه تا آنرید بمونه
        ids.add(d.id)
        if d.unread_count or getattr(d.dialog, "unread_mark", False):
            await client.send_read_acknowledge(ent, clear_mentions=True)
            await asyncio.sleep(0.3)
    _arch_ids.clear()
    _arch_ids.update(ids)


async def archive_loop(client) -> None:
    while True:
        try:
            await asyncio.sleep(ARCHIVE_REFRESH)
            if client.is_connected():
                await archive_refresh(client)
        except asyncio.CancelledError:
            raise
        except FloodWaitError as e:
            await asyncio.sleep(min(e.seconds + 1, 120))
        except Exception as e:  # noqa
            log_err(f"archive loop: {e!r}")


async def archive_on_message(event, client) -> None:
    if event.chat_id not in _arch_ids or event.chat_id in _arch_pending:
        return
    _arch_pending.add(event.chat_id)  # چند پیام پشت‌هم: فقط یک بار خوندن
    try:
        await asyncio.sleep(ARCHIVE_READ_GAP)
        await client.send_read_acknowledge(await event.get_input_chat(), clear_mentions=True)
    finally:
        _arch_pending.discard(event.chat_id)


async def start_user_session(app):
    global SESSION_CLIENT
    session_client = TelegramClient(
        StringSession(SESSION_STRING),
        API_ID,
        API_HASH
    )
    try:
        await session_client.connect()
        if not await session_client.is_user_authorized():
            raise RuntimeError("SESSION_STRING نامعتبر یا منقضی شده")
    except Exception as e:  # noqa
        # قبلا start() اینجا منتظر ورود دستی میموند یا کل ربات بالا نمیومد؛ حالا ربات بالا میاد و به کارفرما خبر میده
        log.error("session login failed: %r", e)
        log_err(f"session login failed: {e!r}")
        try:
            await session_client.disconnect()
        except Exception:  # noqa
            pass
        try:
            await app.bot.send_message(OWNER_ID, fb("⚠️ سشن اکانت شخصی وصل نشد؛ ثبت جذب از دایرکت اکانتت و بکاپ Saved Messages کار نمیکنه. "
                                                 "SESSION_STRING رو دوباره بساز."), parse_mode=H)
        except Exception:  # noqa
            pass
        return
    SESSION_CLIENT = session_client

    async def handle_incoming(sender, text: str, msg_id: int, catchup: bool = False, ts=None):
        """پیام خصوصی ورودی: ثبت جذب مثل قبل، بعدش ارسال خودکار؛ شناسه‌ی آخرین پیام پردازش‌شده نگه داشته میشه."""
        if not sender or getattr(sender, "bot", False):
            return
        try:
            if sender.id != OWNER_ID:
                save_question(text)
        except Exception as e:  # noqa
            log_err(f"save question: {e!r}")
        # همون منطق مشترک ثبت جذب، پورسانت و اعلان‌ها (مثل مسیر ربات و Business)
        _is_contact = bool(getattr(sender, "contact", False) or getattr(sender, "mutual_contact", False))
        try:  # آمار روزانه (مستقل از سپر و ارسال خودکار)
            await stat_incoming(sender, text, allow_bare=not _is_contact, ts=ts)
            stat_words(sender.id, text, ts=ts)
        except Exception as e:  # noqa
            log_err(f"stat incoming: {e!r}")
        await process_hire(SimpleNamespace(bot=app.bot), sender, text, allow_bare=not _is_contact, shield=True,
                           catchup=catchup)
        try:
            await auto_on_incoming(sender, text, app.bot, msg_id, catchup=catchup)
        except Exception as e:  # noqa
            log_err(f"auto incoming: {e!r}")
        if msg_id:
            ex("INSERT INTO proc_msg(user_id,last_id) VALUES(?,?) ON CONFLICT(user_id) DO UPDATE SET "
               "last_id=MAX(last_id, excluded.last_id)", (sender.id, msg_id))

    @session_client.on(events.NewMessage(incoming=True))
    async def handle_private_message(event):
        try:
            if not event.is_private or event.out:
                return
            sender = await event.get_sender()
            await handle_incoming(sender, event.raw_text or "", event.id, ts=_event_ts(event))
        except Exception:
            log.exception("Error processing incoming message")

    session_client.add_event_handler(autocomment_on_post, events.NewMessage(incoming=True))

    @session_client.on(events.NewMessage(incoming=True))
    async def handle_archive_read(event):
        try:
            await archive_on_message(event, session_client)
        except Exception as e:  # noqa
            log_err(f"archive read: {e!r}")

    @session_client.on(events.Raw)
    async def handle_history_cleared(update):
        try:  # طرف مقابل چت رو پاک کرد (پیام سرویسی «تاریخچه پاک شد» یا حذف پیام‌ها) => پاکسازی چت خالی همین الان
            from telethon.tl import types as _tl
            if isinstance(update, _tl.UpdateDeleteMessages):
                ecl_kick()
            elif (isinstance(update, (_tl.UpdateNewMessage, _tl.UpdateEditMessage))
                  and isinstance(getattr(update, "message", None), _tl.MessageService)
                  and isinstance(update.message.action, _tl.MessageActionHistoryClear)):
                ecl_kick()
        except Exception as e:  # noqa
            log_err(f"history cleared handler: {e!r}")

    @session_client.on(events.NewMessage(outgoing=True))
    async def handle_private_outgoing(event):
        try:
            if event.is_private and event.chat_id and event.chat_id not in FINDER_IGNORE_CHATS:
                try:  # اول از همه و همون لحظه ثبت میشه: «تایید استخدام» بعد از ارسال درجا پاک میشه
                    stat_outgoing(event.chat_id, event.raw_text or "", ts=_event_ts(event))
                except Exception as e:  # noqa
                    log_err(f"stat outgoing: {e!r}")
                shield_owner_replied(event.chat_id)  # پیام کارفرما به متقاضی (برای سپر)
                await auto_on_outgoing(event, app.bot)
        except Exception:
            log.exception("Error processing outgoing message")

    async def catch_up(since: int = 0):
        """بعد از روشن شدن مجدد: لیست چت‌ها چک میشه و هر پیامی که وقت خاموشی اومده (خونده‌شده یا نشده) و هنوز پردازش
        نشده، طبق سیستم جواب داده میشه. جذب‌ها به ترتیب زمان رسیدن، دونه‌دونه ثبت و برای پنل مدیر ارسال میشن."""
        _skip_reset = False
        try:
            if getattr(catch_up, "_running", False):
                _skip_reset = True
                return
            catch_up._running = True
            alive = int(get_setting("auto_alive") or 0)
            if alive <= 0 and since <= 0:
                log_err("catch_up: ساعت آخرین روشن بودن ثبت نشده بود؛ بررسی پیام‌های وقت خاموشی انجام نشد")
                return
            base = min(x for x in (alive, since) if x > 0)
            start = max(base - 120, int(time.time()) - CATCHUP_MAX)
            items = []
            async for d in session_client.iter_dialogs(limit=300):
                ent = d.entity
                if (not d.is_user or getattr(ent, "bot", False) or getattr(ent, "is_self", False)
                        or d.message is None or d.message.date.timestamp() < start):
                    continue
                r = q1("SELECT last_id FROM proc_msg WHERE user_id=?", (ent.id,))
                last = r["last_id"] if r else 0
                async for m in session_client.iter_messages(ent, limit=40):
                    if m.date.timestamp() < start:
                        break
                    if m.out or m.id > last:
                        items.append((m.date.timestamp(), m.id, ent, m))
            items.sort(key=lambda x: (x[0], x[1]))
            done = bad = 0
            for _ts, _id, ent, m in items:
                try:  # خطا توی یک پیام نباید بقیه‌ی پیام‌ها رو متوقف کنه
                    if m.out:  # پیامِ خودت وقت خاموشی: برای سپر حساب میشه (جواب دادی)
                        shield_owner_replied(ent.id)
                        stat_outgoing(ent.id, m.raw_text or "", ts=int(m.date.timestamp()))
                        continue
                    await handle_incoming(ent, m.raw_text or "", m.id, catchup=True, ts=int(m.date.timestamp()))
                    done += 1
                except Exception as e:  # noqa
                    bad += 1
                    log_err(f"catch_up msg {getattr(ent, 'id', '?')}/{_id}: {e!r}")
                await asyncio.sleep(0.5)  # نوتیف‌ها یکی‌یکی و بدون فلود برای مدیر میره
            log.info("catch_up: window=%ss found=%s handled=%s errors=%s", int(time.time() - start), len(items), done, bad)
        except Exception as e:  # noqa
            log_err(f"auto catch_up: {e!r}")
        finally:
            if not _skip_reset:
                catch_up._running = False

    global _auto_task, _sv_task, _finder_task, _arch_task, _ecl_task
    if _auto_task is None or _auto_task.done():
        _auto_task = asyncio.ensure_future(auto_loop(app.bot))
    if _arch_task is None or _arch_task.done():
        _arch_task = asyncio.ensure_future(archive_loop(session_client))
    if _ecl_task is None or _ecl_task.done():
        _ecl_task = asyncio.ensure_future(empty_clean_loop(session_client))
    if _sv_task is None or _sv_task.done():
        _sv_task = asyncio.ensure_future(saved_video_sync_loop(app.bot))
    if _finder_task is None or _finder_task.done():
        _finder_task = asyncio.ensure_future(finder_loop(app))
    bg(signups_scan(session_client, app.bot))  # شمردن ثبت‌نام هر ادمین از روی چت‌ها
    bg(stats_backfill(session_client, app.bot))  # آمار از ۶ صبحِ روز شروع تا الان از روی تاریخچه‌ی چت‌ها بازسازی میشه
    bg(catch_up())

    app.bot_data["session_client"] = session_client
    app.bot_data["catch_up"] = catch_up
    log.info("اتصال سشن تلگرام برقرار شد")
    
def main():
    if not BOT_TOKEN:
        raise SystemExit("BOT_TOKEN تنظیم نشده است.")
    if not OWNER_ID:
        raise SystemExit("OWNER_ID تنظیم نشده است.")

    init_db()
    migrate_levels()
    fix_pinky_counts()
    cheat_seed()
    app = build_app()
    log.info("Jazban bot started")
    app.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()