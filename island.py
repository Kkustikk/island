import sys
import os
import json
import time
import re
import math
import uuid
import socket
import ctypes
import winreg
import bisect
import tempfile
import threading
import traceback
import webbrowser
import subprocess
from ctypes import wintypes
from datetime import datetime, timezone
from pathlib import Path

import requests
import psutil

from PyQt6 import sip
from PyQt6.QtCore import (
    Qt, QTimer, QRect, QRectF, QPoint, QPointF, QSize, QUrl, QMimeData,
    pyqtSignal, QThread, QFileInfo
)
from PyQt6.QtGui import (
    QPainter, QColor, QPen, QBrush, QLinearGradient, QRadialGradient, QConicalGradient,
    QPainterPath, QFont, QFontMetrics, QFontDatabase, QGuiApplication, QIcon, QPixmap,
    QImage, QAction, QCursor, QTransform, QTextLayout, QTextOption, QDrag
)
from PyQt6.QtWidgets import (
    QApplication, QWidget, QVBoxLayout, QHBoxLayout, QLabel, QPushButton, QSlider,
    QLineEdit, QScrollArea, QFrame, QColorDialog, QFileDialog, QSystemTrayIcon, QMenu,
    QStackedWidget, QSizePolicy, QFileIconProvider
)

# Опциональные библиотеки (с безопасным фоллбэком)
try:
    import keyboard
    HAS_KEYBOARD = True
except ImportError:
    HAS_KEYBOARD = False

try:
    import asyncio
    from winsdk.windows.media.control import (
        GlobalSystemMediaTransportControlsSessionManager as MediaManager
    )
    HAS_WINSDK = True
except ImportError:
    HAS_WINSDK = False

try:
    from winsdk.windows.storage.streams import DataReader, Buffer, InputStreamOptions
    HAS_WINSDK_STREAMS = True
except ImportError:
    HAS_WINSDK_STREAMS = False

try:
    import speech_recognition as sr_lib
    HAS_SR = True
except ImportError:
    HAS_SR = False

# Корректный путь к конфигу как для .py, так и для скомпилированного .exe (PyInstaller)
if getattr(sys, "frozen", False):
    BASE_DIR = Path(sys.executable).parent
else:
    BASE_DIR = Path(__file__).parent

CONFIG_FILE = BASE_DIR / "island_config.json"
TEMP_DIR = Path(tempfile.gettempdir()) / "WindowsDynamicIsland"
TEMP_DIR.mkdir(parents=True, exist_ok=True)

DEFAULT_CONFIG = {
    "pos_cx": None,          # центр острова по X (глобальные координаты), None = по центру экрана
    "pos_top": None,         # верхний край острова, None = у верхней кромки
    "island_scale": 1.0,     # масштаб острова
    "style": "glass",        # glass — матовое стекло, clear — прозрачное жидкое стекло, iphone — чёрный как на iPhone
    "glass_tint": 105,       # плотность тёмной подложки стекла 0..230
    "blur": 80,              # сила размытия 0..100
    "live_blur": True,       # живое размытие того, что под островом
    "accent": "#0A84FF",
    "expanded_w": 620,
    "expanded_h": 430,
    "last_tab": 0,
    "karing_path": "",
    "karing_proxy": "127.0.0.1:3067",
    "lyrics_offsets": {},    # сохранённые сдвиги тайминга текста по трекам
    "autostart": False,
    "volume_hud": True,      # перехват ползунка громкости в острове
    "device_toasts": True,   # анимация подключения наушников / устройств
    "shelf_files": [],       # файлы на полке Dropover
    "shortcuts": [
        {"name": "Я.Музыка", "icon": "🎵", "target": "yandexmusic://", "fallback": "https://music.yandex.ru", "color": "#FFCC00"},
        {"name": "YouTube", "icon": "▶️", "target": "https://youtube.com", "color": "#FF3B30"},
        {"name": "GitHub", "icon": "🐙", "target": "https://github.com", "color": "#6E6E73"},
        {"name": "ChatGPT", "icon": "🤖", "target": "https://chatgpt.com", "color": "#10A37F"},
        {"name": "Telegram", "icon": "✈️", "target": "tg://", "fallback": "https://web.telegram.org", "color": "#2AABEE"}
    ]
}

PRESET_ACCENTS = [
    ("Синий", "#0A84FF"),
    ("Фиолетовый", "#BF5AF2"),
    ("Розовый", "#FF375F"),
    ("Оранжевый", "#FF9F0A"),
    ("Зелёный", "#30D158"),
    ("Бирюзовый", "#64D2FF"),
    ("Графит", "#AEAEB2"),
]

DEMO_LYRICS = [
    (0.0, "♪ Инструментальное вступление ♪"),
    (3.5, "Огни ночного города мерцают в стекле"),
    (7.5, "Dynamic Island оживает на твоем столе"),
    (11.5, "Синхронный текст бежит волной за битом"),
    (15.5, "Стекло мерцает мягким светом"),
    (19.5, "Твой буфер обмена и музыка здесь"),
    (23.5, "Весь быстрый контроль в одном острове весь!"),
    (27.5, "♪ Соло синтезатора ♪")
]

NO_MEDIA = {
    "playing": False, "title": "", "artist": "",
    "position": 0.0, "raw_pos": 0.0, "updated_ts": 0.0, "duration": 0.0
}

STYLES = ["glass", "clear", "iphone"]

# Геометрия: фиксированный прозрачный холст исключает любые рывки окна Windows при ресайзе и анимациях
MARGIN = 36
DEFAULT_TOP = 10
EXP_MIN = (480, 290)
EXP_MAX = (1000, 780)
EXP_RADIUS = 36
CANVAS_W = EXP_MAX[0] + 2 * MARGIN
CANVAS_H = EXP_MAX[1] + 2 * MARGIN


# =====================================================================
# WIN32: ПРОЗРАЧНОСТЬ, COM COREAUDIO (ГРОМКОСТЬ / НАУШНИКИ), MCI АУДИО
# =====================================================================
user32 = ctypes.windll.user32
gdi32 = ctypes.windll.gdi32
wininet = ctypes.windll.wininet
ole32 = ctypes.windll.ole32
winmm = ctypes.windll.winmm

user32.GetWindowLongW.argtypes = [wintypes.HWND, ctypes.c_int]
user32.GetWindowLongW.restype = ctypes.c_long
user32.SetWindowLongW.argtypes = [wintypes.HWND, ctypes.c_int, ctypes.c_long]
user32.SetWindowLongW.restype = ctypes.c_long
user32.SetWindowDisplayAffinity.argtypes = [wintypes.HWND, wintypes.DWORD]
user32.SetWindowDisplayAffinity.restype = wintypes.BOOL
user32.GetWindowRect.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.RECT)]
user32.GetDC.argtypes = [wintypes.HWND]
user32.GetDC.restype = wintypes.HDC
user32.ReleaseDC.argtypes = [wintypes.HWND, wintypes.HDC]
user32.GetAsyncKeyState.restype = ctypes.c_short
gdi32.CreateCompatibleDC.argtypes = [wintypes.HDC]
gdi32.CreateCompatibleDC.restype = wintypes.HDC
gdi32.CreateDIBSection.argtypes = [wintypes.HDC, ctypes.c_void_p, wintypes.UINT, ctypes.POINTER(ctypes.c_void_p),
                                  wintypes.HANDLE, wintypes.DWORD]
gdi32.CreateDIBSection.restype = wintypes.HBITMAP
gdi32.SelectObject.argtypes = [wintypes.HDC, wintypes.HGDIOBJ]
gdi32.SelectObject.restype = wintypes.HGDIOBJ
gdi32.DeleteObject.argtypes = [wintypes.HGDIOBJ]
gdi32.DeleteDC.argtypes = [wintypes.HDC]
gdi32.BitBlt.argtypes = [wintypes.HDC, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int,
                         wintypes.HDC, ctypes.c_int, ctypes.c_int, wintypes.DWORD]
wininet.InternetSetOptionW.argtypes = [wintypes.HANDLE, wintypes.DWORD, wintypes.LPVOID, wintypes.DWORD]
wininet.InternetSetOptionW.restype = wintypes.BOOL
winmm.mciSendStringW.argtypes = [wintypes.LPCWSTR, wintypes.LPWSTR, wintypes.UINT, wintypes.HWND]
winmm.mciSendStringW.restype = wintypes.DWORD

GWL_EXSTYLE = -20
WS_EX_TRANSPARENT = 0x20
WDA_NONE = 0x0
WDA_EXCLUDEFROMCAPTURE = 0x11
SRCCOPY = 0x00CC0020
INTERNET_OPTION_REFRESH = 37
INTERNET_OPTION_SETTINGS_CHANGED = 39


class BITMAPINFOHEADER(ctypes.Structure):
    _fields_ = [
        ("biSize", wintypes.DWORD), ("biWidth", wintypes.LONG), ("biHeight", wintypes.LONG),
        ("biPlanes", wintypes.WORD), ("biBitCount", wintypes.WORD), ("biCompression", wintypes.DWORD),
        ("biSizeImage", wintypes.DWORD), ("biXPelsPerMeter", wintypes.LONG),
        ("biYPelsPerMeter", wintypes.LONG), ("biClrUsed", wintypes.DWORD), ("biClrImportant", wintypes.DWORD)
    ]


class GUID(ctypes.Structure):
    _fields_ = [
        ("Data1", wintypes.DWORD),
        ("Data2", wintypes.WORD),
        ("Data3", wintypes.WORD),
        ("Data4", ctypes.c_ubyte * 8)
    ]

    @classmethod
    def from_str(cls, s: str):
        u = uuid.UUID(s)
        d4 = (ctypes.c_ubyte * 8)(*u.bytes[8:])
        return cls(u.time_low, u.time_mid, u.time_hi_version, d4)


class PROPERTYKEY(ctypes.Structure):
    _fields_ = [("fmtid", GUID), ("pid", wintypes.DWORD)]


class PROPVARIANT(ctypes.Structure):
    _fields_ = [
        ("vt", wintypes.USHORT),
        ("wReserved1", wintypes.WORD),
        ("wReserved2", wintypes.WORD),
        ("wReserved3", wintypes.WORD),
        ("pwszVal", wintypes.LPWSTR),
        ("ullPad", ctypes.c_uint64),
    ]


CLSID_MMDeviceEnumerator = GUID.from_str("{BCDE0395-E52F-467C-8E3D-C4579291692E}")
IID_IMMDeviceEnumerator = GUID.from_str("{A95664D2-9614-4F35-A746-DE8DB63617E6}")
IID_IAudioEndpointVolume = GUID.from_str("{5CDF2C82-841E-4546-9722-0CF74078229A}")
PKEY_Device_FriendlyName = PROPERTYKEY(GUID.from_str("{A45C254E-DF1C-4EFD-8020-67D146A850E0}"), 14)

ole32.CoInitializeEx.argtypes = [ctypes.c_void_p, wintypes.DWORD]
ole32.CoCreateInstance.argtypes = [
    ctypes.POINTER(GUID), ctypes.c_void_p, wintypes.DWORD,
    ctypes.POINTER(GUID), ctypes.POINTER(ctypes.c_void_p)
]
ole32.CoTaskMemFree.argtypes = [ctypes.c_void_p]
ole32.PropVariantClear.argtypes = [ctypes.POINTER(PROPVARIANT)]


def _com_vfunc(obj_ptr, index, restype, *argtypes):
    vtbl = ctypes.cast(obj_ptr, ctypes.POINTER(ctypes.POINTER(ctypes.c_void_p))).contents
    func_ptr = vtbl[index]
    proto = ctypes.WINFUNCTYPE(restype, ctypes.c_void_p, *argtypes)
    return proto(func_ptr)


def _com_release(obj_ptr):
    if obj_ptr:
        try:
            _com_vfunc(obj_ptr, 2, wintypes.ULONG)(obj_ptr)
        except Exception:
            pass


class WinAudioBridge:
    """Нативный мост к Windows CoreAudio (через ctypes COM) для чтения/изменения громкости
    и определения подключения наушников / аудиоустройств без внешних зависимостей."""

    @staticmethod
    def _get_default_endpoint():
        try:
            ole32.CoInitializeEx(None, 0)
        except Exception:
            pass
        enum_ptr = ctypes.c_void_p()
        hr = ole32.CoCreateInstance(
            ctypes.byref(CLSID_MMDeviceEnumerator), None, 23,
            ctypes.byref(IID_IMMDeviceEnumerator), ctypes.byref(enum_ptr)
        )
        if hr != 0 or not enum_ptr.value:
            return None
        dev_ptr = ctypes.c_void_p()
        # 4 = GetDefaultAudioEndpoint(eRender=0, eMultimedia=1, &dev_ptr)
        get_ep = _com_vfunc(enum_ptr, 4, ctypes.c_long, ctypes.c_int, ctypes.c_int, ctypes.POINTER(ctypes.c_void_p))
        hr = get_ep(enum_ptr, 0, 1, ctypes.byref(dev_ptr))
        _com_release(enum_ptr)
        if hr != 0 or not dev_ptr.value:
            return None
        return dev_ptr

    @classmethod
    def get_state(cls):
        """Возвращает (volume_0_100: int, muted: bool, device_id: str, device_name: str) или None."""
        dev_ptr = cls._get_default_endpoint()
        if not dev_ptr:
            return None
        vol_int = -1
        muted = False
        dev_id = ""
        dev_name = ""
        try:
            # 5 = IMMDevice::GetId(&pwszId)
            pwsz_id = wintypes.LPWSTR()
            get_id = _com_vfunc(dev_ptr, 5, ctypes.c_long, ctypes.POINTER(wintypes.LPWSTR))
            if get_id(dev_ptr, ctypes.byref(pwsz_id)) == 0 and pwsz_id.value:
                dev_id = str(pwsz_id.value)
                ole32.CoTaskMemFree(pwsz_id)

            # 4 = IMMDevice::OpenPropertyStore(STGM_READ=0, &store_ptr)
            store_ptr = ctypes.c_void_p()
            open_store = _com_vfunc(dev_ptr, 4, ctypes.c_long, wintypes.DWORD, ctypes.POINTER(ctypes.c_void_p))
            if open_store(dev_ptr, 0, ctypes.byref(store_ptr)) == 0 and store_ptr.value:
                pv = PROPVARIANT()
                # 5 = IPropertyStore::GetValue(&PKEY, &pv)
                get_val = _com_vfunc(store_ptr, 5, ctypes.c_long, ctypes.POINTER(PROPERTYKEY), ctypes.POINTER(PROPVARIANT))
                if get_val(store_ptr, ctypes.byref(PKEY_Device_FriendlyName), ctypes.byref(pv)) == 0:
                    if pv.vt == 31 and pv.pwszVal:
                        dev_name = str(pv.pwszVal)
                    ole32.PropVariantClear(ctypes.byref(pv))
                _com_release(store_ptr)

            # 3 = IMMDevice::Activate(IID_IAudioEndpointVolume, CLSCTX_ALL=23, None, &vol_ptr)
            vol_ptr = ctypes.c_void_p()
            activate = _com_vfunc(
                dev_ptr, 3, ctypes.c_long,
                ctypes.POINTER(GUID), wintypes.DWORD, ctypes.c_void_p, ctypes.POINTER(ctypes.c_void_p)
            )
            if activate(dev_ptr, ctypes.byref(IID_IAudioEndpointVolume), 23, None, ctypes.byref(vol_ptr)) == 0 and vol_ptr.value:
                level = ctypes.c_float(0.0)
                # 9 = GetMasterVolumeLevelScalar(&level)
                get_vol = _com_vfunc(vol_ptr, 9, ctypes.c_long, ctypes.POINTER(ctypes.c_float))
                if get_vol(vol_ptr, ctypes.byref(level)) == 0:
                    vol_int = int(round(max(0.0, min(1.0, float(level.value))) * 100))

                b_mute = wintypes.BOOL(0)
                # 15 = GetMute(&b_mute)
                get_mute = _com_vfunc(vol_ptr, 15, ctypes.c_long, ctypes.POINTER(wintypes.BOOL))
                if get_mute(vol_ptr, ctypes.byref(b_mute)) == 0:
                    muted = bool(b_mute.value)
                _com_release(vol_ptr)
        except Exception:
            pass
        finally:
            _com_release(dev_ptr)

        if vol_int < 0:
            return None
        return vol_int, muted, dev_id, dev_name

    @classmethod
    def set_volume(cls, percent: int, unmute: bool = True) -> bool:
        dev_ptr = cls._get_default_endpoint()
        if not dev_ptr:
            return False
        ok = False
        try:
            vol_ptr = ctypes.c_void_p()
            activate = _com_vfunc(
                dev_ptr, 3, ctypes.c_long,
                ctypes.POINTER(GUID), wintypes.DWORD, ctypes.c_void_p, ctypes.POINTER(ctypes.c_void_p)
            )
            if activate(dev_ptr, ctypes.byref(IID_IAudioEndpointVolume), 23, None, ctypes.byref(vol_ptr)) == 0 and vol_ptr.value:
                scalar = ctypes.c_float(max(0.0, min(1.0, percent / 100.0)))
                # 7 = SetMasterVolumeLevelScalar(scalar, None)
                set_vol = _com_vfunc(vol_ptr, 7, ctypes.c_long, ctypes.c_float, ctypes.c_void_p)
                if set_vol(vol_ptr, scalar, None) == 0:
                    ok = True
                if unmute and percent > 0:
                    # 14 = SetMute(0, None)
                    set_mute = _com_vfunc(vol_ptr, 14, ctypes.c_long, wintypes.BOOL, ctypes.c_void_p)
                    set_mute(vol_ptr, 0, None)
                _com_release(vol_ptr)
        except Exception:
            pass
        finally:
            _com_release(dev_ptr)
        return ok


def check_xinput_controllers() -> int:
    """Возвращает битовую маску подключенных геймпадов XInput (0..3)."""
    mask = 0
    for dll_name in ("xinput1_4.dll", "xinput1_3.dll", "xinput9_1_0.dll"):
        try:
            xinput = getattr(ctypes.windll, dll_name.replace(".dll", ""))
            buf = (ctypes.c_byte * 16)()
            for i in range(4):
                if xinput.XInputGetState(i, ctypes.byref(buf)) == 0:
                    mask |= (1 << i)
            return mask
        except Exception:
            continue
    return mask


def set_click_through(hwnd: int, enabled: bool, exclude_capture: bool = False):
    ex = user32.GetWindowLongW(hwnd, GWL_EXSTYLE)
    new = (ex | WS_EX_TRANSPARENT) if enabled else (ex & ~WS_EX_TRANSPARENT)
    if new != ex:
        user32.SetWindowLongW(hwnd, GWL_EXSTYLE, new)
        if exclude_capture:
            user32.SetWindowDisplayAffinity(hwnd, WDA_EXCLUDEFROMCAPTURE)


def window_rect_phys(hwnd: int) -> QRect:
    rc = wintypes.RECT()
    user32.GetWindowRect(hwnd, ctypes.byref(rc))
    return QRect(rc.left, rc.top, rc.right - rc.left, rc.bottom - rc.top)


def virtual_screen_phys() -> QRect:
    return QRect(user32.GetSystemMetrics(76), user32.GetSystemMetrics(77),
                 user32.GetSystemMetrics(78), user32.GetSystemMetrics(79))


def grab_screen(rect: QRect):
    """Снимок области экрана в физических пикселях (окна с WDA_EXCLUDEFROMCAPTURE не попадают)."""
    w, h = rect.width(), rect.height()
    if w <= 0 or h <= 0:
        return None
    sdc = user32.GetDC(None)
    mdc = gdi32.CreateCompatibleDC(sdc)
    bi = BITMAPINFOHEADER(ctypes.sizeof(BITMAPINFOHEADER), w, -h, 1, 32, 0, 0, 0, 0, 0, 0)
    bits = ctypes.c_void_p()
    hbm = gdi32.CreateDIBSection(mdc, ctypes.byref(bi), 0, ctypes.byref(bits), None, 0)
    img = None
    if hbm and bits.value:
        old = gdi32.SelectObject(mdc, hbm)
        gdi32.BitBlt(mdc, 0, 0, w, h, sdc, rect.x(), rect.y(), SRCCOPY)
        img = QImage(sip.voidptr(bits.value), w, h, w * 4, QImage.Format.Format_RGB32).copy()
        gdi32.SelectObject(mdc, old)
        gdi32.DeleteObject(hbm)
    gdi32.DeleteDC(mdc)
    user32.ReleaseDC(None, sdc)
    return img


# =====================================================================
# ШРИФТЫ, ЦВЕТА, БЫСТРЫЙ БЛЮР И ФИЗИКА АНИМАЦИЙ
# =====================================================================
FONT_TEXT = "Segoe UI"
FONT_DISPLAY = "Segoe UI"
FONT_EMOJI = "Segoe UI Emoji"


def init_fonts():
    global FONT_TEXT, FONT_DISPLAY
    families = set(QFontDatabase.families())
    if "Segoe UI Variable Text" in families:
        FONT_TEXT = "Segoe UI Variable Text"
    if "Segoe UI Variable Display" in families:
        FONT_DISPLAY = "Segoe UI Variable Display"


def ui_font(px, weight=QFont.Weight.Normal, display=False):
    f = QFont(FONT_DISPLAY if display else FONT_TEXT)
    f.setPixelSize(max(1, int(round(px))))
    f.setWeight(weight)
    f.setHintingPreference(QFont.HintingPreference.PreferNoHinting)
    return f


def emoji_font(px):
    f = QFont(FONT_EMOJI)
    f.setPixelSize(max(1, int(round(px))))
    return f


def white(alpha: int) -> QColor:
    return QColor(255, 255, 255, max(0, min(255, int(alpha))))


def mix(c1: QColor, c2: QColor, t: float) -> QColor:
    t = max(0.0, min(1.0, t))
    return QColor(
        int(c1.red() + (c2.red() - c1.red()) * t),
        int(c1.green() + (c2.green() - c1.green()) * t),
        int(c1.blue() + (c2.blue() - c1.blue()) * t),
        int(c1.alpha() + (c2.alpha() - c1.alpha()) * t),
    )


def with_alpha(c: QColor, alpha: int) -> QColor:
    c = QColor(c)
    c.setAlpha(max(0, min(255, int(alpha))))
    return c


def clamp(v, lo, hi):
    return max(lo, min(hi, v))


def fmt_time(sec: float) -> str:
    sec = max(0, int(sec))
    return f"{sec // 60}:{sec % 60:02d}"


def fmt_size(num_bytes: int) -> str:
    if num_bytes < 1024:
        return f"{num_bytes} Б"
    if num_bytes < 1024 * 1024:
        return f"{num_bytes / 1024:.1f} КБ"
    if num_bytes < 1024 * 1024 * 1024:
        return f"{num_bytes / (1024 * 1024):.1f} МБ"
    return f"{num_bytes / (1024 * 1024 * 1024):.2f} ГБ"


def fast_blur_opaque(img: QImage, radius: float) -> QImage:
    """Потокобезопасное многопроходное размытие Гаусса на чистом QImage."""
    if img.isNull() or radius <= 0.5:
        return img
    work = img.convertToFormat(QImage.Format.Format_ARGB32_Premultiplied)
    passes = max(2, min(5, int(round(radius / 2.2))))
    for step in range(passes):
        d = max(1, int(round((step + 1) * (radius / (passes * 1.35)))))
        tmp = QImage(work)
        p = QPainter(tmp)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        p.setOpacity(1.0 / 3.0)
        p.drawImage(-d, 0, work)
        p.setOpacity(0.25)
        p.drawImage(d, 0, work)
        p.end()

        work = QImage(tmp)
        p = QPainter(work)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        p.setOpacity(1.0 / 3.0)
        p.drawImage(0, -d, tmp)
        p.setOpacity(0.25)
        p.drawImage(0, d, tmp)
        p.end()
    return work


def blur_qimage(img: QImage, radius: float) -> QImage:
    """Мягкое свечение для прозрачного текста активной строки без QGraphicsScene."""
    if img.isNull():
        return img
    out = QImage(img.width(), img.height(), QImage.Format.Format_ARGB32_Premultiplied)
    out.fill(0)
    q = QPainter(out)
    q.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
    offsets = [
        (-2, 0), (2, 0), (0, -2), (0, 2),
        (-4, -3), (4, -3), (-4, 3), (4, 3),
        (-7, 0), (7, 0), (0, -6), (0, 6)
    ]
    q.setOpacity(0.11)
    for dx, dy in offsets:
        q.drawImage(dx, dy, img)
    q.end()
    return out


class Spring:
    """Пружина как в SwiftUI: response — период (сек), damping — доля затухания (1 = без отскока)."""

    def __init__(self, value=0.0, response=0.45, damping=0.78, eps=0.05):
        self.value = self.target = float(value)
        self.velocity = 0.0
        self.eps = eps
        self.configure(response, damping)

    def configure(self, response, damping):
        self.k = (2 * math.pi / response) ** 2
        self.c = 4 * math.pi * damping / response

    def snap(self, v):
        self.value = self.target = float(v)
        self.velocity = 0.0

    @property
    def settled(self):
        return self.value == self.target and self.velocity == 0.0

    def step(self, dt) -> bool:
        if self.settled:
            return False
        n = max(1, int(math.ceil(dt * 240)))
        h = dt / n
        for _ in range(n):
            a = -self.k * (self.value - self.target) - self.c * self.velocity
            self.velocity += a * h
            self.value += self.velocity * h
        if abs(self.value - self.target) < self.eps and abs(self.velocity) < self.eps * 8:
            self.snap(self.target)
            return False
        return True


class Fade:
    """Плавное экспоненциальное приближение (для прозрачностей — без перелёта)."""

    def __init__(self, value=0.0, speed=14.0):
        self.value = self.target = float(value)
        self.speed = speed

    def snap(self, v):
        self.value = self.target = float(v)

    def step(self, dt) -> bool:
        if self.value == self.target:
            return False
        self.value += (self.target - self.value) * (1 - math.exp(-self.speed * dt))
        if abs(self.value - self.target) < 0.003:
            self.value = self.target
            return False
        return True


class Animated(QWidget):
    """Виджет с собственным кадровым таймером, который работает только пока идёт анимация."""

    def __init__(self, parent=None):
        super().__init__(parent)
        self._anim_timer = QTimer(self)
        self._anim_timer.setTimerType(Qt.TimerType.PreciseTimer)
        self._anim_timer.setInterval(16)
        self._anim_timer.timeout.connect(self._anim_step)
        self._anim_clock = time.perf_counter()

    def animate(self):
        if not self._anim_timer.isActive():
            self._anim_clock = time.perf_counter()
            self._anim_timer.start()

    def _anim_step(self):
        now = time.perf_counter()
        dt = min(0.05, now - self._anim_clock)
        self._anim_clock = now
        if not self.advance(dt):
            self._anim_timer.stop()
        self.update()

    def advance(self, dt) -> bool:
        return False


# =====================================================================
# ФОНОВЫЕ ПОТОКИ: МЕДИА, СТАТУС, АУДИО/BLUETOOTH, ПЕРЕВОД/ИИ, ДИКТОВКА, OCR
# =====================================================================
class MediaWorker(QThread):
    media_updated = pyqtSignal(dict)
    lyrics_updated = pyqtSignal(str, list, str)    # ключ трека, синхронные строки, обычный текст
    artwork_updated = pyqtSignal(str, bytes)       # ключ трека, байты обложки

    def __init__(self):
        super().__init__()
        self.running = True
        self.demo_mode = False
        self.demo_start_time = 0.0
        self.last_track_key = ""
        self.art_attempts = 0
        self._was_playing = False
        self._paused_updated_ts = 0.0

    def toggle_demo(self, enabled: bool):
        self.demo_mode = enabled
        self.last_track_key = ""
        if enabled:
            self.demo_start_time = time.time()
            self.lyrics_updated.emit("demo", DEMO_LYRICS, "")
            self.artwork_updated.emit("demo", b"")

    def run(self):
        loop = asyncio.new_event_loop() if HAS_WINSDK else None
        if loop:
            asyncio.set_event_loop(loop)

        while self.running:
            if self.demo_mode:
                elapsed = (time.time() - self.demo_start_time) % 31.0
                self.media_updated.emit({
                    "key": "demo", "playing": True,
                    "title": "Glass Horizon", "artist": "Cyber Island Synth",
                    "position": elapsed, "raw_pos": elapsed, "updated_ts": time.time(), "duration": 31.0
                })
                time.sleep(0.4)
                continue

            info, art = dict(NO_MEDIA), None
            if loop:
                try:
                    info, art = loop.run_until_complete(self._query(self.art_attempts > 0))
                except Exception:
                    pass

            key = f"{info['artist']} — {info['title']}" if info["title"] else ""
            info["key"] = key
            if key != self.last_track_key:
                self.last_track_key = key
                self.art_attempts = 4 if key else 0
                if key:
                    threading.Thread(
                        target=self._fetch_lyrics,
                        args=(key, info["artist"], info["title"], info["duration"]),
                        daemon=True
                    ).start()
                else:
                    self.artwork_updated.emit("", b"")
            elif art is not None:
                if art or self.art_attempts == 1:
                    self.artwork_updated.emit(key, art)
                    self.art_attempts = 0
                else:
                    self.art_attempts -= 1

            self.media_updated.emit(info)
            time.sleep(0.45)

    async def _query(self, want_art: bool):
        sessions = await MediaManager.request_async()
        current = sessions.get_current_session()
        if not current:
            self._was_playing = False
            return dict(NO_MEDIA), None

        props = await current.try_get_media_properties_async()
        playback = current.get_playback_info()
        timeline = current.get_timeline_properties()

        is_playing = int(playback.playback_status) == 4  # 4 = Playing
        raw_pos = timeline.position.total_seconds() if timeline and timeline.position else 0.0
        dur = timeline.end_time.total_seconds() if timeline and timeline.end_time else 0.0
        pos = raw_pos
        updated_ts = 0.0

        if timeline is not None:
            try:
                updated = timeline.last_updated_time
                if updated is not None:
                    if updated.tzinfo is None:
                        updated = updated.replace(tzinfo=timezone.utc)
                    updated_ts = updated.timestamp()
                    if not is_playing:
                        self._paused_updated_ts = updated_ts
                    elif is_playing and updated_ts > 946684800:
                        if not self._was_playing and abs(updated_ts - self._paused_updated_ts) < 0.01:
                            drift = 0.0
                        else:
                            drift = (datetime.now(timezone.utc) - updated).total_seconds()
                        if 0.0 <= drift < 600.0:
                            pos = raw_pos + drift
            except Exception:
                pass

        self._was_playing = is_playing
        if dur > 0:
            pos = min(pos, dur)

        art = None
        if want_art:
            try:
                art = await self._read_thumbnail(props)
            except Exception:
                art = b""

        return {
            "playing": is_playing,
            "title": props.title or "",
            "artist": props.artist or "",
            "position": pos,
            "raw_pos": raw_pos,
            "updated_ts": updated_ts,
            "duration": dur
        }, art

    @staticmethod
    async def _read_thumbnail(props) -> bytes:
        if not HAS_WINSDK_STREAMS or props.thumbnail is None:
            return b""
        stream = await props.thumbnail.open_read_async()
        size = int(stream.size)
        if size <= 0 or size > 10_000_000:
            return b""
        buf = Buffer(size)
        await stream.read_async(buf, size, InputStreamOptions.READ_AHEAD)
        reader = DataReader.from_buffer(buf)
        data = bytearray(buf.length)
        reader.read_bytes(data)
        return bytes(data)

    def _fetch_lyrics(self, key: str, artist: str, title: str, duration: float):
        synced, plain = [], ""
        headers = {"User-Agent": "WindowsDynamicIsland/2.5"}
        clean_title = re.sub(r"\s*[\(\[].*?[\)\]]", "", title).strip() or title
        clean_artist = artist.split(",")[0].split("&")[0].strip() or artist
        try:
            candidates = []
            params = {"artist_name": artist, "track_name": clean_title}
            if duration > 1:
                params["duration"] = int(round(duration))
            resp = requests.get("https://lrclib.net/api/get", params=params, headers=headers, timeout=4)
            if resp.status_code == 200:
                d = resp.json()
                if isinstance(d, dict):
                    candidates.append(d)

            resp = requests.get(
                "https://lrclib.net/api/search",
                params={"q": f"{clean_artist} {clean_title}"},
                headers=headers, timeout=5
            )
            if resp.status_code == 200:
                found = resp.json()
                if isinstance(found, list):
                    candidates.extend(found)

            best_synced = []
            best_plain = ""
            best_score = -1e9

            for cand in candidates:
                if not isinstance(cand, dict):
                    continue
                s_raw = cand.get("syncedLyrics") or ""
                p_raw = cand.get("plainLyrics") or ""
                parsed = self._parse_lrc(s_raw) if s_raw else []
                c_dur = float(cand.get("duration") or 0.0)
                dur_diff = abs(c_dur - duration) if (duration > 5 and c_dur > 5) else 4.0

                score = (1000.0 if parsed else 0.0) - dur_diff * 15.0
                c_title = (cand.get("trackName") or "").lower()
                if clean_title.lower() in c_title:
                    score += 40.0
                if score > best_score and (parsed or p_raw):
                    best_score = score
                    best_synced = parsed
                    best_plain = p_raw

            synced, plain = best_synced, best_plain
        except Exception:
            pass
        self.lyrics_updated.emit(key, synced, plain)

    @staticmethod
    def _parse_lrc(lrc_text: str):
        result = []
        pattern = re.compile(r"\[(\d+):(\d+(?:\.\d+)?)\](.*)")
        offset_sec = 0.0
        off_match = re.search(r"\[offset:\s*([+-]?\d+)\s*\]", lrc_text, re.IGNORECASE)
        if off_match:
            try:
                offset_sec = int(off_match.group(1)) / 1000.0
            except Exception:
                pass
        for line in lrc_text.splitlines():
            m = pattern.match(line.strip())
            if m:
                text = m.group(3).strip()
                if text:
                    ts = max(0.0, int(m.group(1)) * 60 + float(m.group(2)) - offset_sec)
                    result.append((ts, text))
        return sorted(result, key=lambda x: x[0])


class StatusWorker(QThread):
    status_updated = pyqtSignal(dict)
    volume_changed = pyqtSignal(int, bool)                 # percent, muted
    device_event = pyqtSignal(str, str, str, bool)         # icon, title, subtitle, connected

    def __init__(self):
        super().__init__()
        self.running = True
        self._last_vol = None
        self._last_mute = None
        self._last_dev_id = None
        self._last_dev_name = ""
        self._last_pad_mask = None

    def run(self):
        psutil.cpu_percent(None)
        tick = 0
        while self.running:
            # Быстрый опрос громкости, аудиоустройств и геймпадов каждые ~100 мс
            try:
                audio = WinAudioBridge.get_state()
                if audio is not None:
                    vol, muted, dev_id, dev_name = audio
                    if self._last_vol is not None and (vol != self._last_vol or muted != self._last_mute):
                        self.volume_changed.emit(vol, muted)
                    self._last_vol = vol
                    self._last_mute = muted

                    if self._last_dev_id is not None and dev_id and dev_id != self._last_dev_id:
                        icon, clean_name = self._classify_audio_device(dev_name)
                        self.device_event.emit(icon, "Подключено", clean_name, True)
                    if dev_id:
                        self._last_dev_id = dev_id
                        self._last_dev_name = dev_name
            except Exception:
                pass

            try:
                pad_mask = check_xinput_controllers()
                if self._last_pad_mask is not None and pad_mask != self._last_pad_mask:
                    if pad_mask > self._last_pad_mask:
                        self.device_event.emit("🎮", "Подключено", "Беспроводной геймпад", True)
                    else:
                        self.device_event.emit("🎮", "Отключено", "Геймпад отключён", False)
                self._last_pad_mask = pad_mask
            except Exception:
                pass

            # Раз в 1.5 сек опрашиваем CPU, RAM и Karing VPN
            if tick % 15 == 0:
                karing_running = False
                karing_exe = ""
                tun_active = False
                detected_port = None

                try:
                    for p in psutil.process_iter(["name", "exe"]):
                        name = (p.info.get("name") or "").lower()
                        if "karing" in name:
                            karing_running = True
                            if name == "karing.exe" and p.info.get("exe"):
                                karing_exe = p.info["exe"]
                except Exception:
                    pass

                try:
                    for nic, st in psutil.net_if_stats().items():
                        if st.isup:
                            low = nic.lower()
                            if any(k in low for k in ("karing", "sing-box", "wintun", "tun", "mihomo", "clash")):
                                tun_active = True
                                break
                except Exception:
                    pass

                for port in (3067, 3066, 7890, 10808, 2080):
                    if is_local_port_open(port):
                        detected_port = port
                        break

                proxy, proxy_server = get_system_proxy_info()
                self.status_updated.emit({
                    "karing": karing_running,
                    "karing_exe": karing_exe,
                    "tun": tun_active,
                    "proxy": proxy,
                    "proxy_server": proxy_server,
                    "detected_port": detected_port,
                    "vpn": proxy or tun_active,
                    "cpu": int(psutil.cpu_percent(None)),
                    "ram": int(psutil.virtual_memory().percent)
                })
            tick += 1
            time.sleep(0.1)

    @staticmethod
    def _classify_audio_device(raw_name: str):
        name = raw_name.strip() or "Аудиоустройство"
        low = name.lower()
        if any(k in low for k in ("airpods", "headphone", "headset", "наушник", "гарнитур", "buds", "ソニー", "wh-", "wf-")):
            icon = "🎧"
        elif any(k in low for k in ("controller", "gamepad", "xbox", "dualsense", "dualshock")):
            icon = "🎮"
        else:
            icon = "🔊"
        # Если имя вида "Наушники (AirPods Pro)", красиво извлекаем модель
        m = re.match(r"^(.+?)\s*\((.+?)\)$", name)
        if m:
            outer, inner = m.group(1).strip(), m.group(2).strip()
            if len(inner) >= 3 and not any(x in inner.lower() for x in ("realtek", "high definition", "amd", "nvidia")):
                return icon, f"{inner} · {outer}"
        return icon, name


class TextAssistantWorker(QThread):
    """Фоновый переводчик и мини-ИИ для буфера обмена."""
    finished_result = pyqtSignal(str, str)  # title, result_text

    def __init__(self, text: str, mode: str = "translate"):
        super().__init__()
        self.text = text.strip()
        self.mode = mode  # "translate" | "ai"

    def run(self):
        if not self.text:
            self.finished_result.emit("Пусто", "В буфере обмена нет текста.")
            return
        if self.mode == "translate":
            res = self._translate(self.text)
            self.finished_result.emit("🌐 Перевод", res)
        else:
            res = self._ask_ai(self.text)
            self.finished_result.emit("✦ Ответ ИИ", res)

    @staticmethod
    def _has_cyrillic(s: str) -> bool:
        return bool(re.search(r"[а-яА-ЯёЁ]", s))

    def _translate(self, text: str) -> str:
        # Автоопределение целевого языка: русский -> английский, иначе -> русский
        cyr_count = len(re.findall(r"[а-яА-ЯёЁ]", text))
        lat_count = len(re.findall(r"[a-zA-Z]", text))
        target_lang = "en" if (cyr_count > lat_count and cyr_count > 2) else "ru"
        try:
            resp = requests.get(
                "https://translate.googleapis.com/translate_a/single",
                params={
                    "client": "gtx",
                    "sl": "auto",
                    "tl": target_lang,
                    "dt": "t",
                    "q": text[:3500]
                },
                headers={"User-Agent": "Mozilla/5.0"},
                timeout=6
            )
            if resp.status_code == 200:
                data = resp.json()
                if isinstance(data, list) and data and isinstance(data[0], list):
                    parts = [seg[0] for seg in data[0] if isinstance(seg, list) and seg and seg[0]]
                    if parts:
                        return "".join(parts).strip()
        except Exception as e:
            return f"Не удалось выполнить перевод: {e}"
        return "Перевод не найден."

    def _ask_ai(self, text: str) -> str:
        prompt = (
            "Ответь очень кратко, по делу и на русском языке (максимум 3-4 предложения). "
            "Если это ошибка из консоли или код — объясни причину и как исправить. "
            "Если это обычный текст — дай краткую суть и перевод ключевых мыслей:\n\n"
            f"{text[:2500]}"
        )
        try:
            resp = requests.post(
                "https://text.pollinations.ai/",
                json={
                    "messages": [
                        {"role": "system", "content": "Ты лаконичный ИИ-ассистент внутри Dynamic Island на Windows. Отвечай кратко и по сути на русском языке."},
                        {"role": "user", "content": prompt}
                    ],
                    "model": "openai"
                },
                headers={"Content-Type": "application/json", "User-Agent": "WindowsDynamicIsland/2.5"},
                timeout=10
            )
            if resp.status_code == 200 and resp.text.strip():
                return resp.text.strip()
        except Exception:
            pass
        # Надёжный фоллбэк: перевод + краткая статистика
        translated = self._translate(text)
        words = len(text.split())
        lines = len(text.splitlines())
        return f"{translated}\n\n(Слов: {words} · Строк: {lines})"


class VoiceRecorder:
    """Нативная запись голоса в .wav через встроенный в Windows winmm.dll (MCI)
    с последующим распознаванием речи (Speech-to-Text)."""

    def __init__(self):
        self.recording = False
        self.start_ts = 0.0
        self.wav_path = ""

    @staticmethod
    def _mci(cmd: str) -> int:
        buf = ctypes.create_unicode_buffer(256)
        return winmm.mciSendStringW(cmd, buf, 255, None)

    def start(self) -> bool:
        if self.recording:
            return True
        self._mci("close island_mic")
        if self._mci("open new type waveaudio alias island_mic") != 0:
            return False
        self._mci("set island_mic time format ms bitspersample 16 samplespersec 16000 channels 1")
        if self._mci("record island_mic") != 0:
            self._mci("close island_mic")
            return False
        self.recording = True
        self.start_ts = time.monotonic()
        self.wav_path = str(TEMP_DIR / f"Голосовая_заметка_{datetime.now().strftime('%H-%M-%S')}.wav")
        return True

    def stop(self) -> str:
        if not self.recording:
            return ""
        self.recording = False
        self._mci("stop island_mic")
        self._mci(f'save island_mic "{self.wav_path}"')
        self._mci("close island_mic")
        return self.wav_path if os.path.exists(self.wav_path) else ""


class SpeechTranscribeWorker(QThread):
    """Распознаёт записанный .wav файл в текст (SpeechRecognition / Windows SAPI)."""
    transcribed = pyqtSignal(str, str)  # recognized_text, wav_path

    def __init__(self, wav_path: str):
        super().__init__()
        self.wav_path = wav_path

    def run(self):
        if not self.wav_path or not os.path.exists(self.wav_path):
            self.transcribed.emit("", "")
            return

        # 1. Если установлен пакет SpeechRecognition — используем его (высокая точность RU/EN)
        if HAS_SR:
            try:
                rec = sr_lib.Recognizer()
                with sr_lib.AudioFile(self.wav_path) as src:
                    audio = rec.record(src)
                text = rec.recognize_google(audio, language="ru-RU")
                if text and text.strip():
                    self.transcribed.emit(text.strip(), self.wav_path)
                    return
            except Exception:
                pass

        # 2. Встроенный в Windows движок System.Speech.Recognition (без внешних библиотек)
        try:
            ps_script = (
                "[Console]::OutputEncoding = [System.Text.Encoding]::UTF8; "
                "Add-Type -AssemblyName System.Speech; "
                "$ cultures = @('ru-RU', 'en-US'); "
                "$rec = $null; "
                "foreach ($c in $cultures) { "
                "  try { $rec = New-Object System.Speech.Recognition.SpeechRecognitionEngine([System.Globalization.CultureInfo]$c); break } catch {} "
                "} "
                "if ($null -eq $rec) { $rec = New-Object System.Speech.Recognition.SpeechRecognitionEngine }; "
                "$rec.LoadGrammar((New-Object System.Speech.Recognition.DictationGrammar)); "
                f"$rec.SetInputToWaveFile('{self.wav_path}'); "
                "$res = $rec.Recognize(); "
                "if ($res) { Write-Output $res.Text }"
            )
            creation_flags = getattr(subprocess, "CREATE_NO_WINDOW", 0x08000000)
            proc = subprocess.run(
                ["powershell", "-NoProfile", "-NonInteractive", "-Command", ps_script],
                capture_output=True, text=True, encoding="utf-8", errors="ignore",
                timeout=12, creationflags=creation_flags
            )
            out = (proc.stdout or "").strip()
            if out:
                self.transcribed.emit(out, self.wav_path)
                return
        except Exception:
            pass

        self.transcribed.emit("", self.wav_path)


class OcrWorker(QThread):
    """Распознаёт текст с вырезанной области экрана через встроенный Windows 10/11 Media.Ocr."""
    ocr_finished = pyqtSignal(str)

    def __init__(self, image: QImage):
        super().__init__()
        self.image = image

    def run(self):
        if self.image is None or self.image.isNull():
            self.ocr_finished.emit("")
            return
        img_path = TEMP_DIR / "ocr_capture.png"
        # Увеличиваем мелкий текст в 2 раза для повышения точности Windows OCR
        scaled = self.image
        if scaled.width() < 900 and scaled.height() < 900:
            scaled = scaled.scaled(
                scaled.width() * 2, scaled.height() * 2,
                Qt.AspectRatioMode.KeepAspectRatio,
                Qt.TransformationMode.SmoothTransformation
            )
        scaled.save(str(img_path), "PNG")

        ps_script = f"""
[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
Add-Type -AssemblyName System.Runtime.WindowsRuntime
$null = [Windows.Storage.StorageFile, Windows.Storage, ContentType=WindowsRuntime]
$null = [Windows.Media.Ocr.OcrEngine, Windows.Foundation, ContentType=WindowsRuntime]
$null = [Windows.Graphics.Imaging.BitmapDecoder, Windows.Foundation, ContentType=WindowsRuntime]

$asTaskGeneric = ([System.WindowsRuntimeSystemExtensions].GetMethods() | Where-Object {{
    $_.Name -eq 'AsTask' -and $_.GetParameters().Count -eq 1 -and $_.GetParameters()[0].ParameterType.Name -eq 'IAsyncOperation`1'
}})[0]

function Await($WinRtTask, $ResultType) {{
    $asTask = $asTaskGeneric.MakeGenericMethod($ResultType)
    $netTask = $asTask.Invoke($null, @($WinRtTask))
    $netTask.Wait(-1) | Out-Null
    $netTask.Result
}}

$file = Await ([Windows.Storage.StorageFile]::GetFileFromPathAsync('{str(img_path)}')) ([Windows.Storage.StorageFile])
$stream = Await ($file.OpenAsync([Windows.Storage.FileAccessMode]::Read)) ([Windows.Storage.Streams.IRandomAccessStream])
$decoder = Await ([Windows.Graphics.Imaging.BitmapDecoder]::CreateAsync($stream)) ([Windows.Graphics.Imaging.BitmapDecoder])
$bitmap = Await ($decoder.GetSoftwareBitmapAsync()) ([Windows.Graphics.Imaging.SoftwareBitmap])
$engine = [Windows.Media.Ocr.OcrEngine]::TryCreateFromUserProfileLanguages()
if ($null -eq $engine) {{
    $lang = New-Object Windows.Globalization.Language('en-US')
    $engine = [Windows.Media.Ocr.OcrEngine]::TryCreateFromLanguage($lang)
}}
$result = Await ($engine.RecognizeAsync($bitmap)) ([Windows.Media.Ocr.OcrResult])
$lines = $result.Lines | ForEach-Object {{ $_.Text }}
$stream.Dispose()
Write-Output ($lines -join "`n")
"""
        text = ""
        try:
            creation_flags = getattr(subprocess, "CREATE_NO_WINDOW", 0x08000000)
            proc = subprocess.run(
                ["powershell", "-NoProfile", "-NonInteractive", "-Command", ps_script],
                capture_output=True, text=True, encoding="utf-8", errors="ignore",
                timeout=12, creationflags=creation_flags
            )
            text = (proc.stdout or "").strip()
        except Exception:
            pass
        self.ocr_finished.emit(text)


class BackdropGrabber(QThread):
    """Снимает область экрана под островом и размывает её в фоновом потоке."""
    captured = pyqtSignal(QImage, object)

    DOWNSCALE = 2

    def __init__(self):
        super().__init__()
        self.running = True
        self._lock = threading.Lock()
        self._event = threading.Event()
        self._request = None

    def request(self, phys_rect: QRect, blur_radius: float, token):
        with self._lock:
            self._request = (QRect(phys_rect), float(blur_radius), token)
        self._event.set()

    def stop(self):
        self.running = False
        self._event.set()

    def run(self):
        while self.running:
            self._event.wait(0.5)
            self._event.clear()
            with self._lock:
                req, self._request = self._request, None
            if not req or not self.running:
                continue
            rect, blur_radius, token = req
            try:
                img = grab_screen(rect)
            except Exception:
                img = None
            if img is None or img.isNull():
                continue
            sw = max(1, rect.width() // self.DOWNSCALE)
            sh = max(1, rect.height() // self.DOWNSCALE)
            small = img.scaled(sw, sh, Qt.AspectRatioMode.IgnoreAspectRatio,
                               Qt.TransformationMode.SmoothTransformation)
            blurred = fast_blur_opaque(small, blur_radius)
            self.captured.emit(blurred, token)


def is_local_port_open(port: int) -> bool:
    try:
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.settimeout(0.04)
            return s.connect_ex(("127.0.0.1", port)) == 0
    except Exception:
        return False


def get_system_proxy_info():
    enabled = False
    server = ""
    try:
        key = winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                             r"Software\Microsoft\Windows\CurrentVersion\Internet Settings", 0, winreg.KEY_READ)
        try:
            val, _ = winreg.QueryValueEx(key, "ProxyEnable")
            enabled = bool(val)
        except FileNotFoundError:
            pass
        try:
            srv, _ = winreg.QueryValueEx(key, "ProxyServer")
            server = str(srv or "").strip()
        except FileNotFoundError:
            pass
        winreg.CloseKey(key)
    except Exception:
        pass
    return enabled, server


def is_system_proxy_enabled() -> bool:
    return get_system_proxy_info()[0]


def is_url_scheme_registered(scheme: str) -> bool:
    try:
        key = winreg.OpenKey(winreg.HKEY_CLASSES_ROOT, scheme, 0, winreg.KEY_READ)
        winreg.CloseKey(key)
        return True
    except Exception:
        return False


def apply_windows_proxy(enabled: bool, server: str) -> bool:
    """Включает или выключает системный прокси Windows и мгновенно применяет настройки через WinINet."""
    try:
        key = winreg.OpenKey(
            winreg.HKEY_CURRENT_USER,
            r"Software\Microsoft\Windows\CurrentVersion\Internet Settings",
            0, winreg.KEY_SET_VALUE
        )
        if enabled and server:
            winreg.SetValueEx(key, "ProxyServer", 0, winreg.REG_SZ, server)
        winreg.SetValueEx(key, "ProxyEnable", 0, winreg.REG_DWORD, 1 if enabled else 0)
        winreg.CloseKey(key)

        wininet.InternetSetOptionW(0, INTERNET_OPTION_SETTINGS_CHANGED, None, 0)
        wininet.InternetSetOptionW(0, INTERNET_OPTION_REFRESH, None, 0)
        return True
    except Exception as e:
        print("Ошибка применения системного прокси:", e)
        return False


# =====================================================================
# ЭКРАННЫЕ ИНСТРУМЕНТЫ: СКАНЕР ТЕКСТА (OCR) И ПИПЕТКА ЦВЕТА С ЛУПОЙ
# =====================================================================
class ScreenSnipOverlay(QWidget):
    """Оверлей выделения области экрана для распознавания текста (OCR)."""
    area_selected = pyqtSignal(QImage)

    def __init__(self, accent=QColor("#0A84FF")):
        super().__init__(None)
        self.accent = QColor(accent)
        self.setWindowFlags(
            Qt.WindowType.FramelessWindowHint |
            Qt.WindowType.WindowStaysOnTopHint |
            Qt.WindowType.Tool
        )
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, True)
        self.setCursor(Qt.CursorShape.CrossCursor)
        self.setMouseTracking(True)

        screen = QGuiApplication.primaryScreen()
        self.virtual_geo = screen.virtualGeometry()
        self.phys_rect = virtual_screen_phys()
        self.full_img = grab_screen(self.phys_rect)
        self.start_pos = None
        self.cur_pos = None
        self.setGeometry(self.virtual_geo)

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self.start_pos = e.position().toPoint()
            self.cur_pos = self.start_pos
            self.update()
        elif e.button() == Qt.MouseButton.RightButton:
            self.close()

    def mouseMoveEvent(self, e):
        if self.start_pos is not None:
            self.cur_pos = e.position().toPoint()
            self.update()

    def mouseReleaseEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton and self.start_pos is not None:
            end_pos = e.position().toPoint()
            sel = QRect(self.start_pos, end_pos).normalized()
            self.close()
            if sel.width() > 8 and sel.height() > 8 and self.full_img is not None:
                kx = self.full_img.width() / max(1, self.width())
                ky = self.full_img.height() / max(1, self.height())
                crop = QRect(
                    int(sel.x() * kx), int(sel.y() * ky),
                    int(sel.width() * kx), int(sel.height() * ky)
                ).intersected(self.full_img.rect())
                if not crop.isEmpty():
                    self.area_selected.emit(self.full_img.copy(crop))

    def keyPressEvent(self, e):
        if e.key() == Qt.Key.Key_Escape:
            self.close()

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        if self.full_img is not None:
            p.drawImage(self.rect(), self.full_img)
        p.fillRect(self.rect(), QColor(0, 0, 0, 115))

        if self.start_pos and self.cur_pos:
            sel = QRectF(self.start_pos, self.cur_pos).normalized()
            if self.full_img is not None and sel.width() > 2 and sel.height() > 2:
                kx = self.full_img.width() / max(1, self.width())
                ky = self.full_img.height() / max(1, self.height())
                src = QRectF(sel.x() * kx, sel.y() * ky, sel.width() * kx, sel.height() * ky)
                p.drawImage(sel, self.full_img, src)
            p.setPen(QPen(self.accent, 2.0))
            p.setBrush(Qt.BrushStyle.NoBrush)
            p.drawRoundedRect(sel, 6, 6)

        # Плашка-подсказка сверху
        banner = QRectF(self.width() / 2 - 210, 28, 420, 38)
        p.setPen(QPen(white(45), 1))
        p.setBrush(QColor(18, 20, 28, 220))
        p.drawRoundedRect(banner, 19, 19)
        p.setFont(ui_font(13, QFont.Weight.DemiBold))
        p.setPen(white(240))
        p.drawText(banner, Qt.AlignmentFlag.AlignCenter, "🔍 Выделите область с текстом на экране (Esc — отмена)")


class ColorPickerOverlay(QWidget):
    """Экранная пипетка с 8-кратной пиксельной лупой и копированием HEX."""
    color_picked = pyqtSignal(QColor)

    def __init__(self):
        super().__init__(None)
        self.setWindowFlags(
            Qt.WindowType.FramelessWindowHint |
            Qt.WindowType.WindowStaysOnTopHint |
            Qt.WindowType.Tool
        )
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, True)
        self.setCursor(Qt.CursorShape.CrossCursor)
        self.setMouseTracking(True)

        screen = QGuiApplication.primaryScreen()
        self.virtual_geo = screen.virtualGeometry()
        self.phys_rect = virtual_screen_phys()
        self.full_img = grab_screen(self.phys_rect)
        self.pos_cursor = QPoint(self.virtual_geo.width() // 2, self.virtual_geo.height() // 2)
        self.setGeometry(self.virtual_geo)

    def _color_at(self, pt: QPoint) -> QColor:
        if self.full_img is None or self.full_img.isNull():
            return QColor("#0A84FF")
        kx = self.full_img.width() / max(1, self.width())
        ky = self.full_img.height() / max(1, self.height())
        px = clamp(int(pt.x() * kx), 0, self.full_img.width() - 1)
        py = clamp(int(pt.y() * ky), 0, self.full_img.height() - 1)
        return self.full_img.pixelColor(px, py)

    def mouseMoveEvent(self, e):
        self.pos_cursor = e.position().toPoint()
        self.update()

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            c = self._color_at(e.position().toPoint())
            self.close()
            self.color_picked.emit(c)
        elif e.button() == Qt.MouseButton.RightButton:
            self.close()

    def keyPressEvent(self, e):
        if e.key() == Qt.Key.Key_Escape:
            self.close()

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        if self.full_img is not None:
            p.drawImage(self.rect(), self.full_img)

        pt = self.pos_cursor
        c = self._color_at(pt)
        hex_str = c.name().upper()

        # Круглая лупа рядом с курсором
        lens_r = 58
        cx = pt.x() + 75 if pt.x() + 160 < self.width() else pt.x() - 75
        cy = pt.y() + 75 if pt.y() + 170 < self.height() else pt.y() - 75
        lens_rect = QRectF(cx - lens_r, cy - lens_r, lens_r * 2, lens_r * 2)

        if self.full_img is not None:
            kx = self.full_img.width() / max(1, self.width())
            ky = self.full_img.height() / max(1, self.height())
            px = clamp(int(pt.x() * kx), 0, self.full_img.width() - 1)
            py = clamp(int(pt.y() * ky), 0, self.full_img.height() - 1)
            patch = self.full_img.copy(px - 5, py - 5, 11, 11)

            clip = QPainterPath()
            clip.addEllipse(lens_rect)
            p.save()
            p.setClipPath(clip)
            p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform, False)
            p.drawImage(lens_rect, patch)
            p.restore()

        # Окантовка лупы цветом выбранного пикселя
        p.setPen(QPen(QColor(0, 0, 0, 160), 6))
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.drawEllipse(lens_rect)
        p.setPen(QPen(c, 3.5))
        p.drawEllipse(lens_rect)

        # Центральный пиксель-прицел внутри лупы
        cell = (lens_r * 2) / 11.0
        p.setPen(QPen(white(230), 1.4))
        p.drawRect(QRectF(cx - cell / 2, cy - cell / 2, cell, cell))

        # Плашка с HEX и RGB под лупой
        pill = QRectF(cx - 74, cy + lens_r + 8, 148, 30)
        p.setPen(QPen(white(45), 1))
        p.setBrush(QColor(16, 18, 24, 235))
        p.drawRoundedRect(pill, 10, 10)
        p.setBrush(c)
        p.drawEllipse(QRectF(pill.left() + 8, pill.top() + 7, 16, 16))
        p.setFont(ui_font(12, QFont.Weight.Bold))
        p.setPen(white(245))
        p.drawText(pill.adjusted(30, 0, -6, 0), Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft,
                   f"{hex_str} · {c.red()},{c.green()},{c.blue()}")


# =====================================================================
# ЭЛЕМЕНТЫ ИНТЕРФЕЙСА В СТИЛЕ iOS
# =====================================================================
class Switch(Animated):
    toggled = pyqtSignal(bool)

    def __init__(self, checked=False, accent=QColor("#0A84FF"), parent=None):
        super().__init__(parent)
        self.setFixedSize(46, 28)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self._checked = bool(checked)
        self.knob = Spring(1.0 if checked else 0.0, 0.32, 0.8, eps=0.002)
        self.press = Fade(0.0, 18)
        self.accent = QColor(accent)

    def isChecked(self):
        return self._checked

    def setChecked(self, value: bool, emit=False):
        value = bool(value)
        if value != self._checked:
            self._checked = value
            self.knob.target = 1.0 if value else 0.0
            self.animate()
            if emit:
                self.toggled.emit(value)

    def set_accent(self, color: QColor):
        self.accent = QColor(color)
        self.update()

    def mousePressEvent(self, e):
        self.press.target = 1.0
        self.animate()
        e.accept()

    def mouseReleaseEvent(self, e):
        self.press.target = 0.0
        self.animate()
        if self.rect().contains(e.position().toPoint()):
            self.setChecked(not self._checked, emit=True)

    def advance(self, dt):
        a = self.knob.step(dt)
        b = self.press.step(dt)
        return a or b

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        t = clamp(self.knob.value, 0.0, 1.0)
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(mix(QColor(120, 120, 128, 82), self.accent, t))
        p.drawRoundedRect(QRectF(0, 0, 46, 28), 14, 14)
        kw = 24 + 5 * self.press.value
        x = 2 + clamp(self.knob.value, -0.05, 1.05) * (46 - 4 - kw)
        p.setBrush(QColor(0, 0, 0, 45))
        p.drawRoundedRect(QRectF(x, 3, kw, 24), 12, 12)
        p.setBrush(QColor(255, 255, 255))
        p.drawRoundedRect(QRectF(x, 2, kw, 24), 12, 12)


class Segmented(Animated):
    changed = pyqtSignal(int)

    def __init__(self, items, parent=None):
        super().__init__(parent)
        self.items = items
        self.index = 0
        self.hover = -1
        self.thumb = Spring(0.0, 0.36, 0.82, eps=0.002)
        self.setFixedHeight(32)
        self.setMinimumWidth(len(items) * 68)
        self.setMouseTracking(True)
        self.setCursor(Qt.CursorShape.PointingHandCursor)

    def set_index(self, i, animate=True):
        self.index = clamp(i, 0, len(self.items) - 1)
        if animate:
            self.thumb.target = float(self.index)
            self.animate()
        else:
            self.thumb.snap(float(self.index))
            self.update()

    def _seg_w(self):
        return (self.width() - 4) / len(self.items)

    def _hit(self, x):
        return clamp(int((x - 2) // self._seg_w()), 0, len(self.items) - 1)

    def mouseMoveEvent(self, e):
        h = self._hit(e.position().x())
        if h != self.hover:
            self.hover = h
            self.update()

    def leaveEvent(self, e):
        self.hover = -1
        self.update()

    def mousePressEvent(self, e):
        i = self._hit(e.position().x())
        if i != self.index:
            self.set_index(i)
            self.changed.emit(i)
        e.accept()

    def advance(self, dt):
        return self.thumb.step(dt)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        w, h = self.width(), self.height()
        seg = self._seg_w()
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor(118, 118, 128, 56))
        p.drawRoundedRect(QRectF(0, 0, w, h), 10, 10)

        thumb = QRectF(2 + self.thumb.value * seg, 2, seg, h - 4)
        p.setBrush(white(48))
        p.setPen(QPen(white(30), 0.8))
        p.drawRoundedRect(thumb, 8, 8)

        p.setFont(ui_font(12.0, QFont.Weight.DemiBold))
        for i, text in enumerate(self.items):
            r = QRectF(2 + i * seg, 0, seg, h)
            closeness = 1.0 - clamp(abs(self.thumb.value - i), 0.0, 1.0)
            alpha = 165 + 90 * closeness + (25 if i == self.hover and i != self.index else 0)
            p.setPen(white(alpha))
            p.drawText(r, Qt.AlignmentFlag.AlignCenter, text)


class IconButton(Animated):
    clicked = pyqtSignal()

    def __init__(self, kind, size=36, glyph=1.0, filled=False, primary=False, parent=None):
        super().__init__(parent)
        self.kind = kind
        self.glyph = glyph
        self.filled = filled
        self.primary = primary
        self.setFixedSize(size, size)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.hover = Fade(0.0, 16)
        self.press = Spring(0.0, 0.25, 0.7, eps=0.002)

    def set_kind(self, kind):
        if kind != self.kind:
            self.kind = kind
            self.update()

    def enterEvent(self, e):
        self.hover.target = 1.0
        self.animate()

    def leaveEvent(self, e):
        self.hover.target = 0.0
        self.animate()

    def mousePressEvent(self, e):
        self.press.target = 1.0
        self.animate()
        e.accept()

    def mouseReleaseEvent(self, e):
        self.press.target = 0.0
        self.animate()
        if self.rect().contains(e.position().toPoint()):
            self.clicked.emit()

    def advance(self, dt):
        a = self.hover.step(dt)
        b = self.press.step(dt)
        return a or b

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        s = self.width()
        c = QPointF(s / 2, s / 2)
        scale = 1.0 - 0.14 * self.press.value
        p.setPen(Qt.PenStyle.NoPen)
        if self.primary:
            p.setBrush(white(255 - 30 * self.hover.value))
            p.drawEllipse(c, s / 2 * scale, s / 2 * scale)
        else:
            bg_alpha = (34 if self.filled else 0) + 34 * self.hover.value
            if bg_alpha > 1:
                p.setBrush(white(bg_alpha))
                p.drawEllipse(c, s / 2 * scale, s / 2 * scale)

        p.translate(c)
        p.scale(scale, scale)
        u = s * 0.3 * self.glyph
        glyph = QColor(14, 14, 16) if self.primary else QColor(255, 255, 255)
        p.setBrush(glyph)
        p.setPen(QPen(glyph, max(1.2, u * 0.12), Qt.PenStyle.SolidLine,
                      Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin))

        def tri(x0, flip=1):
            path = QPainterPath()
            path.moveTo(x0, -0.42 * u)
            path.lineTo(x0 + flip * 0.62 * u, 0)
            path.lineTo(x0, 0.42 * u)
            path.closeSubpath()
            p.drawPath(path)

        k = self.kind
        if k == "play":
            path = QPainterPath()
            path.moveTo(-0.34 * u, -0.52 * u)
            path.lineTo(0.56 * u, 0)
            path.lineTo(-0.34 * u, 0.52 * u)
            path.closeSubpath()
            p.drawPath(path)
        elif k == "pause":
            p.setPen(Qt.PenStyle.NoPen)
            p.drawRoundedRect(QRectF(-0.42 * u, -0.5 * u, 0.28 * u, u), 0.08 * u, 0.08 * u)
            p.drawRoundedRect(QRectF(0.14 * u, -0.5 * u, 0.28 * u, u), 0.08 * u, 0.08 * u)
        elif k == "next":
            tri(-0.62 * u)
            tri(0.0)
        elif k == "prev":
            tri(0.62 * u, -1)
            tri(0.0, -1)
        else:
            p.setBrush(Qt.BrushStyle.NoBrush)
            p.setPen(QPen(white(235), max(1.6, u * 0.16), Qt.PenStyle.SolidLine,
                          Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin))
            if k == "chevron_up":
                path = QPainterPath()
                path.moveTo(-0.45 * u, 0.2 * u)
                path.lineTo(0, -0.22 * u)
                path.lineTo(0.45 * u, 0.2 * u)
                p.drawPath(path)
            elif k == "close":
                p.drawLine(QPointF(-0.35 * u, -0.35 * u), QPointF(0.35 * u, 0.35 * u))
                p.drawLine(QPointF(0.35 * u, -0.35 * u), QPointF(-0.35 * u, 0.35 * u))


class ElidedLabel(QWidget):
    def __init__(self, text="", px=13, weight=QFont.Weight.Normal, color=None, display=False, parent=None):
        super().__init__(parent)
        self._text = text
        self._font = ui_font(px, weight, display)
        self._color = color or white(255)
        self.setFixedHeight(QFontMetrics(self._font).height() + 2)
        self.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        self.setMinimumWidth(20)

    def setText(self, text):
        if text != self._text:
            self._text = text
            self.update()

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.TextAntialiasing)
        p.setFont(self._font)
        p.setPen(self._color)
        fm = QFontMetrics(self._font)
        p.drawText(self.rect(), Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter,
                   fm.elidedText(self._text, Qt.TextElideMode.ElideRight, self.width()))


class Artwork(QWidget):
    def __init__(self, size=84, parent=None):
        super().__init__(parent)
        self.setFixedSize(size, size)
        self.pix = None
        self.color = QColor("#0A84FF")

    def set_image(self, img, color: QColor):
        self.color = QColor(color)
        if img is not None and not img.isNull():
            s = self.width() * self.devicePixelRatioF()
            scaled = img.scaled(int(s), int(s), Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                                Qt.TransformationMode.SmoothTransformation)
            x = (scaled.width() - int(s)) // 2
            y = (scaled.height() - int(s)) // 2
            self.pix = QPixmap.fromImage(scaled.copy(x, y, int(s), int(s)))
        else:
            self.pix = None
        self.update()

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        s = self.width()
        path = QPainterPath()
        path.addRoundedRect(QRectF(0, 0, s, s), s * 0.2, s * 0.2)
        if self.pix is not None:
            brush = QBrush(self.pix)
            brush.setTransform(QTransform.fromScale(s / self.pix.width(), s / self.pix.height()))
            p.fillPath(path, brush)
        else:
            g = QLinearGradient(0, 0, s, s)
            g.setColorAt(0.0, self.color.lighter(125))
            g.setColorAt(1.0, self.color.darker(220))
            p.fillPath(path, QBrush(g))
            p.setPen(white(215))
            p.setFont(ui_font(s * 0.42, QFont.Weight.Bold, display=True))
            p.drawText(QRectF(0, 0, s, s), Qt.AlignmentFlag.AlignCenter, "♪")
        p.setPen(QPen(white(26), 1))
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.drawPath(path)


class ProgressBar(QWidget):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setFixedHeight(28)
        self.position = 0.0
        self.dur = 0.0

    def set_progress(self, pos, dur):
        self.position, self.dur = pos, dur
        self.update()

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        w = self.width()
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(white(48))
        p.drawRoundedRect(QRectF(0, 4, w, 5), 2.5, 2.5)
        if self.dur > 0:
            frac = clamp(self.position / self.dur, 0.0, 1.0)
            p.setBrush(white(225))
            p.drawRoundedRect(QRectF(0, 4, max(5.0, w * frac), 5), 2.5, 2.5)
        p.setFont(ui_font(11, QFont.Weight.DemiBold))
        p.setPen(white(135))
        left = fmt_time(self.position) if self.dur > 0 else "–:––"
        right = ("-" + fmt_time(self.dur - self.position)) if self.dur > 0 else "–:––"
        p.drawText(QRectF(0, 12, w, 16), Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter, left)
        p.drawText(QRectF(0, 12, w, 16), Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter, right)


def wipe_brush(x0, width, frac, bright: QColor, dim: QColor, feather_px=26.0):
    """Кисть «караоке»: слева от frac текст яркий, справа — приглушённый, с мягкой границей."""
    if frac >= 1.0:
        return QBrush(bright)
    if frac <= 0.0:
        return QBrush(dim)
    width = max(1.0, width)
    feather = feather_px / width
    g = QLinearGradient(x0, 0, x0 + width, 0)
    g.setColorAt(0.0, bright)
    g.setColorAt(clamp(frac - feather / 2, 0.0, 1.0), bright)
    g.setColorAt(clamp(frac + feather / 2, 0.0, 1.0), dim)
    g.setColorAt(1.0, dim)
    return QBrush(g)


def wave_level(t, i):
    v = 0.5 + 0.5 * math.sin(t * (5.1 + i * 1.7) + i * 1.3)
    v *= 0.55 + 0.45 * math.sin(t * (2.3 + i * 0.6) + i)
    return abs(v)



class WaveBars(Animated):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setFixedSize(30, 24)
        self.playing = False
        self.color = QColor("#0A84FF")
        self.level = Fade(0.0, 6)
        self.t = 0.0

    def set_state(self, playing: bool, color: QColor):
        self.playing = playing
        self.color = QColor(color)
        self.level.target = 1.0 if playing else 0.0
        self.animate()

    def showEvent(self, e):
        self.animate()
        super().showEvent(e)

    def advance(self, dt):
        self.t += dt
        moving = self.level.step(dt)
        return moving or (self.playing and self.isVisible())

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        bars, bw, gap = 5, 3.2, 2.6
        x0 = (self.width() - (bars * bw + (bars - 1) * gap)) / 2
        maxh = self.height() - 2
        col = self.color.lighter(140) if self.color.lightness() < 120 else self.color
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(col)
        for i in range(bars):
            h = max(bw, maxh * (0.18 + 0.82 * wave_level(self.t, i) * self.level.value))
            p.drawRoundedRect(QRectF(x0 + i * (bw + gap), (self.height() - h) / 2, bw, h), bw / 2, bw / 2)


class LyricsView(Animated):
    """Текст песни с караоке-заливкой и поддержкой ручного сдвига тайминга через Ctrl + колесо мыши."""
    offset_step_requested = pyqtSignal(float)

    GAP = 16

    def __init__(self, parent=None):
        super().__init__(parent)
        self.items = []
        self.times = []
        self.synced = False
        self.active = -1
        self.content_h = 0
        self.message = "Текст песни появится автоматически"
        self.clock = None
        self.scroll_target = -12.0
        self.user_scroll_until = 0.0
        self.glow = None
        self.font = ui_font(21, QFont.Weight.Bold, display=True)
        self.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)
        self.setMinimumHeight(60)

    def set_clock(self, fn):
        self.clock = fn

    def set_lyrics(self, synced, plain, message=""):
        if synced:
            pairs = list(synced)
            self.synced = True
        elif plain:
            pairs = [(None, s.strip()) for s in plain.splitlines() if s.strip()]
            self.synced = False
        else:
            pairs = []
            self.synced = False
        self.times = [t for t, _ in pairs] if self.synced else []
        self.items = [{
            "t": t, "text": s, "lines": [], "y": 0, "h": 0, "pending": None,
            "scroll": Spring(-12.0, 0.62, 0.84, eps=0.2),
            "scale": Spring(0.94 if self.synced else 1.0, 0.45, 0.78, eps=0.0008),
            "alpha": Fade(0.32 if self.synced else 0.75, 8),
        } for t, s in pairs]
        self.message = message or "Текст для этого трека не найден"
        self.active = -1
        self.user_scroll_until = 0.0
        self._relayout()
        self.scroll_target = -12.0
        for i, it in enumerate(self.items):
            it["scroll"].snap(-40.0)
            it["pending"] = (time.monotonic() + min(0.4, 0.04 * i), -12.0)
        self.animate()
        self.update()

    def _relayout(self):
        fm = QFontMetrics(self.font)
        width = max(40, self.width() - 28)
        option = QTextOption()
        option.setWrapMode(QTextOption.WrapMode.WordWrap)
        y = 0
        for it in self.items:
            layout = QTextLayout(it["text"], self.font)
            layout.setTextOption(option)
            raw = it["text"].encode("utf-16-le")
            lines = []
            layout.beginLayout()
            while True:
                line = layout.createLine()
                if not line.isValid():
                    break
                line.setLineWidth(width)
                s, n = line.textStart(), line.textLength()
                lines.append((raw[s * 2:(s + n) * 2].decode("utf-16-le", "ignore").rstrip(), line.naturalTextWidth()))
            layout.endLayout()
            it["lines"] = lines or [("", 0.0)]
            it["h"] = len(it["lines"]) * fm.lineSpacing()
            it["y"] = y
            y += it["h"] + self.GAP
        self.content_h = y
        self.glow = None

    def _clamp(self, v):
        return clamp(v, -12, max(-12, self.content_h - self.height() * 0.55))

    def _follow(self):
        if 0 <= self.active < len(self.items):
            it = self.items[self.active]
            return self._clamp(it["y"] + it["h"] / 2 - self.height() * 0.34)
        return -12.0

    def _move_to(self, target, stagger):
        self.scroll_target = target
        now = time.monotonic()
        for i, it in enumerate(self.items):
            delay = 0.0
            if stagger and self.active >= 0 and i >= self.active - 1:
                delay = min(0.36, 0.045 * (i - self.active + 1))
            it["pending"] = (now + delay, target)
        self.animate()

    def set_position(self, pos):
        if not self.synced or not self.items:
            return
        idx = max(0, bisect.bisect_right(self.times, pos) - 1)
        if idx == self.active:
            return
        self.active = idx
        for i, it in enumerate(self.items):
            d = abs(i - idx)
            it["scale"].target = 1.0 if d == 0 else 0.94
            it["alpha"].target = 1.0 if d == 0 else (0.42 if d == 1 else 0.22)
        self.glow = None
        if time.monotonic() > self.user_scroll_until:
            self._move_to(self._follow(), stagger=True)
        self.animate()

    def resizeEvent(self, e):
        self._relayout()
        target = self._follow() if self.synced else self._clamp(self.scroll_target)
        self.scroll_target = target
        for it in self.items:
            it["scroll"].snap(target)
            it["pending"] = None
        super().resizeEvent(e)

    def showEvent(self, e):
        self.animate()
        super().showEvent(e)

    def wheelEvent(self, e):
        if e.modifiers() & Qt.KeyboardModifier.ControlModifier:
            step = 0.25 if e.angleDelta().y() > 0 else -0.25
            self.offset_step_requested.emit(step)
            e.accept()
            return
        if not self.items:
            return
        self.user_scroll_until = time.monotonic() + 4.0
        self._move_to(self._clamp(self.scroll_target - e.angleDelta().y() / 120 * 80), stagger=False)
        e.accept()

    def _progress(self, i, pos):
        t0 = self.items[i]["t"]
        t1 = self.items[i + 1]["t"] if i + 1 < len(self.items) else t0 + 4.0
        dur = clamp(t1 - t0, 0.35, 12.0)
        return clamp((pos - t0) / (dur * 0.94), 0.0, 1.0)

    def advance(self, dt):
        now = time.monotonic()
        moving = False
        for it in self.items:
            if it["pending"] and now >= it["pending"][0]:
                it["scroll"].target = it["pending"][1]
                it["pending"] = None
            moving = moving or it["pending"] is not None
            moving = it["scroll"].step(dt) or moving
            moving = it["scale"].step(dt) or moving
            moving = it["alpha"].step(dt) or moving
        if self.synced and self.user_scroll_until and now > self.user_scroll_until:
            self.user_scroll_until = 0.0
            self._move_to(self._follow(), stagger=False)
            moving = True
        playing = bool(self.clock and self.clock()[1])
        self._anim_timer.setInterval(16 if moving else 33)
        return moving or bool(self.user_scroll_until) or (self.synced and playing and self.isVisible())

    def _glow_for(self, i):
        if self.glow and self.glow[0] == i:
            return self.glow
        it = self.items[i]
        fm = QFontMetrics(self.font)
        pad = 16
        w = int(max(wd for _, wd in it["lines"]) + 2 * pad) + 1
        h = int(it["h"] + 2 * pad) + 1
        img = QImage(max(1, w), max(1, h), QImage.Format.Format_ARGB32_Premultiplied)
        img.fill(0)
        q = QPainter(img)
        q.setRenderHint(QPainter.RenderHint.TextAntialiasing)
        q.setFont(self.font)
        q.setPen(QColor(255, 255, 255, 200))
        for k, (text, _) in enumerate(it["lines"]):
            q.drawText(QPointF(pad, pad + k * fm.lineSpacing() + fm.ascent()), text)
        q.end()
        self.glow = (i, blur_qimage(img, 10), pad)
        return self.glow

    def paintEvent(self, e):
        p = QPainter(self)
        if not self.items:
            p.setPen(white(110))
            p.setFont(ui_font(13, QFont.Weight.Medium))
            p.drawText(self.rect(), Qt.AlignmentFlag.AlignCenter | Qt.TextFlag.TextWordWrap, self.message)
            return
        dpr = self.devicePixelRatioF()
        img = QImage(int(self.width() * dpr), int(self.height() * dpr), QImage.Format.Format_ARGB32_Premultiplied)
        img.setDevicePixelRatio(dpr)
        img.fill(0)
        q = QPainter(img)
        q.setRenderHint(QPainter.RenderHint.Antialiasing)
        q.setRenderHint(QPainter.RenderHint.TextAntialiasing)
        q.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        q.setFont(self.font)
        fm = QFontMetrics(self.font)
        ls, asc = fm.lineSpacing(), fm.ascent()
        pos = self.clock()[0] if self.clock else 0.0

        for i, it in enumerate(self.items):
            y = it["y"] - it["scroll"].value
            if y + it["h"] < -12 or y > self.height() + 12:
                continue
            s, a = it["scale"].value, it["alpha"].value
            q.save()
            q.translate(12, y + it["h"] * (1 - s) / 2)
            q.scale(s, s)
            if self.synced and i == self.active:
                _, glow, pad = self._glow_for(i)
                q.setOpacity(0.5 * clamp((s - 0.94) / 0.06, 0.0, 1.0))
                q.drawImage(QPointF(-pad, -pad), glow)
                q.setOpacity(1.0)
                total = sum(wd for _, wd in it["lines"]) or 1.0
                filled = self._progress(i, pos) * total
                acc = 0.0
                for k, (text, wd) in enumerate(it["lines"]):
                    local = clamp((filled - acc) / max(1.0, wd), 0.0, 1.0)
                    acc += wd
                    q.setPen(QPen(wipe_brush(0, wd, local, white(255 * a), white(255 * 0.38 * a)), 1))
                    q.drawText(QPointF(0, k * ls + asc), text)
            else:
                q.setPen(white(255 * a))
                for k, (text, _) in enumerate(it["lines"]):
                    q.drawText(QPointF(0, k * ls + asc), text)
            q.restore()

        q.setCompositionMode(QPainter.CompositionMode.CompositionMode_DestinationIn)
        g = QLinearGradient(0, 0, 0, self.height())
        g.setColorAt(0.0, QColor(0, 0, 0, 0))
        g.setColorAt(0.14, QColor(0, 0, 0, 255))
        g.setColorAt(0.80, QColor(0, 0, 0, 255))
        g.setColorAt(1.0, QColor(0, 0, 0, 0))
        q.fillRect(QRectF(0, 0, self.width(), self.height()), g)
        q.end()
        p.drawImage(0, 0, img)


# =====================================================================
# ФАЙЛОВАЯ ПОЛКА «DROPOVER SHELF» (ВРЕМЕННЫЙ КАРМАН ДЛЯ ФАЙЛОВ)
# =====================================================================
class DragAllButton(QPushButton):
    """Кнопка-хэндл: можно кликнуть или зажать и вытащить сразу ВСЕ файлы с полки."""
    drag_all_requested = pyqtSignal()

    def __init__(self, text="📤 Вытащить все", parent=None):
        super().__init__(text, parent)
        self._press_pos = None
        self.setCursor(Qt.CursorShape.OpenHandCursor)

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self._press_pos = e.position().toPoint()
            self.setCursor(Qt.CursorShape.ClosedHandCursor)
        super().mousePressEvent(e)

    def mouseMoveEvent(self, e):
        if self._press_pos is not None:
            if (e.position().toPoint() - self._press_pos).manhattanLength() > 6:
                self._press_pos = None
                self.setCursor(Qt.CursorShape.OpenHandCursor)
                self.drag_all_requested.emit()
                return
        super().mouseMoveEvent(e)

    def mouseReleaseEvent(self, e):
        self._press_pos = None
        self.setCursor(Qt.CursorShape.OpenHandCursor)
        super().mouseReleaseEvent(e)


class ShelfView(QWidget):
    """Сетка файлов на полке Dropover с поддержкой Drag-out и превью картинок."""
    remove_requested = pyqtSignal(int)
    open_requested = pyqtSignal(int)
    drag_started = pyqtSignal(list)

    CELL_W, CELL_H, THUMB = 112, 108, 56

    def __init__(self, parent=None):
        super().__init__(parent)
        self.files = []        # [{"path": str, "name": str, "size": int, "pix": QPixmap}]
        self.hover = -1
        self.press_idx = -1
        self.press_pos = None
        self.drop_highlight = False
        self.accent = QColor("#0A84FF")
        self.icon_provider = QFileIconProvider()
        self.setMouseTracking(True)
        self.setMinimumHeight(140)

    def set_files(self, paths: list):
        new_items = []
        for p in paths:
            if not p or not os.path.exists(p):
                continue
            info = QFileInfo(p)
            size = info.size() if info.isFile() else 0
            pix = self._make_preview(p, info)
            new_items.append({
                "path": p,
                "name": info.fileName() or os.path.basename(p),
                "size": size,
                "pix": pix
            })
        self.files = new_items
        self._relayout()
        self.update()

    def _make_preview(self, path: str, info: QFileInfo) -> QPixmap:
        ext = info.suffix().lower()
        if ext in ("png", "jpg", "jpeg", "webp", "bmp", "gif"):
            img = QImage(path)
            if not img.isNull():
                s = int(self.THUMB * 2)
                scaled = img.scaled(s, s, Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                                    Qt.TransformationMode.SmoothTransformation)
                x = (scaled.width() - s) // 2
                y = (scaled.height() - s) // 2
                return QPixmap.fromImage(scaled.copy(x, y, s, s))
        ic = self.icon_provider.icon(info)
        if not ic.isNull():
            return ic.pixmap(64, 64)
        return QPixmap()

    def _cols(self):
        return max(1, self.width() // self.CELL_W)

    def _relayout(self):
        n = max(1, len(self.files))
        rows = math.ceil(n / self._cols())
        h = max(145, rows * self.CELL_H + 10)
        if self.minimumHeight() != h:
            self.setMinimumHeight(h)

    def resizeEvent(self, e):
        self._relayout()
        super().resizeEvent(e)

    def _cell(self, i):
        cols = self._cols()
        x0 = (self.width() - cols * self.CELL_W) / 2
        return QRectF(x0 + (i % cols) * self.CELL_W + 4, (i // cols) * self.CELL_H + 4,
                      self.CELL_W - 8, self.CELL_H - 8)

    def _badge_del(self, i):
        c = self._cell(i)
        return QRectF(c.right() - 22, c.top() + 4, 18, 18)

    def _hit(self, pos):
        for i in range(len(self.files)):
            if self._cell(i).contains(pos):
                return i
        return -1

    def mouseMoveEvent(self, e):
        if self.press_idx >= 0 and self.press_pos is not None:
            if (e.position() - self.press_pos).manhattanLength() > 7:
                idx = self.press_idx
                self.press_idx = -1
                self.press_pos = None
                if 0 <= idx < len(self.files):
                    self.drag_started.emit([self.files[idx]["path"]])
                return
        h = self._hit(e.position())
        self.setCursor(Qt.CursorShape.OpenHandCursor if h >= 0 else Qt.CursorShape.ArrowCursor)
        if h != self.hover:
            self.hover = h
            self.update()

    def leaveEvent(self, e):
        self.hover = -1
        self.update()

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            i = self._hit(e.position())
            if i >= 0:
                if self._badge_del(i).adjusted(-3, -3, 3, 3).contains(e.position()):
                    self.remove_requested.emit(i)
                    return
                self.press_idx = i
                self.press_pos = e.position()
                self.setCursor(Qt.CursorShape.ClosedHandCursor)
                e.accept()
                return
        e.ignore()

    def mouseReleaseEvent(self, e):
        self.press_idx = -1
        self.press_pos = None
        self.setCursor(Qt.CursorShape.OpenHandCursor if self.hover >= 0 else Qt.CursorShape.ArrowCursor)

    def mouseDoubleClickEvent(self, e):
        i = self._hit(e.position())
        if i >= 0:
            self.open_requested.emit(i)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setRenderHint(QPainter.RenderHint.TextAntialiasing)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)

        if self.drop_highlight:
            p.setPen(QPen(self.accent, 2, Qt.PenStyle.DashLine))
            p.setBrush(with_alpha(self.accent, 35))
            p.drawRoundedRect(QRectF(self.rect()).adjusted(2, 2, -2, -2), 16, 16)

        if not self.files:
            p.setPen(QPen(white(40), 1.4, Qt.PenStyle.DashLine))
            p.setBrush(white(10))
            box = QRectF(self.rect()).adjusted(4, 4, -4, -4)
            p.drawRoundedRect(box, 16, 16)
            p.setPen(white(135))
            p.setFont(ui_font(13, QFont.Weight.DemiBold))
            p.drawText(
                box, Qt.AlignmentFlag.AlignCenter,
                "📥 Перетащите сюда файлы, картинки или архивы\n"
                "Они подождут здесь, пока вы переключите окно, чтобы вытащить их обратно"
            )
            return

        fm_name = QFontMetrics(ui_font(11.5, QFont.Weight.DemiBold))
        for i, it in enumerate(self.files):
            cell = self._cell(i)
            p.setPen(QPen(white(38 if i == self.hover else 18), 1))
            p.setBrush(white(32 if i == self.hover else 16))
            p.drawRoundedRect(cell, 14, 14)

            tr = QRectF(cell.center().x() - self.THUMB / 2, cell.top() + 8, self.THUMB, self.THUMB)
            pix = it["pix"]
            if pix and not pix.isNull():
                path = QPainterPath()
                path.addRoundedRect(tr, 10, 10)
                p.save()
                p.setClipPath(path)
                p.drawPixmap(tr.toRect(), pix)
                p.restore()
            else:
                p.setFont(emoji_font(28))
                p.setPen(white(230))
                p.drawText(tr, Qt.AlignmentFlag.AlignCenter, "📄")

            p.setFont(ui_font(11.5, QFont.Weight.DemiBold))
            p.setPen(white(235))
            name_rect = QRectF(cell.left() + 6, tr.bottom() + 4, cell.width() - 12, 16)
            p.drawText(name_rect, Qt.AlignmentFlag.AlignCenter,
                       fm_name.elidedText(it["name"], Qt.TextElideMode.ElideMiddle, int(name_rect.width())))

            p.setFont(ui_font(10))
            p.setPen(white(120))
            size_rect = QRectF(cell.left() + 6, name_rect.bottom(), cell.width() - 12, 14)
            p.drawText(size_rect, Qt.AlignmentFlag.AlignCenter, fmt_size(it["size"]))

            if i == self.hover:
                b = self._badge_del(i)
                p.setPen(Qt.PenStyle.NoPen)
                p.setBrush(QColor(255, 69, 58, 220))
                p.drawEllipse(b)
                p.setPen(QPen(white(255), 1.8, cap=Qt.PenCapStyle.RoundCap))
                cx, cy = b.center().x(), b.center().y()
                p.drawLine(QPointF(cx - 3.5, cy - 3.5), QPointF(cx + 3.5, cy + 3.5))
                p.drawLine(QPointF(cx + 3.5, cy - 3.5), QPointF(cx - 3.5, cy + 3.5))


class ShortcutGrid(QWidget):
    """Сетка ярлыков в виде иконок приложений iOS."""
    launch = pyqtSignal(int)
    remove = pyqtSignal(int)
    add_requested = pyqtSignal()

    CELL_W, CELL_H, ICON = 80, 88, 52

    def __init__(self, parent=None):
        super().__init__(parent)
        self.items = []
        self.hover = -1
        self.pressed = -1
        self.accent = QColor("#0A84FF")
        self.setMouseTracking(True)

    def set_items(self, items):
        self.items = list(items)
        self._relayout()
        self.update()

    def _cols(self):
        return max(1, self.width() // self.CELL_W)

    def _relayout(self):
        n = len(self.items) + 1
        rows = math.ceil(n / self._cols())
        h = rows * self.CELL_H + 4
        if self.minimumHeight() != h:
            self.setMinimumHeight(h)

    def resizeEvent(self, e):
        self._relayout()
        super().resizeEvent(e)

    def _cell(self, i):
        cols = self._cols()
        x0 = (self.width() - cols * self.CELL_W) / 2
        return QRectF(x0 + (i % cols) * self.CELL_W, (i // cols) * self.CELL_H, self.CELL_W, self.CELL_H)

    def _icon(self, i):
        c = self._cell(i)
        return QRectF(c.center().x() - self.ICON / 2, c.top() + 8, self.ICON, self.ICON)

    def _badge(self, i):
        r = self._icon(i)
        return QRectF(r.left() - 6, r.top() - 6, 20, 20)

    def _hit(self, pos):
        for i in range(len(self.items) + 1):
            if self._cell(i).contains(pos):
                return i
        return -1

    def mouseMoveEvent(self, e):
        h = self._hit(e.position())
        self.setCursor(Qt.CursorShape.PointingHandCursor if h >= 0 else Qt.CursorShape.ArrowCursor)
        if h != self.hover:
            self.hover = h
            self.update()

    def leaveEvent(self, e):
        self.hover = -1
        self.update()

    def mousePressEvent(self, e):
        self.pressed = self._hit(e.position())
        if self.pressed < 0:
            e.ignore()
            return
        self.update()

    def mouseReleaseEvent(self, e):
        i, self.pressed = self.pressed, -1
        self.update()
        if i < 0 or self._hit(e.position()) != i:
            return
        if i == len(self.items):
            self.add_requested.emit()
        elif self._badge(i).adjusted(-4, -4, 4, 4).contains(e.position()):
            self.remove.emit(i)
        else:
            self.launch.emit(i)

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setRenderHint(QPainter.RenderHint.TextAntialiasing)
        fm_label = QFontMetrics(ui_font(11, QFont.Weight.Medium))
        for i in range(len(self.items) + 1):
            cell, icon = self._cell(i), self._icon(i)
            if i == self.pressed:
                icon = QRectF(icon.center().x() - self.ICON * 0.46, icon.center().y() - self.ICON * 0.46,
                              self.ICON * 0.92, self.ICON * 0.92)
            path = QPainterPath()
            path.addRoundedRect(icon, icon.width() * 0.26, icon.width() * 0.26)
            if i == len(self.items):
                p.fillPath(path, white(28 if i == self.hover else 18))
                p.setPen(QPen(white(200), 2.2, cap=Qt.PenCapStyle.RoundCap))
                c = icon.center()
                p.drawLine(QPointF(c.x() - 9, c.y()), QPointF(c.x() + 9, c.y()))
                p.drawLine(QPointF(c.x(), c.y() - 9), QPointF(c.x(), c.y() + 9))
                label = "Добавить"
            else:
                sc = self.items[i]
                col = QColor(sc.get("color") or self.accent.name())
                g = QLinearGradient(icon.topLeft(), icon.bottomLeft())
                g.setColorAt(0.0, col.lighter(118))
                g.setColorAt(1.0, col.darker(135))
                p.fillPath(path, QBrush(g))
                sheen = QLinearGradient(icon.topLeft(), icon.bottomLeft())
                sheen.setColorAt(0.0, white(60))
                sheen.setColorAt(0.5, white(0))
                p.fillPath(path, QBrush(sheen))
                if i == self.hover:
                    p.fillPath(path, white(22))
                p.setPen(QPen(white(40), 0.8))
                p.drawPath(path)
                p.setFont(emoji_font(icon.width() * 0.46))
                p.setPen(QColor(255, 255, 255))
                p.drawText(icon, Qt.AlignmentFlag.AlignCenter, sc.get("icon", "🔗"))
                label = sc.get("name", "")
            p.setFont(ui_font(11, QFont.Weight.Medium))
            p.setPen(white(225))
            p.drawText(QRectF(cell.left() + 2, cell.top() + 8 + self.ICON + 6, cell.width() - 4, 16),
                       Qt.AlignmentFlag.AlignHCenter | Qt.AlignmentFlag.AlignTop,
                       fm_label.elidedText(label, Qt.TextElideMode.ElideRight, int(cell.width() - 4)))
            if i == self.hover and i < len(self.items):
                b = self._badge(i)
                p.setPen(QPen(white(60), 0.8))
                p.setBrush(QColor(58, 58, 62, 245))
                p.drawEllipse(b)
                p.setPen(QPen(QColor(255, 255, 255), 2, cap=Qt.PenCapStyle.RoundCap))
                p.drawLine(QPointF(b.center().x() - 4.5, b.center().y()), QPointF(b.center().x() + 4.5, b.center().y()))


class ClipList(QWidget):
    """Список истории буфера обмена с быстрыми кнопками «🌐 Перевод» и «✦ ИИ» на каждой строке."""
    picked = pyqtSignal(int)
    translate_requested = pyqtSignal(int)
    ai_requested = pyqtSignal(int)

    ROW, GAP = 50, 6

    def __init__(self, parent=None):
        super().__init__(parent)
        self.items = []
        self.hover = -1
        self.hover_btn = ""   # "" | "tr" | "ai"
        self.flash = -1
        self.accent = QColor("#0A84FF")
        self.flash_timer = QTimer(self)
        self.flash_timer.setSingleShot(True)
        self.flash_timer.timeout.connect(self._end_flash)
        self.setMouseTracking(True)
        self.setMinimumHeight(120)

    def set_items(self, items):
        self.items = list(items)
        self.flash = -1
        self.setMinimumHeight(max(120, len(self.items) * (self.ROW + self.GAP)))
        self.update()

    def flash_row(self, i):
        self.flash = i
        self.flash_timer.start(1300)
        self.update()

    def _end_flash(self):
        self.flash = -1
        self.update()

    def _row_rect(self, i):
        return QRectF(0, i * (self.ROW + self.GAP), self.width(), self.ROW)

    def _btn_rects(self, i):
        r = self._row_rect(i)
        ai_r = QRectF(r.right() - 62, r.top() + 12, 52, 26)
        tr_r = QRectF(ai_r.left() - 88, r.top() + 12, 82, 26)
        return tr_r, ai_r

    def _hit(self, y):
        i = int(y // (self.ROW + self.GAP))
        return i if 0 <= i < len(self.items) and (y % (self.ROW + self.GAP)) < self.ROW else -1

    def mouseMoveEvent(self, e):
        pos = e.position()
        h = self._hit(pos.y())
        btn = ""
        if h >= 0:
            tr_r, ai_r = self._btn_rects(h)
            if tr_r.contains(pos):
                btn = "tr"
            elif ai_r.contains(pos):
                btn = "ai"
        self.setCursor(Qt.CursorShape.PointingHandCursor if h >= 0 else Qt.CursorShape.ArrowCursor)
        if h != self.hover or btn != self.hover_btn:
            self.hover = h
            self.hover_btn = btn
            self.update()

    def leaveEvent(self, e):
        self.hover = -1
        self.hover_btn = ""
        self.update()

    def mousePressEvent(self, e):
        if self._hit(e.position().y()) < 0:
            e.ignore()

    def mouseReleaseEvent(self, e):
        pos = e.position()
        i = self._hit(pos.y())
        if i >= 0:
            tr_r, ai_r = self._btn_rects(i)
            if tr_r.contains(pos):
                self.translate_requested.emit(i)
            elif ai_r.contains(pos):
                self.ai_requested.emit(i)
            else:
                self.picked.emit(i)

    @staticmethod
    def _ago(ts):
        d = time.time() - ts
        if d < 60:
            return "только что"
        if d < 3600:
            return f"{int(d // 60)} мин назад"
        return f"{int(d // 3600)} ч назад"

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setRenderHint(QPainter.RenderHint.TextAntialiasing)
        w = self.width()
        if not self.items:
            p.setPen(white(110))
            p.setFont(ui_font(13, QFont.Weight.Medium))
            p.drawText(self.rect(), Qt.AlignmentFlag.AlignCenter,
                       "Скопируйте что-нибудь — история появится здесь")
            return
        f_main = ui_font(13, QFont.Weight.Medium)
        f_meta = ui_font(11)
        fm_main = QFontMetrics(f_main)
        for i, (text, ts) in enumerate(self.items):
            r = self._row_rect(i)
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(white(30 if i == self.hover else 16))
            p.drawRoundedRect(r, 12, 12)

            if i == self.flash:
                right_pad = 120
            elif i == self.hover:
                right_pad = 158
            else:
                right_pad = 14

            one_line = " ".join(text.split())
            p.setFont(f_main)
            p.setPen(white(235))
            p.drawText(QRectF(r.left() + 14, r.top() + 7, max(40, w - 14 - right_pad), 20),
                       Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter,
                       fm_main.elidedText(one_line, Qt.TextElideMode.ElideRight, int(max(40, w - 14 - right_pad))))
            p.setFont(f_meta)
            p.setPen(white(115))
            p.drawText(QRectF(r.left() + 14, r.top() + 27, max(40, w - 14 - right_pad), 16),
                       Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter,
                       f"{len(text)} симв. · {self._ago(ts)}")

            if i == self.flash:
                p.setFont(ui_font(12, QFont.Weight.DemiBold))
                p.setPen(self.accent)
                p.drawText(QRectF(r.right() - 120, r.top(), 106, r.height()),
                           Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter, "✓ Скопировано")
            elif i == self.hover:
                tr_r, ai_r = self._btn_rects(i)
                p.setPen(QPen(white(35), 0.8))
                p.setBrush(self.accent if self.hover_btn == "tr" else white(38))
                p.drawRoundedRect(tr_r, 8, 8)
                p.setFont(ui_font(11, QFont.Weight.DemiBold))
                p.setPen(white(245))
                p.drawText(tr_r, Qt.AlignmentFlag.AlignCenter, "🌐 Перевод")

                p.setBrush(self.accent if self.hover_btn == "ai" else white(38))
                p.drawRoundedRect(ai_r, 8, 8)
                p.drawText(ai_r, Qt.AlignmentFlag.AlignCenter, "✦ ИИ")


class ColorDots(QWidget):
    picked = pyqtSignal(str)
    custom_requested = pyqtSignal()

    D, GAP = 22, 9

    def __init__(self, current, parent=None):
        super().__init__(parent)
        self.colors = [c for _, c in PRESET_ACCENTS]
        self.current = current.upper()
        n = len(self.colors) + 1
        self.setFixedSize(n * self.D + (n - 1) * self.GAP + 6, self.D + 8)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setToolTip("Акцентный цвет")

    def set_current(self, c):
        self.current = c.upper()
        self.update()

    def _rect(self, i):
        return QRectF(3 + i * (self.D + self.GAP), 4, self.D, self.D)

    def mouseReleaseEvent(self, e):
        for i in range(len(self.colors) + 1):
            if self._rect(i).adjusted(-4, -4, 4, 4).contains(e.position()):
                if i == len(self.colors):
                    self.custom_requested.emit()
                else:
                    self.picked.emit(self.colors[i])
                return

    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        custom_selected = self.current not in [c.upper() for c in self.colors]
        for i in range(len(self.colors) + 1):
            r = self._rect(i)
            if i < len(self.colors):
                p.setPen(Qt.PenStyle.NoPen)
                p.setBrush(QColor(self.colors[i]))
                selected = self.colors[i].upper() == self.current
            else:
                g = QConicalGradient(r.center(), 90)
                for k, c in enumerate(["#FF453A", "#FF9F0A", "#FFD60A", "#30D158", "#64D2FF", "#0A84FF", "#BF5AF2", "#FF453A"]):
                    g.setColorAt(k / 7, QColor(c))
                p.setPen(Qt.PenStyle.NoPen)
                p.setBrush(QBrush(g))
                selected = custom_selected
            p.drawEllipse(r)
            if selected:
                p.setBrush(Qt.BrushStyle.NoBrush)
                p.setPen(QPen(QColor(255, 255, 255), 2))
                p.drawEllipse(r.adjusted(-3, -3, 3, 3))


# =====================================================================
# ГЛАВНЫЙ ВИДЖЕТ: DYNAMIC ISLAND
# =====================================================================
class DynamicIsland(QWidget):
    paste_signal = pyqtSignal()

    COMPACT = "compact"
    EXPANDED = "expanded"

    TABS = ["Музыка", "Полка", "Ярлыки", "Буфер", "Настройки"]
    VARIANTS = ("idle", "music", "toast", "timer", "volume", "device", "recording")

    def __init__(self):
        super().__init__()
        self.config = self.load_config()
        self.accent = QColor(self.config.get("accent", "#0A84FF"))
        self.mode = self.COMPACT

        # Медиа, синхронизация времени и тексты
        self.media = dict(NO_MEDIA, key="")
        self.pos_base = 0.0
        self.pos_stamp = time.monotonic()
        self.last_raw_pos = -1.0
        self.synced_lyrics = []
        self.lyrics_key = None
        self.lyrics_cache = {}
        self.lyric_text = ""
        self.lyric_prev = ""
        self.lyric_idx = -1
        self.lyric_anim = Spring(1.0, 0.5, 0.8, eps=0.002)
        self.art_image = None
        self.art_pix = None
        self.art_color = QColor(self.accent)

        # Статус системы, буфер, тосты, помодоро, громкость, наушники, диктовка
        self.status = {
            "vpn": False, "proxy": False, "proxy_server": "",
            "karing": False, "karing_exe": "", "tun": False,
            "detected_port": None, "cpu": 0, "ram": 0
        }
        self._proxy_lock_until = 0.0
        self.clip_history = []
        self.ignore_next_clip = False

        # Тосты (с поддержкой кнопки «Перевести ✦»)
        self.toast = None
        self.toast_action = None       # None | "translate"
        self.toast_source_text = ""
        self.toast_btn_rect = QRectF()

        # Volume HUD (Фича 6)
        self.volume_banner = None      # (percent: int, muted: bool)
        self.vol_bar_spring = Spring(0.5, 0.28, 0.84, eps=0.002)

        # Уведомление о наушниках / Bluetooth / геймпаде (Фича 8)
        self.device_banner = None      # (icon: str, title: str, subtitle: str, connected: bool)
        self.device_pulse = Spring(1.0, 0.45, 0.55, eps=0.002)

        # Диктовка / Голосовые заметки (Фича 5)
        self.voice_recorder = VoiceRecorder()
        self.dictation_active = False
        self.last_voice_wav = ""
        self.transcribe_worker = None

        # Файловая полка Dropover (Фича 1)
        self.shelf_files = [p for p in self.config.get("shelf_files", []) if os.path.exists(p)]
        self.config["shelf_files"] = self.shelf_files
        self.external_drag_over = False

        # Помощник перевода/ИИ и OCR/Пипетка
        self.assistant_worker = None
        self.ocr_worker = None
        self.active_overlay = None

        # Фокус-таймер
        self.pomo_total = 25 * 60
        self.pomo_left = self.pomo_total
        self.pomo_running = False

        # Взаимодействие
        self.press_global = None
        self.press_zone = None
        self.drag_active = False
        self.press_start = None
        self.hovered = False
        self.dialog_open = False
        self.home_pos = None
        self.click_through = None

        # Подложка стекла
        self.backdrop = None
        self.backdrop_rect = None
        self.last_capture = 0.0

        # Окно
        self.setWindowFlags(
            Qt.WindowType.FramelessWindowHint |
            Qt.WindowType.WindowStaysOnTopHint |
            Qt.WindowType.Tool
        )
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, True)
        self.setMouseTracking(True)
        self.setAcceptDrops(True)
        self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        self.setWindowTitle("Dynamic Island")

        # Пружины формы и положения
        self.sw = Spring(200, eps=0.08)
        self.sh = Spring(36, eps=0.08)
        self.sr = Spring(18, eps=0.08)
        self.scx = Spring(0, 0.38, 0.82, eps=0.08)
        self.stop = Spring(DEFAULT_TOP, 0.38, 0.82, eps=0.08)
        self.sscale = Spring(1.0, 0.32, 0.62, eps=0.0005)
        self.slift = Spring(0.0, 0.35, 0.9, eps=0.002)
        self.compact_alpha = Fade(1.0, 20)
        self.content_alpha = Fade(0.0, 16)
        self.variant_alpha = {k: Fade(1.0 if k == "idle" else 0.0, 14) for k in self.VARIANTS}
        self.wave_t = 0.0

        self.anim_clock = time.perf_counter()
        self.anim_timer = QTimer(self)
        self.anim_timer.setTimerType(Qt.TimerType.PreciseTimer)
        self.anim_timer.setInterval(16)
        self.anim_timer.timeout.connect(self._tick)

        self._build_content()
        self._init_clipboard_and_hotkeys()
        self._init_workers_and_timers()
        self._init_tray()
        self._place_initial()

    # -----------------------------------------------------------------
    # КОНФИГУРАЦИЯ И АВТОЗАПУСК
    # -----------------------------------------------------------------
    def load_config(self):
        merged = json.loads(json.dumps(DEFAULT_CONFIG))
        if CONFIG_FILE.exists():
            try:
                with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                    merged.update(json.load(f))
            except Exception:
                pass
        if not isinstance(merged.get("lyrics_offsets"), dict):
            merged["lyrics_offsets"] = {}
        if not isinstance(merged.get("shelf_files"), list):
            merged["shelf_files"] = []
        return merged

    def save_config(self):
        if not hasattr(self, "_save_timer"):
            self._save_timer = QTimer(self)
            self._save_timer.setSingleShot(True)
            self._save_timer.timeout.connect(self._write_config)
        self._save_timer.start(400)

    def _write_config(self):
        try:
            with open(CONFIG_FILE, "w", encoding="utf-8") as f:
                json.dump(self.config, f, ensure_ascii=False, indent=2)
        except Exception as e:
            print("Ошибка сохранения конфига:", e)

    def set_autostart(self, enabled: bool):
        key_path = r"Software\Microsoft\Windows\CurrentVersion\Run"
        app_name = "WindowsDynamicIslandGlass"
        if getattr(sys, "frozen", False):
            exe_cmd = f'"{sys.executable}"'
        else:
            pythonw = Path(sys.executable).with_name("pythonw.exe")
            exe = pythonw if pythonw.exists() else Path(sys.executable)
            exe_cmd = f'"{exe}" "{os.path.abspath(__file__)}"'

        try:
            key = winreg.OpenKey(winreg.HKEY_CURRENT_USER, key_path, 0, winreg.KEY_SET_VALUE)
            if enabled:
                winreg.SetValueEx(key, app_name, 0, winreg.REG_SZ, exe_cmd)
            else:
                try:
                    winreg.DeleteValue(key, app_name)
                except FileNotFoundError:
                    pass
            winreg.CloseKey(key)
            self.config["autostart"] = enabled
            self.save_config()
        except Exception as e:
            print("Ошибка реестра автозапуска:", e)

    # -----------------------------------------------------------------
    # РАЗВЁРНУТЫЙ ИНТЕРФЕЙС
    # -----------------------------------------------------------------
    def _stylesheet(self):
        a = self.accent
        acc = a.name()
        acc_hover = a.lighter(115).name()
        acc_soft = f"rgba({a.red()},{a.green()},{a.blue()},170)"
        return f"""
            QWidget {{ color: white; font-family: "{FONT_TEXT}"; }}
            QLabel {{ background: transparent; }}
            QLabel#h1 {{ font-family: "{FONT_DISPLAY}"; font-size: 17px; font-weight: 700; }}
            QLabel#h2 {{ font-size: 13px; font-weight: 600; color: rgba(255,255,255,150); }}
            QLabel#row {{ font-size: 13px; }}
            QLabel#caption {{ font-size: 11px; color: rgba(255,255,255,120); }}
            QStackedWidget, QWidget#page {{ background: transparent; }}
            QScrollArea {{ background: transparent; border: none; }}
            QScrollArea > QWidget > QWidget {{ background: transparent; }}
            QScrollBar:vertical {{ width: 6px; background: transparent; margin: 4px 0; }}
            QScrollBar::handle:vertical {{ background: rgba(255,255,255,55); border-radius: 3px; min-height: 30px; }}
            QScrollBar::handle:vertical:hover {{ background: rgba(255,255,255,95); }}
            QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {{ height: 0; }}
            QScrollBar::add-page:vertical, QScrollBar::sub-page:vertical {{ background: none; }}
            QFrame#group {{ background: rgba(255,255,255,16); border-radius: 14px; }}
            QFrame#sep {{ background: rgba(255,255,255,20); border: none; }}
            QLineEdit {{
                background: rgba(255,255,255,20); border: 1px solid rgba(255,255,255,22);
                border-radius: 10px; padding: 6px 10px; font-size: 12px; color: white;
                selection-background-color: {acc};
            }}
            QLineEdit:focus {{ border: 1px solid {acc_soft}; background: rgba(255,255,255,28); }}
            QPushButton {{ border: none; color: white; font-size: 12px; font-weight: 600; }}
            QPushButton#pill {{ background: rgba(255,255,255,30); border-radius: 10px; padding: 7px 12px; }}
            QPushButton#pill:hover {{ background: rgba(255,255,255,46); }}
            QPushButton#pill:pressed {{ background: rgba(255,255,255,20); }}
            QPushButton#accent {{ background: {acc}; border-radius: 10px; padding: 7px 14px; }}
            QPushButton#accent:hover {{ background: {acc_hover}; }}
            QPushButton#text {{ background: transparent; color: {acc}; font-size: 13px; padding: 4px 6px; }}
            QPushButton#text:hover {{ color: {acc_hover}; }}
            QPushButton#danger {{ background: transparent; color: #FF453A; font-size: 13px; padding: 4px 6px; }}
            QPushButton#chip {{ background: rgba(255,255,255,26); border-radius: 11px; padding: 4px 10px; font-size: 11px; }}
            QPushButton#chip:hover {{ background: rgba(255,255,255,42); }}
            QPushButton#chip:checked {{ background: {acc}; }}
            QSlider {{ background: transparent; min-height: 22px; }}
            QSlider::groove:horizontal {{ height: 4px; background: rgba(255,255,255,45); border-radius: 2px; }}
            QSlider::sub-page:horizontal {{ background: {acc}; border-radius: 2px; }}
            QSlider::handle:horizontal {{ background: white; width: 20px; height: 20px; margin: -8px 0; border-radius: 10px; }}
        """

    def _build_content(self):
        self.content = QWidget(self)
        self.content.setObjectName("content")
        self.content.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, True)
        self.content.setStyleSheet(self._stylesheet())

        layout = QVBoxLayout(self.content)
        layout.setContentsMargins(18, 14, 18, 12)
        layout.setSpacing(12)

        header = QHBoxLayout()
        header.setSpacing(10)
        self.segmented = Segmented(self.TABS)
        self.segmented.changed.connect(self.switch_tab)
        self.btn_collapse = IconButton("chevron_up", 30, 1.0, filled=True)
        self.btn_collapse.setToolTip("Свернуть (Esc)")
        self.btn_collapse.clicked.connect(self.collapse)
        header.addWidget(self.segmented, 1)
        header.addWidget(self.btn_collapse)
        layout.addLayout(header)

        self.pages = QStackedWidget()
        self.pages.addWidget(self._build_player_page())     # 0: Музыка
        self.pages.addWidget(self._build_shelf_page())      # 1: Полка (Dropover)
        self.pages.addWidget(self._build_shortcuts_page())  # 2: Ярлыки + Инструменты
        self.pages.addWidget(self._build_clipboard_page())  # 3: Буфер + Перевод/ИИ
        self.pages.addWidget(self._build_settings_page())   # 4: Настройки
        layout.addWidget(self.pages, 1)

        tab = clamp(int(self.config.get("last_tab", 0)), 0, len(self.TABS) - 1)
        self.segmented.set_index(tab, animate=False)
        self.pages.setCurrentIndex(tab)
        self.content.hide()

    @staticmethod
    def _page():
        page = QWidget()
        page.setObjectName("page")
        return page

    @staticmethod
    def _scroll(widget):
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        scroll.viewport().setAutoFillBackground(False)
        widget.setAutoFillBackground(False)
        scroll.setWidget(widget)
        return scroll

    # ---- 0. Музыка ----------------------------------------------------
    def _build_player_page(self):
        page = self._page()
        layout = QVBoxLayout(page)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(10)

        top = QHBoxLayout()
        top.setSpacing(14)
        self.artwork = Artwork(88)
        self.artwork.set_image(None, self.accent)
        top.addWidget(self.artwork, 0, Qt.AlignmentFlag.AlignTop)

        info = QVBoxLayout()
        info.setSpacing(2)
        title_row = QHBoxLayout()
        title_row.setSpacing(6)
        self.lbl_title = ElidedLabel("Ничего не играет", 17, QFont.Weight.Bold, display=True)

        self.btn_sync_minus = QPushButton("–0.5с")
        self.btn_sync_minus.setObjectName("chip")
        self.btn_sync_minus.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_sync_minus.setToolTip("Замедлить текст на 0.5 сек (если текст спешит)")
        self.btn_sync_minus.clicked.connect(lambda: self.adjust_lyrics_offset(-0.5))

        self.btn_sync_reset = QPushButton("0.0с")
        self.btn_sync_reset.setObjectName("chip")
        self.btn_sync_reset.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_sync_reset.setToolTip("Текущий сдвиг текста (нажмите для сброса в 0)")
        self.btn_sync_reset.clicked.connect(lambda: self.adjust_lyrics_offset(0.0, reset=True))
        self.btn_sync_reset.hide()

        self.btn_sync_plus = QPushButton("+0.5с")
        self.btn_sync_plus.setObjectName("chip")
        self.btn_sync_plus.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_sync_plus.setToolTip("Ускорить текст на 0.5 сек (если текст отстаёт)")
        self.btn_sync_plus.clicked.connect(lambda: self.adjust_lyrics_offset(0.5))

        self.btn_demo = QPushButton("Демо")
        self.btn_demo.setObjectName("chip")
        self.btn_demo.setCheckable(True)
        self.btn_demo.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_demo.setToolTip("Включить демо-трек с синхронным текстом")
        self.btn_demo.toggled.connect(self.toggle_demo_track)

        self.player_wave = WaveBars()
        title_row.addWidget(self.lbl_title, 1)
        title_row.addWidget(self.btn_sync_minus)
        title_row.addWidget(self.btn_sync_reset)
        title_row.addWidget(self.btn_sync_plus)
        title_row.addWidget(self.btn_demo)
        title_row.addWidget(self.player_wave)
        info.addLayout(title_row)

        self.lbl_artist = ElidedLabel("Запустите Яндекс Музыку, Spotify или браузер", 13, QFont.Weight.Medium,
                                      color=white(150))
        info.addWidget(self.lbl_artist)
        info.addSpacing(6)
        self.progress = ProgressBar()
        info.addWidget(self.progress)

        controls = QHBoxLayout()
        controls.setSpacing(16)
        controls.addStretch()
        self.btn_prev = IconButton("prev", 42, 0.9, filled=True)
        self.btn_play = IconButton("play", 50, 1.0, primary=True)
        self.btn_next = IconButton("next", 42, 0.9, filled=True)
        self.btn_prev.clicked.connect(lambda: self.send_media_key(0xB1))
        self.btn_play.clicked.connect(self.on_play_pause)
        self.btn_next.clicked.connect(lambda: self.send_media_key(0xB0))
        for b in (self.btn_prev, self.btn_play, self.btn_next):
            controls.addWidget(b)
        controls.addStretch()
        info.addLayout(controls)
        top.addLayout(info, 1)
        layout.addLayout(top)

        self.lyrics_view = LyricsView()
        self.lyrics_view.set_clock(lambda: (self.current_lyric_position(), bool(self.media.get("playing"))))
        self.lyrics_view.offset_step_requested.connect(self.adjust_lyrics_offset)
        self.lyrics_view.set_lyrics([], "", "Текст песни появится автоматически.\nПотяните остров за нижний край, чтобы видеть больше строк.")
        layout.addWidget(self.lyrics_view, 1)
        return page

    # ---- 1. Файловая полка Dropover -----------------------------------
    def _build_shelf_page(self):
        page = self._page()
        layout = QVBoxLayout(page)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(8)

        head = QHBoxLayout()
        head.setSpacing(8)
        title = QLabel("Файловая полка")
        title.setObjectName("h1")
        self.lbl_shelf_count = QLabel("пусто")
        self.lbl_shelf_count.setObjectName("caption")

        self.btn_drag_all = DragAllButton("📤 Вытащить все")
        self.btn_drag_all.setObjectName("accent")
        self.btn_drag_all.setToolTip("Зажмите кнопку и потяните все файлы сразу в Telegram, браузер или папку")
        self.btn_drag_all.drag_all_requested.connect(lambda: self.start_shelf_drag(self.shelf_files))
        self.btn_drag_all.clicked.connect(self.copy_shelf_files_to_clipboard)

        btn_copy_all = QPushButton("📋 В буфер")
        btn_copy_all.setObjectName("pill")
        btn_copy_all.setCursor(Qt.CursorShape.PointingHandCursor)
        btn_copy_all.setToolTip("Скопировать все файлы с полки в буфер обмена (для Ctrl+V)")
        btn_copy_all.clicked.connect(self.copy_shelf_files_to_clipboard)

        btn_add_files = QPushButton("➕ Файлы")
        btn_add_files.setObjectName("pill")
        btn_add_files.setCursor(Qt.CursorShape.PointingHandCursor)
        btn_add_files.clicked.connect(self.pick_files_for_shelf)

        btn_clear_shelf = QPushButton("Очистить")
        btn_clear_shelf.setObjectName("text")
        btn_clear_shelf.setCursor(Qt.CursorShape.PointingHandCursor)
        btn_clear_shelf.clicked.connect(self.clear_shelf)

        head.addWidget(title)
        head.addWidget(self.lbl_shelf_count, 0, Qt.AlignmentFlag.AlignBottom)
        head.addStretch()
        head.addWidget(self.btn_drag_all)
        head.addWidget(btn_copy_all)
        head.addWidget(btn_add_files)
        head.addWidget(btn_clear_shelf)
        layout.addLayout(head)

        self.shelf_view = ShelfView()
        self.shelf_view.accent = self.accent
        self.shelf_view.remove_requested.connect(self.remove_from_shelf)
        self.shelf_view.open_requested.connect(self.open_from_shelf)
        self.shelf_view.drag_started.connect(self.start_shelf_drag)
        layout.addWidget(self._scroll(self.shelf_view), 1)
        self._refresh_shelf_ui()
        return page

    # ---- 2. Ярлыки, быстрые инструменты (OCR, Пипетка, Диктовка) и VPN --
    def _build_shortcuts_page(self):
        page = self._page()
        layout = QVBoxLayout(page)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(10)

        # Панель быстрых инструментов: OCR, Пипетка, Диктовка, На полку
        tools = QHBoxLayout()
        tools.setSpacing(8)
        btn_ocr = QPushButton("🔍 Сканер текста (OCR)")
        btn_ocr.setObjectName("pill")
        btn_ocr.setCursor(Qt.CursorShape.PointingHandCursor)
        btn_ocr.setToolTip("Выделить область экрана и распознать текст в буфер обмена")
        btn_ocr.clicked.connect(self.start_screen_ocr)

        btn_picker = QPushButton("🎨 Пипетка цвета")
        btn_picker.setObjectName("pill")
        btn_picker.setCursor(Qt.CursorShape.PointingHandCursor)
        btn_picker.setToolTip("Выбрать цвет любого пикселя на экране с лупой (копирует #HEX)")
        btn_picker.clicked.connect(self.start_color_picker)

        self.btn_quick_mic = QPushButton("🎙️ Диктовка")
        self.btn_quick_mic.setObjectName("pill")
        self.btn_quick_mic.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_quick_mic.setToolTip("Записать голос и перевести речь в текст (сразу в буфер обмена)")
        self.btn_quick_mic.clicked.connect(self.toggle_voice_dictation)

        btn_shelf_jump = QPushButton("📂 Полка")
        btn_shelf_jump.setObjectName("pill")
        btn_shelf_jump.setCursor(Qt.CursorShape.PointingHandCursor)
        btn_shelf_jump.clicked.connect(lambda: self._open_tab(1))

        tools.addWidget(btn_ocr, 1)
        tools.addWidget(btn_picker, 1)
        tools.addWidget(self.btn_quick_mic, 1)
        tools.addWidget(btn_shelf_jump)
        layout.addLayout(tools)

        vpn = QFrame()
        vpn.setObjectName("group")
        vl = QHBoxLayout(vpn)
        vl.setContentsMargins(14, 10, 12, 10)
        vl.setSpacing(12)
        self.vpn_dot = QLabel()
        self.vpn_dot.setFixedSize(34, 34)
        vl.addWidget(self.vpn_dot)
        texts = QVBoxLayout()
        texts.setSpacing(0)
        t = QLabel("Karing VPN")
        t.setObjectName("row")
        t.setStyleSheet("font-weight: 600;")
        self.lbl_vpn_status = QLabel("Проверка…")
        self.lbl_vpn_status.setObjectName("caption")
        texts.addWidget(t)
        texts.addWidget(self.lbl_vpn_status)
        vl.addLayout(texts, 1)
        btn_karing = QPushButton("Открыть")
        btn_karing.setObjectName("pill")
        btn_karing.setCursor(Qt.CursorShape.PointingHandCursor)
        btn_karing.clicked.connect(self.handle_karing_vpn)
        vl.addWidget(btn_karing)
        lbl_proxy = QLabel("Прокси")
        lbl_proxy.setObjectName("caption")
        vl.addWidget(lbl_proxy)
        self.sw_proxy = Switch(is_system_proxy_enabled(), self.accent)
        self.sw_proxy.toggled.connect(self.set_system_proxy)
        vl.addWidget(self.sw_proxy)
        layout.addWidget(vpn)
        self._update_vpn_badge()

        self.grid = ShortcutGrid()
        self.grid.accent = self.accent
        self.grid.launch.connect(lambda i: self.launch_shortcut(self.config["shortcuts"][i]))
        self.grid.remove.connect(self.remove_shortcut)
        self.grid.add_requested.connect(self.toggle_add_form)
        self.grid.set_items(self.config.get("shortcuts", []))
        layout.addWidget(self._scroll(self.grid), 1)

        self.add_form = QWidget()
        af = QHBoxLayout(self.add_form)
        af.setContentsMargins(0, 0, 0, 0)
        af.setSpacing(8)
        self.inp_sc_icon = QLineEdit("🔥")
        self.inp_sc_icon.setFixedWidth(44)
        self.inp_sc_icon.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.inp_sc_name = QLineEdit()
        self.inp_sc_name.setPlaceholderText("Название")
        self.inp_sc_url = QLineEdit()
        self.inp_sc_url.setPlaceholderText("Сайт, ссылка или путь к .exe")
        self.inp_sc_url.returnPressed.connect(self.add_custom_shortcut)
        btn_add = QPushButton("Добавить")
        btn_add.setObjectName("accent")
        btn_add.setCursor(Qt.CursorShape.PointingHandCursor)
        btn_add.clicked.connect(self.add_custom_shortcut)
        af.addWidget(self.inp_sc_icon)
        af.addWidget(self.inp_sc_name, 1)
        af.addWidget(self.inp_sc_url, 2)
        af.addWidget(btn_add)
        self.add_form.hide()
        layout.addWidget(self.add_form)
        return page

    # ---- 3. Буфер обмена + Мгновенный переводчик и мини-ИИ -------------
    def _build_clipboard_page(self):
        page = self._page()
        layout = QVBoxLayout(page)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(8)

        head = QHBoxLayout()
        head.setSpacing(6)
        title = QLabel("Буфер и ИИ")
        title.setObjectName("h1")

        self.btn_clip_mic = QPushButton("🎙️ Диктовка")
        self.btn_clip_mic.setObjectName("chip")
        self.btn_clip_mic.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_clip_mic.setToolTip("Надиктовать голосом в буфер обмена")
        self.btn_clip_mic.clicked.connect(self.toggle_voice_dictation)

        btn_tr_current = QPushButton("🌐 Перевести буфер")
        btn_tr_current.setObjectName("chip")
        btn_tr_current.setCursor(Qt.CursorShape.PointingHandCursor)
        btn_tr_current.clicked.connect(lambda: self.run_text_assistant(self.clipboard.text(), "translate"))

        btn_ai_current = QPushButton("✦ Спросить ИИ")
        btn_ai_current.setObjectName("chip")
        btn_ai_current.setCursor(Qt.CursorShape.PointingHandCursor)
        btn_ai_current.clicked.connect(lambda: self.run_text_assistant(self.clipboard.text(), "ai"))

        btn_clear = QPushButton("Очистить")
        btn_clear.setObjectName("text")
        btn_clear.setCursor(Qt.CursorShape.PointingHandCursor)
        btn_clear.clicked.connect(self.clear_clipboard_history)

        head.addWidget(title)
        head.addStretch()
        head.addWidget(self.btn_clip_mic)
        head.addWidget(btn_tr_current)
        head.addWidget(btn_ai_current)
        head.addWidget(btn_clear)
        layout.addLayout(head)

        # Карточка результата перевода / ответа ИИ / голосовой заметки
        self.ai_card = QFrame()
        self.ai_card.setObjectName("group")
        al = QVBoxLayout(self.ai_card)
        al.setContentsMargins(14, 10, 14, 10)
        al.setSpacing(6)
        at = QHBoxLayout()
        self.lbl_ai_title = QLabel("🌐 Перевод")
        self.lbl_ai_title.setStyleSheet("font-weight: 700; font-size: 12px;")
        self.btn_voice_to_shelf = QPushButton("📂 Аудио на полку")
        self.btn_voice_to_shelf.setObjectName("chip")
        self.btn_voice_to_shelf.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_voice_to_shelf.clicked.connect(self.put_last_voice_on_shelf)
        self.btn_voice_to_shelf.hide()

        btn_copy_ai = QPushButton("Скопировать")
        btn_copy_ai.setObjectName("chip")
        btn_copy_ai.setCursor(Qt.CursorShape.PointingHandCursor)
        btn_copy_ai.clicked.connect(self.copy_ai_result)
        btn_close_ai = QPushButton("✕")
        btn_close_ai.setObjectName("text")
        btn_close_ai.setCursor(Qt.CursorShape.PointingHandCursor)
        btn_close_ai.clicked.connect(self.ai_card.hide)
        at.addWidget(self.lbl_ai_title)
        at.addStretch()
        at.addWidget(self.btn_voice_to_shelf)
        at.addWidget(btn_copy_ai)
        at.addWidget(btn_close_ai)
        al.addLayout(at)

        self.lbl_ai_body = QLabel("")
        self.lbl_ai_body.setWordWrap(True)
        self.lbl_ai_body.setTextInteractionFlags(Qt.TextInteractionFlag.TextSelectableByMouse)
        self.lbl_ai_body.setStyleSheet("font-size: 12.5px; color: rgba(255,255,255,235);")
        al.addWidget(self.lbl_ai_body)
        self.ai_card.hide()
        layout.addWidget(self.ai_card)

        self.clip_list = ClipList()
        self.clip_list.accent = self.accent
        self.clip_list.picked.connect(self.copy_from_history)
        self.clip_list.translate_requested.connect(
            lambda i: self.run_text_assistant(self.clip_history[i][0], "translate") if 0 <= i < len(self.clip_history) else None
        )
        self.clip_list.ai_requested.connect(
            lambda i: self.run_text_assistant(self.clip_history[i][0], "ai") if 0 <= i < len(self.clip_history) else None
        )
        layout.addWidget(self._scroll(self.clip_list), 1)
        return page

    # ---- 4. Настройки -------------------------------------------------
    def _group(self, layout, title):
        lbl = QLabel(title.upper())
        lbl.setObjectName("caption")
        lbl.setContentsMargins(14, 4, 0, 0)
        layout.addWidget(lbl)
        frame = QFrame()
        frame.setObjectName("group")
        gl = QVBoxLayout(frame)
        gl.setContentsMargins(14, 2, 14, 2)
        gl.setSpacing(0)
        layout.addWidget(frame)
        self._last_group = (lbl, frame)
        return gl

    @staticmethod
    def _row(group_layout, title, widget=None, caption=None, stretch_widget=False):
        if group_layout.count():
            sep = QFrame()
            sep.setObjectName("sep")
            sep.setFixedHeight(1)
            group_layout.addWidget(sep)
        row = QWidget()
        hl = QHBoxLayout(row)
        hl.setContentsMargins(0, 9, 0, 9)
        hl.setSpacing(12)
        texts = QVBoxLayout()
        texts.setSpacing(1)
        lbl = QLabel(title)
        lbl.setObjectName("row")
        texts.addWidget(lbl)
        if caption:
            cap = QLabel(caption)
            cap.setObjectName("caption")
            cap.setWordWrap(True)
            texts.addWidget(cap)
        hl.addLayout(texts, 0 if stretch_widget else 1)
        if widget is not None:
            if stretch_widget:
                hl.addWidget(widget, 1)
            else:
                hl.addWidget(widget, 0, Qt.AlignmentFlag.AlignVCenter)
        group_layout.addWidget(row)
        return lbl

    def _slider(self, lo, hi, value, callback):
        s = QSlider(Qt.Orientation.Horizontal)
        s.setRange(lo, hi)
        s.setValue(int(value))
        s.setMinimumWidth(160)
        s.setCursor(Qt.CursorShape.PointingHandCursor)
        s.valueChanged.connect(callback)
        return s

    def _build_settings_page(self):
        page = self._page()
        outer = QVBoxLayout(page)
        outer.setContentsMargins(0, 0, 0, 0)
        holder = QWidget()
        layout = QVBoxLayout(holder)
        layout.setContentsMargins(0, 0, 8, 8)
        layout.setSpacing(6)

        g = self._group(layout, "Вид")
        self.style_picker = Segmented(["Стекло", "Прозрачный", "iPhone"])
        self.style_picker.set_index(STYLES.index(self._style()), animate=False)
        self.style_picker.changed.connect(lambda i: self.set_style(STYLES[i]))
        self._row(g, "Стиль острова", self.style_picker, stretch_widget=True)
        self.color_dots = ColorDots(self.accent.name())
        self.color_dots.picked.connect(self.set_accent)
        self.color_dots.custom_requested.connect(self.pick_custom_color)
        self._row(g, "Акцент", self.color_dots)
        self.sld_scale = self._slider(80, 140, int(float(self.config["island_scale"]) * 100), self.on_scale_changed)
        self._row(g, "Размер", self.sld_scale, stretch_widget=True)

        g = self._group(layout, "Стекло")
        self.glass_group = self._last_group
        self.sld_tint = self._slider(0, 230, self.config["glass_tint"], self.on_glass_changed)
        self._row(g, "Плотность", self.sld_tint, stretch_widget=True)
        self.sld_blur = self._slider(0, 100, self.config["blur"], self.on_glass_changed)
        self._row(g, "Размытие", self.sld_blur, stretch_widget=True)
        self.sw_live = Switch(bool(self.config.get("live_blur", True)), self.accent)
        self.sw_live.toggled.connect(self.set_live_blur)
        self._row(g, "Живое размытие фона", self.sw_live,
                  "Стекло размывает то, что под ним. Остров при этом не попадает на скриншоты и записи экрана.")
        for w in self.glass_group:
            w.setVisible(self._style() != "iphone")

        g = self._group(layout, "Интерактивные функции")
        self.sw_vol_hud = Switch(bool(self.config.get("volume_hud", True)), self.accent)
        self.sw_vol_hud.toggled.connect(self.set_volume_hud_enabled)
        self._row(g, "Шкала громкости в острове (Volume HUD)", self.sw_vol_hud,
                  "Показывать ползунок громкости в острове + менять звук колесом мыши по свёрнутому острову.")
        self.sw_dev_toast = Switch(bool(self.config.get("device_toasts", True)), self.accent)
        self.sw_dev_toast.toggled.connect(self.set_device_toasts_enabled)
        self._row(g, "Анимация подключения наушников и геймпадов", self.sw_dev_toast,
                  "Всплывающий тост в стиле AirPods при переключении аудиоустройств или геймпада.")

        g = self._group(layout, "Система")
        self.sw_autostart = Switch(bool(self.config.get("autostart", False)), self.accent)
        self.sw_autostart.toggled.connect(self.set_autostart)
        self._row(g, "Запускать вместе с Windows", self.sw_autostart)
        self.btn_pomo = QPushButton("Старт")
        self.btn_pomo.setObjectName("pill")
        self.btn_pomo.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_pomo.clicked.connect(self.toggle_pomodoro)
        self.lbl_pomo = self._row(g, "Фокус-таймер · 25:00", self.btn_pomo)
        self.lbl_sys = QLabel("CPU — · RAM —")
        self.lbl_sys.setObjectName("caption")
        self._row(g, "Нагрузка", self.lbl_sys)

        g = self._group(layout, "Остров")
        btn_center = QPushButton("По центру")
        btn_center.setObjectName("pill")
        btn_center.setCursor(Qt.CursorShape.PointingHandCursor)
        btn_center.clicked.connect(self.reset_island_position)
        self._row(g, "Позиция", btn_center, "Остров можно просто перетаскивать мышью, а развёрнутый — растягивать за края.")
        btn_quit = QPushButton("Выйти")
        btn_quit.setObjectName("danger")
        btn_quit.setCursor(Qt.CursorShape.PointingHandCursor)
        btn_quit.clicked.connect(QApplication.instance().quit)
        self._row(g, "Закрыть Dynamic Island", btn_quit)
        layout.addStretch()

        outer.addWidget(self._scroll(holder))
        return page

    def switch_tab(self, index: int):
        self.pages.setCurrentIndex(index)
        self.config["last_tab"] = index
        self.save_config()

    def _open_tab(self, index: int):
        self.segmented.set_index(index)
        self.switch_tab(index)
        if self.mode == self.COMPACT:
            self.expand()

    # -----------------------------------------------------------------
    # ГЕОМЕТРИЯ, ПРУЖИНЫ И ФИКСИРОВАННЫЙ ХОЛСТ ОКНА
    # -----------------------------------------------------------------
    def _scale(self):
        return float(self.config.get("island_scale", 1.0))

    def _variant(self):
        if self.dictation_active:
            return "recording"
        if self.device_banner:
            return "device"
        if self.volume_banner:
            return "volume"
        if self.toast:
            return "toast"
        if self.media.get("playing"):
            return "music"
        if self.pomo_running:
            return "timer"
        return "idle"

    def _compact_size(self):
        s = self._scale()
        v = self._variant()
        if v == "recording":
            return 330 * s, 44 * s
        if v == "device":
            _, title, sub, _ = self.device_banner
            tw = max(QFontMetrics(ui_font(13 * s, QFont.Weight.DemiBold)).horizontalAdvance(title),
                     QFontMetrics(ui_font(12 * s)).horizontalAdvance(sub))
            return clamp(tw + 96 * s, 260 * s, 440 * s), 52 * s
        if v == "volume":
            return 300 * s, 42 * s
        if v == "toast":
            icon, title, text = self.toast
            extra_btn = 104 * s if self.toast_action == "translate" else 0
            tw = max(QFontMetrics(ui_font(13 * s, QFont.Weight.DemiBold)).horizontalAdvance(title),
                     QFontMetrics(ui_font(12 * s)).horizontalAdvance(text))
            return clamp(tw + 84 * s + extra_btn, 260 * s, 500 * s), 52 * s
        if v == "music":
            return 380 * s, 40 * s
        if v == "timer":
            return 236 * s, 36 * s
        # В режиме ожидания немного шире, если на полке лежат файлы (бейдж 📎 N)
        extra_shelf = 44 * s if self.shelf_files else 0
        return 190 * s + extra_shelf, 36 * s

    def _expanded_size(self):
        return (clamp(float(self.config.get("expanded_w", 620)), EXP_MIN[0], EXP_MAX[0]),
                clamp(float(self.config.get("expanded_h", 430)), EXP_MIN[1], EXP_MAX[1]))

    def _target_size(self):
        if self.mode == self.EXPANDED:
            w, h = self._expanded_size()
            return w, h, EXP_RADIUS
        w, h = self._compact_size()
        return w, h, h / 2

    def island_rect(self) -> QRectF:
        s = self.sscale.value
        w, h = self.sw.value * s, self.sh.value * s
        return QRectF(self.width() / 2 - w / 2, MARGIN + (self.sh.value - h) / 2, w, h)

    def _target_rect(self) -> QRectF:
        return QRectF(self.width() / 2 - self.sw.target / 2, MARGIN, self.sw.target, self.sh.target)

    def _place_initial(self):
        screen = QGuiApplication.primaryScreen().geometry()
        cx, top = self.config.get("pos_cx"), self.config.get("pos_top")
        if cx is None or top is None or QGuiApplication.screenAt(QPoint(int(cx), int(top) + 5)) is None:
            cx, top = screen.center().x(), screen.top() + DEFAULT_TOP
        w, h, r = self._target_size()
        self.sw.snap(w)
        self.sh.snap(h)
        self.sr.snap(r)
        self.scx.snap(cx)
        self.stop.snap(top)
        x = int(round(self.scx.value - CANVAS_W / 2))
        y = int(round(self.stop.value - MARGIN))
        self.setGeometry(x, y, CANVAS_W, CANVAS_H)
        self._layout_content()

    def _sync_window_pos(self):
        x = int(round(self.scx.value - self.width() / 2))
        y = int(round(self.stop.value - MARGIN))
        if x != self.x() or y != self.y():
            self.move(x, y)

    def _layout_content(self):
        if not hasattr(self, "content"):
            return
        r = self._target_rect()
        target_geom = QRect(int(round(r.x())), int(round(r.y())), int(round(r.width())), int(round(r.height())) - 8)
        if self.content.geometry() != target_geom:
            self.content.setGeometry(target_geom)

    def _retarget(self):
        w, h, r = self._target_size()
        self.sw.target, self.sh.target, self.sr.target = w, h, r
        if self.mode == self.COMPACT:
            v = self._variant()
            for k, f in self.variant_alpha.items():
                f.target = 1.0 if k == v else 0.0
        self._update_scale_target()
        self._layout_content()
        self.kick()

    def _update_scale_target(self):
        if self.drag_active and self.press_zone == "move":
            target = 1.04
        elif self.press_global is not None and self.mode == self.COMPACT:
            target = 0.965
        elif self.hovered and self.mode == self.COMPACT:
            target = 1.03
        else:
            target = 1.0
        if self.sscale.target != target:
            self.sscale.target = target
            self.kick()

    def _set_shape_springs(self, response, damping):
        for s in (self.sw, self.sh, self.sr):
            s.configure(response, damping)

    def kick(self):
        if not self.anim_timer.isActive():
            self.anim_clock = time.perf_counter()
            self.anim_timer.start()

    def _tick(self):
        now = time.perf_counter()
        dt = min(0.05, now - self.anim_clock)
        self.anim_clock = now
        moving = False
        for s in (self.sw, self.sh, self.sr, self.scx, self.stop, self.sscale,
                  self.slift, self.lyric_anim, self.vol_bar_spring, self.device_pulse):
            moving = s.step(dt) or moving

        cw, ch = self._compact_size()
        ew, eh = self._expanded_size()
        progress = clamp((self.sh.value - ch) / max(1.0, eh - ch), 0.0, 1.0)
        if self.mode == self.EXPANDED:
            self.compact_alpha.target = 0.0
            if progress > 0.62 or self.press_zone == "resize":
                self.content_alpha.target = 1.0
                if not self.content.isVisible():
                    self._layout_content()
                    self.content.show()
        else:
            self.content_alpha.target = 0.0
            if self.content.isVisible():
                self.content.hide()
            if progress < 0.35:
                self.compact_alpha.target = 1.0

        fades = [self.compact_alpha, self.content_alpha, *self.variant_alpha.values()]
        for f in fades:
            moving = f.step(dt) or moving

        self._sync_window_pos()

        continuous = self.mode == self.COMPACT and (self.media.get("playing") or self.dictation_active)
        if continuous:
            self.wave_t += dt

        if moving and now - self.last_capture > 0.045:
            self._request_backdrop()
        self.update()

        if not moving and self.press_zone is None:
            if continuous:
                self.anim_timer.setInterval(33)
            else:
                self.anim_timer.stop()
                self._request_backdrop()
        else:
            self.anim_timer.setInterval(16)

    # -----------------------------------------------------------------
    # РАСКРЫТИЕ / СВОРАЧИВАНИЕ
    # -----------------------------------------------------------------
    def expand(self):
        if self.mode == self.EXPANDED:
            return
        self.mode = self.EXPANDED
        self.toast = None
        self.toast_action = None
        self.toast_timer.stop()
        self._set_shape_springs(0.48, 0.74)
        self.content_alpha.speed = 16
        self.compact_alpha.speed = 26

        w, h = self._expanded_size()
        geo = self._screen_geo()
        cx = clamp(self.scx.target, geo.left() + w / 2 + 8, geo.right() - w / 2 - 8)
        top = clamp(self.stop.target, geo.top(), geo.bottom() - h - 8)
        if (cx, top) != (self.scx.target, self.stop.target):
            self.home_pos = (self.scx.target, self.stop.target)
            self.scx.target, self.stop.target = cx, top
        else:
            self.home_pos = None

        self._retarget()
        self.raise_()
        self.activateWindow()
        self.setFocus()

    def collapse(self):
        if self.mode == self.COMPACT:
            return
        self.mode = self.COMPACT
        self.content.hide()
        self._set_shape_springs(0.42, 0.78)
        self.content_alpha.speed = 24
        self.compact_alpha.speed = 14
        if self.home_pos:
            self.scx.target, self.stop.target = self.home_pos
            self.home_pos = None
        if self.add_form.isVisible():
            self.add_form.hide()
        self._retarget()

    def _screen_geo(self):
        screen = QGuiApplication.screenAt(QPoint(int(self.scx.value), int(self.stop.value) + 10))
        return (screen or QGuiApplication.primaryScreen()).geometry()

    # -----------------------------------------------------------------
    # ОТРИСОВКА СТЕКЛА И ВСЕХ КАПСУЛ ОСТРОВА
    # -----------------------------------------------------------------
    def paintEvent(self, event):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        p.setRenderHint(QPainter.RenderHint.TextAntialiasing)

        rect = self.island_rect()
        if rect.width() < 2 or rect.height() < 2:
            return
        radius = min(self.sr.value * self.sscale.value, rect.height() / 2, rect.width() / 2)
        path = QPainterPath()
        path.addRoundedRect(rect, radius, radius)
        lift = self.slift.value

        outer = QPainterPath()
        outer.addRect(QRectF(self.rect()))
        p.save()
        p.setClipPath(outer.subtracted(path))
        p.setPen(Qt.PenStyle.NoPen)
        layers = 8
        for i in range(layers, 0, -1):
            spread = i * (2.0 + 0.7 * lift)
            alpha = int((9 + 5 * lift) * (1 - i / (layers + 1)) ** 1.6 + 1)
            p.setBrush(QColor(0, 0, 0, alpha))
            sr = rect.adjusted(-spread, -spread + 3 + 5 * lift, spread, spread + 3 + 5 * lift)
            p.drawRoundedRect(sr, radius + spread, radius + spread)
        p.restore()

        style = self._style()
        if style == "iphone":
            self._paint_iphone_body(p, rect, path)
        else:
            self._paint_glass_body(p, rect, path, radius, clear=(style == "clear"))

        self._paint_overlay(p, rect)

    def _paint_iphone_body(self, p, rect, path):
        p.fillPath(path, QColor(0, 0, 0, 252))
        rim = QLinearGradient(rect.topLeft(), rect.bottomLeft())
        rim.setColorAt(0.0, white(34))
        rim.setColorAt(1.0, white(12))
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.setPen(QPen(QBrush(rim), 1.0))
        p.drawPath(path)

    def _paint_glass_body(self, p, rect, path, radius, clear=False):
        blur_pct = clamp(float(self.config.get("blur", 80)) / 100.0, 0.0, 1.0)
        raw_tint = int(self.config.get("glass_tint", 105))
        tint = int(raw_tint * 0.35) if clear else raw_tint

        live = self._needs_backdrop() and self.backdrop is not None and self.backdrop_rect is not None
        if live and blur_pct > 0.02:
            br = self.backdrop_rect
            local_br = QRectF(
                br.x() - self.geometry().x(),
                br.y() - self.geometry().y(),
                br.width(),
                br.height()
            )
            p.save()
            p.setClipPath(path)
            bd_opacity = clamp((0.20 if clear else 0.38) + (0.35 if clear else 0.44) * blur_pct, 0.15, 0.84)
            p.setOpacity(bd_opacity)
            p.drawPixmap(local_br, self.backdrop, QRectF(0, 0, self.backdrop.width(), self.backdrop.height()))
            p.restore()

        p.fillPath(path, QColor(14, 16, 24, tint))

        frost = QLinearGradient(rect.topLeft(), rect.bottomLeft())
        if clear:
            frost.setColorAt(0.0, white(int(28 + 18 * blur_pct)))
            frost.setColorAt(0.5, white(int(6 + 8 * blur_pct)))
            frost.setColorAt(1.0, white(int(18 + 14 * blur_pct)))
        else:
            frost.setColorAt(0.0, white(int(36 + 24 * blur_pct)))
            frost.setColorAt(0.45, white(int(10 + 14 * blur_pct)))
            frost.setColorAt(1.0, white(int(20 + 18 * blur_pct)))
        p.fillPath(path, QBrush(frost))

        glow = QColor("#FF453A") if self.dictation_active else QColor(self.art_color if self.media.get("playing") else self.accent)
        glow_strength = 75 if (self.media.get("playing") or self.dictation_active) else 38
        g_center = QPointF(rect.left() + min(rect.width() * 0.25, 120), rect.top() + rect.height() * 0.25)
        rg = QRadialGradient(g_center, max(rect.width(), rect.height()) * 0.78)
        rg.setColorAt(0.0, with_alpha(glow, glow_strength))
        rg.setColorAt(1.0, with_alpha(glow, 0))
        p.fillPath(path, QBrush(rg))

        sheen_h = max(14.0, min(rect.height() * 0.55, 85.0))
        sheen = QLinearGradient(rect.topLeft(), QPointF(rect.left(), rect.top() + sheen_h))
        sheen.setColorAt(0.0, white(54 if clear else 38))
        sheen.setColorAt(1.0, white(0))
        p.fillPath(path, QBrush(sheen))

        k = 1.4 if clear else 1.1
        rim = QLinearGradient(rect.topLeft(), rect.bottomLeft())
        rim.setColorAt(0.0, white(int(135 * k)))
        rim.setColorAt(0.35, white(int(42 * k)))
        rim.setColorAt(0.75, white(int(24 * k)))
        rim.setColorAt(1.0, white(int(65 * k)))
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.setPen(QPen(QBrush(rim), 1.15))
        p.drawPath(path)

        inner = QPainterPath()
        ir = rect.adjusted(1.4, 1.4, -1.4, -1.4)
        inner.addRoundedRect(ir, max(0.0, radius - 1.4), max(0.0, radius - 1.4))
        p.setPen(QPen(white(18), 1.0))
        p.drawPath(inner)

    def _paint_overlay(self, p, rect):
        ca = self.compact_alpha.value
        if ca > 0.01:
            compact_h = self._compact_size()[1] * self.sscale.value
            crect = QRectF(rect.left(), rect.top(), rect.width(), min(rect.height(), compact_h))
            painters = {
                "idle": self._paint_idle,
                "music": self._paint_music,
                "toast": self._paint_toast,
                "timer": self._paint_timer,
                "volume": self._paint_volume,
                "device": self._paint_device,
                "recording": self._paint_recording,
            }
            for k, f in self.variant_alpha.items():
                a = f.value * ca
                if a > 0.01:
                    p.save()
                    p.setOpacity(a)
                    painters[k](p, crect)
                    p.restore()

        ea = self.content_alpha.value
        if ea > 0.01 and self.mode == self.EXPANDED:
            p.setOpacity(ea)
            active = self.press_zone == "resize" or self._zone_at(self.mapFromGlobal(QCursor.pos())) in ("b", "bl", "br")
            gw = 44 if active else 36
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(white(150 if active else 80))
            p.drawRoundedRect(QRectF(rect.center().x() - gw / 2, rect.bottom() - 9, gw, 5), 2.5, 2.5)

    def _paint_idle(self, p, rect):
        s = self._scale()
        p.setPen(white(245))
        p.setFont(ui_font(13.5 * s, QFont.Weight.DemiBold, display=True))
        p.drawText(rect.adjusted(16 * s, 0, 0, 0), Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter,
                   time.strftime("%H:%M"))

        if self.shelf_files:
            badge_w = 40 * s
            br = QRectF(rect.center().x() - badge_w / 2 - 6 * s, rect.center().y() - 10 * s, badge_w, 20 * s)
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(with_alpha(self.accent, 90))
            p.drawRoundedRect(br, 10 * s, 10 * s)
            p.setFont(ui_font(10.5 * s, QFont.Weight.Bold))
            p.setPen(white(245))
            p.drawText(br, Qt.AlignmentFlag.AlignCenter, f"📎{len(self.shelf_files)}")

        p.setFont(ui_font(11.5 * s, QFont.Weight.DemiBold))
        txt = f"CPU {self.status.get('cpu', 0)}%"
        p.setPen(white(165))
        p.drawText(rect.adjusted(0, 0, -16 * s, 0), Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter, txt)

    def _paint_music(self, p, rect):
        s = self._scale()
        h = rect.height()
        tile = h - 12 * s
        tr = QRectF(rect.left() + 7 * s, rect.center().y() - tile / 2, tile, tile)
        path = QPainterPath()
        path.addRoundedRect(tr, tile * 0.28, tile * 0.28)
        if self.art_pix is not None:
            brush = QBrush(self.art_pix)
            t = QTransform()
            t.translate(tr.x(), tr.y())
            t.scale(tile / self.art_pix.width(), tile / self.art_pix.height())
            brush.setTransform(t)
            p.fillPath(path, brush)
        else:
            g = QLinearGradient(tr.topLeft(), tr.bottomRight())
            g.setColorAt(0.0, self.art_color.lighter(125))
            g.setColorAt(1.0, self.art_color.darker(200))
            p.fillPath(path, QBrush(g))
            p.setPen(white(220))
            p.setFont(ui_font(tile * 0.55, QFont.Weight.Bold))
            p.drawText(tr, Qt.AlignmentFlag.AlignCenter, "♪")

        bars = 5
        bw, gap = 3.0 * s, 2.6 * s
        total = bars * bw + (bars - 1) * gap
        bx = rect.right() - 16 * s - total
        maxh = h * 0.5
        col = self.art_color.lighter(140) if self.art_color.lightness() < 120 else self.art_color
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(col)
        for i in range(bars):
            bh = max(bw, maxh * (0.25 + 0.75 * wave_level(self.wave_t, i)))
            p.drawRoundedRect(QRectF(bx + i * (bw + gap), rect.center().y() - bh / 2, bw, bh), bw / 2, bw / 2)

        tx = tr.right() + 10 * s
        tw = bx - 12 * s - tx
        font = ui_font(13 * s, QFont.Weight.DemiBold)
        fm = QFontMetrics(font)
        p.setFont(font)
        f = self.lyric_anim.value
        fa = clamp(f, 0.0, 1.0)
        current = self._compact_line()
        p.save()
        p.setClipRect(QRectF(tx - 2, rect.top() + 2, tw + 4, h - 4))
        if fa < 1.0 and self.lyric_prev:
            p.setPen(white(235 * (1 - fa) ** 2))
            p.drawText(QRectF(tx, rect.top() - h * 0.6 * fa, tw, h), Qt.AlignmentFlag.AlignVCenter,
                       fm.elidedText(self.lyric_prev, Qt.TextElideMode.ElideRight, int(tw)))
        text = fm.elidedText(current, Qt.TextElideMode.ElideRight, int(tw))
        if self.synced_lyrics and self.lyric_text:
            frac = self._lyric_progress()
            brush = wipe_brush(tx, fm.horizontalAdvance(text), frac, white(250 * fa), white(115 * fa), 18 * s)
            p.setPen(QPen(brush, 1))
        else:
            p.setPen(white(240 * fa))
        p.drawText(QRectF(tx, rect.top() + h * 0.6 * (1 - f), tw, h), Qt.AlignmentFlag.AlignVCenter, text)
        p.restore()

    def _lyric_progress(self):
        i = self.lyric_idx
        if not (0 <= i < len(self.synced_lyrics)):
            return 1.0
        t0 = self.synced_lyrics[i][0]
        t1 = self.synced_lyrics[i + 1][0] if i + 1 < len(self.synced_lyrics) else t0 + 4.0
        return clamp((self.current_lyric_position() - t0) / (clamp(t1 - t0, 0.35, 12.0) * 0.94), 0.0, 1.0)

    def _compact_line(self):
        if self.synced_lyrics and self.lyric_text:
            return self.lyric_text
        title = self.media.get("title", "")
        artist = self.media.get("artist", "")
        return f"{title} — {artist}" if artist else title

    def _paint_toast(self, p, rect):
        if not self.toast:
            return
        s = self._scale()
        icon, title, text = self.toast
        d = rect.height() - 14 * s
        ir = QRectF(rect.left() + 8 * s, rect.center().y() - d / 2, d, d)
        g = QLinearGradient(ir.topLeft(), ir.bottomLeft())
        g.setColorAt(0.0, self.accent.lighter(120))
        g.setColorAt(1.0, self.accent.darker(130))
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QBrush(g))
        p.drawEllipse(ir)
        p.setPen(QColor(255, 255, 255))
        p.setFont(emoji_font(d * 0.46))
        p.drawText(ir, Qt.AlignmentFlag.AlignCenter, icon)

        # Кнопка «Перевести ✦» прямо на тосте «Скопировано»
        right_reserve = 16 * s
        if self.toast_action == "translate":
            bw = 94 * s
            bh = 28 * s
            btn_r = QRectF(rect.right() - bw - 10 * s, rect.center().y() - bh / 2, bw, bh)
            self.toast_btn_rect = btn_r
            right_reserve = bw + 18 * s
            btn_hover = btn_r.contains(QPointF(self.mapFromGlobal(QCursor.pos())))
            p.setPen(QPen(white(55), 0.9))
            p.setBrush(self.accent.lighter(115) if btn_hover else with_alpha(self.accent, 210))
            p.drawRoundedRect(btn_r, bh / 2, bh / 2)
            p.setFont(ui_font(11.5 * s, QFont.Weight.Bold))
            p.setPen(white(250))
            p.drawText(btn_r, Qt.AlignmentFlag.AlignCenter, "Перевести ✦")
        else:
            self.toast_btn_rect = QRectF()

        tx = ir.right() + 11 * s
        tw = max(40.0, rect.right() - right_reserve - tx)
        f1 = ui_font(13 * s, QFont.Weight.DemiBold)
        f2 = ui_font(12 * s)
        p.setFont(f1)
        p.setPen(white(245))
        p.drawText(QRectF(tx, rect.top() + 8 * s, tw, 18 * s), Qt.AlignmentFlag.AlignVCenter,
                   QFontMetrics(f1).elidedText(title, Qt.TextElideMode.ElideRight, int(tw)))
        p.setFont(f2)
        p.setPen(white(160))
        p.drawText(QRectF(tx, rect.top() + 26 * s, tw, 17 * s), Qt.AlignmentFlag.AlignVCenter,
                   QFontMetrics(f2).elidedText(text, Qt.TextElideMode.ElideRight, int(tw)))

    def _paint_timer(self, p, rect):
        s = self._scale()
        orange = QColor("#FF9F0A")
        d = 18 * s
        c = QPointF(rect.left() + 14 * s + d / 2, rect.center().y())
        ring = QRectF(c.x() - d / 2, c.y() - d / 2, d, d)
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.setPen(QPen(with_alpha(orange, 70), 2.6 * s))
        p.drawEllipse(ring)
        frac = self.pomo_left / self.pomo_total if self.pomo_total else 0
        p.setPen(QPen(orange, 2.6 * s, cap=Qt.PenCapStyle.RoundCap))
        p.drawArc(ring, 90 * 16, int(360 * 16 * frac))
        p.setFont(ui_font(12.5 * s, QFont.Weight.DemiBold))
        p.setPen(white(230))
        p.drawText(QRectF(ring.right() + 9 * s, rect.top(), 100 * s, rect.height()),
                   Qt.AlignmentFlag.AlignVCenter, "Фокус")
        m, sec = divmod(self.pomo_left, 60)
        p.setFont(ui_font(14 * s, QFont.Weight.DemiBold, display=True))
        p.setPen(orange)
        p.drawText(rect.adjusted(0, 0, -16 * s, 0), Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter,
                   f"{m:02d}:{sec:02d}")

    def _paint_volume(self, p, rect):
        """Стеклянный ползунок громкости внутри острова (Volume HUD)."""
        if not self.volume_banner:
            return
        s = self._scale()
        vol, muted = self.volume_banner
        frac = 0.0 if muted else clamp(self.vol_bar_spring.value, 0.0, 1.0)

        icon = "🔇" if (muted or vol == 0) else ("🔈" if vol < 33 else ("🔉" if vol < 68 else "🔊"))
        p.setFont(emoji_font(16 * s))
        p.setPen(white(245))
        p.drawText(QRectF(rect.left() + 14 * s, rect.top(), 26 * s, rect.height()),
                   Qt.AlignmentFlag.AlignCenter, icon)

        bar_x = rect.left() + 46 * s
        bar_w = max(40.0, rect.width() - 106 * s)
        bar_h = 6 * s
        bar_y = rect.center().y() - bar_h / 2
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(white(45))
        p.drawRoundedRect(QRectF(bar_x, bar_y, bar_w, bar_h), bar_h / 2, bar_h / 2)

        if frac > 0.01:
            fill_col = QColor("#FF453A") if muted else self.accent.lighter(115)
            p.setBrush(fill_col)
            p.drawRoundedRect(QRectF(bar_x, bar_y, max(bar_h, bar_w * frac), bar_h), bar_h / 2, bar_h / 2)

        p.setFont(ui_font(12.5 * s, QFont.Weight.Bold, display=True))
        p.setPen(QColor("#FF453A") if muted else white(240))
        label = "MUTE" if muted else f"{vol}%"
        p.drawText(rect.adjusted(0, 0, -16 * s, 0), Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter, label)

    def _paint_device(self, p, rect):
        """Анимация подключения наушников / Bluetooth-устройств / геймпада (в стиле AirPods)."""
        if not self.device_banner:
            return
        s = self._scale()
        icon, title, subtitle, connected = self.device_banner
        col = QColor("#30D158") if connected else QColor("#AEAEB2")
        d = (rect.height() - 14 * s) * clamp(self.device_pulse.value, 0.85, 1.15)
        ir = QRectF(rect.left() + 10 * s, rect.center().y() - d / 2, d, d)

        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(with_alpha(col, 55))
        p.drawEllipse(ir.adjusted(-3 * s, -3 * s, 3 * s, 3 * s))
        p.setBrush(col)
        p.drawEllipse(ir)

        p.setFont(emoji_font(d * 0.5))
        p.setPen(white(255))
        p.drawText(ir, Qt.AlignmentFlag.AlignCenter, icon)

        tx = rect.left() + rect.height() + 4 * s
        tw = max(40.0, rect.right() - 16 * s - tx)
        f1 = ui_font(12 * s, QFont.Weight.Bold)
        f2 = ui_font(12.5 * s, QFont.Weight.DemiBold)
        p.setFont(f1)
        p.setPen(col)
        p.drawText(QRectF(tx, rect.top() + 8 * s, tw, 16 * s), Qt.AlignmentFlag.AlignVCenter, title)
        p.setFont(f2)
        p.setPen(white(240))
        p.drawText(QRectF(tx, rect.top() + 25 * s, tw, 18 * s), Qt.AlignmentFlag.AlignVCenter,
                   QFontMetrics(f2).elidedText(subtitle, Qt.TextElideMode.ElideRight, int(tw)))

    def _paint_recording(self, p, rect):
        """Капсула голосовой диктовки с живой звуковой волной и секундомером."""
        s = self._scale()
        red = QColor("#FF453A")
        pulse = 0.75 + 0.25 * math.sin(self.wave_t * 6.0)
        dot_r = 6.5 * s
        cx = rect.left() + 18 * s
        cy = rect.center().y()
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(with_alpha(red, int(90 * pulse)))
        p.drawEllipse(QPointF(cx, cy), dot_r * 1.6, dot_r * 1.6)
        p.setBrush(red)
        p.drawEllipse(QPointF(cx, cy), dot_r, dot_r)

        elapsed = max(0.0, time.monotonic() - self.voice_recorder.start_ts)
        p.setFont(ui_font(12.5 * s, QFont.Weight.Bold, display=True))
        p.setPen(white(245))
        p.drawText(QRectF(cx + 12 * s, rect.top(), 46 * s, rect.height()),
                   Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft, fmt_time(elapsed))

        p.setFont(ui_font(12 * s, QFont.Weight.DemiBold))
        p.setPen(white(190))
        p.drawText(QRectF(cx + 56 * s, rect.top(), max(40.0, rect.width() - 135 * s), rect.height()),
                   Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft, "Говорите… (клик — стоп)")

        bars = 5
        bw, gap = 3.0 * s, 2.5 * s
        total = bars * bw + (bars - 1) * gap
        bx = rect.right() - 16 * s - total
        maxh = rect.height() * 0.52
        p.setBrush(red.lighter(120))
        for i in range(bars):
            bh = max(bw, maxh * (0.22 + 0.78 * wave_level(self.wave_t * 1.35, i)))
            p.drawRoundedRect(QRectF(bx + i * (bw + gap), cy - bh / 2, bw, bh), bw / 2, bw / 2)

    # -----------------------------------------------------------------
    # ЖИВАЯ ПОДЛОЖКА (РАЗМЫТИЕ ТОГО, ЧТО ПОД ОСТРОВОМ)
    # -----------------------------------------------------------------
    def _apply_capture_exclusion(self):
        hwnd = int(self.winId())
        affinity = WDA_EXCLUDEFROMCAPTURE if self._needs_backdrop() else WDA_NONE
        if not user32.SetWindowDisplayAffinity(hwnd, affinity) and affinity:
            self.config["live_blur"] = False
            self.sw_live.setChecked(False)

    def _request_backdrop(self):
        if not self._needs_backdrop() or not self.isVisible():
            return
        self.last_capture = time.perf_counter()
        hwnd = int(self.winId())
        win_phys = window_rect_phys(hwnd)
        if win_phys.width() <= 0 or self.width() <= 0:
            return
        kx = win_phys.width() / self.width()
        ky = win_phys.height() / self.height()
        ir = self.island_rect().adjusted(-6, -6, 6, 6)
        island_phys = QRect(
            int(round(win_phys.x() + ir.x() * kx)),
            int(round(win_phys.y() + ir.y() * ky)),
            max(8, int(round(ir.width() * kx))),
            max(8, int(round(ir.height() * ky)))
        )
        cap = island_phys.intersected(virtual_screen_phys())
        if cap.isEmpty():
            return
        radius = 2.0 + float(self.config.get("blur", 80)) * 0.14
        if self._style() == "clear":
            radius *= 0.65
        self.grabber.request(cap, radius, (QRect(self.geometry()), win_phys, cap))

    def _on_backdrop(self, blurred: QImage, token):
        geo, win_phys, cap = token
        if win_phys.width() <= 0 or blurred.isNull():
            return
        kx = geo.width() / win_phys.width()
        ky = geo.height() / win_phys.height()
        self.backdrop = QPixmap.fromImage(blurred)
        self.backdrop_rect = QRectF(geo.x() + (cap.x() - win_phys.x()) * kx,
                                    geo.y() + (cap.y() - win_phys.y()) * ky,
                                    cap.width() * kx, cap.height() * ky)
        self.update()

    def _style(self):
        style = self.config.get("style", "glass")
        return style if style in STYLES else "glass"

    def _needs_backdrop(self):
        return self._style() != "iphone" and bool(self.config.get("live_blur", True))

    def set_style(self, style: str):
        self.config["style"] = style
        self.save_config()
        self.style_picker.set_index(STYLES.index(style))
        for w in self.glass_group:
            w.setVisible(style != "iphone")
        self._apply_capture_exclusion()
        if self._needs_backdrop():
            self._request_backdrop()
        else:
            self.backdrop = None
        self.update()

    def set_live_blur(self, enabled: bool):
        self.config["live_blur"] = enabled
        self.save_config()
        self._apply_capture_exclusion()
        if self._needs_backdrop():
            self._request_backdrop()
        else:
            self.backdrop = None
        self.update()

    # -----------------------------------------------------------------
    # МЫШЬ, КОЛЕСО ГРОМКОСТИ И DRAG & DROP НА ПОЛКУ
    # -----------------------------------------------------------------
    def _zone_at(self, pos) -> str:
        r = self.island_rect()
        if not r.adjusted(-2, -2, 2, 2).contains(QPointF(pos)):
            return ""
        if self.mode != self.EXPANDED:
            return "move"
        x, y = pos.x(), pos.y()
        edge = 10
        bottom = y > r.bottom() - 14
        left = x < r.left() + edge
        right = x > r.right() - edge
        corner_x = x < r.left() + 26 or x > r.right() - 26
        if bottom and corner_x:
            return "bl" if x < r.center().x() else "br"
        if bottom:
            return "b"
        if left:
            return "l"
        if right:
            return "r"
        return "move"

    CURSORS = {
        "b": Qt.CursorShape.SizeVerCursor,
        "l": Qt.CursorShape.SizeHorCursor,
        "r": Qt.CursorShape.SizeHorCursor,
        "bl": Qt.CursorShape.SizeBDiagCursor,
        "br": Qt.CursorShape.SizeFDiagCursor,
    }

    def mousePressEvent(self, event):
        if event.button() != Qt.MouseButton.LeftButton:
            return
        zone = self._zone_at(event.position())
        if not zone:
            event.ignore()
            return
        self.press_global = event.globalPosition()
        self.press_zone = "move" if zone == "move" else "resize"
        self.resize_edges = zone
        self.drag_active = False
        self.press_start = (self.scx.value, self.stop.value, *self._expanded_size())
        self._update_scale_target()
        self.kick()
        event.accept()

    def mouseMoveEvent(self, event):
        if self.press_global is None:
            zone = self._zone_at(event.position())
            if self.mode == self.COMPACT and self.toast_action == "translate" and self.toast_btn_rect.contains(event.position()):
                self.setCursor(Qt.CursorShape.PointingHandCursor)
                self.update()
            else:
                self.setCursor(self.CURSORS.get(zone, Qt.CursorShape.ArrowCursor))
            return
        delta = event.globalPosition() - self.press_global
        if not self.drag_active and (abs(delta.x()) > 4 or abs(delta.y()) > 4):
            self.drag_active = True
            if self.press_zone == "move":
                self.slift.target = 1.0
                self.setCursor(Qt.CursorShape.ClosedHandCursor)
            self._update_scale_target()
        if not self.drag_active:
            return

        cx0, top0, w0, h0 = self.press_start
        if self.press_zone == "move":
            self.scx.snap(cx0 + delta.x())
            self.stop.snap(top0 + delta.y())
            self.home_pos = None
            self._sync_window_pos()
        else:
            w, h = w0, h0
            if self.resize_edges in ("r", "br"):
                w = w0 + 2 * delta.x()
            elif self.resize_edges in ("l", "bl"):
                w = w0 - 2 * delta.x()
            if self.resize_edges in ("b", "bl", "br"):
                h = h0 + delta.y()
            w = clamp(w, EXP_MIN[0], EXP_MAX[0])
            h = clamp(h, EXP_MIN[1], EXP_MAX[1])
            self.sw.snap(w)
            self.sh.snap(h)
            self.config["expanded_w"] = int(round(w))
            self.config["expanded_h"] = int(round(h))
            self._layout_content()
        self.kick()

    def mouseReleaseEvent(self, event):
        if self.press_global is None:
            return
        zone, was_drag = self.press_zone, self.drag_active
        self.press_global = None
        self.press_zone = None
        self.drag_active = False
        self.slift.target = 0.0
        self.setCursor(Qt.CursorShape.ArrowCursor)

        if zone == "move" and was_drag:
            self._settle_position(QCursor.pos())
        elif zone == "resize" and was_drag:
            self._set_shape_springs(0.36, 0.82)
            self._retarget()
            self.save_config()
        elif not was_drag and self.mode == self.COMPACT:
            # 1. Если идёт диктовка — клик по острову завершает запись и распознаёт текст
            if self.dictation_active:
                self.toggle_voice_dictation()
            # 2. Если нажата кнопка «Перевести ✦» на тосте «Скопировано»
            elif self.toast and self.toast_action == "translate" and self.toast_btn_rect.contains(event.position()):
                src = self.toast_source_text or self.clipboard.text()
                self._open_tab(3)
                self.run_text_assistant(src, "translate")
            else:
                self.expand()
        self._update_scale_target()
        self.kick()

    def wheelEvent(self, event):
        """Колесо мыши по компактному острову плавно меняет системную громкость Windows."""
        if self.mode == self.COMPACT and self.config.get("volume_hud", True):
            step = 2 if event.angleDelta().y() > 0 else -2
            state = WinAudioBridge.get_state()
            cur_vol = state[0] if state else (self.volume_banner[0] if self.volume_banner else 50)
            new_vol = clamp(cur_vol + step, 0, 100)
            WinAudioBridge.set_volume(new_vol, unmute=True)
            self.on_volume_changed(new_vol, False)
            event.accept()
            return
        super().wheelEvent(event)

    def dragEnterEvent(self, event):
        md = event.mimeData()
        if md.hasUrls() or md.hasImage() or md.hasText():
            self.external_drag_over = True
            self.shelf_view.drop_highlight = True
            self.shelf_view.update()
            event.acceptProposedAction()
            if self.mode == self.COMPACT:
                self._open_tab(1)
            elif self.pages.currentIndex() != 1:
                self._open_tab(1)

    def dragMoveEvent(self, event):
        event.acceptProposedAction()

    def dragLeaveEvent(self, event):
        self.external_drag_over = False
        self.shelf_view.drop_highlight = False
        self.shelf_view.update()

    def dropEvent(self, event):
        self.external_drag_over = False
        self.shelf_view.drop_highlight = False
        md = event.mimeData()
        added = []
        if md.hasUrls():
            for u in md.urls():
                if u.isLocalFile():
                    p = u.toLocalFile()
                    if os.path.exists(p):
                        added.append(p)
        elif md.hasImage():
            img = QImage(md.imageData())
            if not img.isNull():
                p = str(TEMP_DIR / f"Картинка_{datetime.now().strftime('%H-%M-%S')}.png")
                img.save(p, "PNG")
                added.append(p)
        elif md.hasText() and md.text().strip():
            p = str(TEMP_DIR / f"Заметка_{datetime.now().strftime('%H-%M-%S')}.txt")
            Path(p).write_text(md.text(), encoding="utf-8")
            added.append(p)

        if added:
            self.add_paths_to_shelf(added)
        event.acceptProposedAction()

    def _settle_position(self, cursor: QPoint):
        screen = QGuiApplication.screenAt(cursor) or QGuiApplication.primaryScreen()
        geo = screen.geometry()
        w, h = self.sw.target, self.sh.target
        cx, top = self.scx.value, self.stop.value
        if abs(cx - geo.center().x()) < 70:
            cx = geo.center().x()
        if top - geo.top() < 28:
            top = geo.top() + DEFAULT_TOP
        cx = clamp(cx, geo.left() + w / 2 + 6, geo.right() - w / 2 - 6)
        top = clamp(top, geo.top(), geo.bottom() - h - 6)
        self.scx.target, self.stop.target = cx, top
        self.config["pos_cx"], self.config["pos_top"] = int(cx), int(top)
        self.save_config()
        self.kick()

    def mouseDoubleClickEvent(self, event):
        if self.mode == self.EXPANDED and self._zone_at(event.position()) == "move":
            self.collapse()

    def contextMenuEvent(self, event):
        if not self._zone_at(event.pos()):
            return
        menu = QMenu(self)
        menu.addAction("Развернуть" if self.mode == self.COMPACT else "Свернуть",
                       self.expand if self.mode == self.COMPACT else self.collapse)
        menu.addSeparator()
        menu.addAction("🔍 Сканер текста с экрана (OCR)", self.start_screen_ocr)
        menu.addAction("🎨 Пипетка цвета", self.start_color_picker)
        menu.addAction("🎙️ Голосовая диктовка", self.toggle_voice_dictation)
        menu.addAction("📂 Открыть файловую полку", lambda: self._open_tab(1))
        menu.addSeparator()
        menu.addAction("Вернуть в центр", self.reset_island_position)
        menu.addAction("Выход", QApplication.instance().quit)
        self.dialog_open = True
        menu.exec(event.globalPos())
        self.dialog_open = False

    def keyPressEvent(self, event):
        if event.key() == Qt.Key.Key_Escape:
            self.collapse()
        else:
            super().keyPressEvent(event)

    def _poll_cursor(self):
        if not self.isVisible():
            return
        local = self.mapFromGlobal(QCursor.pos())
        lmb_down = bool(user32.GetAsyncKeyState(0x01) & 0x8000)
        # Если зажата ЛКМ снаружи (пользователь тянет файл к острову), расширяем зону приёма Drag & Drop
        pad = 28 if (lmb_down and self.press_global is None) else 3
        inside = self.island_rect().adjusted(-pad, -pad, pad, pad).contains(QPointF(local))
        busy = (
            self.press_global is not None
            or self.external_drag_over
            or self.dialog_open
            or QApplication.activePopupWidget() is not None
        )
        through = not (inside or busy)
        if through != self.click_through:
            self.click_through = through
            set_click_through(int(self.winId()), through, exclude_capture=self._needs_backdrop())

        strict_inside = self.island_rect().adjusted(-3, -3, 3, 3).contains(QPointF(local))
        if strict_inside != self.hovered:
            self.hovered = strict_inside
            # Пока мышь наведена на тост с кнопкой «Перевести», не закрываем его
            if self.toast:
                if strict_inside:
                    self.toast_timer.stop()
                else:
                    self.toast_timer.start(1600)
            self._update_scale_target()
            self.update()

        if self.mode == self.EXPANDED and not strict_inside and not busy and QApplication.activeModalWidget() is None:
            if lmb_down or (user32.GetAsyncKeyState(0x02) & 0x8000):
                self.collapse()

    # -----------------------------------------------------------------
    # ФАЙЛОВАЯ ПОЛКА «DROPOVER SHELF» (ФИЧА 1)
    # -----------------------------------------------------------------
    def _refresh_shelf_ui(self):
        self.shelf_files = [p for p in self.shelf_files if os.path.exists(p)]
        self.config["shelf_files"] = self.shelf_files
        n = len(self.shelf_files)
        self.lbl_shelf_count.setText(f"{n} файл(ов)" if n else "пусто")
        self.btn_drag_all.setVisible(n > 0)
        self.shelf_view.set_files(self.shelf_files)
        if self.mode == self.COMPACT:
            self._retarget()

    def add_paths_to_shelf(self, paths: list):
        added_count = 0
        for p in paths:
            norm = os.path.abspath(p)
            if os.path.exists(norm) and norm not in self.shelf_files:
                self.shelf_files.insert(0, norm)
                added_count += 1
        self.shelf_files = self.shelf_files[:40]
        self._refresh_shelf_ui()
        self.save_config()
        if added_count and self.mode == self.COMPACT:
            self.show_toast("📥", "Добавлено на полку", f"Файлов в кармане: {len(self.shelf_files)}")

    def pick_files_for_shelf(self):
        self.dialog_open = True
        files, _ = QFileDialog.getOpenFileNames(self, "Добавить файлы на полку", str(Path.home()))
        self.dialog_open = False
        if files:
            self.add_paths_to_shelf(files)

    def remove_from_shelf(self, idx: int):
        if 0 <= idx < len(self.shelf_files):
            self.shelf_files.pop(idx)
            self._refresh_shelf_ui()
            self.save_config()

    def open_from_shelf(self, idx: int):
        if 0 <= idx < len(self.shelf_files):
            p = self.shelf_files[idx]
            if os.path.exists(p):
                os.startfile(p)

    def clear_shelf(self):
        self.shelf_files.clear()
        self._refresh_shelf_ui()
        self.save_config()

    def copy_shelf_files_to_clipboard(self):
        valid = [QUrl.fromLocalFile(p) for p in self.shelf_files if os.path.exists(p)]
        if not valid:
            return
        mime = QMimeData()
        mime.setUrls(valid)
        self.ignore_next_clip = True
        self.clipboard.setMimeData(mime)
        self.collapse()
        self.show_toast("📂", "Файлы скопированы", f"Нажмите Ctrl+V в любом окне ({len(valid)} шт.)")

    def start_shelf_drag(self, paths: list):
        valid = [p for p in paths if os.path.exists(p)]
        if not valid:
            return
        mime = QMimeData()
        mime.setUrls([QUrl.fromLocalFile(p) for p in valid])
        drag = QDrag(self)
        drag.setMimeData(mime)

        # Красивая плашка перетаскивания
        pix = QPixmap(180, 44)
        pix.fill(Qt.GlobalColor.transparent)
        q = QPainter(pix)
        q.setRenderHint(QPainter.RenderHint.Antialiasing)
        q.setPen(QPen(white(60), 1))
        q.setBrush(QColor(22, 24, 34, 235))
        q.drawRoundedRect(QRectF(2, 2, 176, 40), 12, 12)
        q.setFont(ui_font(12, QFont.Weight.Bold))
        q.setPen(white(245))
        label = os.path.basename(valid[0]) if len(valid) == 1 else f"📦 Файлов: {len(valid)}"
        q.drawText(QRectF(12, 2, 156, 40), Qt.AlignmentFlag.AlignVCenter,
                   QFontMetrics(q.font()).elidedText(label, Qt.TextElideMode.ElideMiddle, 156))
        q.end()
        drag.setPixmap(pix)
        drag.setHotSpot(QPoint(24, 22))
        drag.exec(Qt.DropAction.CopyAction | Qt.DropAction.MoveAction)

    # -----------------------------------------------------------------
    # БУФЕР ОБМЕНА, МГНОВЕННЫЙ ПЕРЕВОДЧИК И МИНИ-ИИ (ФИЧА 3)
    # -----------------------------------------------------------------
    def _init_clipboard_and_hotkeys(self):
        self.clipboard = QGuiApplication.clipboard()
        self.clipboard.dataChanged.connect(self.on_clipboard_changed)
        self.paste_signal.connect(self.on_paste_triggered)
        self.toast_timer = QTimer(self)
        self.toast_timer.setSingleShot(True)
        self.toast_timer.timeout.connect(self._end_toast)

        if HAS_KEYBOARD:
            try:
                keyboard.add_hotkey("ctrl+v", lambda: self.paste_signal.emit())
            except Exception:
                pass

    def on_clipboard_changed(self):
        if self.ignore_next_clip:
            self.ignore_next_clip = False
            return
        text = self.clipboard.text().strip()
        if not text:
            return
        if not self.clip_history or self.clip_history[0][0] != text:
            self.clip_history = [(t, ts) for t, ts in self.clip_history if t != text]
            self.clip_history.insert(0, (text, time.time()))
            self.clip_history = self.clip_history[:30]
            self.clip_list.set_items(self.clip_history)
        self.show_toast("📋", "Скопировано", " ".join(text.split()), action="translate", source_text=text)

    def on_paste_triggered(self):
        text = self.clipboard.text().strip()
        self.show_toast("✨", "Вставлено", " ".join(text.split()) or "элемент")

    def show_toast(self, icon: str, title: str, text: str = "", action: str = None, source_text: str = ""):
        if self.mode == self.EXPANDED:
            return
        self.toast = (icon, title, text[:120])
        self.toast_action = action
        self.toast_source_text = source_text
        self._set_shape_springs(0.42, 0.66)
        self.toast_timer.start(3200 if action else 2300)
        self._retarget()

    def _end_toast(self):
        self.toast = None
        self.toast_action = None
        self.toast_btn_rect = QRectF()
        self._set_shape_springs(0.46, 0.74)
        self._retarget()

    def run_text_assistant(self, text: str, mode: str = "translate"):
        text = (text or "").strip()
        if not text:
            return
        self.btn_voice_to_shelf.hide()
        self.lbl_ai_title.setText("🌐 Перевожу…" if mode == "translate" else "✦ ИИ анализирует…")
        self.lbl_ai_body.setText("Подождите секунду…")
        self.ai_card.show()
        self.assistant_worker = TextAssistantWorker(text, mode)
        self.assistant_worker.finished_result.connect(self._on_assistant_finished)
        self.assistant_worker.start()

    def _on_assistant_finished(self, title: str, result: str):
        self.lbl_ai_title.setText(title)
        self.lbl_ai_body.setText(result)
        self.ai_card.show()

    def copy_ai_result(self):
        txt = self.lbl_ai_body.text().strip()
        if txt:
            self.ignore_next_clip = True
            self.clipboard.setText(txt)
            self.lbl_ai_title.setText("✓ Результат скопирован")

    def copy_from_history(self, index: int):
        if 0 <= index < len(self.clip_history):
            self.ignore_next_clip = True
            self.clipboard.setText(self.clip_history[index][0])
            self.clip_list.flash_row(index)

    def clear_clipboard_history(self):
        self.clip_history.clear()
        self.clip_list.set_items(self.clip_history)

    # -----------------------------------------------------------------
    # ГОЛОСОВЫЕ ЗАМЕТКИ И ДИКТОВКА SPEECH-TO-TEXT (ФИЧА 5)
    # -----------------------------------------------------------------
    def toggle_voice_dictation(self):
        if not self.dictation_active:
            if not self.voice_recorder.start():
                self.show_toast("⚠️", "Микрофон недоступен", "Проверьте подключение микрофона")
                return
            self.dictation_active = True
            self.btn_quick_mic.setText("⏹ Стоп")
            self.btn_clip_mic.setText("⏹ Стоп")
            if self.mode == self.EXPANDED:
                self.collapse()
            self._set_shape_springs(0.42, 0.70)
            self._retarget()
            self.kick()
        else:
            self.dictation_active = False
            self.btn_quick_mic.setText("🎙️ Диктовка")
            self.btn_clip_mic.setText("🎙️ Диктовка")
            wav_path = self.voice_recorder.stop()
            self.last_voice_wav = wav_path
            self._retarget()
            if wav_path:
                self.show_toast("🎙️", "Распознаю речь…", "Обработка голосовой заметки")
                self.transcribe_worker = SpeechTranscribeWorker(wav_path)
                self.transcribe_worker.transcribed.connect(self._on_speech_transcribed)
                self.transcribe_worker.start()

    def _on_speech_transcribed(self, text: str, wav_path: str):
        if text:
            self.ignore_next_clip = True
            self.clipboard.setText(text)
            self.clip_history = [(t, ts) for t, ts in self.clip_history if t != text]
            self.clip_history.insert(0, (text, time.time()))
            self.clip_list.set_items(self.clip_history)
            self.lbl_ai_title.setText("🎙️ Распознанная диктовка (уже в буфере)")
            self.lbl_ai_body.setText(text)
            self.btn_voice_to_shelf.setVisible(bool(wav_path and os.path.exists(wav_path)))
            self.ai_card.show()
            self.show_toast("🎙️", "Скопировано в буфер", text, action="translate", source_text=text)
        elif wav_path and os.path.exists(wav_path):
            self.add_paths_to_shelf([wav_path])
            self.show_toast("🎙️", "Голосовая заметка сохранена", "Аудиофайл добавлен на Файловую полку")

    def put_last_voice_on_shelf(self):
        if self.last_voice_wav and os.path.exists(self.last_voice_wav):
            self.add_paths_to_shelf([self.last_voice_wav])
            self._open_tab(1)

    # -----------------------------------------------------------------
    # СКАНЕР ТЕКСТА С ЭКРАНА (OCR) И ПИПЕТКА ЦВЕТА (ФИЧА 7)
    # -----------------------------------------------------------------
    def start_screen_ocr(self):
        if self.mode == self.EXPANDED:
            self.collapse()
        QTimer.singleShot(180, self._launch_ocr_overlay)

    def _launch_ocr_overlay(self):
        self.active_overlay = ScreenSnipOverlay(self.accent)
        self.active_overlay.area_selected.connect(self._on_ocr_area_selected)
        self.active_overlay.show()
        self.active_overlay.activateWindow()

    def _on_ocr_area_selected(self, img: QImage):
        self.show_toast("🔍", "Сканер текста (OCR)", "Распознаю текст с выбранной области…")
        self.ocr_worker = OcrWorker(img)
        self.ocr_worker.ocr_finished.connect(self._on_ocr_finished)
        self.ocr_worker.start()

    def _on_ocr_finished(self, text: str):
        if text:
            self.ignore_next_clip = True
            self.clipboard.setText(text)
            self.clip_history = [(t, ts) for t, ts in self.clip_history if t != text]
            self.clip_history.insert(0, (text, time.time()))
            self.clip_list.set_items(self.clip_history)
            self.show_toast("🔍", "Текст распознан и скопирован", " ".join(text.split()),
                            action="translate", source_text=text)
        else:
            self.show_toast("🔍", "Текст не найден", "Попробуйте выделить более крупный участок")

    def start_color_picker(self):
        if self.mode == self.EXPANDED:
            self.collapse()
        QTimer.singleShot(180, self._launch_picker_overlay)

    def _launch_picker_overlay(self):
        self.active_overlay = ColorPickerOverlay()
        self.active_overlay.color_picked.connect(self._on_screen_color_picked)
        self.active_overlay.show()
        self.active_overlay.activateWindow()

    def _on_screen_color_picked(self, color: QColor):
        hex_code = color.name().upper()
        self.ignore_next_clip = True
        self.clipboard.setText(hex_code)
        self.clip_history = [(t, ts) for t, ts in self.clip_history if t != hex_code]
        self.clip_history.insert(0, (hex_code, time.time()))
        self.clip_list.set_items(self.clip_history)
        self.show_toast("🎨", f"Цвет {hex_code} скопирован",
                        f"RGB({color.red()}, {color.green()}, {color.blue()})")

    # -----------------------------------------------------------------
    # ПОЛЗУНОК ГРОМКОСТИ (ФИЧА 6) И ТОСТЫ УСТРОЙСТВ (ФИЧА 8)
    # -----------------------------------------------------------------
    def on_volume_changed(self, vol: int, muted: bool):
        if not self.config.get("volume_hud", True) or self.mode == self.EXPANDED:
            return
        first_show = self.volume_banner is None
        self.volume_banner = (vol, muted)
        if first_show:
            self.vol_bar_spring.snap(vol / 100.0)
        else:
            self.vol_bar_spring.target = vol / 100.0
        self._set_shape_springs(0.36, 0.72)
        self.volume_timer.start(1650)
        self._retarget()

    def _end_volume_banner(self):
        self.volume_banner = None
        self._set_shape_springs(0.44, 0.76)
        self._retarget()

    def set_volume_hud_enabled(self, enabled: bool):
        self.config["volume_hud"] = bool(enabled)
        self.save_config()

    def on_device_event(self, icon: str, title: str, subtitle: str, connected: bool):
        if not self.config.get("device_toasts", True) or self.mode == self.EXPANDED:
            return
        self.device_banner = (icon, title, subtitle, connected)
        self.device_pulse.snap(0.72)
        self.device_pulse.target = 1.0
        self._set_shape_springs(0.44, 0.64)
        self.device_timer.start(3000)
        self._retarget()

    def _end_device_banner(self):
        self.device_banner = None
        self._set_shape_springs(0.46, 0.76)
        self._retarget()

    def set_device_toasts_enabled(self, enabled: bool):
        self.config["device_toasts"] = bool(enabled)
        self.save_config()

    # -----------------------------------------------------------------
    # МЕДИА, СИНХРОНИЗАЦИЯ ТЕКСТА ПЕСЕН (PLL), СТАТУС, ТАЙМЕРЫ
    # -----------------------------------------------------------------
    def _init_workers_and_timers(self):
        self.volume_timer = QTimer(self)
        self.volume_timer.setSingleShot(True)
        self.volume_timer.timeout.connect(self._end_volume_banner)

        self.device_timer = QTimer(self)
        self.device_timer.setSingleShot(True)
        self.device_timer.timeout.connect(self._end_device_banner)

        self.media_worker = MediaWorker()
        self.media_worker.media_updated.connect(self.on_media_updated)
        self.media_worker.lyrics_updated.connect(self.on_lyrics_updated)
        self.media_worker.artwork_updated.connect(self.on_artwork_updated)
        self.media_worker.start()

        self.status_worker = StatusWorker()
        self.status_worker.status_updated.connect(self.on_status_updated)
        self.status_worker.volume_changed.connect(self.on_volume_changed)
        self.status_worker.device_event.connect(self.on_device_event)
        self.status_worker.start()

        self.grabber = BackdropGrabber()
        self.grabber.captured.connect(self._on_backdrop)
        self.grabber.start()

        self.backdrop_timer = QTimer(self)
        self.backdrop_timer.timeout.connect(self._request_backdrop)
        self.backdrop_timer.start(120)

        self.cursor_timer = QTimer(self)
        self.cursor_timer.timeout.connect(self._poll_cursor)
        self.cursor_timer.start(16)

        self.media_timer = QTimer(self)
        self.media_timer.setTimerType(Qt.TimerType.PreciseTimer)
        self.media_timer.timeout.connect(self._on_media_tick)
        self.media_timer.start(50)

        self.second_timer = QTimer(self)
        self.second_timer.timeout.connect(self._on_second)
        self.second_timer.start(1000)

        QApplication.instance().aboutToQuit.connect(self._shutdown)

    def _shutdown(self):
        if self.dictation_active:
            self.voice_recorder.stop()
        for worker in (self.media_worker, self.status_worker):
            worker.running = False
        self.grabber.stop()
        self._write_config()
        for worker in (self.media_worker, self.status_worker, self.grabber):
            worker.wait(1500)

    def current_position(self) -> float:
        pos = self.pos_base
        if self.media.get("playing"):
            pos += time.monotonic() - self.pos_stamp
        dur = self.media.get("duration", 0.0)
        return min(pos, dur) if dur > 0 else max(0.0, pos)

    def current_lyric_position(self) -> float:
        key = self.media.get("key") or ""
        offset = float(self.config.get("lyrics_offsets", {}).get(key, 0.0))
        return max(0.0, self.current_position() + offset)

    def adjust_lyrics_offset(self, delta: float, reset: bool = False):
        key = self.media.get("key") or ""
        if not key:
            return
        offsets = self.config.setdefault("lyrics_offsets", {})
        if reset:
            offsets.pop(key, None)
        else:
            cur = float(offsets.get(key, 0.0))
            new_val = round(clamp(cur + delta, -15.0, 15.0), 2)
            if abs(new_val) < 0.05:
                offsets.pop(key, None)
            else:
                offsets[key] = new_val
        self.save_config()
        self._update_sync_badge()
        self._on_media_tick()

    def _update_sync_badge(self):
        key = self.media.get("key") or ""
        off = float(self.config.get("lyrics_offsets", {}).get(key, 0.0))
        if abs(off) >= 0.05:
            sign = "+" if off > 0 else ""
            self.btn_sync_reset.setText(f"{sign}{off:.2f}с".replace(".00", ".0").replace("0с", "с"))
            self.btn_sync_reset.show()
        else:
            self.btn_sync_reset.hide()

    def on_media_updated(self, info: dict):
        prev_variant = self._variant()
        prev_key = self.media.get("key")
        prev_playing = bool(self.media.get("playing"))
        local_pos = self.current_position()

        self.media = info
        incoming_pos = float(info.get("position", 0.0))
        raw_pos = float(info.get("raw_pos", 0.0))
        playing = bool(info.get("playing"))

        if info.get("key") != prev_key or playing != prev_playing:
            self.pos_base = incoming_pos
            self.pos_stamp = time.monotonic()
            self.last_raw_pos = raw_pos
        elif playing:
            err = incoming_pos - local_pos
            raw_changed = abs(raw_pos - self.last_raw_pos) > 0.05
            self.last_raw_pos = raw_pos
            if abs(err) > 1.25:
                self.pos_base = incoming_pos
                self.pos_stamp = time.monotonic()
            elif raw_changed and abs(err) > 0.10:
                self.pos_base = local_pos + err * 0.35
                self.pos_stamp = time.monotonic()
        else:
            self.pos_base = incoming_pos
            self.pos_stamp = time.monotonic()

        if info.get("title"):
            self.lbl_title.setText(info["title"])
            self.lbl_artist.setText(info.get("artist") or "Неизвестный исполнитель")
        else:
            self.lbl_title.setText("Ничего не играет")
            self.lbl_artist.setText("Запустите Яндекс Музыку, Spotify или браузер")
        if info.get("key") != prev_key:
            self._update_sync_badge()
            self._show_lyrics_for(info.get("key", ""))
        self.btn_play.set_kind("pause" if playing else "play")
        self.player_wave.set_state(playing, self.art_color)
        self.btn_demo.setVisible(not info.get("title") or info.get("key") == "demo")
        self.progress.set_progress(self.current_position(), info.get("duration", 0.0))
        if self._variant() != prev_variant and self.mode == self.COMPACT:
            self._set_shape_springs(0.46, 0.68)
            self._retarget()
        if playing:
            self.kick()

    def on_lyrics_updated(self, key: str, synced: list, plain: str):
        self.lyrics_cache[key] = (synced, plain)
        if len(self.lyrics_cache) > 40:
            self.lyrics_cache.pop(next(iter(self.lyrics_cache)))
        if key == self.media.get("key"):
            self._show_lyrics_for(key)

    def _show_lyrics_for(self, key: str):
        if key == self.lyrics_key:
            return
        self.lyric_text = ""
        self.lyric_idx = -1
        if key in self.lyrics_cache:
            synced, plain = self.lyrics_cache[key]
            self.lyrics_key = key
            self.synced_lyrics = synced
            self.lyrics_view.set_lyrics(synced, plain, "Текст для этого трека не найден в LRCLIB")
        else:
            self.lyrics_key = None
            self.synced_lyrics = []
            self.lyrics_view.set_lyrics([], "", "Ищу текст песни…" if key else "Текст песни появится автоматически")

    def on_artwork_updated(self, key: str, data: bytes):
        img = QImage.fromData(data) if data else QImage()
        if img.isNull():
            self.art_image, self.art_pix = None, None
            self.art_color = QColor(self.accent)
        else:
            self.art_image = img
            self.art_pix = QPixmap.fromImage(img.scaled(96, 96, Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                                                        Qt.TransformationMode.SmoothTransformation))
            self.art_color = self._dominant_color(img)
        self.artwork.set_image(self.art_image, self.art_color)
        self.player_wave.set_state(bool(self.media.get("playing")), self.art_color)
        self.update()

    @staticmethod
    def _dominant_color(img: QImage) -> QColor:
        small = img.scaled(12, 12, Qt.AspectRatioMode.IgnoreAspectRatio, Qt.TransformationMode.SmoothTransformation)
        best, best_score = QColor(10, 132, 255), -1.0
        for y in range(small.height()):
            for x in range(small.width()):
                c = small.pixelColor(x, y)
                score = c.hsvSaturationF() * 0.7 + c.valueF() * 0.3
                if c.valueF() > 0.2 and score > best_score:
                    best, best_score = c, score
        h, s, v, _ = best.getHsvF()
        return QColor.fromHsvF(max(0.0, h), clamp(s, 0.35, 0.9), clamp(v, 0.75, 1.0))

    def _on_media_tick(self):
        if not self.media.get("title"):
            return
        pos = self.current_position()
        lyric_pos = self.current_lyric_position()
        self.progress.set_progress(pos, self.media.get("duration", 0.0))
        self.lyrics_view.set_position(lyric_pos)
        if self.synced_lyrics:
            times = [t for t, _ in self.synced_lyrics]
            idx = max(0, bisect.bisect_right(times, lyric_pos) - 1)
            self.lyric_idx = idx
            line = self.synced_lyrics[idx][1]
            if line != self.lyric_text:
                self.lyric_prev = self.lyric_text or self._compact_line()
                self.lyric_text = line
                self.lyric_anim.snap(0.0)
                self.lyric_anim.target = 1.0
                self.kick()

    def on_status_updated(self, status: dict):
        changed = status.get("cpu") != self.status.get("cpu") or status.get("vpn") != self.status.get("vpn")
        self.status = status

        if status.get("karing_exe") and not self.config.get("karing_path"):
            self.config["karing_path"] = status["karing_exe"]
            self.save_config()
        if status.get("detected_port"):
            self.config["karing_proxy"] = f"127.0.0.1:{status['detected_port']}"

        self.lbl_sys.setText(f"CPU {status['cpu']}% · RAM {status['ram']}%")
        if time.monotonic() > self._proxy_lock_until:
            active_state = bool(status.get("proxy") or status.get("tun"))
            if self.sw_proxy.isChecked() != active_state:
                self.sw_proxy.setChecked(active_state)
        self._update_vpn_badge()
        if changed and self.mode == self.COMPACT:
            self.update()

    def _update_vpn_badge(self):
        on = bool(self.status.get("proxy") or self.status.get("tun"))
        color = QColor("#30D158") if on else QColor(142, 142, 147)
        pix = QPixmap(68, 68)
        pix.fill(Qt.GlobalColor.transparent)
        pix.setDevicePixelRatio(2)
        p = QPainter(pix)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(with_alpha(color, 60))
        p.drawEllipse(QRectF(0, 0, 34, 34))
        shield = QPainterPath()
        shield.moveTo(17, 8)
        shield.lineTo(25, 11)
        shield.lineTo(25, 17)
        shield.cubicTo(25, 22, 21, 25.5, 17, 27)
        shield.cubicTo(13, 25.5, 9, 22, 9, 17)
        shield.lineTo(9, 11)
        shield.closeSubpath()
        p.setBrush(color)
        p.drawPath(shield)
        p.end()
        self.vpn_dot.setPixmap(pix)

        if self.status.get("tun"):
            text = "Активен TUN-режим Karing"
        elif self.status.get("proxy"):
            srv = self.status.get("proxy_server") or self.config.get("karing_proxy", "127.0.0.1:3067")
            text = f"Прокси включён ({srv})"
        elif self.status.get("karing"):
            text = "Karing запущен · Прокси выключен"
        else:
            text = "Не подключено"
        self.lbl_vpn_status.setText(text)

    def _on_second(self):
        if self.pomo_running:
            self.pomo_left = max(0, self.pomo_left - 1)
            m, s = divmod(self.pomo_left, 60)
            self.lbl_pomo.setText(f"Фокус-таймер · {m:02d}:{s:02d}")
            if self.pomo_left == 0:
                self.pomo_running = False
                self.pomo_left = self.pomo_total
                self.btn_pomo.setText("Старт")
                self.lbl_pomo.setText("Фокус-таймер · 25:00")
                self.show_toast("🎉", "Фокус-сессия завершена", "Время отдохнуть")
        if self.mode == self.COMPACT and not self.anim_timer.isActive():
            self.update()

    def toggle_demo_track(self, checked: bool):
        self.media_worker.toggle_demo(checked)

    def on_play_pause(self):
        self.send_media_key(0xB3)
        self.btn_play.set_kind("play" if self.btn_play.kind == "pause" else "pause")

    @staticmethod
    def send_media_key(vk_code: int):
        user32.keybd_event(vk_code, 0, 0, 0)
        user32.keybd_event(vk_code, 0, 2, 0)

    # -----------------------------------------------------------------
    # KARING VPN, СИСТЕМНЫЙ ПРОКСИ И ЯРЛЫКИ
    # -----------------------------------------------------------------
    def _find_karing_exe(self) -> str:
        candidates = [
            self.config.get("karing_path", ""),
            self.status.get("karing_exe", ""),
            os.path.expandvars(r"%LocalAppData%\Programs\Karing\karing.exe"),
            r"C:\Program Files\Karing\karing.exe",
            r"C:\Program Files (x86)\Karing\karing.exe",
            os.path.expandvars(r"%UserProfile%\Desktop\Karing\karing.exe"),
        ]
        for p in candidates:
            if p and os.path.exists(p):
                return p
        return ""

    def handle_karing_vpn(self):
        exe_path = self._find_karing_exe()
        if exe_path:
            if exe_path != self.config.get("karing_path"):
                self.config["karing_path"] = exe_path
                self.save_config()
            subprocess.Popen([exe_path], shell=False)
            self.collapse()
            self.show_toast("🛡️", "Karing VPN", "Открываю…")
            return

        if is_url_scheme_registered("karing"):
            try:
                os.startfile("karing://")
                self.collapse()
                self.show_toast("🛡️", "Karing VPN", "Открываю…")
                return
            except Exception:
                pass

        self.dialog_open = True
        file_path, _ = QFileDialog.getOpenFileName(
            self, "Укажите путь к karing.exe (один раз)", "C:\\", "Executable (*.exe)"
        )
        self.dialog_open = False
        if file_path:
            self.config["karing_path"] = file_path
            self.save_config()
            subprocess.Popen([file_path], shell=False)
            self.collapse()
            self.show_toast("🛡️", "Karing VPN", "Путь сохранён, запускаю")

    def set_system_proxy(self, enabled: bool):
        self._proxy_lock_until = time.monotonic() + 3.5

        _, current_srv = get_system_proxy_info()
        port = self.status.get("detected_port")
        if port:
            server = f"127.0.0.1:{port}"
        elif current_srv:
            server = current_srv
        else:
            server = self.config.get("karing_proxy") or "127.0.0.1:3067"

        self.config["karing_proxy"] = server
        self.save_config()

        if enabled:
            if is_url_scheme_registered("karing"):
                try:
                    os.startfile("karing://connect")
                except Exception:
                    pass
            elif not self.status.get("karing"):
                exe_path = self._find_karing_exe()
                if exe_path:
                    try:
                        subprocess.Popen([exe_path], shell=False)
                    except Exception:
                        pass
        else:
            if is_url_scheme_registered("karing") and self.status.get("tun"):
                try:
                    os.startfile("karing://disconnect")
                except Exception:
                    pass

        apply_windows_proxy(enabled, server)

        self.status["proxy"] = enabled
        self.status["proxy_server"] = server
        if not enabled:
            self.status["tun"] = False
        self.status["vpn"] = enabled or self.status.get("tun", False)
        self._update_vpn_badge()

    def launch_shortcut(self, sc: dict):
        target = sc.get("target", "")
        fallback = sc.get("fallback", "")
        try:
            if target.endswith(".exe") and os.path.exists(target):
                subprocess.Popen([target], shell=False)
            else:
                os.startfile(target)
        except Exception:
            webbrowser.open(fallback or target)
        self.collapse()
        self.show_toast(sc.get("icon", "🚀"), sc.get("name", ""), "Открываю…")

    def toggle_add_form(self):
        self.add_form.setVisible(not self.add_form.isVisible())
        if self.add_form.isVisible():
            self.inp_sc_name.setFocus()

    def add_custom_shortcut(self):
        icon = self.inp_sc_icon.text().strip() or "🔗"
        name = self.inp_sc_name.text().strip()
        target = self.inp_sc_url.text().strip()
        if not name or not target:
            return
        if "://" not in target and not os.path.exists(target):
            target = "https://" + target
        palette = [c for _, c in PRESET_ACCENTS]
        color = palette[len(self.config["shortcuts"]) % len(palette)]
        self.config["shortcuts"].append({"name": name, "icon": icon, "target": target, "color": color})
        self.save_config()
        self.inp_sc_name.clear()
        self.inp_sc_url.clear()
        self.add_form.hide()
        self.grid.set_items(self.config["shortcuts"])

    def remove_shortcut(self, index: int):
        if 0 <= index < len(self.config["shortcuts"]):
            self.config["shortcuts"].pop(index)
            self.save_config()
            self.grid.set_items(self.config["shortcuts"])

    # -----------------------------------------------------------------
    # НАСТРОЙКИ: АКЦЕНТ, СТЕКЛО, РАЗМЕР, ПОЗИЦИЯ, POMODORO
    # -----------------------------------------------------------------
    def set_accent(self, hex_color: str):
        self.accent = QColor(hex_color)
        self.config["accent"] = self.accent.name()
        self.save_config()
        self.content.setStyleSheet(self._stylesheet())
        for sw in (self.sw_proxy, self.sw_live, self.sw_autostart, self.sw_vol_hud, self.sw_dev_toast):
            sw.set_accent(self.accent)
        self.grid.accent = self.accent
        self.shelf_view.accent = self.accent
        self.clip_list.accent = self.accent
        self.color_dots.set_current(self.accent.name())
        if self.art_image is None:
            self.art_color = QColor(self.accent)
            self.artwork.set_image(None, self.accent)
        self.update()

    def pick_custom_color(self):
        self.dialog_open = True
        col = QColorDialog.getColor(self.accent, self, "Акцентный цвет")
        self.dialog_open = False
        if col.isValid():
            self.set_accent(col.name())

    def on_glass_changed(self):
        self.config["glass_tint"] = self.sld_tint.value()
        self.config["blur"] = self.sld_blur.value()
        self.save_config()
        self._request_backdrop()
        self.update()

    def on_scale_changed(self):
        scale = round(self.sld_scale.value() / 100.0, 2)
        self.config["island_scale"] = scale
        self.config["expanded_w"] = int(clamp(round(620 * scale), EXP_MIN[0], EXP_MAX[0]))
        self.config["expanded_h"] = int(clamp(round(430 * scale), EXP_MIN[1], EXP_MAX[1]))
        self.save_config()
        self.sw.snap(self.config["expanded_w"] if self.mode == self.EXPANDED else self._compact_size()[0])
        self.sh.snap(self.config["expanded_h"] if self.mode == self.EXPANDED else self._compact_size()[1])
        self._retarget()
        self.update()

    def reset_island_position(self):
        geo = QGuiApplication.primaryScreen().geometry()
        self.home_pos = None
        self.scx.target, self.stop.target = geo.center().x(), geo.top() + DEFAULT_TOP
        self.config["pos_cx"], self.config["pos_top"] = None, None
        self.save_config()
        self.kick()

    def toggle_pomodoro(self):
        self.pomo_running = not self.pomo_running
        if self.pomo_running:
            self.btn_pomo.setText("Сброс")
        else:
            self.pomo_left = self.pomo_total
            self.btn_pomo.setText("Старт")
            self.lbl_pomo.setText("Фокус-таймер · 25:00")
        if self.mode == self.COMPACT:
            self._retarget()

    # -----------------------------------------------------------------
    # СИСТЕМНЫЙ ТРЕЙ
    # -----------------------------------------------------------------
    def _init_tray(self):
        pix = QPixmap(64, 64)
        pix.fill(Qt.GlobalColor.transparent)
        p = QPainter(pix)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setPen(QPen(white(200), 3))
        p.setBrush(QColor(18, 18, 22))
        p.drawRoundedRect(QRectF(4, 18, 56, 28), 14, 14)
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor("#0A84FF"))
        p.drawEllipse(QPointF(46, 32), 4.5, 4.5)
        p.end()

        self.tray = QSystemTrayIcon(QIcon(pix), self)
        self.tray.setToolTip("Dynamic Island")
        menu = QMenu()
        act_open = QAction("Развернуть остров", self)
        act_open.triggered.connect(self.expand)
        act_shelf = QAction("📂 Файловая полка", self)
        act_shelf.triggered.connect(lambda: self._open_tab(1))
        act_ocr = QAction("🔍 Сканер текста с экрана (OCR)", self)
        act_ocr.triggered.connect(self.start_screen_ocr)
        act_picker = QAction("🎨 Пипетка цвета", self)
        act_picker.triggered.connect(self.start_color_picker)
        act_mic = QAction("🎙️ Голосовая диктовка", self)
        act_mic.triggered.connect(self.toggle_voice_dictation)
        act_center = QAction("Вернуть в центр", self)
        act_center.triggered.connect(self.reset_island_position)
        act_quit = QAction("Выход", self)
        act_quit.triggered.connect(QApplication.instance().quit)
        menu.addAction(act_open)
        menu.addAction(act_shelf)
        menu.addSeparator()
        menu.addAction(act_ocr)
        menu.addAction(act_picker)
        menu.addAction(act_mic)
        menu.addSeparator()
        menu.addAction(act_center)
        menu.addSeparator()
        menu.addAction(act_quit)
        self.tray_menu = menu
        self.tray.setContextMenu(menu)
        self.tray.activated.connect(
            lambda reason: self.expand() if reason == QSystemTrayIcon.ActivationReason.Trigger else None)
        self.tray.show()

    def showEvent(self, event):
        super().showEvent(event)
        self._apply_capture_exclusion()
        self.click_through = None
        QTimer.singleShot(20, self._request_backdrop)


def main():
    sys.excepthook = lambda t, v, tb: traceback.print_exception(t, v, tb)
    app = QApplication(sys.argv)
    app.setQuitOnLastWindowClosed(False)
    init_fonts()
    app.setFont(ui_font(13))

    island = DynamicIsland()
    island.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()