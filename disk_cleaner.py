# -*- coding: utf-8 -*-
"""
Анализатор диска: поиск больших файлов, тяжёлых папок, мусора и дубликатов.
Запуск:  python disk_cleaner.py   (или двойной клик по «Запустить.bat»)
Ничего не удаляет само — только по вашей команде и только в Корзину.
"""
import os
import struct
import sys
import time
import csv
import heapq
import fnmatch
import hashlib
import queue
import string
import threading
import subprocess
from collections import defaultdict
from datetime import datetime
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import tkinter.font as tkfont
import shutil

try:
    import sv_ttk            # тема Sun Valley — внешний вид Windows 11
except ImportError:
    sv_ttk = None

IS_WIN = os.name == "nt"
FILE_ATTRIBUTE_REPARSE_POINT = 0x400

# ---------------------------------------------------------------- правила мусора
JUNK_FILE_RULES = [
    ("Временные файлы", ["*.tmp", "*.temp", "~$*", "*.~*", "*.crdownload", "*.part", "*.partial"]),
    ("Логи", ["*.log", "*.log.*", "*.etl"]),
    ("Резервные копии", ["*.bak", "*.old", "*.backup", "*.bkp"]),
    ("Дампы памяти", ["*.dmp", "*.mdmp", "*.hdmp"]),
    ("Служебные миниатюры", ["thumbs.db", "ehthumbs.db", ".ds_store", "iconcache*.db", "thumbcache_*.db"]),
]
JUNK_DIR_NAMES = {
    "temp": "Папки Temp", "tmp": "Папки Temp",
    "cache": "Кэш", "caches": "Кэш", ".cache": "Кэш", "inetcache": "Кэш браузера",
    "code cache": "Кэш", "gpucache": "Кэш", "shadercache": "Кэш", "dxcache": "Кэш",
    "__pycache__": "Кэш Python",
    "crashdumps": "Дампы памяти", "crashpad": "Отчёты о сбоях", "crashreports": "Отчёты о сбоях",
    "softwaredistribution": "Кэш обновлений Windows",
}


def _compile_rules(rules):
    """Превращает шаблоны вида *.tmp / ~$* / *.log.* / thumbcache_*.db в быстрые строковые проверки."""
    compiled = []
    for cat, patterns in rules:
        exact, suffix, prefix, contains, pre_suf = set(), [], [], [], []
        for p in patterns:
            n = p.count("*")
            if n == 0:
                exact.add(p)
            elif n == 1 and p.startswith("*"):
                suffix.append(p[1:])
            elif n == 1 and p.endswith("*"):
                prefix.append(p[:-1])
            elif n == 2 and p.startswith("*") and p.endswith("*"):
                contains.append(p[1:-1])
            else:
                a, _, b = p.partition("*")
                pre_suf.append((a, b.replace("*", "")))
        compiled.append((cat, exact, tuple(suffix), tuple(prefix), tuple(contains), tuple(pre_suf)))
    return compiled


_JUNK_COMPILED = _compile_rules(JUNK_FILE_RULES)


def junk_category(name_lower):
    for cat, exact, suffix, prefix, contains, pre_suf in _JUNK_COMPILED:
        if (name_lower in exact
                or (suffix and name_lower.endswith(suffix))
                or (prefix and name_lower.startswith(prefix))
                or any(c in name_lower for c in contains)
                or any(name_lower.startswith(a) and name_lower.endswith(b) for a, b in pre_suf)):
            return cat
    return None


# ---------------------------------------------------------------- оформление
PALETTE = {
    "light": dict(card="#ffffff", border="#e2e2e2", text="#1b1b1b", muted="#6b6b6b", accent="#005fb8",
                  track="#e5e5e5", warn="#c42b1c", orange="#b35900", ok="#0f7b0f", stripe="#f5f5f5",
                  panel="#ececec"),
    "dark": dict(card="#2b2b2b", border="#3a3a3a", text="#f2f2f2", muted="#a3a3a3", accent="#60cdff",
                 track="#454545", warn="#ff99a4", orange="#ffb86b", ok="#6ccb5f", stripe="#232323",
                 panel="#242424"),
}
GB = 1 << 30


def windows_prefers_dark():
    try:
        import winreg
        k = winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                           r"Software\Microsoft\Windows\CurrentVersion\Themes\Personalize")
        return winreg.QueryValueEx(k, "AppsUseLightTheme")[0] == 0
    except Exception:
        return False


def pct_bar(p, width=10):
    """Текстовая полоска доли: ███████░░░ 68.2 %"""
    n = max(0, min(width * 2, round(p * width * 2 / 100)))
    return f"{p:5.1f} %   " + "█" * (n // 2) + ("▌" if n % 2 else "")


def size_tag(size):
    return "huge" if size >= 10 * GB else ("big" if size >= GB else "")


def human(n):
    n = float(n)
    for unit in ("Б", "КБ", "МБ", "ГБ", "ТБ"):
        if abs(n) < 1024 or unit == "ТБ":
            return f"{n:.0f} {unit}" if unit == "Б" else f"{n:.1f} {unit}"
        n /= 1024


def fmt_date(ts):
    try:
        return datetime.fromtimestamp(ts).strftime("%Y-%m-%d %H:%M")
    except (OSError, ValueError, OverflowError):
        return ""


def list_drives():
    if not IS_WIN:
        return ["/"]
    return [f"{d}:\\" for d in string.ascii_uppercase if os.path.exists(f"{d}:\\")]


# ---------------------------------------------------------------- ответственность и настройки
APP_VERSION = "1.1"
DISCLAIMER = (
    "DiskCleaner показывает, что занимает место на диске, и помогает удалять ненужное.\n\n"
    "Программа предоставляется «как есть», без каких-либо гарантий. Списки «Мусор» и «Дубликаты» — "
    "только подсказки: программа не знает, что важно лично вам, и может ошибаться.\n\n"
    "Все решения об удалении принимаете вы, и вы несёте за них ответственность. Автор программы "
    "не отвечает за потерю данных, сбои Windows или программ, вызванные удалением файлов.\n\n"
    "Перед удалением проверяйте, что это за файл. Не удаляйте системные папки (Windows, Program Files, "
    "ProgramData, AppData), если не уверены. Удалённое попадает в Корзину — пока она не очищена, "
    "файлы можно восстановить. Важные данные храните в резервной копии."
)


# Файлы и папки, которые нельзя удалять вручную — даже если они огромные.
CRITICAL_FILES = {
    "pagefile.sys": ("Файл подкачки Windows",
                     "Windows использует его как продолжение оперативной памяти. Удалять нельзя.\n\n"
                     "Уменьшить можно так: Пуск → «Настройка представления и производительности системы» → "
                     "Дополнительно → Виртуальная память → Изменить. Слишком маленький файл подкачки "
                     "может привести к вылетам программ."),
    "hiberfil.sys": ("Файл гибернации",
                     "Хранит содержимое памяти, когда компьютер уходит в гибернацию, и нужен для быстрого запуска "
                     "Windows. Удалять вручную нельзя.\n\nЕсли гибернация не нужна: откройте командную строку "
                     "от имени администратора и выполните  powercfg /h off  — Windows сама удалит файл. "
                     "Вернуть: powercfg /h on."),
    "swapfile.sys": ("Файл подкачки приложений Windows",
                     "Служебный файл Windows для приложений из Microsoft Store. Удалять нельзя, им управляет система."),
    "bootmgr": ("Загрузчик Windows", "Без него компьютер перестанет загружаться. Удалять нельзя."),
    "bootnxt": ("Загрузчик Windows", "Без него компьютер может перестать загружаться. Удалять нельзя."),
    "ntuser.dat": ("Реестр пользователя", "Содержит все настройки вашего профиля Windows. Удалять нельзя."),
    "memory.dmp": None,   # дамп памяти — это как раз можно удалить (в «Мусоре»)
}
CRITICAL_ROOT_DIRS = {
    "windows": "Папка Windows — сама операционная система",
    "program files": "Установленные программы — удаляйте их через «Установка и удаление программ»",
    "program files (x86)": "Установленные программы — удаляйте их через «Установка и удаление программ»",
    "programdata": "Общие данные программ и Windows",
    "system volume information": "Точки восстановления и служебные данные Windows",
    "$recycle.bin": "Корзина — очищайте её через саму Корзину",
    "recovery": "Среда восстановления Windows",
    "boot": "Файлы загрузки Windows",
}
CRITICAL_WIN_SUBDIRS = {
    "winsxs": "Хранилище компонентов Windows. Уменьшить можно только «Очисткой диска» → «Очистить системные файлы»",
    "system32": "Системные файлы Windows",
    "syswow64": "Системные файлы Windows",
    "installer": "Установщики программ — без них не удалить и не обновить программы",
    "softwaredistribution": "Обновления Windows — очищайте через «Очистку диска»",
}


def critical_info(path):
    """(название, пояснение), если файл/папку нельзя удалять вручную, иначе None."""
    name = os.path.basename(path.rstrip("\\/")).lower()
    info = CRITICAL_FILES.get(name)
    if info:
        return info
    parent = os.path.dirname(path.rstrip("\\/"))
    is_root_child = os.path.dirname(parent) == parent
    if is_root_child and name in CRITICAL_ROOT_DIRS:
        return (CRITICAL_ROOT_DIRS[name], "Системная папка — удалять её или её содержимое вручную нельзя.")
    if os.path.basename(parent).lower() == "windows" and name in CRITICAL_WIN_SUBDIRS:
        return (CRITICAL_WIN_SUBDIRS[name], "Удалять вручную нельзя — Windows перестанет работать или обновляться.")
    return None


def settings_path():
    base = os.environ.get("APPDATA") or os.path.expanduser("~")
    return os.path.join(base, "DiskCleaner", "settings.json")


def load_settings():
    import json
    try:
        with open(settings_path(), encoding="utf-8-sig") as f:   # -sig: файл мог сохранить редактор с BOM
            return json.load(f)
    except (OSError, ValueError):
        return {}


def save_settings(data):
    import json
    try:
        os.makedirs(os.path.dirname(settings_path()), exist_ok=True)
        with open(settings_path(), "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except OSError:
        pass


def _system_roots():
    env = os.environ
    roots = [env.get("SystemRoot", r"C:\Windows"), env.get("ProgramFiles", r"C:\Program Files"),
             env.get("ProgramFiles(x86)", r"C:\Program Files (x86)"), env.get("ProgramData", r"C:\ProgramData"),
             env.get("APPDATA", ""), env.get("LOCALAPPDATA", ""),
             os.path.join(os.path.splitdrive(env.get("SystemRoot", "C:"))[0] + "\\", "$Recycle.Bin"),
             os.path.join(os.path.splitdrive(env.get("SystemRoot", "C:"))[0] + "\\", "Recovery"),
             os.path.join(os.path.splitdrive(env.get("SystemRoot", "C:"))[0] + "\\", "Boot")]
    return [os.path.normcase(os.path.abspath(r)) for r in roots if r]


def is_risky_path(p):
    """Системные папки, файлы программ, корень диска, папка профиля целиком."""
    n = os.path.normcase(os.path.abspath(p))
    for tmp in {os.environ.get("TEMP", ""), os.environ.get("TMP", "")}:
        t = os.path.normcase(os.path.abspath(tmp)) if tmp else ""
        if t and n.startswith(t + os.sep):                # содержимое Temp — обычный мусор, не система
            return False
    if os.path.dirname(n) == n:                       # корень диска
        return True
    home = os.path.normcase(os.path.expanduser("~"))
    if n == home or n == os.path.dirname(home):         # весь профиль или папка Users
        return True
    return any(n == r or n.startswith(r + os.sep) for r in _system_roots())


# ---------------------------------------------------------------- здоровье дисков (SMART)
# Всё читается через IOCTL с доступом 0 («только запросы к устройству») — права администратора не нужны.
BUS_NAMES = {1: "SCSI", 3: "ATA", 7: "USB", 8: "RAID", 10: "SAS", 11: "SATA", 12: "SD", 13: "MMC",
             16: "Storage Spaces", 17: "NVMe", 19: "UFS"}
ATA_WEAR_ATTRS = (231, 233, 202, 177, 169)      # нормализованное значение ≈ оставшийся ресурс SSD, %


ATA_NAMES = {
    1: "Ошибки чтения (частота)", 2: "Производительность обмена", 3: "Время раскрутки", 4: "Запусков/остановок",
    5: "Переназначенные сектора", 7: "Ошибки позиционирования", 8: "Скорость позиционирования",
    9: "Наработка, ч", 10: "Повторы раскрутки", 11: "Повторы калибровки", 12: "Включений питания",
    13: "Программные ошибки чтения", 160: "Неисправимые секторы (чтение)", 161: "Годные блоки",
    163: "Начальные плохие блоки", 164: "Всего стираний", 165: "Макс. стираний блока", 166: "Мин. стираний блока",
    167: "Среднее стираний блока", 168: "Ошибки PHY SATA", 169: "Остаток ресурса", 170: "Резервные блоки",
    171: "Ошибки программирования", 172: "Ошибки стирания", 173: "Выравнивание износа",
    174: "Внезапные отключения питания", 175: "Ошибки программирования (чип)", 176: "Ошибки стирания (чип)",
    177: "Выравнивание износа", 178: "Использовано резервных блоков (чип)", 179: "Использовано резервных блоков",
    180: "Неиспользованные резервные блоки", 181: "Ошибки программирования (всего)", 182: "Ошибки стирания (всего)",
    183: "Плохие блоки в работе / понижение SATA", 184: "Ошибки сквозной проверки", 187: "Неисправимые ошибки",
    188: "Таймауты команд", 189: "Запись с высоты полёта", 190: "Температура воздушного потока",
    191: "Ошибки от ударов", 192: "Аварийные парковки головок", 193: "Циклы загрузки/выгрузки головок",
    194: "Температура", 195: "Исправлено ECC", 196: "События переназначения", 197: "Нестабильные сектора",
    198: "Неисправимые сектора", 199: "Ошибки CRC (кабель)", 200: "Ошибки записи", 201: "Программные ошибки",
    202: "Остаток ресурса", 206: "Высота полёта головок", 210: "Ошибки RAIN", 220: "Смещение пластин",
    222: "Часы с загруженными головками", 223: "Повторы загрузки головок", 225: "Циклы загрузки головок",
    226: "Время загрузки головок", 230: "Амплитуда головок / защита ресурса", 231: "Остаток ресурса SSD",
    232: "Резерв ресурса", 233: "Износ носителя", 234: "Среднее/макс. стираний", 235: "Годные блоки / отключения",
    240: "Часы полёта головок", 241: "Всего записано (LBA)", 242: "Всего прочитано (LBA)",
    243: "Записано (LBA, старшая часть)", 244: "Прочитано (LBA, старшая часть)", 246: "Всего записано хостом",
    247: "Страниц записано хостом", 248: "Страниц записано FTL", 249: "Записано в NAND, ГБ",
    250: "Повторы чтения", 251: "Остаток ресурса (мин.)", 252: "Сбросы после плохих блоков",
    254: "Защита от падения",
}
ATA_CRITICAL = {5, 10, 184, 187, 188, 196, 197, 198, 201}


def smart_rows(d):
    """Строки для окна SMART: (ID, название, текущее, худшее, порог, raw, состояние, уровень)."""
    rows = []
    if d.get("nvme"):
        nv = d["nvme"]
        cw = nv["crit_warning"]
        bits = ["резерв ниже порога", "температура", "надёжность снижена", "только чтение", "резервное питание"]
        cw_text = ", ".join(b for i, b in enumerate(bits) if cw >> i & 1) or "нет"
        u = lambda n: f"{n:,}".replace(",", " ")
        items = [
            ("01", "Критические предупреждения", cw_text, "bad" if cw else ""),
            ("02", "Температура (общая)", f"{nv['temp']} °C", "warn" if nv["temp"] >= 70 else ""),
            ("03", "Доступный резерв", f"{nv['spare']} %", "bad" if nv["spare"] < nv["spare_thr"] else ""),
            ("04", "Порог резерва", f"{nv['spare_thr']} %", ""),
            ("05", "Израсходовано ресурса", f"{nv['used']} %", "bad" if nv["used"] >= 100 else
             ("warn" if nv["used"] >= 90 else "")),
            ("06", "Прочитано", f"{tb(nv['read_bytes'])}  ({u(nv['read_units'])} × 512 000 байт)", ""),
            ("07", "Записано", f"{tb(nv['written_bytes'])}  ({u(nv['written_units'])} × 512 000 байт)", ""),
            ("08", "Команд чтения", u(nv["host_reads"]), ""),
            ("09", "Команд записи", u(nv["host_writes"]), ""),
            ("0A", "Время под нагрузкой", f"{u(nv['busy_min'])} мин", ""),
            ("0B", "Включений питания", u(nv["power_cycles"]), ""),
            ("0C", "Наработка", f"{u(nv['hours'])} ч", ""),
            ("0D", "Аварийных выключений", u(nv["unsafe_shutdowns"]), ""),
            ("0E", "Ошибки носителя и целостности", u(nv["media_errors"]), "warn" if nv["media_errors"] else ""),
            ("0F", "Записей в журнале ошибок", u(nv["err_log"]), ""),
            ("10", "Время выше порога предупреждения", f"{u(nv['warn_temp_min'])} мин", ""),
            ("11", "Время выше критической температуры", f"{u(nv['crit_temp_min'])} мин",
             "warn" if nv["crit_temp_min"] else ""),
        ]
        for i, t in enumerate(nv.get("sensors", []), 1):
            items.append((f"S{i}", f"Датчик температуры {i}", f"{t} °C", ""))
        for aid, name, val, lvl in items:
            rows.append((aid, name, "", "", "", val, "", lvl))
    elif d.get("ata"):
        thr = d.get("thresholds", {})
        for aid in sorted(d["ata"]):
            cur, worst, raw = d["ata"][aid]
            t = thr.get(aid)
            lvl, state = "", "OK"
            if t and cur <= t:
                lvl, state = "bad", "ОТКАЗ (ниже порога)"
            elif aid in ATA_CRITICAL and raw:
                lvl, state = "warn", "внимание"
            elif aid == 199 and raw:
                lvl, state = "warn", "проверьте кабель"
            raw_s = f"{raw:,}".replace(",", " ")
            if aid in (190, 194):
                raw_s = f"{raw & 0xFF} °C   (0x{raw:012X})"
            else:
                raw_s += f"   (0x{raw:012X})"
            rows.append((f"{aid:02X}", ATA_NAMES.get(aid, "Производитель"), cur, worst,
                         t if t is not None else "—", raw_s, state, lvl))
    return rows


def smart_report(d):
    lines = [f"{d['model']}   {d.get('serial', '')}",
             f"{d['bus']} · {('SSD' if d.get('ssd') else 'HDD') if d.get('ssd') is not None else ''} · "
             f"{human(d['size']) if d.get('size') else ''} · {', '.join(d.get('letters', []))}",
             f"Состояние: {d.get('level')}  ·  источник: {d.get('source') or '—'}", ""]
    for r in smart_rows(d):
        aid, name, cur, worst, thr, raw, state, _ = r
        if d.get("nvme"):
            lines.append(f"{aid:>3}  {name:<38} {raw}")
        else:
            lines.append(f"{aid:>3}  {name:<38} {cur!s:>4} {worst!s:>4} {thr!s:>4}  {raw:<32} {state}")
    return "\n".join(lines)


def is_admin():
    if not IS_WIN:
        return False
    try:
        import ctypes
        return bool(ctypes.windll.shell32.IsUserAnAdmin())
    except Exception:
        return False


def _win_io():
    import ctypes
    from ctypes import wintypes
    k32 = ctypes.WinDLL("kernel32", use_last_error=True)
    k32.CreateFileW.restype = wintypes.HANDLE
    k32.CreateFileW.argtypes = [wintypes.LPCWSTR, wintypes.DWORD, wintypes.DWORD, ctypes.c_void_p,
                                wintypes.DWORD, wintypes.DWORD, wintypes.HANDLE]
    k32.DeviceIoControl.argtypes = [wintypes.HANDLE, wintypes.DWORD, ctypes.c_void_p, wintypes.DWORD,
                                    ctypes.c_void_p, wintypes.DWORD, ctypes.POINTER(wintypes.DWORD), ctypes.c_void_p]
    k32.CloseHandle.argtypes = [wintypes.HANDLE]
    invalid = wintypes.HANDLE(-1).value

    def open_dev(path, access=0):
        h = k32.CreateFileW(path, access, 3, None, 3, 0, None)   # FILE_SHARE_READ|WRITE, OPEN_EXISTING
        return None if (not h or h == invalid) else h

    def ioctl(h, code, inbuf=b"", outsize=512):
        size = max(len(inbuf), outsize)
        buf = ctypes.create_string_buffer(inbuf, size) if inbuf else ctypes.create_string_buffer(size)
        ret = wintypes.DWORD()
        ok = k32.DeviceIoControl(h, code, buf if inbuf else None, len(inbuf), buf, size, ctypes.byref(ret), None)
        return buf.raw[:ret.value] if ok else None

    return open_dev, ioctl, k32.CloseHandle


IOCTL_STORAGE_QUERY_PROPERTY = 0x2D1400
IOCTL_STORAGE_PREDICT_FAILURE = 0x2D1100
IOCTL_STORAGE_GET_DEVICE_NUMBER = 0x2D1080
IOCTL_DISK_GET_DRIVE_GEOMETRY_EX = 0x700A0
SMART_RCV_DRIVE_DATA = 0x7C088


def _query(ioctl, h, prop_id, outsize=1024, extra=b""):
    return ioctl(h, IOCTL_STORAGE_QUERY_PROPERTY, struct.pack("<II", prop_id, 0) + (extra or b"\0\0\0\0"), outsize)


def parse_ata_smart(data):
    """512 байт SMART READ DATA -> {id: (нормализованное, худшее, raw)}"""
    attrs = {}
    if not data or len(data) < 362:
        return attrs
    for i in range(30):
        o = 2 + i * 12
        aid = data[o]
        if aid == 0:
            continue
        attrs[aid] = (data[o + 3], data[o + 4], int.from_bytes(data[o + 5:o + 11], "little"))
    return attrs


def parse_nvme_health(d):
    u128 = lambda o: int.from_bytes(d[o:o + 16], "little")
    sensors = [struct.unpack_from("<H", d, 200 + 2 * i)[0] for i in range(8)]
    return dict(crit_warning=d[0], temp=struct.unpack_from("<H", d, 1)[0] - 273, spare=d[3], spare_thr=d[4],
                used=d[5], read_units=u128(32), written_units=u128(48),
                read_bytes=u128(32) * 512000, written_bytes=u128(48) * 512000,
                host_reads=u128(64), host_writes=u128(80), busy_min=u128(96),
                power_cycles=u128(112), hours=u128(128), unsafe_shutdowns=u128(144),
                media_errors=u128(160), err_log=u128(176),
                warn_temp_min=struct.unpack_from("<I", d, 192)[0], crit_temp_min=struct.unpack_from("<I", d, 196)[0],
                sensors=[t - 273 for t in sensors if t])


def _read_disk(n, open_dev, ioctl, close):
    h = open_dev(f"\\\\.\\PhysicalDrive{n}")
    if h is None:
        return None
    d = dict(index=n, model=f"Диск {n}", bus="?", size=0, ssd=None, temp=None, letters=[],
             nvme=None, ata=None, predict_failure=None, source="")
    try:
        desc = _query(ioctl, h, 0)                                   # StorageDeviceProperty
        if desc and len(desc) >= 36:
            v_off, p_off, _, s_off, bus = struct.unpack_from("<IIIII", desc, 12)

            def sz(off):
                if not off or off >= len(desc):
                    return ""
                return desc[off:desc.index(b"\0", off) if b"\0" in desc[off:] else len(desc)].decode("ascii", "ignore").strip()
            d["model"] = " ".join(x for x in (sz(v_off), sz(p_off)) if x) or d["model"]
            d["serial"] = sz(s_off).rstrip(".").strip()
            d["bus"] = BUS_NAMES.get(bus, str(bus))
        geo = ioctl(h, IOCTL_DISK_GET_DRIVE_GEOMETRY_EX, b"", 256)
        if geo and len(geo) >= 32:
            d["size"] = struct.unpack_from("<q", geo, 24)[0]
        seek = _query(ioctl, h, 7, 16)                               # StorageDeviceSeekPenaltyProperty
        if seek and len(seek) >= 9:
            d["ssd"] = not seek[8]
        t = _query(ioctl, h, 51, 256)                                # StorageDeviceTemperatureProperty
        if t and len(t) >= 28 and struct.unpack_from("<H", t, 12)[0] > 0:
            val = struct.unpack_from("<h", t, 26)[0]
            if -40 < val < 150:
                d["temp"] = val
        if d["bus"] == "NVMe":
            # StorageDeviceProtocolSpecificProperty: NVMe, LogPage, Health Information (0x02)
            spec = struct.pack("<10I", 3, 2, 2, 0, 40, 512, 0, 0, 0, 0)
            r = ioctl(h, IOCTL_STORAGE_QUERY_PROPERTY, struct.pack("<II", 50, 0) + spec + b"\0" * 512, 8 + 40 + 512)
            if r and len(r) >= 8 + 40 + 512:
                off = struct.unpack_from("<I", r, 8 + 16)[0]
                d["nvme"] = parse_nvme_health(r[8 + off: 8 + off + 512])
                d["source"] = "журнал здоровья NVMe"
        else:
            pf = ioctl(h, IOCTL_STORAGE_PREDICT_FAILURE, b"", 516)    # PredictFailure + 512 байт SMART
            if pf and len(pf) >= 516:
                d["predict_failure"] = bool(struct.unpack_from("<I", pf, 0)[0])
                attrs = parse_ata_smart(pf[4:])
                if attrs:
                    d["ata"] = attrs
                    d["source"] = "SMART (через прогноз отказа)"
    finally:
        close(h)
    if d["bus"] != "NVMe" and is_admin():
        _read_ata_admin(n, d, open_dev, ioctl, close)
    return d


def _read_ata_admin(n, d, open_dev, ioctl, close):
    """Классический SMART READ DATA — требует прав администратора (доступ на чтение и запись)."""
    h = open_dev(f"\\\\.\\PhysicalDrive{n}", 0xC0000000)
    if h is None:
        return
    try:
        # SENDCMDINPARAMS: cBufferSize, IDEREGS(Features=0xD0 READ DATA, Count=1, Number=1, CylLow=0x4F,
        #                  CylHigh=0xC2, DriveHead=0xA0, Command=0xB0), bDriveNumber, reserved
        inp = struct.pack("<I8BB3x4I", 512, 0xD0, 1, 1, 0x4F, 0xC2, 0xA0, 0xB0, 0, 0, 0, 0, 0, 0) + b"\0"
        if not d.get("ata"):
            r = ioctl(h, SMART_RCV_DRIVE_DATA, inp, 16 + 512)
            if r and len(r) >= 16 + 362:
                attrs = parse_ata_smart(r[16:16 + 512])
                if attrs:
                    d["ata"] = attrs
                    d["source"] = "SMART (права администратора)"
        # READ THRESHOLDS (Features = 0xD1) — пороги отказа по каждому атрибуту
        inp_t = inp[:4] + bytes([0xD1]) + inp[5:]
        r = ioctl(h, SMART_RCV_DRIVE_DATA, inp_t, 16 + 512)
        if r and len(r) >= 16 + 362:
            thr = {}
            for i in range(30):
                o = 16 + 2 + i * 12
                if r[o]:
                    thr[r[o]] = r[o + 1]
            if thr:
                d["thresholds"] = thr
    finally:
        close(h)


def read_disks_health():
    if not IS_WIN:
        return []
    open_dev, ioctl, close = _win_io()
    disks = []
    for n in range(32):
        try:
            d = _read_disk(n, open_dev, ioctl, close)
        except Exception:
            d = None
        if d:
            disks.append(d)
    by_num = {d["index"]: d for d in disks}
    for letter in list_drives():
        h = open_dev("\\\\.\\" + letter.rstrip("\\"))
        if h is None:
            continue
        try:
            r = ioctl(h, IOCTL_STORAGE_GET_DEVICE_NUMBER, b"", 12)
            if r and len(r) >= 8:
                num = struct.unpack_from("<I", r, 4)[0]
                if num in by_num:
                    by_num[num]["letters"].append(letter.rstrip("\\"))
        finally:
            close(h)
    for d in disks:
        evaluate_health(d)
    return disks


def tb(n):
    """Десятичные терабайты — в них производители указывают ресурс записи (TBW)."""
    return f"{n / 1e12:.1f} ТБ" if n >= 1e12 else f"{n / 1e9:.0f} ГБ"


def plural_years(n):
    if n % 10 == 1 and n % 100 != 11:
        return f"{n} год"
    if 2 <= n % 10 <= 4 and not 12 <= n % 100 <= 14:
        return f"{n} года"
    return f"{n} лет"


def evaluate_health(d):
    """Выставляет d['level'] (good/warn/bad/unknown), d['life'], d['problems'], d['metrics'], d['forecast']."""
    problems, metrics, life, level = [], [], None, "good"

    def flag(lvl, text):
        nonlocal level
        problems.append((lvl, text))
        if lvl == "bad" or (lvl == "warn" and level == "good"):
            level = lvl

    nv, ata = d.get("nvme"), d.get("ata")
    hours = None
    if nv:
        life = max(0, 100 - nv["used"])
        hours = nv["hours"]
        temp = nv["temp"] if -40 < nv["temp"] < 150 else d.get("temp")
        cw = nv["crit_warning"]
        if cw & 1:
            flag("bad", "Резервные ячейки почти закончились — диск может скоро отказать")
        if cw & 2:
            flag("warn", "Диск сообщает о перегреве или переохлаждении")
        if cw & 4:
            flag("bad", "Диск сообщает о снижении надёжности из-за ошибок носителя")
        if cw & 8:
            flag("bad", "Диск перешёл в режим «только чтение» — срочно скопируйте данные")
        if cw & 16:
            flag("warn", "Сбой резервного питания кэша")
        if nv["used"] >= 100:
            flag("bad", "Заявленный ресурс записи исчерпан")
        elif nv["used"] >= 90:
            flag("warn", f"Израсходовано {nv['used']} % ресурса записи")
        if nv["spare"] < nv["spare_thr"]:
            flag("bad", f"Резерв ячеек {nv['spare']} % — ниже порога {nv['spare_thr']} %")
        elif nv["spare"] < 50:
            flag("warn", f"Резерв ячеек снизился до {nv['spare']} %")
        if nv["media_errors"]:
            flag("warn", f"Ошибок носителя: {nv['media_errors']}")
        metrics = [("Температура", f"{temp} °C" if temp is not None else "—"),
                   ("Наработка", f"{nv['hours']:,} ч".replace(",", " ")),
                   ("Включений", f"{nv['power_cycles']:,}".replace(",", " ")),
                   ("Записано", tb(nv["written_bytes"])), ("Прочитано", tb(nv["read_bytes"])),
                   ("Резерв ячеек", f"{nv['spare']} %"), ("Ошибки носителя", str(nv["media_errors"])),
                   ("Аварийных выключений", f"{nv['unsafe_shutdowns']:,}".replace(",", " "))]
    elif ata:
        raw = lambda a: ata[a][2] if a in ata else None
        temp_raw = raw(194) if 194 in ata else raw(190)
        temp = (temp_raw & 0xFF) if temp_raw is not None else d.get("temp")
        hours = (raw(9) & 0xFFFFFFFF) if 9 in ata else None
        for a in ATA_WEAR_ATTRS:
            if a in ata and 0 < ata[a][0] <= 100 and d.get("ssd"):
                life = ata[a][0]
                break
        if d.get("predict_failure"):
            flag("bad", "Диск сам предсказывает скорый отказ (SMART) — срочно скопируйте данные")
        realloc, pending, uncorr = raw(5) or 0, raw(197) or 0, raw(198) or 0
        if realloc:
            flag("bad" if realloc >= 100 else "warn", f"Переназначено секторов: {realloc} — поверхность изнашивается")
        if pending:
            flag("bad" if pending >= 10 else "warn", f"Нестабильных секторов: {pending} — возможна потеря данных")
        if uncorr:
            flag("bad", f"Неисправимых секторов: {uncorr}")
        if raw(187):
            flag("warn", f"Неисправимых ошибок чтения: {raw(187)}")
        if raw(10) and not d.get("ssd"):
            flag("warn", f"Повторные попытки раскрутки: {raw(10)} — проблемы с механикой или питанием")
        if raw(199):
            flag("warn", f"Ошибки передачи данных (CRC): {raw(199)} — проверьте SATA-кабель")
        if life is not None and life <= 10:
            flag("bad" if life <= 3 else "warn", f"Осталось {life} % ресурса SSD")
        metrics = [("Температура", f"{temp} °C" if temp is not None else "—"),
                   ("Наработка", f"{hours:,} ч".replace(",", " ") if hours is not None else "—"),
                   ("Включений", f"{raw(12):,}".replace(",", " ") if 12 in ata else "—"),
                   ("Переназначено", str(realloc)), ("Нестабильных", str(pending)),
                   ("Неисправимых", str(uncorr)), ("Ошибки CRC", str(raw(199) or 0))]
    else:
        level = "unknown"
        temp = d.get("temp")
        if d.get("predict_failure"):
            flag("bad", "Диск сам предсказывает скорый отказ (SMART)")
        metrics = [("Температура", f"{temp} °C" if temp is not None else "—")]
    hot = 70 if d.get("ssd") else 55
    if temp is not None and temp >= hot:
        flag("warn", f"Высокая температура: {temp} °C")
    forecast = ""
    if life is not None and hours and life < 100:
        used = 100 - life
        remain_h = hours * life / used
        years = remain_h / (8 * 365)
        if years > 15:
            forecast = "Износ записью не станет проблемой ещё много лет (больше 15 при 8 ч работы в день)"
        else:
            forecast = (f"При нынешнем темпе ресурса хватит примерно на {remain_h / 1000:,.0f} тыс. часов работы "
                        f"(≈ {plural_years(max(1, round(years)))} при 8 ч в день)").replace(",", " ")
    elif life == 100:
        forecast = "Износ пока не заметен"
    d.update(level=level, life=life, problems=problems, metrics=metrics, forecast=forecast)
    return d


# ---------------------------------------------------------------- удаление в Корзину
def send_to_recycle_bin(paths):
    """Перемещает файлы/папки в Корзину Windows. Возвращает список ошибок."""
    errors = []
    if not IS_WIN:
        try:
            from send2trash import send2trash
        except ImportError:
            return ["Удаление в корзину поддерживается только в Windows (или установите send2trash)"]
        for p in paths:
            try:
                send2trash(p)
            except Exception as ex:
                errors.append(f"{p}: {ex}")
        return errors

    import ctypes
    from ctypes import wintypes

    class SHFILEOPSTRUCTW(ctypes.Structure):
        _fields_ = [("hwnd", wintypes.HWND), ("wFunc", wintypes.UINT),
                    ("pFrom", wintypes.LPCWSTR), ("pTo", wintypes.LPCWSTR),
                    ("fFlags", ctypes.c_ushort), ("fAnyOperationsAborted", wintypes.BOOL),
                    ("hNameMappings", ctypes.c_void_p), ("lpszProgressTitle", wintypes.LPCWSTR)]

    FO_DELETE, FOF_SILENT, FOF_NOCONFIRMATION, FOF_ALLOWUNDO, FOF_NOERRORUI = 3, 0x4, 0x10, 0x40, 0x400
    for p in paths:
        op = SHFILEOPSTRUCTW()
        op.wFunc = FO_DELETE
        op.pFrom = os.path.abspath(p) + "\0"   # строка должна заканчиваться двумя нулями
        op.fFlags = FOF_ALLOWUNDO | FOF_NOCONFIRMATION | FOF_SILENT | FOF_NOERRORUI
        rc = ctypes.windll.shell32.SHFileOperationW(ctypes.byref(op))
        if rc != 0 or op.fAnyOperationsAborted or os.path.exists(p):
            errors.append(f"{p}: не удалось удалить (код {rc}) — возможно, файл занят или нет прав")
    return errors


# ---------------------------------------------------------------- сканирование
class ScanResult:
    def __init__(self):
        self.root = ""
        self.big_files = []          # (size, path, mtime)
        self.dir_total = {}          # path -> суммарный размер
        self.dir_files = {}          # path -> число файлов (рекурсивно)
        self.children = defaultdict(list)
        self.junk = []               # (category, size, path, is_dir)
        self.ext_stats = defaultdict(lambda: [0, 0])  # ext -> [count, size]
        self.files = 0
        self.total = 0
        self.errors = 0
        self.seconds = 0.0
        self.cancelled = False
        self.parent = {}             # path -> родительская папка


HDD_WORKERS = 2          # на HDD параллельное чтение гоняет головку туда-сюда — больше 2 только медленнее
NETWORK_WORKERS = 4


def default_workers():
    return max(1, min(16, os.cpu_count() or 4))


_drive_cache = {}


def drive_kind(path):
    """Тип носителя, на котором лежит path: "SSD", "HDD", "USB", "Сеть" или None (не удалось определить).
    Используется IOCTL_STORAGE_QUERY_PROPERTY / StorageDeviceSeekPenaltyProperty — работает без прав администратора."""
    if not IS_WIN:
        return None
    drive = os.path.splitdrive(os.path.abspath(path))[0]
    if not drive or drive.startswith("\\\\"):
        return "Сеть" if drive else None
    drive = drive.upper()
    if drive in _drive_cache:
        return _drive_cache[drive]
    kind = None
    try:
        import ctypes
        from ctypes import wintypes
        k32 = ctypes.WinDLL("kernel32", use_last_error=True)
        dtype = k32.GetDriveTypeW(drive + "\\")
        if dtype == 4:            # DRIVE_REMOTE
            kind = "Сеть"
        else:
            class STORAGE_PROPERTY_QUERY(ctypes.Structure):
                _fields_ = [("PropertyId", wintypes.DWORD), ("QueryType", wintypes.DWORD),
                            ("AdditionalParameters", ctypes.c_ubyte * 1)]

            class DEVICE_SEEK_PENALTY_DESCRIPTOR(ctypes.Structure):
                _fields_ = [("Version", wintypes.DWORD), ("Size", wintypes.DWORD),
                            ("IncursSeekPenalty", ctypes.c_ubyte)]

            k32.CreateFileW.restype = wintypes.HANDLE
            k32.CreateFileW.argtypes = [wintypes.LPCWSTR, wintypes.DWORD, wintypes.DWORD, ctypes.c_void_p,
                                        wintypes.DWORD, wintypes.DWORD, wintypes.HANDLE]
            k32.DeviceIoControl.argtypes = [wintypes.HANDLE, wintypes.DWORD, ctypes.c_void_p, wintypes.DWORD,
                                            ctypes.c_void_p, wintypes.DWORD, ctypes.POINTER(wintypes.DWORD),
                                            ctypes.c_void_p]
            k32.CloseHandle.argtypes = [wintypes.HANDLE]
            # доступ 0 = только запросы к устройству, права администратора не нужны
            h = k32.CreateFileW("\\\\.\\" + drive, 0, 3, None, 3, 0, None)   # FILE_SHARE_READ|WRITE, OPEN_EXISTING
            if h and h != wintypes.HANDLE(-1).value:
                try:
                    q = STORAGE_PROPERTY_QUERY(7, 0)                    # StorageDeviceSeekPenaltyProperty, Standard
                    out = DEVICE_SEEK_PENALTY_DESCRIPTOR()
                    ret = wintypes.DWORD()
                    ok = k32.DeviceIoControl(h, 0x2D1400, ctypes.byref(q), ctypes.sizeof(q),   # IOCTL_STORAGE_QUERY_PROPERTY
                                             ctypes.byref(out), ctypes.sizeof(out), ctypes.byref(ret), None)
                    if ok and ret.value >= 9:
                        kind = "HDD" if out.IncursSeekPenalty else "SSD"
                finally:
                    k32.CloseHandle(h)
            if kind is None and dtype == 2:                     # DRIVE_REMOVABLE (флешка)
                kind = "USB"
    except Exception:
        kind = None
    _drive_cache[drive] = kind
    return kind


def workers_for(path):
    """Сколько процессов запускать: SSD — по числу ядер, HDD/флешка — 2, сеть — 4."""
    kind = drive_kind(path)
    if kind in ("HDD", "USB"):
        return kind, HDD_WORKERS
    if kind == "Сеть":
        return kind, NETWORK_WORKERS
    return kind, default_workers()


class _WorkerState:
    def __init__(self):
        self.big_files, self.junk, self.empty = [], [], []
        self.ext_stats = defaultdict(lambda: [0, 0])
        self.files = self.total = self.errors = 0
        self.current = ""


def _scan_dir(path, par, in_junk, min_size, st_, own_size, own_count, parent, push):
    """Обрабатывает одну папку. Вложенные папки отдаёт в очередь через push()."""
    parent[path] = par
    st_.current = path
    size = cnt = entries = 0
    try:
        with os.scandir(path) as it:
            for e in it:
                entries += 1
                try:
                    if e.is_dir(follow_symlinks=False):
                        if IS_WIN:
                            st = e.stat(follow_symlinks=False)
                            if getattr(st, "st_file_attributes", 0) & FILE_ATTRIBUTE_REPARSE_POINT:
                                continue  # ссылки/junction — пропускаем, чтобы не считать дважды
                        cat = JUNK_DIR_NAMES.get(e.name.lower())
                        if cat and not in_junk:
                            st_.junk.append([cat, 0, e.path, True])
                        push((e.path, path, in_junk or bool(cat)))
                    elif e.is_file(follow_symlinks=False):
                        st = e.stat(follow_symlinks=False)
                        sz = st.st_size
                        size += sz
                        cnt += 1
                        name = e.name
                        dot = name.rfind(".")
                        ext = name[dot:].lower() if dot > 0 else "(без расширения)"
                        s = st_.ext_stats[ext]
                        s[0] += 1
                        s[1] += sz
                        if sz >= min_size:
                            st_.big_files.append((sz, e.path, st.st_mtime))
                        if not in_junk:
                            cat = junk_category(e.name.lower())
                            if cat:
                                st_.junk.append([cat, sz, e.path, False])
                except OSError:
                    st_.errors += 1
    except OSError:
        st_.errors += 1
    own_size[path] = size
    own_count[path] = cnt
    st_.files += cnt
    st_.total += size
    if entries == 0 and par is not None:
        st_.empty.append(path)


_cancel_event = None


def _init_process(ev):
    global _cancel_event
    _cancel_event = ev


def _scan_chunk(items, min_size, budget=0.5):
    """Выполняется в отдельном процессе. Обходит папки из items, но не дольше budget секунд;
    необработанный остаток возвращает, чтобы его раздали свободным процессам (балансировка)."""
    st = _WorkerState()
    own_size, own_count, parent = {}, {}, {}
    stack = list(items)
    deadline = time.time() + budget
    while stack and time.time() < deadline:
        if _cancel_event is not None and _cancel_event.is_set():
            stack = []
            break
        _scan_dir(*stack.pop(), min_size, st, own_size, own_count, parent, stack.append)
    return (own_size, own_count, parent, st.big_files, st.junk, st.empty,
            dict(st.ext_stats), st.files, st.total, st.errors), stack, st.current


def scan(root, min_size, q, cancel, workers=None):
    """Верхние уровни обходятся здесь, а поддеревья раздаются нескольким процессам —
    так задействуются все ядра процессора (потоки Python упираются в GIL)."""
    workers = max(1, int(workers or default_workers()))
    r = ScanResult()
    r.root = root
    t0 = time.time()
    own_size, own_count, parent = {}, {}, {}
    empty = []

    def merge(res):
        o_s, o_c, par, big, junk, emp, ext, files, total, errors = res
        own_size.update(o_s)
        own_count.update(o_c)
        parent.update(par)
        r.big_files.extend(big)
        r.junk.extend(junk)
        empty.extend(emp)
        for k, (c, sz) in ext.items():
            e = r.ext_stats[k]
            e[0] += c
            e[1] += sz
        r.files += files
        r.total += total
        r.errors += errors

    # 1. нарезаем работу: раскрываем до 3 верхних уровней, пока частей не станет достаточно
    main = _WorkerState()
    frontier = [(root, None, False)]
    for _ in range(3):
        if len(frontier) >= workers * 4 or not frontier or cancel.is_set():
            break
        nxt = []
        for item in frontier:
            _scan_dir(*item, min_size, main, own_size, own_count, parent, nxt.append)
        frontier = nxt
    merge(({}, {}, {}, main.big_files, main.junk, main.empty, dict(main.ext_stats),
           main.files, main.total, main.errors))

    # 2. обходим части
    if workers == 1 or len(frontier) < 2:
        st = _WorkerState()
        stack = list(frontier)
        last = 0.0
        while stack and not cancel.is_set():
            _scan_dir(*stack.pop(), min_size, st, own_size, own_count, parent, stack.append)
            now = time.time()
            if now - last > 0.25:
                last = now
                q.put(("progress", r.files + st.files, r.total + st.total, st.current))
        merge(({}, {}, {}, st.big_files, st.junk, st.empty, dict(st.ext_stats), st.files, st.total, st.errors))
    else:
        import multiprocessing as mp
        from collections import deque
        from concurrent.futures import ProcessPoolExecutor, wait, FIRST_COMPLETED
        ctx = mp.get_context("spawn")
        ev = ctx.Event()
        tasks = deque([item] for item in frontier)
        with ProcessPoolExecutor(max_workers=workers, mp_context=ctx,
                                 initializer=_init_process, initargs=(ev,)) as ex:
            in_flight = set()

            def submit_more():
                while tasks and len(in_flight) < workers * 2 and not cancel.is_set():
                    in_flight.add(ex.submit(_scan_chunk, tasks.popleft(), min_size))

            submit_more()
            current = ""
            while in_flight:
                done, _ = wait(in_flight, timeout=0.25, return_when=FIRST_COMPLETED)
                if cancel.is_set():
                    ev.set()
                    tasks.clear()
                for f in done:
                    in_flight.discard(f)
                    try:
                        res, rest, current = f.result()
                        merge(res)
                    except Exception:
                        r.errors += 1
                        continue
                    if rest and not cancel.is_set():
                        # делим остаток на части, чтобы им занялись сразу несколько процессов
                        n = min(len(rest), workers)
                        for i in range(n):
                            tasks.append(rest[i::n])
                submit_more()
                q.put(("progress", r.files, r.total, f"[{workers} проц.] {current}"))
    r.cancelled = cancel.is_set()

    # 3. суммируем размеры снизу вверх: от самых глубоких папок к корню
    tot, fc = dict(own_size), dict(own_count)
    for p in sorted(own_size, key=lambda x: x.count(os.sep), reverse=True):
        par = parent.get(p)
        if par is not None and par in tot:
            tot[par] += tot[p]
            fc[par] += fc[p]
            r.children[par].append(p)
    r.dir_total, r.dir_files, r.parent = tot, fc, parent
    for j in r.junk:
        if j[3]:
            j[1] = tot.get(j[2], 0)
    r.junk = [j for j in r.junk if j[1] > 0 or not j[3]]
    for p in empty:
        r.junk.append(["Пустые папки", 0, p, True])
    r.big_files.sort(reverse=True)
    r.seconds = time.time() - t0
    q.put(("done", r))


def find_duplicates(files, q, cancel, workers=None):
    """files: [(size, path, mtime)]. Группировка по размеру -> хэш первого 1 МБ -> полный хэш.
    Хэширование идёт параллельно в нескольких потоках (hashlib и чтение файла отпускают GIL)."""
    from concurrent.futures import ThreadPoolExecutor
    workers = max(1, int(workers or default_workers()))
    by_size = defaultdict(list)
    for sz, p, _ in files:
        if sz > 0:
            by_size[sz].append(p)
    candidates = {sz: ps for sz, ps in by_size.items() if len(ps) > 1}

    def digest(path, limit=None):
        h = hashlib.blake2b(digest_size=20)
        read = 0
        try:
            with open(path, "rb") as f:
                while not cancel.is_set():
                    chunk = f.read(4 << 20)
                    if not chunk:
                        break
                    h.update(chunk)
                    read += len(chunk)
                    if limit and read >= limit:
                        break
        except OSError:
            return None
        return h.hexdigest()

    def run_stage(jobs, limit, label):
        """jobs: [(key, path)] -> {(key, hash): [paths]}"""
        out = defaultdict(list)
        total = len(jobs)
        with ThreadPoolExecutor(max_workers=workers) as ex:
            futs = {ex.submit(digest, p, limit): (k, p) for k, p in jobs}
            from concurrent.futures import as_completed
            for i, fut in enumerate(as_completed(futs), 1):
                k, p = futs[fut]
                if i % 5 == 0 or i == total:
                    q.put(("dupprogress", i, total, f"{label}: {p}"))
                h = fut.result()
                if h is not None:
                    out[(k, h)].append(p)
                if cancel.is_set():
                    for f in futs:
                        f.cancel()
                    return None
        return out

    stage1 = run_stage([(sz, p) for sz, ps in candidates.items() for p in ps], 1 << 20, "начало файлов")
    if stage1 is None:
        q.put(("dupdone", None))
        return
    groups, need_full = [], []
    for (sz, _), ps in stage1.items():
        if len(ps) < 2:
            continue
        if sz <= (1 << 20):
            groups.append((sz, ps))
        else:
            need_full.append((sz, ps))
    stage2 = run_stage([((sz, i), p) for i, (sz, ps) in enumerate(need_full) for p in ps], None, "полная проверка")
    if stage2 is None:
        q.put(("dupdone", None))
        return
    for ((sz, _), _h), ps in stage2.items():
        if len(ps) > 1:
            groups.append((sz, ps))
    groups.sort(key=lambda g: g[0] * (len(g[1]) - 1), reverse=True)
    q.put(("dupdone", groups))


# ---------------------------------------------------------------- таблица с сортировкой
class Table(ttk.Frame):
    """columns: [(id, заголовок, ширина, тип)], тип: size|int|date|text|pct"""

    def __init__(self, master, columns, path_col, note_col=None):
        super().__init__(master)
        self.note_col = note_col
        self.limit = 5000
        self.columns = columns
        self.path_col = path_col
        self.rows = []
        self.sort_col, self.sort_rev = None, True
        ids = [c[0] for c in columns]
        self.tree = ttk.Treeview(self, columns=ids, show="headings", selectmode="extended")
        for cid, title, width, kind in columns:
            anchor = "e" if kind in ("size", "int") else "w"
            self.tree.heading(cid, text=title, command=lambda c=cid: self.sort_by(c))
            self.tree.column(cid, width=width, anchor=anchor, stretch=(kind == "text"))
        ys = ttk.Scrollbar(self, orient="vertical", command=self.tree.yview)
        xs = ttk.Scrollbar(self, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=ys.set, xscrollcommand=xs.set)
        self.tree.grid(row=0, column=0, sticky="nsew")
        ys.grid(row=0, column=1, sticky="ns")
        xs.grid(row=1, column=0, sticky="ew")
        self.rowconfigure(0, weight=1)
        self.columnconfigure(0, weight=1)

    def set_rows(self, rows, limit=5000):
        self.rows = list(rows)
        self.limit = limit
        self.render()

    def render(self):
        self.tree.delete(*self.tree.get_children())
        kinds = [c[3] for c in self.columns]
        for i, row in enumerate(self.rows[: self.limit]):
            vals = []
            for v, k in zip(row, kinds):
                if k == "size":
                    vals.append(human(v))
                elif k == "date":
                    vals.append(fmt_date(v))
                elif k == "pct":
                    vals.append(pct_bar(v))
                elif k == "int":
                    vals.append(f"{v:,}".replace(",", " "))
                else:
                    vals.append(v)
            size = next((v for v, k in zip(row, kinds) if k == "size"), 0)
            tags = ["odd" if i % 2 else "even", size_tag(size)]
            if self.note_col is not None and row[self.note_col]:
                tags.append("critical")
            self.tree.insert("", "end", iid=str(i), values=vals, tags=tags)

    def sort_by(self, cid):
        idx = [c[0] for c in self.columns].index(cid)
        self.sort_rev = not self.sort_rev if self.sort_col == cid else self.columns[idx][3] != "text"
        self.sort_col = cid
        self.rows.sort(key=lambda r: (str(r[idx]).lower() if self.columns[idx][3] == "text" else r[idx]),
                       reverse=self.sort_rev)
        self.render()

    def selected_paths(self):
        return [self.rows[int(i)][self.path_col] for i in self.tree.selection()]

    def remove_paths(self, paths):
        s = set(paths)
        self.rows = [r for r in self.rows if r[self.path_col] not in s]
        self.render()

    def export_rows(self):
        header = [c[1] for c in self.columns]
        if self.rows and len(self.rows[0]) > len(header):
            header.append("Полный путь")
        return header, self.rows


# ---------------------------------------------------------------- обучение (пошаговый мастер)
class Tour:
    """Пошаговое обучение поверх окна.
    Слой 1 (ov): полупрозрачное затемнение с «дырой» — через неё можно нажимать.
    Слой 2 (an): прозрачный слой с мигающей рамкой вокруг кнопки, которую надо нажать, и подписями-выносками.
    Слой 3 (box): карточка с текстом шага и кнопками.
    Шаг: dict(target, click, marks, title, text, wait, cond, cond_auto, action, on_enter).
      target/click: функция -> виджет | [виджеты] | (x0, y0, x1, y1) | None
      marks: функция -> [(прямоугольник, подпись, "below"|"above"|"right"|"left")]"""
    HOLE = "#ff00fe"          # цвет-ключ: такие пиксели прозрачны и пропускают щелчки мыши
    KEY2 = "#00fe01"          # цвет-ключ второго слоя
    ACT = ("#ff7a00", "#ffc400")   # мигающая рамка «нажмите сюда»
    INFO = "#1f6feb"               # выноски-пояснения

    def __init__(self, app, steps, on_finish):
        self.app, self.steps, self.on_finish = app, steps, on_finish
        self.i, self.alive, self._last, self._no_auto, self.pulse = 0, True, None, -1, 0

        def layer(key, alpha=None):
            w = tk.Toplevel(app)
            w.overrideredirect(True)
            w.transient(app)
            try:
                if alpha:
                    w.attributes("-alpha", alpha)
                w.attributes("-transparentcolor", key)
            except tk.TclError:
                pass
            return w
        self.ov = layer(self.HOLE, 0.6)
        self.cv = tk.Canvas(self.ov, bg="#000000", highlightthickness=0, bd=0, cursor="arrow")
        self.cv.pack(fill="both", expand=True)
        self.cv.bind("<Button-1>", lambda e: self._nudge())
        self.an = layer(self.KEY2)
        self.acv = tk.Canvas(self.an, bg=self.KEY2, highlightthickness=0, bd=0)
        self.acv.pack(fill="both", expand=True)
        self.box = tk.Toplevel(app)
        self.box.overrideredirect(True)
        self.box.transient(app)
        self.box.bind("<Escape>", lambda e: self.finish())
        app.bind("<Escape>", lambda e: self.finish(), add="+")
        self.show(0)
        self._tick()

    # --- геометрия
    @staticmethod
    def _rect_of(t):
        t = t() if callable(t) else t
        if t is None:
            return None
        if isinstance(t, tuple):
            return t
        rects = []
        for w in (t if isinstance(t, list) else [t]):
            try:
                if w is not None and w.winfo_ismapped():
                    x, y = w.winfo_rootx(), w.winfo_rooty()
                    rects.append((x, y, x + w.winfo_width(), y + w.winfo_height()))
            except tk.TclError:
                pass
        if not rects:
            return None
        return (min(r[0] for r in rects), min(r[1] for r in rects),
                max(r[2] for r in rects), max(r[3] for r in rects))

    @staticmethod
    def _union(*rs):
        rs = [r for r in rs if r]
        if not rs:
            return None
        return (min(r[0] for r in rs), min(r[1] for r in rs), max(r[2] for r in rs), max(r[3] for r in rs))

    def _tick(self):
        if not self.alive:
            return
        try:
            self.pulse += 1
            self._layout()
            self._draw_marks()
            step = self.steps[self.i]
            if step.get("cond_auto") and self.i != self._no_auto and step["cond_auto"]():
                self.next()
        except Exception:
            pass                      # обучение не должно ломаться из-за одной неудачной отрисовки
        self.app.after(180, self._tick)

    def _layout(self, force=False):
        a = self.app
        if a.state() == "iconic":
            return
        ax, ay, aw, ah = a.winfo_rootx(), a.winfo_rooty(), a.winfo_width(), a.winfo_height()
        step = self.steps[self.i]
        r = self._union(self._rect_of(step.get("target")), self._rect_of(step.get("click")))
        key = (ax, ay, aw, ah, r, self.i)
        if key != self._last or force:
            self._last = key
            for w in (self.ov, self.an):
                w.geometry(f"{aw}x{ah}+{ax}+{ay}")
            self.cv.delete("all")
            pal = PALETTE[a.mode]
            if r:
                p = 6
                x0, y0, x1, y1 = r[0] - ax - p, r[1] - ay - p, r[2] - ax + p, r[3] - ay + p
                self.cv.create_rectangle(x0 - 3, y0 - 3, x1 + 3, y1 + 3, fill=pal["accent"], outline="")
                self.cv.create_rectangle(x0, y0, x1, y1, fill=self.HOLE, outline="")
        self.box.update_idletasks()
        bw, bh = self.box.winfo_reqwidth(), self.box.winfo_reqheight()
        if not r:
            bx, by = ax + (aw - bw) // 2, ay + (ah - bh) // 2
        else:
            # под кнопкой висит метка «Нажмите» — отодвигаем подсказку ниже, чтобы её не закрыть
            gap = 70 if step.get("click") and step.get("click_where", "below") == "below" else 22
            big = r[3] - r[1] > 260           # таблица или крупная панель
            if not big and r[3] + gap + bh < ay + ah - 8:
                by = r[3] + gap
                bx = min(max(r[0], ax + 12), ax + aw - bw - 12)
            elif not big and r[1] - gap - bh > ay + 8:
                by = r[1] - gap - bh
                bx = min(max(r[0], ax + 12), ax + aw - bw - 12)
            else:
                # цель большая (таблица) — подсказку в её правый нижний угол: выноски обычно сверху слева
                bx = max(ax + 12, min(r[2], ax + aw) - bw - 28)
                by = max(ay + 8, min(r[3], ay + ah) - bh - 28)
        # ставим подсказку на место при каждом обновлении: Tk может «думать», что окно уже там,
        # хотя Windows ещё не переместила его (особенно сразу после создания)
        self.box.geometry(f"+{bx}+{by}")
        if force or self.pulse % 10 == 0:
            self.an.lift()
            self.box.lift()

    # --- рамки и выноски
    def _callout(self, rect, text, where, color, ax, ay, aw, ah):
        cv = self.acv
        x0, y0, x1, y1 = rect[0] - ax, rect[1] - ay, rect[2] - ax, rect[3] - ay
        gap = 16
        if where == "above":
            tx, ty, anchor = x0 + 12, y0 - gap, "sw"
        elif where == "right":
            tx, ty, anchor = x1 + gap, (y0 + y1) // 2, "w"
        elif where == "left":
            tx, ty, anchor = x0 - gap, (y0 + y1) // 2, "e"
        else:
            tx, ty, anchor = x0 + 12, y1 + gap, "nw"
        t = cv.create_text(tx, ty, text=text, anchor=anchor, fill="#ffffff", font=self.app.f_bold)
        bx0, by0, bx1, by1 = cv.bbox(t)
        dx = min(0, aw - 10 - (bx1 + 8)) + max(0, 10 - (bx0 - 8))
        dy = min(0, ah - 10 - (by1 + 6)) + max(0, 10 - (by0 - 6))
        cv.move(t, dx, dy)
        bx0, by0, bx1, by1 = cv.bbox(t)
        # «хвостик» от выноски к рамке
        if where == "above":
            cv.create_line(bx0 + 14, by1 + 6, bx0 + 14, y0 - 3, fill=color, width=3)
        elif where == "right":
            cv.create_line(bx0 - 8, (by0 + by1) // 2, x1 + 3, (by0 + by1) // 2, fill=color, width=3)
        elif where == "left":
            cv.create_line(bx1 + 8, (by0 + by1) // 2, x0 - 3, (by0 + by1) // 2, fill=color, width=3)
        else:
            cv.create_line(bx0 + 14, by0 - 6, bx0 + 14, y1 + 3, fill=color, width=3)
        r = cv.create_rectangle(bx0 - 8, by0 - 6, bx1 + 8, by1 + 6, fill=color, outline="")
        cv.tag_raise(t)

    def _draw_marks(self):
        a = self.app
        ax, ay, aw, ah = a.winfo_rootx(), a.winfo_rooty(), a.winfo_width(), a.winfo_height()
        cv = self.acv
        cv.delete("all")
        step = self.steps[self.i]
        marks = []
        if step.get("marks"):
            try:
                marks = [m for m in step["marks"]() if m and m[0]]
            except Exception:
                marks = []
        for m in marks:
            rect, text = m[0], m[1]
            where = m[2] if len(m) > 2 else "below"
            x0, y0, x1, y1 = rect[0] - ax, rect[1] - ay, rect[2] - ax, rect[3] - ay
            cv.create_rectangle(x0 - 3, y0 - 3, x1 + 3, y1 + 3, outline=self.INFO, width=3)
            self._callout(rect, text, where, self.INFO, ax, ay, aw, ah)
        c = self._rect_of(step.get("click"))
        if c:
            col = self.ACT[self.pulse // 3 % 2]
            wdt = 4 if self.pulse // 3 % 2 else 6
            x0, y0, x1, y1 = c[0] - ax, c[1] - ay, c[2] - ax, c[3] - ay
            cv.create_rectangle(x0 - 5, y0 - 5, x1 + 5, y1 + 5, outline=col, width=wdt)
            self._callout(c, step.get("click_label", "👆  Нажмите здесь"), step.get("click_where", "below"),
                          self.ACT[0], ax, ay, aw, ah)

    def _nudge(self):
        """Щелчок мимо подсветки — подсказка «моргает», чтобы было видно, куда смотреть."""
        pal = PALETTE[self.app.mode]
        self.card.configure(highlightbackground=pal["warn"])
        self.app.after(350, lambda: self.alive and self.card.configure(highlightbackground=pal["accent"]))

    # --- содержимое подсказки
    def show(self, i):
        self.i = i
        step = self.steps[i]
        a = self.app
        pal = PALETTE[a.mode]
        if step.get("on_enter"):
            step["on_enter"]()
        for w in self.box.winfo_children():
            w.destroy()
        self.card = tk.Frame(self.box, bg=pal["card"], highlightthickness=2, highlightbackground=pal["accent"])
        self.card.pack()
        inner = tk.Frame(self.card, bg=pal["card"])
        inner.pack(padx=20, pady=16)
        n = len(self.steps)
        width = step.get("width", 420)
        tk.Label(inner, text=f"Шаг {i + 1} из {n}" if 0 < i < n - 1 else "Обучение", bg=pal["card"],
                 fg=pal["accent"], font=a.f_small).pack(anchor="w")
        tk.Label(inner, text=step["title"], bg=pal["card"], fg=pal["text"], font=a.f_big,
                 justify="left", wraplength=width).pack(anchor="w", pady=(2, 6))
        text = step["text"]() if callable(step["text"]) else step["text"]
        tk.Label(inner, text=text, bg=pal["card"], fg=pal["text"], font=a.f_norm,
                 justify="left", wraplength=width).pack(anchor="w")
        if step.get("wait"):
            tk.Label(inner, text="👉  " + step.get("action", "Ждём ваше действие…"), bg=pal["card"],
                     fg=pal["orange"], font=a.f_bold, justify="left", wraplength=width).pack(anchor="w", pady=(10, 0))
        bar = tk.Canvas(inner, width=width, height=4, bg=pal["card"], highlightthickness=0)
        bar.pack(anchor="w", pady=(14, 10))
        bar.create_rectangle(0, 0, width, 4, fill=pal["track"], outline="")
        bar.create_rectangle(0, 0, int(width * (i + 1) / n), 4, fill=pal["accent"], outline="")
        btns = tk.Frame(inner, bg=pal["card"])
        btns.pack(fill="x")
        last = i == n - 1
        acc = "Accent.TButton" if sv_ttk else "TButton"
        if step.get("wait"):
            ttk.Button(btns, text="Пропустить шаг", command=self.next).pack(side="right")
        else:
            ttk.Button(btns, text="Готово" if last else ("Начать" if i == 0 else "Далее"), style=acc,
                       command=self.finish if last else self.next).pack(side="right")
        if 0 < i:
            ttk.Button(btns, text="Назад", command=self.back).pack(side="right", padx=(0, 8))
        if not last:
            close = tk.Label(btns, text="Закрыть обучение", bg=pal["card"], fg=pal["muted"], font=a.f_small,
                             cursor="hand2")
            close.pack(side="left", pady=(6, 0))
            close.bind("<Button-1>", lambda e: self.finish())
        self._last = None
        self._layout(force=True)
        self._draw_marks()

    # --- переходы
    def event(self, name):
        step = self.steps[self.i]
        if step.get("wait") == name and (step.get("cond") is None or step["cond"]()):
            i = self.i            # переходим, только если за это время шаг не сменился
            self.app.after(400, lambda: self.alive and self.i == i and self.next())

    def back(self):
        self._no_auto = self.i - 1        # на шаг, куда вернулись, не перепрыгиваем автоматически
        self.show(self.i - 1)

    def next(self):
        if not self.alive:
            return
        if self.i + 1 < len(self.steps):
            self.show(self.i + 1)
        else:
            self.finish()

    def finish(self):
        if not self.alive:
            return
        self.alive = False
        for w in (self.box, self.an, self.ov):
            try:
                w.destroy()
            except tk.TclError:
                pass
        self.app.unbind("<Escape>")
        self.on_finish()


# ---------------------------------------------------------------- главное окно
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("DiskCleaner — анализатор диска")
        sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
        w, h = min(1280, sw - 60), min(820, sh - 90)
        self.geometry(f"{w}x{h}+{max(0, (sw - w) // 2)}+{max(0, (sh - h) // 2 - 20)}")
        self.minsize(900, 560)
        self.mode = "dark" if windows_prefers_dark() else "light"
        self.cards, self.themed_labels, self.bars, self.plain_frames = [], [], [], []
        if sv_ttk:
            sv_ttk.set_theme(self.mode)
        else:
            try:
                ttk.Style().theme_use("vista")
            except tk.TclError:
                pass
            self.mode = "light"
        self.f_title = tkfont.Font(family="Segoe UI Semibold", size=18)
        self.f_big = tkfont.Font(family="Segoe UI Semibold", size=15)
        self.f_bold = tkfont.Font(family="Segoe UI Semibold", size=10)
        self.f_norm = tkfont.Font(family="Segoe UI", size=10)
        self.f_small = tkfont.Font(family="Segoe UI", size=9)
        self.f_field = tkfont.Font(family="Segoe UI", size=11)
        self.q = queue.Queue()
        self.cancel = threading.Event()
        self.result = None
        self.worker = None
        self._build()
        self.apply_theme(self.mode)
        self.after(100, self._poll)

    # ---------- интерфейс
    # ---------- элементы оформления
    def _frame(self, master, **kw):
        f = tk.Frame(master, bd=0, **kw)
        self.plain_frames.append(f)
        return f

    def _label(self, master, text="", role="text", font=None, **kw):
        # bg_role: None — фон окна или карточки (определяется автоматически), "panel" — подложка полей
        """Метка на карточке: цвет берётся из палитры по роли (text/muted/accent/warn/ok)."""
        lb = tk.Label(master, text=text, font=font or self.f_norm, bd=0, **kw)
        lb.role = role
        self.themed_labels.append(lb)
        return lb

    def _card(self, master, padx=14, pady=10):
        outer = tk.Frame(master, bd=0, highlightthickness=1)
        inner = tk.Frame(outer, bd=0)
        inner.pack(fill="both", expand=True, padx=padx, pady=pady)
        self.cards.append((outer, inner))
        return outer, inner

    def _panel(self, master, pady=(0, 0)):
        """Подложка для полей ввода: чуть темнее фона, чтобы белые поля не сливались."""
        p = ttk.Frame(master, style="Panel.TFrame", padding=(14, 10, 14, 12))
        p.pack(fill="x", pady=pady)
        return p

    def _field(self, parent, label, widget_cls, expand=False, **kw):
        """Поле с подписью сверху. Возвращает сам виджет ввода (его .master — рамка поля)."""
        box = ttk.Frame(parent, style="Panel.TFrame")
        box.pack(side="left", padx=(0, 16), fill="x", expand=expand, anchor="s")
        cap = self._label(box, label, role="muted", font=self.f_small)
        cap.bg_role = "panel"
        cap.pack(anchor="w", pady=(0, 5))
        row = ttk.Frame(box, style="Panel.TFrame")
        row.pack(fill="x")
        w = widget_cls(row, font=self.f_field, **kw)
        w.pack(side="left", fill="x", expand=True, ipady=2)
        w.caption = cap
        return w

    def _reset_file_filters(self):
        self.filter_var.set("")
        self.age_var.set("0")
        self.exclude_var.set("")
        self.fill_files()

    def _bar(self, master, width=220, height=6):
        c = tk.Canvas(master, width=width, height=height, bd=0, highlightthickness=0)
        c.value, c.color = 0.0, "accent"
        self.bars.append(c)
        return c

    def _draw_bar(self, c):
        pal = PALETTE[self.mode]
        w, h = int(c["width"]), int(c["height"])
        c.delete("all")
        c.configure(bg=pal["card"])
        c.create_rectangle(0, 0, w, h, fill=pal["track"], outline="")
        fill = max(0, min(w, int(w * c.value)))
        if fill:
            c.create_rectangle(0, 0, fill, h, fill=pal[c.color], outline="")

    def apply_theme(self, mode):
        self.mode = mode
        if sv_ttk:
            sv_ttk.set_theme(mode)
        pal = PALETTE[mode]
        style = ttk.Style()
        base = style.lookup("TFrame", "background") or ("#fafafa" if mode == "light" else "#1c1c1c")
        self.configure(bg=base)
        style.configure("Treeview", rowheight=30, font=self.f_norm)
        style.configure("Treeview.Heading", font=self.f_bold)
        style.configure("TNotebook.Tab", font=self.f_norm, padding=(14, 6))
        style.configure("Muted.TLabel", foreground=pal["muted"])
        style.configure("Panel.TFrame", background=pal["panel"])
        style.configure("PanelMuted.TLabel", background=pal["panel"], foreground=pal["muted"], font=self.f_small)
        style.configure("Panel.TCheckbutton", background=pal["panel"])
        for st in ("TEntry", "TSpinbox", "TCombobox"):
            style.configure(st, padding=(10, 6, 10, 6))
        self.option_add("*TCombobox*Listbox.font", self.f_field)
        style.configure("Accent.TButton", font=self.f_bold)
        self._recolor()
        for t in self._all_trees():
            t.tag_configure("odd", background=pal["stripe"])
            t.tag_configure("huge", foreground=pal["warn"])
            t.tag_configure("big", foreground=pal["orange"])
            t.tag_configure("group", font=self.f_bold)
            t.tag_configure("critical", foreground=pal["warn"], font=self.f_bold)
        if hasattr(self, "theme_btn"):
            self.theme_btn.configure(text="☀  Светлая тема" if mode == "dark" else "☾  Тёмная тема")
        self._dark_titlebar(mode == "dark")

    def _recolor(self):
        """Перекрашивает «ручные» элементы (карточки, метки, полоски) под текущую палитру."""
        pal = PALETTE[self.mode]
        base = ttk.Style().lookup("TFrame", "background") or ("#fafafa" if self.mode == "light" else "#1c1c1c")
        alive = lambda w: w.winfo_exists()
        self.plain_frames = [f for f in self.plain_frames if alive(f)]
        self.cards = [c for c in self.cards if alive(c[0])]
        self.themed_labels = [l for l in self.themed_labels if alive(l)]
        self.bars = [b for b in self.bars if alive(b)]
        for f in self.plain_frames:
            f.configure(bg=base)
        for c in getattr(self, "plain_canvases", []):
            c.configure(bg=base)
        inners = set()

        def paint(w):
            for ch in w.winfo_children():
                if isinstance(ch, tk.Frame):
                    ch.configure(bg=pal["card"])
                    paint(ch)
        for outer, inner in self.cards:
            outer.configure(bg=pal["card"], highlightbackground=pal["border"], highlightcolor=pal["border"])
            inner.configure(bg=pal["card"])
            paint(inner)
            inners.add(str(inner))

        def on_card(w):
            p = w.master
            while p is not None:
                if str(p) in inners:
                    return True
                p = p.master
            return False
        for lb in self.themed_labels:
            if getattr(lb, "pill", False):
                lb.configure(bg=pal[lb.role], fg=pal["card"])
                continue
            if getattr(lb, "bg_role", None) == "panel":
                bg = pal["panel"]
            elif on_card(lb):
                bg = pal["card"]
            else:
                bg = base
            lb.configure(bg=bg, fg=pal[lb.role])
        for c in self.bars:
            self._draw_bar(c)

    def ask_disclaimer(self):
        """Окно ответственности при первом запуске. Возвращает True, если пользователь согласился."""
        settings = load_settings()
        if settings.get("accepted_disclaimer") == APP_VERSION:
            return True
        pal = PALETTE[self.mode]
        dlg = tk.Toplevel(self)
        dlg.title("Прежде чем начать")
        dlg.resizable(False, False)
        dlg.transient(self)
        base = ttk.Style().lookup("TFrame", "background") or pal["card"]
        dlg.configure(bg=base)
        body = ttk.Frame(dlg, padding=(28, 24, 28, 20))
        body.pack(fill="both", expand=True)
        tk.Label(body, text="⚠  Вы отвечаете за то, что удаляете", font=self.f_big, bg=base,
                 fg=pal["orange"]).pack(anchor="w")
        tk.Label(body, text=DISCLAIMER, font=self.f_norm, bg=base, fg=pal["text"], justify="left",
                 wraplength=560).pack(anchor="w", pady=(14, 16))
        agree = tk.BooleanVar(value=False)
        result = {"ok": False}
        btns = ttk.Frame(body)
        btns.pack(fill="x", side="bottom")
        ok_btn = ttk.Button(btns, text="Продолжить", state="disabled",
                            style="Accent.TButton" if sv_ttk else "TButton", width=16)
        ok_btn.pack(side="right")
        ttk.Button(btns, text="Выйти", width=12, command=dlg.destroy).pack(side="right", padx=(0, 8))
        ttk.Checkbutton(body, text="Я прочитал(а), понимаю риски и принимаю ответственность", variable=agree,
                        command=lambda: ok_btn.configure(state="normal" if agree.get() else "disabled")
                        ).pack(anchor="w", pady=(0, 18))

        def accept():
            result["ok"] = True
            settings["accepted_disclaimer"] = APP_VERSION
            save_settings(settings)
            dlg.destroy()

        ok_btn.configure(command=accept)
        dlg.protocol("WM_DELETE_WINDOW", dlg.destroy)
        dlg.update_idletasks()
        x = self.winfo_rootx() + (self.winfo_width() - dlg.winfo_width()) // 2
        y = self.winfo_rooty() + max(40, (self.winfo_height() - dlg.winfo_height()) // 3)
        dlg.geometry(f"+{max(0, x)}+{max(0, y)}")
        dlg.grab_set()
        dlg.focus_force()
        self.wait_window(dlg)
        return result["ok"]

    def show_disclaimer(self):
        messagebox.showinfo("Ответственность", DISCLAIMER, parent=self)

    def _all_trees(self):
        return [w for w in (getattr(self, n, None) for n in ("dirtree", "duptree")) if w] + \
               [t.tree for t in (getattr(self, n, None) for n in ("t_files", "t_dirs", "t_junk", "t_types")) if t]

    def toggle_theme(self):
        self.apply_theme("light" if self.mode == "dark" else "dark")

    def _dark_titlebar(self, dark):
        if not IS_WIN:
            return
        try:
            import ctypes
            self.update_idletasks()
            hwnd = ctypes.windll.user32.GetParent(self.winfo_id())
            val = ctypes.c_int(1 if dark else 0)
            for attr in (20, 19):   # DWMWA_USE_IMMERSIVE_DARK_MODE (Win10 20H1+ / старые сборки)
                if ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, attr, ctypes.byref(val), ctypes.sizeof(val)) == 0:
                    break
            # Windows перерисовывает рамку только при изменении окна — «пошевелим» его на пиксель
            w, h = self.winfo_width(), self.winfo_height()
            if w > 1:
                self.geometry(f"{w + 1}x{h}")
                self.update_idletasks()
                self.geometry(f"{w}x{h}")
        except Exception:
            pass

    # ---------- интерфейс
    def _build(self):
        root = self._frame(self)
        root.pack(fill="both", expand=True, padx=18, pady=(14, 0))

        # шапка
        head = self._frame(root)
        head.pack(fill="x")
        self._label(head, "DiskCleaner", font=self.f_title).pack(side="left")
        self._label(head, "  анализатор диска", role="muted").pack(side="left", pady=(8, 0))
        self.theme_btn = ttk.Button(head, text="", command=self.toggle_theme, width=16)
        self.theme_btn.pack(side="right")
        ttk.Button(head, text="⭳  Экспорт в CSV", command=self.export_csv).pack(side="right", padx=8)

        # карточки дисков — в той же строке, что и заголовок (экономим высоту)
        self.tour = None
        self.health_refs = []
        self.tour_btn = ttk.Button(head, text="?  Обучение", command=self.start_tour)
        self.tour_btn.pack(side="right", padx=(0, 8))
        drives_row = self._frame(head)
        self.drives_row = drives_row
        drives_row.pack(side="right", padx=(0, 16))
        self.drive_cards, self.drive_health_lbl = {}, {}
        for d in list_drives():
            try:
                du = shutil.disk_usage(d)
            except OSError:
                continue
            outer, inner = self._card(drives_row, padx=12, pady=7)
            outer.pack(side="left", padx=(10, 0))
            kind = drive_kind(d) or "диск"
            top_line = tk.Frame(inner, bd=0)
            top_line.pack(fill="x")
            self._label(top_line, f"🖴  {d.rstrip(chr(92))}", font=self.f_bold).pack(side="left")
            self._label(top_line, f"  {kind}", role="accent", font=self.f_small).pack(side="left")
            bar = self._bar(inner, width=190, height=5)
            bar.value = du.used / du.total if du.total else 0
            bar.color = "warn" if bar.value > 0.9 else "accent"
            bar.pack(fill="x", pady=(5, 4))
            self._label(inner, f"свободно {human(du.free)} из {human(du.total)}", role="muted",
                        font=self.f_small).pack(anchor="w")
            for w in [outer, inner, top_line, bar] + list(inner.winfo_children()) + list(top_line.winfo_children()):
                w.bind("<Button-1>", lambda e, d=d: self.path_var.set(d))
                w.configure(cursor="hand2")
            self.drive_cards[d] = outer
            hl = self._label(top_line, "", role="muted", font=self.f_small)
            hl.pack(side="right")
            self.drive_health_lbl[d.rstrip("\\")] = hl

        # строка запуска: что сканируем + кнопки (вместо панели полей и карточек итогов)
        bar = self._frame(root)
        bar.pack(fill="x", pady=(12, 12))
        self.scan_bar = bar
        self.stop_btn = ttk.Button(bar, text="■  Стоп", command=self.cancel.set, state="disabled")
        self.stop_btn.pack(side="right", ipady=3)
        self.scan_btn = ttk.Button(bar, text="▶   Сканировать", command=self.start_scan,
                                   style="Accent.TButton" if sv_ttk else "TButton", width=18)
        self.scan_btn.pack(side="right", padx=8, ipady=3)
        self.settings_btn = ttk.Button(bar, text="⚙  Настройки", command=self.show_settings)
        self.settings_btn.pack(side="right", ipady=3)
        self.folder_btn = ttk.Button(bar, text="📁  Выбрать папку…", command=self._browse)
        self.folder_btn.pack(side="left", ipady=3)
        self.path_var = tk.StringVar(value=list_drives()[0])
        self.min_var = tk.StringVar(value="50")
        self.workers_var = tk.StringVar(value=str(default_workers()))
        self._label(bar, "   Сканируем:", role="muted").pack(side="left")
        self.path_label = self._label(bar, "", font=self.f_bold, cursor="hand2")
        self.path_label.pack(side="left", padx=(6, 0))
        self.path_label.bind("<Button-1>", lambda e: self._browse())
        self.drive_label = self._label(bar, "", role="muted", font=self.f_small)
        self.drive_label.pack(side="left", padx=(10, 0), pady=(3, 0))
        self.path_var.trace_add("write", lambda *a: self.path_label.configure(text=self._short_path(self.path_var.get())))
        self.path_label.configure(text=self._short_path(self.path_var.get()))
        self.path_var.trace_add("write", lambda *a: self.after_idle(self._auto_workers))
        self.path_var.trace_add("write", lambda *a: self._tour_event("path"))
        self.after_idle(self._auto_workers)

        self.nb = ttk.Notebook(root)
        self.nb.bind("<<NotebookTabChanged>>", lambda e: self._tour_event("tab"))
        self.nb.pack(fill="both", expand=True)

        # Вкладка: большие файлы
        f1 = ttk.Frame(self.nb, padding=(12, 12, 12, 0))
        flt = self._panel(f1, pady=(0, 6))
        fb = ttk.Frame(flt, style="Panel.TFrame")
        fb.pack(side="right", anchor="s")
        ttk.Button(fb, text="Применить", command=self.fill_files, style="Accent.TButton" if sv_ttk else "TButton").pack(side="left", ipady=2)
        ttk.Button(fb, text="Сбросить", command=self._reset_file_filters).pack(side="left", padx=(8, 0), ipady=2)
        self.filter_var = tk.StringVar()
        e_f = self._field(flt, "Поиск по имени или пути", ttk.Entry, textvariable=self.filter_var, width=26)
        self.age_var = tk.StringVar(value="0")
        e_a = self._field(flt, "Не изменялись, дней", ttk.Spinbox, from_=0, to=10000, increment=30,
                          textvariable=self.age_var, width=7)
        self.exclude_var = tk.StringVar()
        ex = self._field(flt, "Скрыть папки через запятую (например: Fortnite, Windows)", ttk.Entry, expand=True,
                         textvariable=self.exclude_var, width=30)
        for w in (e_f, e_a, ex):
            w.bind("<Return>", lambda e: self.fill_files())
        self.files_info = ttk.Label(f1, text="", style="Muted.TLabel")
        self.files_info.pack(anchor="w", pady=(0, 6))
        self.t_files = Table(f1, [("size", "Размер", 90, "size"), ("name", "Имя", 260, "text"),
                                  ("ext", "Тип", 70, "text"), ("date", "Изменён", 120, "date"),
                                  ("dir", "Папка", 420, "text"), ("note", "Примечание", 260, "text")],
                             path_col=6, note_col=5)
        self.t_files.pack(fill="both", expand=True)
        self.nb.add(f1, text="  Большие файлы  ")

        # Вкладка: дерево папок
        f2 = ttk.Frame(self.nb, padding=(12, 12, 12, 0))
        bar2 = self._panel(f2, pady=(0, 6))
        self.dirs_panel = bar2
        db = ttk.Frame(bar2, style="Panel.TFrame")
        db.pack(side="right", anchor="s")
        ttk.Button(db, text="Показать списком", command=self.fill_dir_list, style="Accent.TButton" if sv_ttk else "TButton").pack(side="left", ipady=2)
        ttk.Button(db, text="Дерево", command=self.show_dir_tree).pack(side="left", padx=(8, 0), ipady=2)
        self.dir_search_var = tk.StringVar()
        e1 = self._field(bar2, "Найти папку по имени", ttk.Entry, textvariable=self.dir_search_var, width=20)
        self.dir_depth_var = tk.StringVar(value="любая")
        self._field(bar2, "Вложенность", ttk.Combobox, textvariable=self.dir_depth_var, width=8, state="readonly",
                    values=["любая", "1", "2", "3", "4", "5", "6"])
        self.dir_min_var = tk.StringVar(value="100")
        e2 = self._field(bar2, "От, МБ", ttk.Spinbox, from_=0, to=1000000, increment=100,
                         textvariable=self.dir_min_var, width=8)
        self.dir_exclude_var = tk.StringVar()
        e3 = self._field(bar2, "Скрыть папки", ttk.Entry, expand=True, textvariable=self.dir_exclude_var, width=14)
        self.dir_top_only = tk.BooleanVar(value=True)
        ttk.Checkbutton(bar2, text="без вложенных повторов", variable=self.dir_top_only,
                        style="Panel.TCheckbutton").pack(side="left", anchor="s", pady=(0, 6), padx=(0, 12))
        for w in (e1, e2, e3):
            w.bind("<Return>", lambda e: self.fill_dir_list())
        self.dir_info = ttk.Label(f2, text="Дерево: раскрывайте папки. «Показать списком» — плоский перечень папок "
                                           "по фильтру, от самых тяжёлых.", style="Muted.TLabel")
        self.dir_info.pack(anchor="w", pady=(0, 6))
        self.t_dirs = Table(f2, [("size", "Размер", 100, "size"), ("pct", "Доля", 190, "pct"),
                                 ("files", "Файлов", 90, "int"), ("name", "Папка", 220, "text"),
                                 ("path", "Полный путь", 600, "text")], path_col=4)
        self.dirtree_frame = ttk.Frame(f2)
        self.dirtree_frame.pack(fill="both", expand=True)
        f2_tree = self.dirtree_frame
        self.dirtree = ttk.Treeview(f2_tree, columns=("size", "pct", "files"), selectmode="extended")
        self.dirtree.heading("#0", text="Папка")
        self.dirtree.heading("size", text="Размер")
        self.dirtree.heading("pct", text="% от родителя")
        self.dirtree.heading("files", text="Файлов")
        self.dirtree.column("#0", width=560)
        for c, w in (("size", 100), ("pct", 200), ("files", 100)):
            self.dirtree.column(c, width=w, anchor="w" if c == "pct" else "e", stretch=False)
        ys = ttk.Scrollbar(f2_tree, orient="vertical", command=self.dirtree.yview)
        self.dirtree.configure(yscrollcommand=ys.set)
        self.dirtree.pack(side="left", fill="both", expand=True)
        ys.pack(side="right", fill="y")
        self.dirtree.bind("<<TreeviewOpen>>", self._tree_open)
        self.nb.add(f2, text="  Папки  ")

        # Вкладка: мусор
        f3 = ttk.Frame(self.nb, padding=(12, 12, 12, 0))
        bar3 = ttk.Frame(f3, padding=(0, 0, 0, 8))
        bar3.pack(fill="x")
        self.junk_info = ttk.Label(bar3, text="Кандидаты на удаление. Проверяйте перед удалением!")
        self.junk_info.pack(side="left")
        self.t_junk = Table(f3, [("cat", "Категория", 170, "text"), ("size", "Размер", 90, "size"),
                                 ("kind", "Что", 60, "text"), ("path", "Путь", 700, "text")], path_col=3)
        self.t_junk.pack(fill="both", expand=True)
        self.nb.add(f3, text="  Мусор  ")

        # Вкладка: дубликаты
        f4 = ttk.Frame(self.nb, padding=(12, 12, 12, 0))
        bar4 = ttk.Frame(f4, padding=(0, 0, 0, 8))
        bar4.pack(fill="x")
        self.dup_btn = ttk.Button(bar4, text="Найти дубликаты среди больших файлов", command=self.start_dups,
                                  style="Accent.TButton" if sv_ttk else "TButton")
        self.dup_btn.pack(side="left")
        self.dup_info = ttk.Label(bar4, text="  Сравнение по содержимому (хэш), имена не важны.")
        self.dup_info.pack(side="left")
        self.duptree = ttk.Treeview(f4, columns=("size", "date"), selectmode="extended")
        self.duptree.heading("#0", text="Группа / файл")
        self.duptree.heading("size", text="Размер")
        self.duptree.heading("date", text="Изменён")
        self.duptree.column("#0", width=800)
        self.duptree.column("size", width=100, anchor="e", stretch=False)
        self.duptree.column("date", width=130, stretch=False)
        ys4 = ttk.Scrollbar(f4, orient="vertical", command=self.duptree.yview)
        self.duptree.configure(yscrollcommand=ys4.set)
        self.duptree.pack(side="left", fill="both", expand=True)
        ys4.pack(side="right", fill="y")
        self.nb.add(f4, text="  Дубликаты  ")

        # Вкладка: типы файлов
        f5 = ttk.Frame(self.nb, padding=(12, 12, 12, 12))
        self.t_types = Table(f5, [("ext", "Расширение", 160, "text"), ("count", "Файлов", 100, "int"),
                                  ("size", "Общий размер", 120, "size"), ("pct", "Доля", 190, "pct")], path_col=0)
        self.t_types.pack(fill="both", expand=True)
        self.nb.add(f5, text="  Типы файлов  ")

        # Вкладка: здоровье дисков
        f6 = ttk.Frame(self.nb, padding=(12, 12, 12, 0))
        bar6 = self._panel(f6, pady=(0, 8))
        ttk.Button(bar6, text="Обновить", command=lambda: self.start_health(alert=False),
                   style="Accent.TButton" if sv_ttk else "TButton").pack(side="left", ipady=2)
        if IS_WIN and not is_admin():
            ttk.Button(bar6, text="🛡  Перезапустить от администратора",
                       command=self.restart_as_admin).pack(side="left", padx=(8, 0), ipady=2)
        hint = self._label(bar6, "SMART читается без прав администратора. Прогноз ресурса приблизительный, "
                                 "а исправный SMART не гарантирует, что диск не откажет — делайте резервные копии.",
                           role="muted", font=self.f_small, wraplength=620, justify="left")
        hint.bg_role = "panel"
        hint.pack(side="left", padx=14)
        wrap = self._frame(f6)
        wrap.pack(fill="both", expand=True)
        self.h_canvas = tk.Canvas(wrap, bd=0, highlightthickness=0)
        self.plain_canvases = [self.h_canvas]
        hsb = ttk.Scrollbar(wrap, orient="vertical", command=self.h_canvas.yview)
        self.h_canvas.configure(yscrollcommand=hsb.set)
        hsb.pack(side="right", fill="y")
        self.h_canvas.pack(side="left", fill="both", expand=True)
        self.h_inner = self._frame(self.h_canvas)
        self.h_win = self.h_canvas.create_window(0, 0, window=self.h_inner, anchor="nw")
        self.h_inner.bind("<Configure>", lambda e: self.h_canvas.configure(scrollregion=self.h_canvas.bbox("all")))
        self.h_canvas.bind("<Configure>", lambda e: self.h_canvas.itemconfigure(self.h_win, width=e.width - 4))
        wheel = lambda e: self.h_canvas.yview_scroll(int(-e.delta / 120), "units")
        self.h_canvas.bind("<Enter>", lambda e: self.h_canvas.bind_all("<MouseWheel>", wheel))
        self.h_canvas.bind("<Leave>", lambda e: self.h_canvas.unbind_all("<MouseWheel>"))
        self._label(self.h_inner, "Проверяю диски…", role="muted").pack(anchor="w")
        self.health_tab = f6
        self.nb.add(f6, text="  Здоровье дисков  ")

        # строка состояния
        bottom = self._frame(root)
        self.bottom_bar = bottom
        bottom.pack(side="bottom", fill="x", pady=10, before=self.nb)
        self.progress = ttk.Progressbar(bottom, mode="indeterminate", length=220)
        self.progress.pack(side="left")
        self.status = ttk.Label(bottom, text="Выберите диск (можно щёлкнуть по карточке) и нажмите «Сканировать».",
                                style="Muted.TLabel")
        self.status.pack(side="left", padx=10)
        note = ttk.Label(bottom, text="ⓘ  Вы отвечаете за удаление", style="Muted.TLabel",
                         cursor="hand2")
        note.pack(side="right", before=self.status)   # пометка важнее — длинный статус обрежется, а не она
        note.bind("<Button-1>", lambda e: self.show_disclaimer())

        # контекстное меню
        self.menu = tk.Menu(self, tearoff=0)
        self.menu.add_command(label="Показать в Проводнике", command=self.reveal)
        self.menu.add_command(label="Открыть", command=self.open_item)
        self.menu.add_command(label="Копировать путь", command=self.copy_path)
        self.menu.add_command(label="Что это за файл? Можно ли удалять?", command=self.explain_item)
        self.menu.add_separator()
        self.menu.add_command(label="Показать размер папки (в дереве)", command=self.show_in_tree)
        self.menu.add_command(label="Скрыть эту папку из списка…", command=self.hide_folder)
        self.menu.add_separator()
        self.menu.add_command(label="Удалить в Корзину…", command=self.delete_selected)
        for w in (self.t_files.tree, self.t_junk.tree, self.dirtree, self.duptree, self.t_dirs.tree):
            w.bind("<Button-3>", self._popup)
            w.bind("<Double-1>", lambda e: self.reveal())
            w.bind("<Delete>", lambda e: self.delete_selected())

    def _auto_workers(self):
        """Подбирает число процессов под тип диска выбранной папки."""
        path = self.path_var.get().strip()
        if not path or not os.path.splitdrive(path)[0] and IS_WIN:
            return
        drive = os.path.splitdrive(os.path.abspath(path))[0].upper()
        if getattr(self, "_last_drive", None) == drive:
            return                       # тот же диск — не трогаем ручную настройку
        self._last_drive = drive
        kind, n = workers_for(path)
        self.workers_var.set(str(n))
        cores = os.cpu_count() or 0
        if kind in ("HDD", "USB"):
            note = f"{kind}, медленный"
        elif kind == "SSD":
            note = "SSD"
        elif kind == "Сеть":
            note = "сетевой диск"
        else:
            note = "диск ?"
        self.drive_label.config(text=f"{note} · {n} проц.")

    @staticmethod
    def _short_path(p, limit=60):
        return p if len(p) <= limit else p[:20] + " … " + p[-(limit - 23):]

    def show_settings(self):
        """Маленькое окно настроек поиска (раньше эти поля занимали целую панель)."""
        pal = PALETTE[self.mode]
        win = tk.Toplevel(self)
        win.title("Настройки поиска")
        win.resizable(False, False)
        win.transient(self)
        base = ttk.Style().lookup("TFrame", "background") or pal["card"]
        win.configure(bg=base)
        body = ttk.Frame(win, padding=(22, 18, 22, 16))
        body.pack(fill="both", expand=True)
        tk.Label(body, text="Настройки поиска", font=self.f_big, bg=base, fg=pal["text"]).grid(
            row=0, column=0, columnspan=2, sticky="w", pady=(0, 12))
        tk.Label(body, text="Большие файлы — от, МБ", font=self.f_norm, bg=base, fg=pal["text"]).grid(
            row=1, column=0, sticky="w", pady=6)
        ttk.Spinbox(body, from_=1, to=100000, increment=10, textvariable=self.min_var, width=8,
                    font=self.f_field).grid(row=1, column=1, sticky="e", padx=(16, 0))
        tk.Label(body, text="Файлы меньше этого размера не попадут в список «Большие файлы».", font=self.f_small,
                 bg=base, fg=pal["muted"], wraplength=360, justify="left").grid(row=2, column=0, columnspan=2,
                                                                               sticky="w")
        tk.Label(body, text="Процессов", font=self.f_norm, bg=base, fg=pal["text"]).grid(
            row=3, column=0, sticky="w", pady=(14, 6))
        ttk.Spinbox(body, from_=1, to=64, textvariable=self.workers_var, width=8, font=self.f_field).grid(
            row=3, column=1, sticky="e", padx=(16, 0), pady=(14, 6))
        tk.Label(body, text="Подбирается само по типу диска: SSD — по числу ядер, HDD и флешки — 2.",
                 font=self.f_small, bg=base, fg=pal["muted"], wraplength=360, justify="left").grid(
            row=4, column=0, columnspan=2, sticky="w")

        def done():
            self.drive_label.config(text=self.drive_label.cget("text").split(" · ")[0] + f" · {self._workers()} проц.")
            win.destroy()
        ttk.Button(body, text="Готово", command=done, style="Accent.TButton" if sv_ttk else "TButton").grid(
            row=5, column=1, sticky="e", pady=(18, 0))
        win.bind("<Return>", lambda e: done())
        win.update_idletasks()
        bx, by = self.settings_btn.winfo_rootx(), self.settings_btn.winfo_rooty() + self.settings_btn.winfo_height() + 6
        win.geometry(f"+{max(0, bx - win.winfo_width() + self.settings_btn.winfo_width())}+{by}")
        win.grab_set()
        win.focus_force()

    def _browse(self):
        d = filedialog.askdirectory()
        if d:
            self.path_var.set(os.path.normpath(d))

    # ---------- сканирование
    def start_scan(self):
        root = self.path_var.get().strip()
        if not os.path.isdir(root):
            messagebox.showerror("Ошибка", f"Папка не найдена:\n{root}")
            return
        try:
            min_mb = float(self.min_var.get().replace(",", "."))
        except ValueError:
            min_mb = 50
        self.cancel.clear()
        self.scan_btn.config(state="disabled")
        self.dup_btn.config(state="disabled")
        self.stop_btn.config(state="normal")
        self.progress.start(12)
        self.worker = threading.Thread(target=scan, args=(root, int(min_mb * 1024 * 1024), self.q, self.cancel, self._workers()),
                                       daemon=True)
        self.worker.start()
        self._tour_event("scan_start")

    def _workers(self):
        try:
            return max(1, min(64, int(self.workers_var.get())))
        except ValueError:
            return default_workers()

    def start_dups(self):
        if not self.result or not self.result.big_files:
            messagebox.showinfo("Дубликаты", "Сначала выполните сканирование.")
            return
        self.cancel.clear()
        self.dup_btn.config(state="disabled")
        self.scan_btn.config(state="disabled")
        self.stop_btn.config(state="normal")
        self.progress.config(mode="determinate", value=0)
        self.worker = threading.Thread(target=find_duplicates, args=(self.result.big_files, self.q, self.cancel, self._workers()),
                                       daemon=True)
        self.worker.start()

    def _poll(self):
        try:
            while True:
                msg = self.q.get_nowait()
                kind = msg[0]
                if kind == "progress":
                    _, n, total, path = msg
                    self.status.config(text=f"Файлов: {n:,}  •  {human(total)}  •  {path[-90:]}".replace(",", " "))
                elif kind == "done":
                    self._scan_done(msg[1])
                elif kind == "dupprogress":
                    _, done, total, path = msg
                    self.progress.config(maximum=max(total, 1), value=done)
                    self.status.config(text=f"Проверка дубликатов {done}/{total}: {path[-90:]}")
                elif kind == "dupdone":
                    self._dups_done(msg[1])
                elif kind == "health":
                    self._health_done(msg[1], msg[2])
        except queue.Empty:
            pass
        self.after(100, self._poll)

    def _finish_ui(self):
        self.progress.stop()
        self.progress.config(mode="indeterminate", value=0)
        self.scan_btn.config(state="normal")
        self.dup_btn.config(state="normal")
        self.stop_btn.config(state="disabled")

    def _scan_done(self, r):
        self._finish_ui()
        self.result = r
        self.after(300, lambda: self._tour_event("scan_done"))
        note = "  (остановлено — результаты неполные)" if r.cancelled else ""
        self.fill_files()
        self.fill_tree()
        self.show_dir_tree()
        junk_rows = [(c, s, "папка" if d else "файл", p) for c, s, p, d in r.junk]
        junk_rows.sort(key=lambda x: x[1], reverse=True)
        self.t_junk.set_rows(junk_rows)
        self.junk_info.config(text=f"Найдено кандидатов: {len(junk_rows)}, всего {human(sum(x[1] for x in junk_rows))}. "
                                   f"Проверяйте перед удалением!")
        tot = r.total or 1
        types = [(e, c, s, s * 100 / tot) for e, (c, s) in r.ext_stats.items()]
        types.sort(key=lambda x: x[2], reverse=True)
        self.t_types.set_rows(types)
        self.duptree.delete(*self.duptree.get_children())
        junk_total = sum(x[1] for x in junk_rows)
        big_total = sum(f[0] for f in r.big_files)
        num = lambda n: f"{n:,}".replace(",", " ")
        errs = f"  ·  нет доступа: {num(r.errors)}" if r.errors else ""
        self.status.config(text=f"✓  Занято {human(r.total)}  ·  {num(r.files)} файлов  ·  "
                                f"больших {num(len(r.big_files))} ({human(big_total)})  ·  "
                                f"мусор {human(junk_total)}  ·  {r.seconds:.1f} с{errs}{note}")

    def fill_files(self):
        if not self.result:
            return
        text = self.filter_var.get().strip().lower()
        try:
            age = int(self.age_var.get())
        except ValueError:
            age = 0
        limit_ts = time.time() - age * 86400
        excl = self._split(self.exclude_var.get())
        rows = []
        for sz, p, mt in self.result.big_files:
            pl = p.lower()
            if text and text not in pl:
                continue
            if excl and any(x in pl for x in excl):
                continue
            if age and mt > limit_ts:
                continue
            name = os.path.basename(p)
            crit = critical_info(p)
            note = f"⛔ {crit[0]} — удалять нельзя" if crit else ""
            rows.append((sz, ("🔒 " + name) if crit else name, os.path.splitext(name)[1].lower(), mt,
                         os.path.dirname(p), note, p))
        self.t_files.set_rows(rows)
        shown = min(len(rows), 5000)
        self.files_info.config(text=f"Файлов: {len(rows)} (показано {shown}), всего {human(sum(r[0] for r in rows))}")

    @staticmethod
    def _split(s):
        return [x.strip().lower() for x in s.replace(";", ",").split(",") if x.strip()]

    # ---------- плоский список папок
    def fill_dir_list(self):
        r = self.result
        if not r:
            return
        text = self.dir_search_var.get().strip().lower()
        excl = self._split(self.dir_exclude_var.get())
        depth_s = self.dir_depth_var.get()
        depth = int(depth_s) if depth_s.isdigit() else None
        try:
            min_size = float(self.dir_min_var.get().replace(",", ".")) * 1024 * 1024
        except ValueError:
            min_size = 0
        root_depth = r.root.rstrip("\\/").count(os.sep)
        total = r.dir_total.get(r.root, 0) or 1

        def ok(p):
            if p == r.root or r.dir_total.get(p, 0) < min_size:
                return False
            pl = p.lower()
            if excl and any(x in pl for x in excl):
                return False
            if text and text not in os.path.basename(p).lower():
                return False
            if depth is not None and p.count(os.sep) - root_depth != depth:
                return False
            return True

        matched = {p for p in r.dir_total if ok(p)}
        if self.dir_top_only.get() and depth is None:
            def has_matched_ancestor(p):
                a = r.parent.get(p)
                while a is not None:
                    if a in matched:
                        return True
                    a = r.parent.get(a)
                return False
            matched = {p for p in matched if not has_matched_ancestor(p)}
        rows = [(r.dir_total[p], r.dir_total[p] * 100 / total, r.dir_files.get(p, 0),
                 os.path.basename(p) or p, p) for p in matched]
        rows.sort(reverse=True)
        self.dirtree_frame.pack_forget()
        self.t_dirs.pack(fill="both", expand=True)
        self.t_dirs.set_rows(rows, limit=3000)
        self.dir_info.config(text=f"Папок найдено: {len(rows)}"
                                  + (f" (показано 3000)" if len(rows) > 3000 else "")
                                  + f", вместе {human(sum(x[0] for x in rows))}"
                                  + ("" if not self.dir_top_only.get() or depth else
                                     " — вложенные в найденные папки не повторяются"))

    def show_dir_tree(self):
        self.t_dirs.pack_forget()
        self.dirtree_frame.pack(fill="both", expand=True)
        self.dir_info.config(text="Дерево: раскрывайте папки. «Показать списком» — плоский перечень папок "
                                  "по фильтру, от самых тяжёлых.")

    def show_in_tree(self):
        r = self.result
        paths = self.selected_paths()
        if not r or not paths:
            return
        p = paths[0]
        if p not in r.dir_total:
            p = os.path.dirname(p)
        chain = []
        while p is not None and p in r.dir_total:
            chain.append(p)
            p = r.parent.get(p)
        chain.reverse()
        self.show_dir_tree()
        self.nb.select(1)
        for node in chain[1:]:
            par = r.parent[node]
            kids = self.dirtree.get_children(par)
            if len(kids) == 1 and kids[0].endswith("|dummy"):
                self._populate(par)
            self.dirtree.item(par, open=True)
        target = chain[-1]
        if self.dirtree.exists(target):
            self.dirtree.selection_set(target)
            self.dirtree.focus(target)
            self.dirtree.see(target)

    def hide_folder(self):
        paths = self.selected_paths()
        if not paths:
            return
        p = paths[0]
        folder = p if (self.result and p in self.result.dir_total) else os.path.dirname(p)
        from tkinter import simpledialog
        val = simpledialog.askstring("Скрыть папку",
                                     "Скрыть всё, что лежит в папке (можно укоротить, например до имени игры):",
                                     initialvalue=folder, parent=self)
        if not val:
            return
        cur = self._split(self.exclude_var.get())
        cur.append(val.strip())
        self.exclude_var.set(", ".join(cur))
        self.dir_exclude_var.set(", ".join(self._split(self.dir_exclude_var.get()) + [val.strip()]))
        self.fill_files()
        if self.t_dirs.winfo_ismapped():
            self.fill_dir_list()

    # ---------- дерево папок
    def fill_tree(self):
        t = self.dirtree
        t.delete(*t.get_children())
        r = self.result
        root = r.root
        t.insert("", "end", iid=root, text="  " + root, open=True, tags=("group",),
                 values=(human(r.dir_total.get(root, 0)), pct_bar(100),
                         f"{r.dir_files.get(root, 0):,}".replace(",", " ")))
        self._populate(root)

    def _populate(self, parent):
        r = self.result
        t = self.dirtree
        for ch in t.get_children(parent):
            t.delete(ch)
        ptotal = r.dir_total.get(parent, 0) or 1
        kids = sorted(r.children.get(parent, []), key=lambda p: r.dir_total.get(p, 0), reverse=True)
        for i, p in enumerate(kids):
            size = r.dir_total.get(p, 0)
            crit = critical_info(p)
            t.insert(parent, "end", iid=p, text=("🔒 " if crit else "📁 ") + (os.path.basename(p) or p),
                     tags=("odd" if i % 2 else "even", size_tag(size)) + (("critical",) if crit else ()),
                     values=(human(size), pct_bar(size * 100 / ptotal), f"{r.dir_files.get(p, 0):,}".replace(",", " ")))
            if r.children.get(p):
                t.insert(p, "end", iid=p + "|dummy", text="…")

    def _tree_open(self, _event):
        node = self.dirtree.focus()
        kids = self.dirtree.get_children(node)
        if len(kids) == 1 and kids[0].endswith("|dummy"):
            self._populate(node)

    # ---------- здоровье дисков
    def start_health(self, alert=False):
        def work():
            try:
                disks = read_disks_health()
            except Exception:
                disks = []
            self.q.put(("health", disks, alert))
        threading.Thread(target=work, daemon=True).start()

    def restart_as_admin(self):
        import ctypes
        if getattr(sys, "frozen", False):
            exe, params = sys.executable, ""
        else:
            exe = sys.executable
            w = os.path.join(os.path.dirname(exe), "pythonw.exe")
            exe = w if os.path.exists(w) else exe
            params = f'"{os.path.abspath(sys.argv[0])}"'
        if ctypes.windll.shell32.ShellExecuteW(None, "runas", exe, params, None, 1) > 32:
            self.destroy()

    def _health_done(self, disks, alert):
        self.health = disks
        for w in self.h_inner.winfo_children():
            w.destroy()
        if not disks:
            self._label(self.h_inner, "Не удалось получить данные о дисках.", role="muted").pack(anchor="w")
        self.health_refs = []
        for d in disks:
            self._health_card(d)
        problems = [d for d in disks if d["level"] in ("warn", "bad")]
        self.nb.tab(self.health_tab, text="  ⚠ Здоровье дисков  " if problems else "  Здоровье дисков  ")
        dot = {"good": ("ok", "● исправен"), "warn": ("orange", "● внимание"), "bad": ("warn", "● плохо"),
               "unknown": ("muted", "")}
        for d in disks:
            for letter in d["letters"]:
                lb = self.drive_health_lbl.get(letter)
                if lb is not None:
                    lb.role, text = dot[d["level"]]
                    lb.configure(text=text)
        self._recolor()
        if alert and problems:
            if self.tour is not None:
                self._pending_health_alert = problems      # покажем после обучения
                return
            self._show_health_alert(problems)

    def _show_health_alert(self, problems):
        if True:
            worst = any(d["level"] == "bad" for d in problems)
            parts = []
            for d in problems:
                where = ", ".join(d["letters"]) or "без буквы"
                head = f"• {d['model']} ({where}) — {'ПЛОХО' if d['level'] == 'bad' else 'внимание'}"
                parts.append(head + "".join(f"\n     {t}" for _, t in d["problems"][:3]))
            msg = ("С дисками есть проблемы:\n\n" + "\n\n".join(parts) +
                   "\n\nСделайте резервную копию важных данных как можно скорее. "
                   "Подробности — на вкладке «Здоровье дисков».")
            (messagebox.showerror if worst else messagebox.showwarning)("Проверьте диски", msg, parent=self)
            self.nb.select(self.health_tab)

    # ---------- обучение
    def _tour_event(self, name):
        if self.tour is not None:
            self.tour.event(name)

    def _tab_rect(self, index=None):
        """Прямоугольник полосы вкладок или одной вкладки (в экранных координатах)."""
        nb = self.nb
        x0, y0 = nb.winfo_rootx(), nb.winfo_rooty()
        pane = nb.nametowidget(nb.select())
        y1 = pane.winfo_rooty()
        if index is None:
            return (x0, y0, x0 + nb.winfo_width(), y1)
        ymid = (y1 - y0) // 2
        xs = []
        for x in range(0, nb.winfo_width(), 5):
            try:
                if nb.index(f"@{x},{ymid}") == index:
                    xs.append(x)
            except tk.TclError:
                pass
        if not xs:
            return (x0, y0, x0 + nb.winfo_width(), y1)
        return (x0 + xs[0], y0 + 2, x0 + xs[-1] + 5, y1)

    # ---------- прямоугольники для выносок обучения
    @staticmethod
    def _cell_rect(tree, iid, col=None):
        try:
            b = tree.bbox(iid, col) if col else tree.bbox(iid)
        except tk.TclError:
            return None
        if not b:
            return None
        x, y, w, h = b
        rx, ry = tree.winfo_rootx(), tree.winfo_rooty()
        return (rx + x, ry + y, rx + x + w, ry + y + h)

    def _head_rect(self, tree, col):
        kids = tree.get_children("")
        if not kids:
            return None
        b = tree.bbox(kids[0], col)
        if not b:
            return None
        x, y, w, h = b
        rx, ry = tree.winfo_rootx(), tree.winfo_rooty()
        return (rx + x, ry + 2, rx + x + w, ry + y - 2)

    def _first_child(self):
        r = self.result
        if not r or not self.dirtree.exists(r.root):
            return None
        kids = [k for k in self.dirtree.get_children(r.root) if not k.endswith("|dummy")]
        return kids[0] if kids else None

    def start_tour(self):
        if self.tour is not None:
            return
        self.show_dir_tree()
        self.nb.select(0)
        tab = lambda n: (lambda: self.nb.index("current") == n)
        scanning = lambda: str(self.scan_btn.cget("state")) == "disabled"
        tf = self.t_files

        def top_file_text():
            if not tf.rows:
                return ("Здесь появятся самые крупные файлы. Если список пуст — в выбранной папке нет файлов "
                        "крупнее заданного размера.")
            r0 = tf.rows[0]
            return (f"Самые крупные файлы — сверху. Сейчас первый — «{r0[1]}», {human(r0[0])}.\n\n"
                    "Размеры больше 1 ГБ — оранжевые, больше 10 ГБ — красные. Двойной щелчок — показать файл "
                    "в Проводнике. Правая кнопка — меню: «Что это за файл?», скрыть папку, удалить в Корзину.")

        def crit_rows():
            return [i for i, r in enumerate(tf.rows[:tf.limit]) if r[5]]

        def crit_text():
            rows = crit_rows()
            base = ("Некоторые огромные файлы — части Windows, их удалять нельзя:\n"
                    "• pagefile.sys — файл подкачки\n• hiberfil.sys — файл гибернации\n"
                    "• swapfile.sys, реестр пользователя, папки Windows, WinSxS, System32…\n\n"
                    "Программа помечает их 🔒 и красным и не даст удалить. Как правильно уменьшить такой файл — "
                    "правая кнопка → «Что это за файл?».")
            if rows:
                r = tf.rows[rows[0]]
                return f"Нашёлся системный файл «{r[1][2:]}» — {human(r[0])}.\n\n" + base
            return base + "\n\n(В выбранной папке таких файлов нет — они лежат в корне диска C:.)"

        def folder_marks():
            k = self._first_child()
            if not k:
                return []
            r = self.result
            size = r.dir_total.get(k, 0)
            pct = size * 100 / (r.dir_total.get(r.root, 0) or 1)
            return [(self._cell_rect(self.dirtree, k), f"«{os.path.basename(k)}» — {human(size)}, это {pct:.0f} % "
                     f"всего", "below"),
                    (self._cell_rect(self.dirtree, k, "pct"), "полоска = доля от папки выше", "below")]

        def health_marks():
            if not self.health_refs:
                return []
            h = self.health_refs[0]
            out = [(Tour._rect_of(h["pill"]), "состояние диска", "below")]
            if h["bar"] is not None:
                out.append((Tour._rect_of(h["bar"]), f"осталось ресурса: {h['life']} %", "below"))
            if h["smart"] is not None:
                out.append((Tour._rect_of(h["smart"]), "полная таблица SMART", "above"))
            return out

        steps = [
            dict(target=None, title="Добро пожаловать в DiskCleaner 👋",
                 text="Программа показывает, что занимает место на компьютере: самые большие файлы и папки, "
                      "мусор, дубликаты и какие типы файлов весят больше всего. А ещё следит за здоровьем дисков.\n\n"
                      "Пройдём по шагам на ваших настоящих данных. То, что нужно нажать, будет обведено "
                      "мигающей оранжевой рамкой, а синие выноски подскажут, что где показано.\n\n"
                      "Обучение можно закрыть в любой момент (Esc) и пройти снова кнопкой «? Обучение»."),
            dict(target=lambda: self.drives_row, click=lambda: self.drives_row, wait="path",
                 click_label="👆  Щёлкните по диску", title="Ваши диски",
                 text="Карточки показывают, сколько места свободно на каждом диске, его тип (SSD или HDD) и "
                      "состояние. Полоска — насколько диск заполнен.",
                 action="Щёлкните по карточке диска, который хотите проверить."),
            dict(target=lambda: [self.folder_btn, self.path_label, self.drive_label, self.settings_btn],
                 title="Что сканируем",
                 marks=lambda: [(Tour._rect_of(self.path_label), "выбранный диск или папка", "above"),
                                (Tour._rect_of(self.folder_btn), "проверить одну папку", "above"),
                                (Tour._rect_of(self.settings_btn), "размер больших файлов и процессы", "above")],
                 text="Здесь видно, что будет проверяться. Можно проверить весь диск или только одну папку — "
                      "например, «Загрузки»: кнопка «📁 Выбрать папку…».\n\n"
                      "«⚙ Настройки» — с какого размера файл считается большим и сколько ядер процессора "
                      "задействовать (подбирается само)."),
            dict(target=lambda: self.scan_btn, click=lambda: self.scan_btn, wait="scan_start",
                 click_label="👆  Нажмите «Сканировать»", title="Запускаем поиск",
                 text="Сканирование только читает сведения о файлах и ничего не меняет на диске.",
                 action="Нажмите кнопку «Сканировать»."),
            dict(target=lambda: self.bottom_bar, title="Идёт сканирование…", wait="scan_done",
                 cond_auto=lambda: self.result is not None and not scanning(),
                 marks=lambda: [(Tour._rect_of(self.status), "сколько файлов уже найдено", "above")],
                 text="Внизу видно, сколько файлов найдено и какая папка проверяется. Прервать можно "
                      "кнопкой «Стоп». Обычно это от нескольких секунд до пары минут.",
                 action="Дождитесь окончания — мастер продолжит сам."),
            dict(target=lambda: self.bottom_bar, title="Что нашлось",
                 marks=lambda: [(Tour._rect_of(self.status), "итоги сканирования", "above")],
                 text="Внизу — итоги: сколько места занято, сколько файлов и папок, сколько больших файлов "
                      "и сколько мусора, который, скорее всего, можно удалить."),
            dict(target=lambda: tf, on_enter=lambda: self.nb.select(0), title="Самые большие файлы",
                 marks=lambda: ([(self._cell_rect(tf.tree, "0"),
                                  f"самый большой: {tf.rows[0][1]} — {human(tf.rows[0][0])}", "below")]
                                if tf.rows else []) +
                               [(self._head_rect(tf.tree, "size"), "сколько весит", "above"),
                                (self._head_rect(tf.tree, "dir"), "где лежит", "above")],
                 text=top_file_text),
            dict(target=lambda: tf, on_enter=lambda: self.nb.select(0), title="🔒 Эти файлы удалять нельзя",
                 marks=lambda: ([(self._cell_rect(tf.tree, str(crit_rows()[0])), tf.rows[crit_rows()[0]][5], "below")]
                                if crit_rows() else []) +
                               [(self._head_rect(tf.tree, "note"), "почему нельзя удалять", "above")],
                 text=crit_text, width=460),
            dict(target=lambda: self._tab_rect(1), click=lambda: self._tab_rect(1), wait="tab", cond=tab(1),
                 cond_auto=tab(1), click_label="👆  Откройте «Папки»", title="Какие папки тяжелее всего",
                 text="Большие файлы — не всё: место часто съедают тысячи мелких файлов в одной папке.",
                 action="Откройте вкладку «Папки»."),
            dict(target=lambda: [self.dirs_panel, self.dirtree], on_enter=lambda: (self.nb.select(1), self.show_dir_tree()),
                 title="Дерево папок", marks=folder_marks, width=440,
                 text="Папки отсортированы от самых тяжёлых. Раскрывайте их стрелкой ▸, чтобы дойти до того, "
                      "что занимает место. 🔒 — системные папки, их не трогаем.\n\nСверху можно найти папку по "
                      "имени, например «Fortnite», и нажать «Показать списком»."),
            dict(target=lambda: self._tab_rect(4), click=lambda: self._tab_rect(4), wait="tab", cond=tab(4),
                 cond_auto=tab(4), click_label="👆  Откройте «Типы файлов»", title="Что именно занимает место",
                 text="Видео, игры, архивы, образы дисков? Узнаем, какие файлы весят больше всего вместе.",
                 action="Откройте вкладку «Типы файлов»."),
            dict(target=lambda: self.t_types, on_enter=lambda: self.nb.select(4), title="Типы файлов",
                 marks=lambda: [(self._cell_rect(self.t_types.tree, "0"),
                                 f"больше всего места — {self.t_types.rows[0][0]}: {human(self.t_types.rows[0][2])} "
                                 f"({self.t_types.rows[0][3]:.0f} %)", "below")] if self.t_types.rows else [],
                 text="Все файлы сгруппированы по расширению: сколько их и сколько они весят вместе. "
                      "Так сразу видно, что съедает место — фильмы (.mp4, .mkv), образы (.iso, .vhdx), "
                      "архивы (.zip, .rar) или что-то ещё."),
            dict(target=lambda: self._tab_rect(2), click=lambda: self._tab_rect(2), wait="tab", cond=tab(2),
                 cond_auto=tab(2), click_label="👆  Откройте «Мусор»", title="Мусор",
                 text="Программа собирает кандидатов на удаление: временные файлы, логи, дампы, кэши, пустые папки.",
                 action="Откройте вкладку «Мусор»."),
            dict(target=lambda: self.t_junk, on_enter=lambda: self.nb.select(2), title="Проверяйте перед удалением",
                 marks=lambda: ([(self._cell_rect(self.t_junk.tree, "0"),
                                  f"{self.t_junk.rows[0][0]}: {human(self.t_junk.rows[0][1])}", "below")]
                                if self.t_junk.rows else []) +
                               [(self._head_rect(self.t_junk.tree, "cat"), "что это за мусор", "above")],
                 text="Это подсказки — программа не знает, что важно лично вам. Выделите ненужное и нажмите "
                      "Delete или «Удалить в Корзину» в меню правой кнопки. Всё уходит в Корзину, откуда можно "
                      "восстановить."),
            dict(target=lambda: self._tab_rect(5), click=lambda: self._tab_rect(5), wait="tab", cond=tab(5),
                 cond_auto=tab(5), click_label="👆  Откройте «Здоровье дисков»", title="Здоровье дисков",
                 text="Программа читает SMART и предупреждает, если диск начинает сдавать.",
                 action="Откройте вкладку «Здоровье дисков»."),
            dict(target=lambda: self.h_canvas, on_enter=lambda: self.nb.select(5), title="Состояние дисков",
                 marks=health_marks, box="side", width=380,
                 text="Для каждого диска: состояние, оставшийся ресурс с прогнозом, температура, наработка, "
                      "ошибки. Если с диском что-то не так, программа сама предупредит при запуске — тогда "
                      "сразу сделайте резервную копию."),
            dict(target=None, title="Готово! 🎉",
                 text="Теперь вы знаете, как найти, что занимает место.\n\n"
                      "Помните: 🔒 системные файлы программа удалить не даст, а всё остальное удаляется "
                      "в Корзину и под вашу ответственность. Важные данные держите в резервной копии.\n\n"
                      "Обучение всегда можно пройти снова кнопкой «? Обучение» вверху окна."),
        ]
        self.tour = Tour(self, steps, self._tour_finished)

    def _tour_finished(self):
        self.tour = None
        st = load_settings()
        st["tour_done"] = True
        save_settings(st)
        pending = getattr(self, "_pending_health_alert", None)
        if pending:
            self._pending_health_alert = None
            self.after(300, lambda: self._show_health_alert(pending))

    def show_smart(self, d):
        pal = PALETTE[self.mode]
        win = tk.Toplevel(self)
        win.title(f"SMART — {d['model']}")
        win.geometry("980x640" if d.get("nvme") else "1120x660")
        win.minsize(700, 400)
        win.transient(self)
        base = ttk.Style().lookup("TFrame", "background") or pal["card"]
        win.configure(bg=base)
        body = ttk.Frame(win, padding=(18, 14, 18, 14))
        body.pack(fill="both", expand=True)
        levels = {"good": ("ok", "Исправен"), "warn": ("orange", "Внимание"), "bad": ("warn", "Плохо"),
                  "unknown": ("muted", "Нет данных")}
        role, state = levels.get(d.get("level"), ("muted", "?"))
        head = ttk.Frame(body)
        head.pack(fill="x")
        tk.Label(head, text=d["model"], font=self.f_big, bg=base, fg=pal["text"]).pack(side="left")
        tk.Label(head, text=f"   ●  {state}   ", font=self.f_bold, bg=pal[role], fg=pal["card"]).pack(side="right", ipady=3)
        kind = ("SSD" if d["ssd"] else "HDD") if d.get("ssd") is not None else ""
        info = " · ".join(x for x in (d["bus"], kind, human(d["size"]) if d.get("size") else "",
                                      ("диск " + ", ".join(d["letters"])) if d.get("letters") else "",
                                      ("S/N " + d["serial"]) if d.get("serial") else "") if x)
        tk.Label(body, text=info, font=self.f_norm, bg=base, fg=pal["muted"]).pack(anchor="w", pady=(4, 0))
        src = d.get("source") or "—"
        if d.get("ata") and not d.get("thresholds"):
            src += " · пороги отказа видны только при запуске от администратора"
        tk.Label(body, text="Источник: " + src, font=self.f_small, bg=base, fg=pal["muted"]).pack(anchor="w", pady=(2, 10))

        nv = bool(d.get("nvme"))
        cols = [("id", "ID", 50, "center"), ("name", "Атрибут", 300 if d.get("nvme") else 270, "w")]
        if not nv:
            cols += [("cur", "Текущее", 80, "e"), ("worst", "Худшее", 80, "e"), ("thr", "Порог", 70, "e")]
        cols += [("raw", "Значение" if nv else "Raw (сырое значение)", 290 if not nv else 520, "w")]
        if not nv:
            cols += [("state", "Состояние", 150, "w")]
        frame = ttk.Frame(body)
        frame.pack(fill="both", expand=True)
        tree = ttk.Treeview(frame, columns=[c[0] for c in cols], show="headings")
        for cid, title, w, anchor in cols:
            tree.heading(cid, text=title)
            tree.column(cid, width=w, anchor=anchor, stretch=cid in ("name", "raw"))
        ys = ttk.Scrollbar(frame, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=ys.set)
        tree.pack(side="left", fill="both", expand=True)
        ys.pack(side="right", fill="y")
        tree.tag_configure("odd", background=pal["stripe"])
        tree.tag_configure("warn", foreground=pal["orange"])
        tree.tag_configure("bad", foreground=pal["warn"], font=self.f_bold)
        for i, r in enumerate(smart_rows(d)):
            aid, name, cur, worst, thr, raw, st, lvl = r
            vals = [aid, name] + ([] if nv else [cur, worst, thr]) + [raw] + ([] if nv else [st])
            tree.insert("", "end", values=vals, tags=("odd" if i % 2 else "even", lvl))

        btns = ttk.Frame(body)
        btns.pack(fill="x", pady=(12, 0))
        tk.Label(btns, text="Оранжевым — стоит присмотреться, красным — признак отказа.", font=self.f_small,
                 bg=base, fg=pal["muted"]).pack(side="left")
        ttk.Button(btns, text="Закрыть", command=win.destroy).pack(side="right")

        def copy():
            self.clipboard_clear()
            self.clipboard_append(smart_report(d))
            copy_btn.configure(text="✓ Скопировано")
        copy_btn = ttk.Button(btns, text="Копировать отчёт", command=copy,
                              style="Accent.TButton" if sv_ttk else "TButton")
        copy_btn.pack(side="right", padx=8)
        win.update_idletasks()
        if self.mode == "dark" and IS_WIN:
            try:
                import ctypes
                hwnd = ctypes.windll.user32.GetParent(win.winfo_id())
                v = ctypes.c_int(1)
                ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, 20, ctypes.byref(v), ctypes.sizeof(v))
            except Exception:
                pass
        win.focus_force()
        return win

    def _health_card(self, d):
        levels = {"good": ("ok", "Исправен"), "warn": ("orange", "Внимание"), "bad": ("warn", "Плохо"),
                  "unknown": ("muted", "Нет данных")}
        role, text = levels[d["level"]]
        outer, inner = self._card(self.h_inner, padx=20, pady=14)
        outer.pack(fill="x", pady=(0, 10))
        top = tk.Frame(inner, bd=0)
        top.pack(fill="x")
        self._label(top, d["model"], font=self.f_big).pack(side="left")
        kind = ("SSD" if d["ssd"] else "HDD") if d["ssd"] is not None else ""
        sub = " · ".join(x for x in (d["bus"], kind, human(d["size"]) if d["size"] else "",
                                     ("диск " + ", ".join(d["letters"])) if d["letters"] else "") if x)
        self._label(top, "    " + sub, role="muted").pack(side="left", pady=(6, 0))
        pill = self._label(top, f"   ●  {text}   ", role=role, font=self.f_bold)
        pill.pill = True
        pill.pack(side="right", ipady=3)
        refs = dict(card=outer, pill=pill, bar=None, smart=None, model=d["model"], life=d["life"],
                    letters=d["letters"])
        self.health_refs.append(refs)
        if d.get("nvme") or d.get("ata"):
            sb = ttk.Button(top, text="SMART — подробно", command=lambda d=d: self.show_smart(d))
            sb.pack(side="right", padx=10)
            refs["smart"] = sb
        if d["life"] is not None:
            row = tk.Frame(inner, bd=0)
            row.pack(fill="x", pady=(14, 0))
            self._label(row, f"Ресурс  {d['life']} %", font=self.f_bold).pack(side="left")
            bar = self._bar(row, width=460, height=10)
            bar.value = d["life"] / 100
            bar.color = "ok" if d["life"] > 30 else ("orange" if d["life"] > 10 else "warn")
            bar.pack(side="left", padx=14)
            refs["bar"] = bar
            if d["forecast"]:
                self._label(row, d["forecast"], role="muted", font=self.f_small).pack(side="left")
        grid = tk.Frame(inner, bd=0)
        grid.pack(fill="x", pady=(14, 4))
        for i, (k, v) in enumerate(d["metrics"]):
            cell = tk.Frame(grid, bd=0)
            cell.grid(row=i // 4, column=i % 4, sticky="w", padx=(0, 56), pady=(0, 10))
            self._label(cell, k, role="muted", font=self.f_small).pack(anchor="w")
            self._label(cell, v, font=self.f_bold).pack(anchor="w")
        if d["problems"]:
            for lvl, t in d["problems"]:
                self._label(inner, ("⛔  " if lvl == "bad" else "⚠  ") + t,
                            role="warn" if lvl == "bad" else "orange", font=self.f_bold).pack(anchor="w", pady=(2, 0))
        elif d["level"] == "unknown":
            self._label(inner, "Диск не отдал данные SMART" + (
                "." if is_admin() else " без прав администратора — попробуйте «Перезапустить от администратора»."),
                role="muted").pack(anchor="w")
        else:
            self._label(inner, "✓  Проблем не найдено", role="ok", font=self.f_bold).pack(anchor="w")
        if d.get("source"):
            self._label(inner, "Источник: " + d["source"], role="muted", font=self.f_small).pack(anchor="w", pady=(6, 0))

    # ---------- дубликаты
    def _dups_done(self, groups):
        self._finish_ui()
        t = self.duptree
        t.delete(*t.get_children())
        if groups is None:
            self.status.config(text="Поиск дубликатов остановлен.")
            return
        waste = 0
        for i, (sz, paths) in enumerate(groups, 1):
            extra = sz * (len(paths) - 1)
            waste += extra
            gid = f"group{i}"
            t.insert("", "end", iid=gid, open=True, tags=("group", size_tag(extra)),
                     text=f"Группа {i}: {len(paths)} копии по {human(sz)} — лишнее {human(extra)}",
                     values=(human(extra), ""))
            for p in paths:
                try:
                    mt = fmt_date(os.path.getmtime(p))
                except OSError:
                    mt = ""
                t.insert(gid, "end", iid=p, text="   " + p, values=(human(sz), mt))
        self.dup_info.config(text=f"  Групп: {len(groups)}, можно освободить: {human(waste)}. "
                                  f"Оставьте в каждой группе один файл!")
        self.status.config(text="Поиск дубликатов завершён.")

    # ---------- действия
    def _active(self):
        tab = self.nb.index(self.nb.select())
        folders = self.t_dirs if self.t_dirs.winfo_ismapped() else self.dirtree
        return {0: self.t_files, 1: folders, 2: self.t_junk, 3: self.duptree, 4: self.t_types}.get(tab)

    def selected_paths(self):
        w = self._active()
        if w is None:
            return []
        if isinstance(w, Table):
            return [] if w is self.t_types else w.selected_paths()
        return [i for i in w.selection() if not i.startswith("group") and not i.endswith("|dummy")]

    def _popup(self, event):
        w = event.widget
        row = w.identify_row(event.y)
        if row and row not in w.selection():
            w.selection_set(row)
        self.menu.tk_popup(event.x_root, event.y_root)

    def reveal(self):
        paths = self.selected_paths()
        if not paths:
            return
        p = os.path.normpath(paths[0])
        if IS_WIN:
            subprocess.Popen(f'explorer /select,"{p}"')
        else:
            subprocess.Popen(["xdg-open", os.path.dirname(p)])

    def open_item(self):
        for p in self.selected_paths()[:5]:
            try:
                os.startfile(p) if IS_WIN else subprocess.Popen(["xdg-open", p])
            except OSError as ex:
                messagebox.showerror("Ошибка", str(ex))

    def copy_path(self):
        paths = self.selected_paths()
        if paths:
            self.clipboard_clear()
            self.clipboard_append("\n".join(paths))

    def explain_item(self):
        paths = self.selected_paths()
        if not paths:
            return
        p = paths[0]
        crit = critical_info(p)
        if crit:
            messagebox.showwarning(f"🔒 {crit[0]}", f"{p}\n\n{crit[1]}", parent=self)
        elif is_risky_path(p):
            messagebox.showwarning("Системная область",
                                   f"{p}\n\nФайл лежит в системной папке или папке программ. Удаление может сломать "
                                   f"Windows или программу. Удаляйте, только если точно знаете, что это.", parent=self)
        else:
            messagebox.showinfo("Обычный файл",
                                f"{p}\n\nЭто не системный файл. Решение об удалении за вами — убедитесь, "
                                f"что он вам не нужен (например, откройте его или посмотрите в Проводнике).",
                                parent=self)

    def delete_selected(self):
        paths = self.selected_paths()
        if not paths:
            return
        blocked = [(p, critical_info(p)) for p in paths if critical_info(p)]
        if blocked:
            lines = "\n\n".join(f"🔒 {os.path.basename(p) or p} — {c[0]}\n{c[1]}" for p, c in blocked[:4])
            messagebox.showerror("Эти файлы удалять нельзя",
                                 f"Программа не удаляет системные файлы и папки Windows:\n\n{lines}",
                                 parent=self)
            paths = [p for p in paths if not critical_info(p)]
            if not paths:
                return
        w = self._active()
        if w is self.duptree:
            for gid in self.duptree.get_children():
                left = [c for c in self.duptree.get_children(gid) if c not in paths]
                if not left:
                    messagebox.showwarning("Осторожно", "Выбраны все копии в группе — хотя бы одну нужно оставить.")
                    return
        preview = "\n".join(paths[:10]) + (f"\n… и ещё {len(paths) - 10}" if len(paths) > 10 else "")
        if not messagebox.askyesno("Удалить в Корзину?",
                                   f"Переместить в Корзину {len(paths)} объект(ов)?\n\n{preview}\n\n"
                                   f"Их можно будет восстановить из Корзины, пока она не очищена.\n\n"
                                   f"Вы сами отвечаете за удаление: убедитесь, что эти файлы вам не нужны.",
                                   icon="warning", parent=self):
            return
        risky = [p for p in paths if is_risky_path(p)]
        if risky:
            rp = "\n".join(risky[:8]) + (f"\n… и ещё {len(risky) - 8}" if len(risky) > 8 else "")
            if not messagebox.askyesno(
                    "⚠ Системные файлы",
                    f"Среди выбранного есть системные папки или файлы программ:\n\n{rp}\n\n"
                    f"Их удаление может сломать Windows или установленные программы.\n"
                    f"Удаляйте, только если точно знаете, что делаете.\n\n"
                    f"Всё равно удалить?", icon="warning", default="no", parent=self):
                return
        self.config(cursor="watch")
        self.update()
        errors = send_to_recycle_bin(paths)
        self.config(cursor="")
        removed = [p for p in paths if not os.path.exists(p)]
        for tbl in (self.t_files, self.t_junk, self.t_dirs):
            tbl.remove_paths(removed)
        if self.result:
            gone = set(removed)
            self.result.big_files = [f for f in self.result.big_files if f[1] not in gone]
        for tree in (self.dirtree, self.duptree):
            for p in removed:
                if tree.exists(p):
                    tree.delete(p)
        if errors:
            messagebox.showwarning("Не всё удалено", "\n".join(errors[:15]))
        self.status.config(text=f"Перемещено в Корзину: {len(removed)}. Размеры папок обновятся после пересканирования.")

    def export_csv(self):
        w = self._active()
        if w is None:
            messagebox.showinfo("Экспорт", "На этой вкладке нечего экспортировать — выберите вкладку со списком.")
            return
        if isinstance(w, Table):
            header, rows = w.export_rows()
        elif w is self.duptree:
            header = ["Группа", "Размер (байт)", "Путь"]
            rows = [(g, 0, c) for g in w.get_children() for c in w.get_children(g)]
        else:
            if not self.result:
                return
            header = ["Путь", "Размер (байт)", "Файлов"]
            rows = sorted(((p, s, self.result.dir_files.get(p, 0)) for p, s in self.result.dir_total.items()),
                          key=lambda x: x[1], reverse=True)
        if not rows:
            messagebox.showinfo("Экспорт", "Нет данных для экспорта.")
            return
        fn = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV", "*.csv")],
                                          initialfile="отчёт_диск.csv")
        if not fn:
            return
        with open(fn, "w", newline="", encoding="utf-8-sig") as f:
            wr = csv.writer(f, delimiter=";")
            wr.writerow(header)
            wr.writerows(rows)
        self.status.config(text=f"Сохранено: {fn}")


if __name__ == "__main__":
    import multiprocessing
    multiprocessing.freeze_support()
    if len(sys.argv) >= 3 and sys.argv[1] == "--health":
        import json
        with open(sys.argv[2], "w", encoding="utf-8") as _f:
            json.dump([dict({k: v for k, v in x.items() if k != "ata"}, ata_attrs=len(x.get("ata") or {}))
                       for x in read_disks_health()], _f, ensure_ascii=False, indent=1, default=str)
        sys.exit(0)
    if len(sys.argv) >= 3 and sys.argv[1] == "--selftest":
        # служебная проверка без окна: disk_cleaner --selftest ПАПКА [ФАЙЛ_ОТЧЁТА]
        _q, _c = queue.Queue(), threading.Event()
        scan(sys.argv[2], 50 << 20, _q, _c, workers_for(sys.argv[2])[1])
        while True:
            _m = _q.get()
            if _m[0] == "done":
                break
        _r = _m[1]
        _out = sys.argv[3] if len(sys.argv) > 3 else "selftest.txt"
        with open(_out, "w", encoding="utf-8") as _f:
            _f.write(f"files={_r.files} total={human(_r.total)} dirs={len(_r.dir_total)} "
                     f"sec={_r.seconds:.2f} drive={drive_kind(sys.argv[2])} workers={workers_for(sys.argv[2])[1]}\n")
        sys.exit(0)
    if IS_WIN:
        try:
            import ctypes
            ctypes.windll.shcore.SetProcessDpiAwareness(1)  # чёткий шрифт на мониторах с масштабированием
        except Exception:
            pass
    app = App()
    app.update()
    if app.ask_disclaimer():
        if not load_settings().get("tour_done"):
            app.after(500, app.start_tour)
        app.start_health(alert=True)
        app.mainloop()
    else:
        app.destroy()
