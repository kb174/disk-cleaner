# -*- coding: utf-8 -*-
"""
Анализатор диска: поиск больших файлов, тяжёлых папок, мусора и дубликатов.
Запуск:  python disk_cleaner.py   (или двойной клик по «Запустить.bat»)
Ничего не удаляет само — только по вашей команде и только в Корзину.
"""
import os
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


def default_workers():
    return max(1, min(16, os.cpu_count() or 4))


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

    def __init__(self, master, columns, path_col):
        super().__init__(master)
        self.columns = columns
        self.path_col = path_col
        self.rows = []
        self.sort_col, self.sort_rev = None, True
        ids = [c[0] for c in columns]
        self.tree = ttk.Treeview(self, columns=ids, show="headings", selectmode="extended")
        for cid, title, width, kind in columns:
            anchor = "e" if kind in ("size", "int", "pct") else "w"
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
                    vals.append(f"{v:.1f} %")
                elif k == "int":
                    vals.append(f"{v:,}".replace(",", " "))
                else:
                    vals.append(v)
            self.tree.insert("", "end", iid=str(i), values=vals)

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


# ---------------------------------------------------------------- главное окно
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Анализатор диска — большие файлы, папки и мусор")
        self.geometry("1150x700")
        self.minsize(800, 450)
        self.q = queue.Queue()
        self.cancel = threading.Event()
        self.result = None
        self.worker = None
        self._build()
        self.after(100, self._poll)

    # ---------- интерфейс
    def _build(self):
        top = ttk.Frame(self, padding=6)
        top.pack(fill="x")
        ttk.Label(top, text="Где искать:").pack(side="left")
        self.path_var = tk.StringVar(value=list_drives()[0])
        self.path_box = ttk.Combobox(top, textvariable=self.path_var, values=list_drives(), width=40)
        self.path_box.pack(side="left", padx=4)
        ttk.Button(top, text="Обзор…", command=self._browse).pack(side="left")
        ttk.Label(top, text="   Файлы от (МБ):").pack(side="left")
        self.min_var = tk.StringVar(value="50")
        ttk.Spinbox(top, from_=1, to=100000, increment=10, textvariable=self.min_var, width=7).pack(side="left", padx=4)
        ttk.Label(top, text="   Ядер:").pack(side="left")
        self.workers_var = tk.StringVar(value=str(default_workers()))
        ttk.Spinbox(top, from_=1, to=64, textvariable=self.workers_var, width=4).pack(side="left", padx=4)
        self.scan_btn = ttk.Button(top, text="▶ Сканировать", command=self.start_scan)
        self.scan_btn.pack(side="left", padx=(12, 4))
        self.stop_btn = ttk.Button(top, text="■ Стоп", command=self.cancel.set, state="disabled")
        self.stop_btn.pack(side="left")
        ttk.Button(top, text="Экспорт в CSV", command=self.export_csv).pack(side="right")

        self.nb = ttk.Notebook(self)
        self.nb.pack(fill="both", expand=True, padx=6)

        # Вкладка: большие файлы
        f1 = ttk.Frame(self.nb)
        flt = ttk.Frame(f1, padding=(0, 4))
        flt.pack(fill="x")
        ttk.Label(flt, text="Фильтр по имени/пути:").pack(side="left")
        self.filter_var = tk.StringVar()
        ttk.Entry(flt, textvariable=self.filter_var, width=30).pack(side="left", padx=4)
        ttk.Label(flt, text="  не изменялись дней, не менее:").pack(side="left")
        self.age_var = tk.StringVar(value="0")
        ttk.Spinbox(flt, from_=0, to=10000, increment=30, textvariable=self.age_var, width=6).pack(side="left", padx=4)
        ttk.Button(flt, text="Применить", command=self.fill_files).pack(side="left", padx=4)
        self.files_info = ttk.Label(flt, text="")
        self.files_info.pack(side="left", padx=10)
        flt2 = ttk.Frame(f1, padding=(0, 0, 0, 4))
        flt2.pack(fill="x")
        ttk.Label(flt2, text="Скрыть папки (через запятую):").pack(side="left")
        self.exclude_var = tk.StringVar()
        ex = ttk.Entry(flt2, textvariable=self.exclude_var, width=60)
        ex.pack(side="left", padx=4, fill="x", expand=True)
        ttk.Button(flt2, text="Очистить", command=lambda: (self.exclude_var.set(""), self.fill_files())).pack(side="left")
        ttk.Label(flt2, text="  пример: Fortnite, Program Files, Windows", foreground="gray").pack(side="left")
        for w in flt.winfo_children() + [ex]:
            if isinstance(w, (ttk.Entry, ttk.Spinbox)):
                w.bind("<Return>", lambda e: self.fill_files())
        self.t_files = Table(f1, [("size", "Размер", 90, "size"), ("name", "Имя", 260, "text"),
                                  ("ext", "Тип", 70, "text"), ("date", "Изменён", 120, "date"),
                                  ("dir", "Папка", 500, "text")], path_col=5)
        self.t_files.pack(fill="both", expand=True)
        self.nb.add(f1, text="Большие файлы")

        # Вкладка: дерево папок
        f2 = ttk.Frame(self.nb)
        bar2 = ttk.Frame(f2, padding=(0, 4))
        bar2.pack(fill="x")
        ttk.Label(bar2, text="Найти папку:").pack(side="left")
        self.dir_search_var = tk.StringVar()
        e1 = ttk.Entry(bar2, textvariable=self.dir_search_var, width=22)
        e1.pack(side="left", padx=4)
        ttk.Label(bar2, text=" Вложенность:").pack(side="left")
        self.dir_depth_var = tk.StringVar(value="любая")
        ttk.Combobox(bar2, textvariable=self.dir_depth_var, width=7, state="readonly",
                     values=["любая", "1", "2", "3", "4", "5", "6"]).pack(side="left", padx=4)
        ttk.Label(bar2, text=" от (МБ):").pack(side="left")
        self.dir_min_var = tk.StringVar(value="100")
        e2 = ttk.Spinbox(bar2, from_=0, to=1000000, increment=100, textvariable=self.dir_min_var, width=7)
        e2.pack(side="left", padx=4)
        ttk.Label(bar2, text=" Скрыть:").pack(side="left")
        self.dir_exclude_var = tk.StringVar()
        e3 = ttk.Entry(bar2, textvariable=self.dir_exclude_var, width=18)
        e3.pack(side="left", padx=4)
        self.dir_top_only = tk.BooleanVar(value=True)
        ttk.Checkbutton(bar2, text="без вложенных повторов", variable=self.dir_top_only).pack(side="left", padx=4)
        ttk.Button(bar2, text="Список", command=self.fill_dir_list).pack(side="left", padx=2)
        ttk.Button(bar2, text="Дерево", command=self.show_dir_tree).pack(side="left", padx=2)
        for w in (e1, e2, e3):
            w.bind("<Return>", lambda e: self.fill_dir_list())
        self.dir_info = ttk.Label(f2, text="Дерево: раскрывайте папки. «Список» — плоский перечень папок по фильтру, "
                                           "от самых тяжёлых.", foreground="gray")
        self.dir_info.pack(fill="x")
        self.t_dirs = Table(f2, [("size", "Размер", 100, "size"), ("pct", "% от диска", 90, "pct"),
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
        self.dirtree.column("#0", width=600)
        for c, w in (("size", 100), ("pct", 110), ("files", 100)):
            self.dirtree.column(c, width=w, anchor="e", stretch=False)
        ys = ttk.Scrollbar(f2_tree, orient="vertical", command=self.dirtree.yview)
        self.dirtree.configure(yscrollcommand=ys.set)
        self.dirtree.pack(side="left", fill="both", expand=True)
        ys.pack(side="right", fill="y")
        self.dirtree.bind("<<TreeviewOpen>>", self._tree_open)
        self.nb.add(f2, text="Папки")

        # Вкладка: мусор
        f3 = ttk.Frame(self.nb)
        bar3 = ttk.Frame(f3, padding=(0, 4))
        bar3.pack(fill="x")
        self.junk_info = ttk.Label(bar3, text="Кандидаты на удаление. Проверяйте перед удалением!")
        self.junk_info.pack(side="left")
        self.t_junk = Table(f3, [("cat", "Категория", 170, "text"), ("size", "Размер", 90, "size"),
                                 ("kind", "Что", 60, "text"), ("path", "Путь", 700, "text")], path_col=3)
        self.t_junk.pack(fill="both", expand=True)
        self.nb.add(f3, text="Мусор")

        # Вкладка: дубликаты
        f4 = ttk.Frame(self.nb)
        bar4 = ttk.Frame(f4, padding=(0, 4))
        bar4.pack(fill="x")
        self.dup_btn = ttk.Button(bar4, text="Найти дубликаты среди больших файлов", command=self.start_dups)
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
        self.nb.add(f4, text="Дубликаты")

        # Вкладка: типы файлов
        f5 = ttk.Frame(self.nb)
        self.t_types = Table(f5, [("ext", "Расширение", 160, "text"), ("count", "Файлов", 100, "int"),
                                  ("size", "Общий размер", 120, "size"), ("pct", "Доля", 80, "pct")], path_col=0)
        self.t_types.pack(fill="both", expand=True)
        self.nb.add(f5, text="Типы файлов")

        # строка состояния
        bottom = ttk.Frame(self, padding=6)
        bottom.pack(fill="x")
        self.progress = ttk.Progressbar(bottom, mode="indeterminate", length=180)
        self.progress.pack(side="left")
        self.status = ttk.Label(bottom, text="Выберите диск или папку и нажмите «Сканировать».")
        self.status.pack(side="left", padx=8)

        # контекстное меню
        self.menu = tk.Menu(self, tearoff=0)
        self.menu.add_command(label="Показать в Проводнике", command=self.reveal)
        self.menu.add_command(label="Открыть", command=self.open_item)
        self.menu.add_command(label="Копировать путь", command=self.copy_path)
        self.menu.add_separator()
        self.menu.add_command(label="Показать размер папки (в дереве)", command=self.show_in_tree)
        self.menu.add_command(label="Скрыть эту папку из списка…", command=self.hide_folder)
        self.menu.add_separator()
        self.menu.add_command(label="Удалить в Корзину…", command=self.delete_selected)
        for w in (self.t_files.tree, self.t_junk.tree, self.dirtree, self.duptree, self.t_dirs.tree):
            w.bind("<Button-3>", self._popup)
            w.bind("<Double-1>", lambda e: self.reveal())
            w.bind("<Delete>", lambda e: self.delete_selected())

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
        note = " (остановлено — результаты неполные)" if r.cancelled else ""
        self.status.config(text=(f"Готово{note}: {r.files:,} файлов, {human(r.total)} за {r.seconds:.1f} с "
                                 f"({self._workers()} проц.). "
                                 f"Недоступно (нет прав): {r.errors:,}").replace(",", " "))
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
            rows.append((sz, name, os.path.splitext(name)[1].lower(), mt, os.path.dirname(p), p))
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
        self.dir_info.config(text="Дерево: раскрывайте папки. «Список» — плоский перечень папок по фильтру, "
                                  "от самых тяжёлых.")

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
        t.insert("", "end", iid=root, text=root, open=True,
                 values=(human(r.dir_total.get(root, 0)), "100.0 %", r.dir_files.get(root, 0)))
        self._populate(root)

    def _populate(self, parent):
        r = self.result
        t = self.dirtree
        for ch in t.get_children(parent):
            t.delete(ch)
        ptotal = r.dir_total.get(parent, 0) or 1
        kids = sorted(r.children.get(parent, []), key=lambda p: r.dir_total.get(p, 0), reverse=True)
        for p in kids:
            size = r.dir_total.get(p, 0)
            t.insert(parent, "end", iid=p, text=os.path.basename(p) or p,
                     values=(human(size), f"{size * 100 / ptotal:.1f} %", f"{r.dir_files.get(p, 0):,}".replace(",", " ")))
            if r.children.get(p):
                t.insert(p, "end", iid=p + "|dummy", text="…")

    def _tree_open(self, _event):
        node = self.dirtree.focus()
        kids = self.dirtree.get_children(node)
        if len(kids) == 1 and kids[0].endswith("|dummy"):
            self._populate(node)

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
            t.insert("", "end", iid=gid, open=True,
                     text=f"Группа {i}: {len(paths)} копии по {human(sz)} — лишнее {human(extra)}",
                     values=(human(extra), ""))
            for p in paths:
                try:
                    mt = fmt_date(os.path.getmtime(p))
                except OSError:
                    mt = ""
                t.insert(gid, "end", iid=p, text=p, values=(human(sz), mt))
        self.dup_info.config(text=f"  Групп: {len(groups)}, можно освободить: {human(waste)}. "
                                  f"Оставьте в каждой группе один файл!")
        self.status.config(text="Поиск дубликатов завершён.")

    # ---------- действия
    def _active(self):
        tab = self.nb.index(self.nb.select())
        folders = self.t_dirs if self.t_dirs.winfo_ismapped() else self.dirtree
        return {0: self.t_files, 1: folders, 2: self.t_junk, 3: self.duptree, 4: self.t_types}[tab]

    def selected_paths(self):
        w = self._active()
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

    def delete_selected(self):
        paths = self.selected_paths()
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
                                   f"Их можно будет восстановить из Корзины."):
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
    if len(sys.argv) >= 3 and sys.argv[1] == "--selftest":
        # служебная проверка без окна: disk_cleaner --selftest ПАПКА [ФАЙЛ_ОТЧЁТА]
        _q, _c = queue.Queue(), threading.Event()
        scan(sys.argv[2], 50 << 20, _q, _c)
        while True:
            _m = _q.get()
            if _m[0] == "done":
                break
        _r = _m[1]
        _out = sys.argv[3] if len(sys.argv) > 3 else "selftest.txt"
        with open(_out, "w", encoding="utf-8") as _f:
            _f.write(f"files={_r.files} total={human(_r.total)} dirs={len(_r.dir_total)} "
                     f"sec={_r.seconds:.2f} workers={default_workers()}\n")
        sys.exit(0)
    if IS_WIN:
        try:
            import ctypes
            ctypes.windll.shcore.SetProcessDpiAwareness(1)  # чёткий шрифт на мониторах с масштабированием
        except Exception:
            pass
    App().mainloop()
