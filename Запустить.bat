@echo off
chcp 65001 >nul
cd /d "%~dp0"
where pyw >nul 2>nul && (start "" pyw -3 "%~dp0disk_cleaner.py" & exit /b)
where pythonw >nul 2>nul && (start "" pythonw "%~dp0disk_cleaner.py" & exit /b)
python "%~dp0disk_cleaner.py"
pause
