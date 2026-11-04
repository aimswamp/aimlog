@echo off
chcp 65001 >nul
set PYTHONIOENCODING=utf-8
cd /d "%~dp0"

echo ======================================================================
echo  [AimLog] Shorts Auto Generator and YouTube Uploader
echo ======================================================================
echo.

echo [1/4] Pulling latest articles from GitHub...
git pull --rebase --autostash origin main
echo.

echo [2/4] Syncing published status from Google Sheets...
python pipeline.py --sync-only
echo.

echo [3/4] Generating Shorts and uploading to YouTube...
python make_short.py %*
echo.

echo [4/4] Saving history to GitHub...
git add data/ dist/
git diff --staged --quiet
if errorlevel 1 (
    git commit -m "chore: update shorts history and synced site"
    git push origin main
)

echo.
echo ======================================================================
echo  All tasks finished! Press any key to close this window.
echo ======================================================================
pause
