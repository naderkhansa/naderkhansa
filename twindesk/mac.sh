#!/usr/bin/env bash
# Install and verify TwinDesk 2.4.0 on the Mac. Usage: ./mac.sh [ACER_IP]
set -u
PEER="${1:-}"
V=2.4.0
BASE=https://github.com/InukaAsith/TwinDesk/releases/download/v$V
pass(){ echo "PASS  $*"; }; fail(){ echo "FAIL  $*"; FAILED=1; }; FAILED=0

if [ ! -d /Applications/TwinDesk.app ]; then
  if command -v brew >/dev/null; then
    brew install --cask inukaasith/twindesk/twindesk
  else
    if [ "$(uname -m)" = arm64 ]; then F=TwinDesk-$V-arm64.dmg; H=093376687935351306df27de10e77c7ec7a517c2a3394e23178e90cf5c12a9ed
    else F=TwinDesk-$V-x64_Intel.dmg; H=2c0f8719bc2b1ee7c2a27578f67c5cd7a151437352f908223113fffe96f1e783; fi
    cd "$(mktemp -d)" && curl -fSLO "$BASE/$F" || exit 1
    [ "$(shasum -a 256 "$F" | cut -d' ' -f1)" = "$H" ] || { echo "checksum mismatch"; exit 1; }
    hdiutil attach "$F" -nobrowse -mountpoint /Volumes/TwinDeskInstall >/dev/null
    cp -R /Volumes/TwinDeskInstall/TwinDesk.app /Applications/
    hdiutil detach /Volumes/TwinDeskInstall >/dev/null
  fi
  xattr -dr com.apple.quarantine /Applications/TwinDesk.app 2>/dev/null
fi

[ -d /Applications/TwinDesk.app ] && pass "installed: $(defaults read /Applications/TwinDesk.app/Contents/Info CFBundleShortVersionString)" || fail "app not in /Applications"
open -a TwinDesk; sleep 5
pgrep -fi twindesk >/dev/null && pass "TwinDesk running" || fail "TwinDesk not running"
lsof -nP -iTCP:47800 -sTCP:LISTEN >/dev/null 2>&1 && pass "TCP 47800 listening" || fail "TCP 47800 not listening (finish the Setup screen / grant permissions)"
lsof -nP -iUDP:47801 >/dev/null 2>&1 && pass "UDP 47801 discovery open" || fail "UDP 47801 not open"
if [ -n "$PEER" ]; then
  nc -z -w 3 "$PEER" 47800 && pass "Acer reachable on $PEER:47800" || fail "cannot reach $PEER:47800 (same network? Windows firewall?)"
fi
echo "Next: System Settings > Privacy & Security > Accessibility + Screen Recording for TwinDesk, then pair via Overview > Nearby."
exit $FAILED
