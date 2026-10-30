# TwinDesk: Mac + Acer

Install and check TwinDesk 2.4.0 (https://github.com/InukaAsith/TwinDesk) on both machines.
Installer SHA-256 hashes are pinned in the scripts. Both machines must be on the same network.
Ports: TCP 47800, UDP 47801.

1. Mac: `bash twindesk/mac.sh <ACER_IP>`
2. Acer (PowerShell): `.\twindesk\acer.ps1 -Peer <MAC_IP>`
3. Open TwinDesk on both, Overview > Nearby, pair by comparing the code.
4. Check: cursor crosses the screen edge, keyboard follows, copy on one and paste on the other.
