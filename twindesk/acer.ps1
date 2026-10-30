# Install and verify TwinDesk 2.4.0 on the Acer (Windows). Run in PowerShell: .\acer.ps1 [-Peer MAC_IP]
param([string]$Peer = "")
$V = "2.4.0"; $F = "TwinDesk-Setup-$V.exe"
$Hash = "39ffc5458abbedddf9b3d9da23356e70dd688be4c4af6b16ac31478d5f6c8fda"
$script:Failed = $false
function Pass($m){ Write-Host "PASS  $m" -ForegroundColor Green }
function Fail($m){ Write-Host "FAIL  $m" -ForegroundColor Red; $script:Failed = $true }

$exe = Get-ChildItem "$env:LOCALAPPDATA\Programs\TwinDesk\TwinDesk.exe","$env:ProgramFiles\TwinDesk\TwinDesk.exe" -ErrorAction SilentlyContinue | Select-Object -First 1
if (-not $exe) {
  $dl = Join-Path $env:TEMP $F
  Invoke-WebRequest "https://github.com/InukaAsith/TwinDesk/releases/download/v$V/$F" -OutFile $dl
  if ((Get-FileHash $dl -Algorithm SHA256).Hash.ToLower() -ne $Hash) { Fail "checksum mismatch"; exit 1 }
  Start-Process $dl -ArgumentList "/S" -Wait   # NSIS silent; if SmartScreen blocks: More info > Run anyway
  $exe = Get-ChildItem "$env:LOCALAPPDATA\Programs\TwinDesk\TwinDesk.exe","$env:ProgramFiles\TwinDesk\TwinDesk.exe" -ErrorAction SilentlyContinue | Select-Object -First 1
}
if ($exe) { Pass "installed: $($exe.FullName)"; Start-Process $exe.FullName; Start-Sleep 6 } else { Fail "TwinDesk.exe not found" }
if (Get-Process -Name TwinDesk -ErrorAction SilentlyContinue) { Pass "TwinDesk running" } else { Fail "TwinDesk not running" }
if (Get-NetTCPConnection -LocalPort 47800 -State Listen -ErrorAction SilentlyContinue) { Pass "TCP 47800 listening" } else { Fail "TCP 47800 not listening" }
if (Get-NetUDPEndpoint -LocalPort 47801 -ErrorAction SilentlyContinue) { Pass "UDP 47801 discovery open" } else { Fail "UDP 47801 not open" }
if (Get-NetFirewallRule -DisplayName "*TwinDesk*" -ErrorAction SilentlyContinue) { Pass "firewall rules present" } else { Fail "no TwinDesk firewall rule (use the Setup screen's firewall fix, as admin)" }
if ($Peer) { if (Test-NetConnection $Peer -Port 47800 -InformationLevel Quiet) { Pass "Mac reachable on ${Peer}:47800" } else { Fail "cannot reach ${Peer}:47800" } }
Write-Host "Next: pair via Overview > Nearby, compare the code on both screens."
exit ([int]$script:Failed)
