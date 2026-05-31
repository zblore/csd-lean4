<#
.SYNOPSIS
  Type-check Lean files directly with lean.exe, bypassing lake.

.DESCRIPTION
  Fallback for when `lake.exe` is unavailable (e.g. blocked mid-session by a
  Windows Application Control / Smart App Control policy, as happened
  2026-05-31). Sets LEAN_PATH to the prebuilt dependency oleans and invokes the
  toolchain's lean.exe on each file. Dependency oleans must already be built by a
  prior `lake build`; this only re-checks the named file(s), it does not write
  oleans. Exit code per file is printed as `EXIT[<file>]=<code>`.

.EXAMPLE
  powershell -File scripts/leancheck.ps1 CsdLean4/LF4/MomentRatioUniform.lean
#>
param([Parameter(Mandatory = $true, ValueFromRemainingArguments = $true)][string[]]$Files)
$ErrorActionPreference = 'Stop'
$root = (Resolve-Path "$PSScriptRoot\..").Path
$pk = Join-Path $root ".lake\packages"
$deps = 'Cli', 'batteries', 'Qq', 'aesop', 'proofwidgets', 'importGraph', 'LeanSearchClient', 'plausible', 'mathlib'
$paths = @($deps | ForEach-Object { Join-Path $pk "$_\.lake\build\lib\lean" })
$paths += (Join-Path $root ".lake\build\lib\lean")
$env:LEAN_PATH = $paths -join ';'
$tc = (Get-Content (Join-Path $root "lean-toolchain") -Raw).Trim().Replace('/', '--').Replace(':', '---')
$lean = Join-Path $env:USERPROFILE ".elan\toolchains\$tc\bin\lean.exe"
foreach ($f in $Files) {
  & $lean (Resolve-Path $f).Path
  Write-Output "EXIT[$f]=$LASTEXITCODE"
}
