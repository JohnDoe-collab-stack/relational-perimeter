$ErrorActionPreference = "Stop"

$expected = & "$PSScriptRoot/update-manifest.ps1" -PrintOnly
$actual = if (Test-Path -LiteralPath MANIFEST.sha256) {
  Get-Content -Raw -LiteralPath MANIFEST.sha256
} else {
  ""
}

if (($expected -join "`n") + "`n" -ne $actual.Replace("`r`n", "`n")) {
  Write-Error "MANIFEST.sha256 does not match the published working tree."
  exit 1
}

Write-Output "Manifest passed with $($expected.Count) entries."
