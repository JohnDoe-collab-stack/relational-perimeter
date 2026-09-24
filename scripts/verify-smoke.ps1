$ErrorActionPreference = "Stop"

$output = & lake env lean Smoke/EndogenousOperationalTrace.lean 2>&1
$status = $LASTEXITCODE
$output | ForEach-Object { Write-Output $_ }
if ($status -ne 0) {
  exit $status
}

$observed = @($output | ForEach-Object { "$_" } |
  Where-Object { $_ -match '^SMOKE_TRACE_V1 ' })
$expected = (Get-Content -Raw -LiteralPath `
  "Smoke/endogenous-operational-trace-v1.expected").TrimEnd("`r", "`n")

if ($observed.Count -ne 1 -or $observed[0] -ne $expected) {
  Write-Error "The executable smoke trace does not match its frozen output."
  exit 1
}

Write-Output "Non-confirmatory executable smoke trace passed."
