$ErrorActionPreference = "Stop"
$checker = Join-Path $PSScriptRoot "check-import-boundaries.py"
if ($env:RELATIONAL_PERIMETER_PYTHON) {
  $pythonCommand = $env:RELATIONAL_PERIMETER_PYTHON
} elseif (Get-Command python3 -ErrorAction SilentlyContinue) {
  $pythonCommand = "python3"
} else {
  throw "Python 3 is required for import-boundary checks"
}
& $pythonCommand $checker @args
if ($LASTEXITCODE -ne 0) { throw "import-boundary check failed (exit $LASTEXITCODE)" }
