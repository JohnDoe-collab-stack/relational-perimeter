$ErrorActionPreference = 'Stop'
$pythonPath = if ($env:RELATIONAL_PERIMETER_PYTHON) { $env:RELATIONAL_PERIMETER_PYTHON } else { 'python3' }
$lakePath = (Get-Command lake -ErrorAction Stop).Source
& $pythonPath (Join-Path $PSScriptRoot 'expected_failure_diagnostics.py') --lake $lakePath
if ($LASTEXITCODE -ne 0) { throw 'Expected-failure diagnostic verification failed' }
$global:LASTEXITCODE = 0
