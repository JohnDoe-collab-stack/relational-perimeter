param([string]$EvidenceDirectory = '')

# Confirmatory local verification, not a benchmark or independent audit.
# Freeze this script and all inputs before invoking it; never reuse an output.
$ErrorActionPreference = 'Stop'
$taskRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
if (-not $EvidenceDirectory) {
  $taskRecords = Join-Path (Split-Path $taskRoot -Parent) 'perimeter-variable-decomposition-records-20261006'
  $EvidenceDirectory = Join-Path $taskRecords ('confirmed-' + (Get-Date -Format 'yyyyMMdd-HHmmss'))
}
$taskEvidence = [IO.Path]::GetFullPath($EvidenceDirectory)
if ($taskEvidence -eq $taskRoot -or $taskEvidence.StartsWith($taskRoot + [IO.Path]::DirectorySeparatorChar)) {
  throw 'Evidence must be outside the source directory'
}
if (Test-Path -LiteralPath $taskEvidence) { throw 'Evidence exists; refusing to overwrite it' }
New-Item -ItemType Directory -Path $taskEvidence -Force | Out-Null
$taskLake = (Get-Command lake -ErrorAction Stop).Source
$taskScriptHash = (Get-FileHash -LiteralPath $PSCommandPath -Algorithm SHA256).Hash
$taskBaseline = Join-Path (Split-Path $taskRoot -Parent) 'perimeter-direct-machine-787c8f65b9194dec943e04ade944e237'

function Get-TaskInputs {
  $taskNames = @(& git ls-files --cached --others --exclude-standard)
  if ($LASTEXITCODE -ne 0) { throw 'Input inventory failed' }
  foreach ($taskName in ($taskNames | Sort-Object -Unique)) {
    $taskPath = Join-Path $taskRoot $taskName
    if (Test-Path -LiteralPath $taskPath -PathType Leaf) {
      [pscustomobject]@{ path = $taskName; sha256 = (Get-FileHash -LiteralPath $taskPath -Algorithm SHA256).Hash }
    }
  }
}

function Invoke-TaskCheck([string]$Log, [string]$Command, [scriptblock]$Action) {
  $taskLogPath = Join-Path $taskEvidence $Log
  & $Action *> $taskLogPath
  $taskExit = $LASTEXITCODE
  [pscustomobject]@{ command = $Command; exit = $taskExit; log = $Log;
    sha256 = (Get-FileHash -LiteralPath $taskLogPath -Algorithm SHA256).Hash } |
    ConvertTo-Json -Compress | Add-Content -LiteralPath (Join-Path $taskEvidence 'commands.jsonl')
  if ($taskExit -ne 0) { throw "Check failed ($taskExit): $Command; see $taskLogPath" }
  Write-Output "CHECK_OK $Command"
}

Push-Location $taskRoot
try {
  $taskBefore = @(Get-TaskInputs)
  $taskBefore | ConvertTo-Json -Depth 5 | Set-Content -LiteralPath (Join-Path $taskEvidence 'inputs-before.json')
  Copy-Item -LiteralPath $PSCommandPath -Destination (Join-Path $taskEvidence 'frozen-protocol.ps1')
  [pscustomobject]@{
    script = 'scripts/check-variable-master.ps1'; sha256 = $taskScriptHash
    cwd = $taskRoot; evidence = $taskEvidence; baseline = $taskBaseline
    powershell = $PSVersionTable.PSVersion.ToString(); lake = $taskLake
    python = $env:RELATIONAL_PERIMETER_PYTHON
    toolchain = (Get-Content -LiteralPath (Join-Path $taskRoot 'lean-toolchain') -Raw).Trim()
    parameters = @{ EvidenceDirectory = $EvidenceDirectory }; seeds = @(); data = 'inventoried source inputs'
    commands = @('lake clean', 'lake build +RelationalPerimeter', 'lake build',
      'scripts/verify.ps1', 'lake update', 'git diff --check',
      'git -c core.autocrlf=false -c core.safecrlf=false diff --no-index --check NUL FILE (new or changed text inputs)',
      'compare protected files and existing Lean against baseline', 'check local Markdown links',
      'compare input hashes')
    scope = 'Local constructivity, sharing, examples, boundaries and integrity; no total-cost or independent-audit claim'
  } | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath (Join-Path $taskEvidence 'protocol.json')

  Invoke-TaskCheck 'clean.log' 'lake clean' { & $taskLake clean }
  Invoke-TaskCheck 'root-build.log' 'lake build +RelationalPerimeter' { & $taskLake build +RelationalPerimeter }
  Invoke-TaskCheck 'full-build.log' 'lake build' { & $taskLake build }
  Invoke-TaskCheck 'verify-windows.log' 'scripts/verify.ps1' { & (Join-Path $taskRoot 'scripts/verify.ps1') }
  Invoke-TaskCheck 'lake-update.log' 'lake update' { & $taskLake update }
  Invoke-TaskCheck 'diff-check.log' 'git diff --check' { & git diff --check }
  foreach ($taskBuildLog in @('root-build.log', 'full-build.log')) {
    $taskText = Get-Content -LiteralPath (Join-Path $taskEvidence $taskBuildLog) -Raw
    if ($taskText -notmatch 'Build completed successfully' -or
        $taskText -match 'warning:|error:|depends on axioms:|sorryAx') { throw "Rejected build diagnostics: $taskBuildLog" }
  }

  $taskProtected = @('SegmentedResidualRole.lean', 'AbstractSegmentedTurning.lean',
    'ExactTypeTransport.lean', 'StrongPerimetralTurning.lean', 'LICENSE', 'lean-toolchain', 'lake-manifest.json')
  foreach ($taskName in $taskProtected) {
    $taskOriginal = Join-Path $taskBaseline $taskName
    if (-not (Test-Path -LiteralPath $taskOriginal)) { throw "Missing baseline input: $taskName" }
    if ((Get-FileHash -LiteralPath $taskOriginal).Hash -cne
        (Get-FileHash -LiteralPath (Join-Path $taskRoot $taskName)).Hash) { throw "Protected input changed: $taskName" }
    "PROTECTED_OK $taskName" | Add-Content -LiteralPath (Join-Path $taskEvidence 'baseline-check.log')
  }

  foreach ($taskInput in $taskBefore) {
    $taskOriginal = Join-Path $taskBaseline $taskInput.path
    $taskChanged = -not (Test-Path -LiteralPath $taskOriginal -PathType Leaf)
    if (-not $taskChanged) { $taskChanged = (Get-FileHash -LiteralPath $taskOriginal).Hash -cne $taskInput.sha256 }
    if ($taskChanged -and $taskInput.path.EndsWith('.lean') -and
        $taskInput.path -notin @('RelationalPerimeter.lean', 'Tests/AllConstantsAudit.lean') -and
        $taskInput.path -notmatch '(^|/)VariableMaster(Execution|Instance|Futures)\.lean$') {
      throw "Unrelated scientific input changed: $($taskInput.path)"
    }
    if ($taskChanged -and $taskInput.path -match '\.(lean|md|py|ps1|sh|toml|tsv|json)$') {
      $taskDiagnostics = @(& git -c core.autocrlf=false -c core.safecrlf=false diff --no-index --check -- NUL $taskInput.path 2>&1)
      $taskExit = $LASTEXITCODE
      if ($taskExit -notin @(0, 1) -or $taskDiagnostics.Count -ne 0) {
        throw "Whitespace check failed: $($taskInput.path); $taskDiagnostics"
      }
      "WHITESPACE_OK $($taskInput.path)" | Add-Content -LiteralPath (Join-Path $taskEvidence 'new-text-check.log')
    }
    if ($taskInput.path.EndsWith('.md')) {
      $taskDocument = Join-Path $taskRoot $taskInput.path
      $taskContent = Get-Content -LiteralPath $taskDocument -Raw
      foreach ($taskMatch in [regex]::Matches($taskContent, '\]\(([^)]+)\)')) {
        $taskLink = $taskMatch.Groups[1].Value.Trim()
        if ($taskLink -match '^(https?://|mailto:|#)') { continue }
        $taskLink = ($taskLink -split '#', 2)[0]
        if ($taskLink) {
          $taskTarget = Join-Path (Split-Path $taskDocument -Parent) $taskLink
          if (-not (Test-Path -LiteralPath $taskTarget)) { throw "Broken local link in $($taskInput.path): $taskLink" }
        }
      }
    }
  }
  $taskAfter = @(Get-TaskInputs)
  $taskAfter | ConvertTo-Json -Depth 5 | Set-Content -LiteralPath (Join-Path $taskEvidence 'inputs-after.json')
  if (($taskBefore | ConvertTo-Json -Depth 5 -Compress) -cne ($taskAfter | ConvertTo-Json -Depth 5 -Compress)) {
    throw 'Inputs changed during the confirmatory run'
  }
  [pscustomobject]@{ status = 'LOCAL_CHECKS_PASSED'; inputCount = $taskBefore.Count;
    scriptSha256 = $taskScriptHash; independentAudit = $false; evidence = $taskEvidence } |
    ConvertTo-Json | Set-Content -LiteralPath (Join-Path $taskEvidence 'result.json')
  Write-Output "LOCAL_CHECKS_PASSED $taskEvidence"
} finally { Pop-Location }
