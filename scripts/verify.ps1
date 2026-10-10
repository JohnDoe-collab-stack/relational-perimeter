$ErrorActionPreference = "Stop"

$repoRoot = (Resolve-Path (Join-Path $PSScriptRoot "..")).Path
$pythonCommand = $env:RELATIONAL_PERIMETER_PYTHON
if (-not $pythonCommand) {
  $pythonCommand = (Get-Command python3 -ErrorAction SilentlyContinue).Source
}
if (-not $pythonCommand) { throw "Python 3 is required for documentation and compiled-code checks" }
& $pythonCommand (Join-Path $PSScriptRoot "check-scientific-docs.py") --self-test
if ($LASTEXITCODE -ne 0) { throw "scientific documentation self-test failed" }
& $pythonCommand (Join-Path $PSScriptRoot "check-scientific-docs.py") --static
if ($LASTEXITCODE -ne 0) { throw "scientific documentation check failed" }

Push-Location $repoRoot
try {
  $relativeLeanFiles = @(& git ls-files --cached --others --exclude-standard -- '*.lean') |
    Where-Object { Test-Path -LiteralPath (Join-Path $repoRoot $_) -PathType Leaf } |
    Sort-Object
  if ($LASTEXITCODE -ne 0) { throw "git ls-files failed" }
} finally {
  Pop-Location
}
$leanFiles = $relativeLeanFiles | ForEach-Object { Get-Item -LiteralPath (Join-Path $repoRoot $_) }

& (Join-Path $PSScriptRoot "check-import-boundaries.ps1") --self-test
if ($LASTEXITCODE -ne 0) { throw "import-boundary self-test failed" }
& (Join-Path $PSScriptRoot "check-import-boundaries.ps1")
if ($LASTEXITCODE -ne 0) { throw "import-boundary check failed" }
& (Join-Path $PSScriptRoot "check-import-boundaries.ps1") "scripts/constitutive-normalizer-core-import-boundaries.txt"
if ($LASTEXITCODE -ne 0) { throw "constitutive core import-boundary check failed" }
& (Join-Path $PSScriptRoot "check-import-boundaries.ps1") "scripts/executed-history-import-boundaries.txt"
if ($LASTEXITCODE -ne 0) { throw "executed history import-boundary check failed" }
& (Join-Path $PSScriptRoot "check-import-boundaries.ps1") "scripts/measured-accounting-import-boundaries.txt"
if ($LASTEXITCODE -ne 0) { throw "measured accounting import-boundary check failed" }
& (Join-Path $PSScriptRoot "check-stratification.ps1") --self-test
if ($LASTEXITCODE -ne 0) { throw "stratification parser self-test failed" }
& (Join-Path $PSScriptRoot "check-stratification.ps1")
if ($LASTEXITCODE -ne 0) { throw "stratification check failed" }

$forbiddenTerms =
  '\b(axiom|unsafe|noncomputable|Classical|propext|Quot\.sound|native_decide|implemented_by|sorry|admit)\b'
$forbiddenArchitecture =
  '\b(NPAndOrP|RequestProject|LoggedAlgebra|ConstitutivePersistence|IteratedConstitutivePersistence|StructuralEntrypoint)\b|(?m)^\s*(import|open)\s+(Alignment|Foundations)(\.|\s|$)'

foreach ($file in $leanFiles) {
  $source = Get-Content -LiteralPath $file.FullName -Raw
  $beginCount = ([regex]::Matches($source, '/- AXIOM_AUDIT_BEGIN -/')).Count
  $endCount = ([regex]::Matches($source, '/- AXIOM_AUDIT_END -/')).Count

  if ($beginCount -ne 1 -or $endCount -ne 1) {
    throw "$($file.FullName): expected exactly one AXIOM_AUDIT block"
  }
  if ($source -cnotmatch '/- AXIOM_AUDIT_END -/\s*\z') {
    throw "$($file.FullName): AXIOM_AUDIT block is not at end of file"
  }
  if ($source -cmatch $forbiddenTerms) {
    throw "$($file.FullName): forbidden Lean construct detected: $($Matches[0])"
  }
  if ($source -cmatch $forbiddenArchitecture) {
    throw "$($file.FullName): rejected migration dependency detected: $($Matches[0])"
  }
}

Push-Location $repoRoot
try {
  $buildOutput = @(& lake build 2>&1)
  $buildOutput | ForEach-Object { Write-Output $_ }
  if ($LASTEXITCODE -ne 0) {
    throw "lake build failed with exit code $LASTEXITCODE"
  }
  $joinedOutput = $buildOutput -join "`n"
  if ($joinedOutput -match 'warning:') {
    throw "Lean warning detected in lake build output"
  }
  if ($joinedOutput -match 'depends on axioms:|sorryAx') {
    throw "axiom audit failure detected in lake build output"
  }
  $expectedModules = $leanFiles.Count - 1
  $sweepLines = [regex]::Matches($joinedOutput, 'ALL_CONSTANTS_OK constants=[0-9]+ modules=[0-9]+ generatedExceptions=[0-9]+ writtenExceptions=[0-9]+')
  if ($sweepLines.Count -ne 1 -or $sweepLines[0].Value.TrimEnd("`r") -notmatch
      "^ALL_CONSTANTS_OK constants=[0-9]+ modules=$expectedModules generatedExceptions=[0-9]+ writtenExceptions=0$") {
    throw "Missing or incomplete exhaustive constant audit (including all test modules)"
  }
  & $pythonCommand (Join-Path $PSScriptRoot "check-scientific-docs.py") --lean
  if ($LASTEXITCODE -ne 0) { throw "scientific Lean reference check failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-unified-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "compiled-code dependency check failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-agent-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "compiled agent dependency check failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-documentary-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "compiled documentary sharing check failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "run-documentary-smoke.py")
  if ($LASTEXITCODE -ne 0) { throw "documentary smoke failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-documentary-master-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "compiled documentary master sharing check failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "run-documentary-master-smoke.py")
  if ($LASTEXITCODE -ne 0) { throw "documentary master smoke failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-documentary-dossier-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "compiled documentary dossier sharing check failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "run-documentary-dossier-smoke.py")
  if ($LASTEXITCODE -ne 0) { throw "documentary dossier smoke failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-documentary-deduction-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "compiled documentary deduction sharing check failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "run-documentary-deduction-smoke.py")
  if ($LASTEXITCODE -ne 0) { throw "documentary deduction smoke failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-documentary-program-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "compiled documentary program sharing check failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "run-documentary-program-smoke.py")
  if ($LASTEXITCODE -ne 0) { throw "documentary program smoke failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-documentary-adaptive-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "compiled documentary adaptive sharing check failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "run-documentary-adaptive-smoke.py")
  if ($LASTEXITCODE -ne 0) { throw "documentary adaptive smoke failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-documentary-memory-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "compiled documentary memory sharing check failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "run-documentary-memory-smoke.py")
  if ($LASTEXITCODE -ne 0) { throw "documentary memory smoke failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-documentary-checkpoint-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "compiled documentary checkpoint check failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "run-documentary-checkpoint-smoke.py")
  if ($LASTEXITCODE -ne 0) { throw "documentary physical checkpoint smoke failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-documentary-portable-store-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "documentary portable store compiled dependencies failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "run-documentary-portable-store-smoke.py")
  if ($LASTEXITCODE -ne 0) { throw "documentary portable store smoke failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-restoration-components-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "restoration components compiled dependencies failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "run-restoration-components-smoke.py")
  if ($LASTEXITCODE -ne 0) { throw "restoration components smoke failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-documentary-control-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "documentary control compiled dependencies failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "run-documentary-control-smoke.py")
  if ($LASTEXITCODE -ne 0) { throw "documentary control component smoke failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-master-recipes-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "master recipes compiled dependencies failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "run-master-recipes-smoke.py")
  if ($LASTEXITCODE -ne 0) { throw "master recipes smoke failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-assignment-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "assignment compiled dependencies failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "run-assignment-restart-smoke.py")
  if ($LASTEXITCODE -ne 0) { throw "assignment component restart failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-sequential-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "dependent assignment compiled dependencies failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "run-sequential-restart-smoke.py")
  if ($LASTEXITCODE -ne 0) { throw "dependent assignment component restart failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-state-assembly-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "state and assembled checkpoint compiled dependencies failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "run-state-assembly-smoke.py")
  if ($LASTEXITCODE -ne 0) { throw "state and assembled checkpoint component restart failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-documentary-recovery-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "compiled documentary recovery sharing check failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "run-documentary-recovery-smoke.py")
  if ($LASTEXITCODE -ne 0) { throw "documentary recovery smoke failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-continuation-signature-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "compiled signature dependency check failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-variable-master-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "compiled variable-master sharing check failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-integrated-machine-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "compiled integrated machine sharing check failed" }
  & (Join-Path $PSScriptRoot "check-expected-failures.ps1")
  if ($LASTEXITCODE -ne 0) { throw "expected-failure check failed" }

  foreach ($file in $leanFiles) {
    $relative = $file.FullName.Substring($repoRoot.Length).TrimStart('\', '/')
    $oleanRelative = [IO.Path]::ChangeExtension($relative, ".olean")
    $oleanPath = Join-Path $repoRoot (Join-Path ".lake/build/lib/lean" $oleanRelative)
    if (-not (Test-Path -LiteralPath $oleanPath)) {
      throw "$($file.FullName): lake build produced no corresponding olean"
    }
  }
  & git diff --check
  if ($LASTEXITCODE -ne 0) {
    throw "git diff --check failed"
  }
} finally {
  Pop-Location
}

Write-Output "Verified $($leanFiles.Count) Lean files: build, constructivity, audit blocks, import boundaries, and migration boundaries are clean."
