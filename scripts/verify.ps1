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
& $pythonCommand (Join-Path $PSScriptRoot "check-neural-c1-c17-regression-floor.py")
if ($LASTEXITCODE -ne 0) { throw "neural C1-C17 regression floor check failed" }
& $pythonCommand (Join-Path $PSScriptRoot "check-neural-g1-g10-regression-floor.py")
if ($LASTEXITCODE -ne 0) { throw "neural G1-G10 regression floor check failed" }
& $pythonCommand (Join-Path $PSScriptRoot "check-neural-block-negative-fixtures.py")
if ($LASTEXITCODE -ne 0) { throw "neural per-block negative-fixture check failed" }
& $pythonCommand (Join-Path $PSScriptRoot "check-neural-comparison-protocol-v4.py") --self-test
if ($LASTEXITCODE -ne 0) { throw "neural comparison protocol v4 self-test failed" }
& $pythonCommand (Join-Path $PSScriptRoot "check-neural-comparison-adapters-v6-archive.py") --self-test
if ($LASTEXITCODE -ne 0) { throw "neural comparison adapters v6 archive self-test failed" }
& $pythonCommand (Join-Path $PSScriptRoot "check-neural-comparison-adapters-v6-archive.py")
if ($LASTEXITCODE -ne 0) { throw "neural comparison adapters v6 archive check failed" }
& $pythonCommand (Join-Path $PSScriptRoot "check-neural-joint-protocol-v9.py") --self-test
if ($LASTEXITCODE -ne 0) { throw "neural joint protocol v9 self-test failed" }
& $pythonCommand (Join-Path $PSScriptRoot "check-neural-joint-protocol-v9.py")
if ($LASTEXITCODE -ne 0) { throw "neural joint protocol v9 check failed" }
& $pythonCommand (Join-Path $PSScriptRoot "check-neural-complete-comparison-v10.py") --self-test --allow-results
if ($LASTEXITCODE -ne 0) { throw "neural complete comparison v10 self-test failed" }
& $pythonCommand (Join-Path $PSScriptRoot "check-neural-complete-comparison-v10.py") --allow-results
if ($LASTEXITCODE -ne 0) { throw "neural complete comparison v10 check failed" }
& $pythonCommand (Join-Path $PSScriptRoot "check-compiled-neural-checker-measurement.py") --self-test
if ($LASTEXITCODE -ne 0) { throw "compiled neural checker measurement self-test failed" }
& $pythonCommand (Join-Path $PSScriptRoot "check-compiled-neural-checker-measurement.py")
if ($LASTEXITCODE -ne 0) { throw "compiled neural checker measurement check failed" }
& $pythonCommand (Join-Path $PSScriptRoot "check-compiled-parameterized-neural-scaling-v8.py") --archive-metadata --self-test
if ($LASTEXITCODE -ne 0) { throw "parameterized neural scaling v8 self-test failed" }
& $pythonCommand (Join-Path $PSScriptRoot "check-compiled-parameterized-neural-scaling-v8.py") --archive-metadata
if ($LASTEXITCODE -ne 0) { throw "parameterized neural scaling v8 check failed" }
& $pythonCommand (Join-Path $PSScriptRoot "check-complete-property-scaling-v11.py") --allow-draft --self-test
if ($LASTEXITCODE -ne 0) { throw "complete-property neural scaling v11 check failed" }
& $pythonCommand (Join-Path $PSScriptRoot "check-causal-complete-property-scaling-v12.py") --allow-draft --self-test
if ($LASTEXITCODE -ne 0) { throw "causal complete-property neural scaling v12 check failed" }
& $pythonCommand (Join-Path $PSScriptRoot "check-independent-capability-comparison-v13.py") --allow-draft --self-test
if ($LASTEXITCODE -ne 0) { throw "oracle-independent capability comparison v13 self-test failed" }
& $pythonCommand (Join-Path $PSScriptRoot "check-independent-capability-comparison-v13.py") --allow-draft
if ($LASTEXITCODE -ne 0) { throw "oracle-independent capability comparison v13 check failed" }
& $pythonCommand (Join-Path $PSScriptRoot "check-independent-neural-artifact.py")
if ($LASTEXITCODE -ne 0) { throw "independent neural artifact check failed" }
& $pythonCommand (Join-Path $PSScriptRoot "check-final-neural-campaign.py")
if ($LASTEXITCODE -ne 0) { throw "final neural mutation and scaling campaign check failed" }

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
& (Join-Path $PSScriptRoot "check-import-boundaries.ps1") "scripts/godel-runtime-core-import-boundaries.txt"
if ($LASTEXITCODE -ne 0) { throw "Godel runtime import-boundary check failed" }
foreach ($boundary in @("godel-positive-core", "godel-operational-h1", "godel-operational-closure", "godel-perimetral")) {
  & (Join-Path $PSScriptRoot "check-import-boundaries.ps1") "scripts/$boundary-import-boundaries.txt"
  if ($LASTEXITCODE -ne 0) { throw "$boundary import-boundary check failed" }
}
& (Join-Path $PSScriptRoot "check-import-boundaries.ps1") "scripts/godel-theory-progression-foundation-import-boundaries.txt"
if ($LASTEXITCODE -ne 0) { throw "Godel theory-progression foundation import-boundary check failed" }
foreach ($boundary in @("tarski-continuation", "tarski-diagonal", "tarski-operational-closure", "tarski-ha")) {
  & (Join-Path $PSScriptRoot "check-import-boundaries.ps1") "scripts/$boundary-import-boundaries.txt"
  if ($LASTEXITCODE -ne 0) { throw "$boundary import-boundary check failed" }
}
& (Join-Path $PSScriptRoot "check-import-boundaries.ps1") "scripts/continuation-exact-separation-import-boundaries.txt"
if ($LASTEXITCODE -ne 0) { throw "continuation exact-separation import-boundary check failed" }
foreach ($boundary in @("continuation-directed-incompatibility", "continuation-directed-obstruction", "positive-directed-composition")) {
  & (Join-Path $PSScriptRoot "check-import-boundaries.ps1") "scripts/$boundary-import-boundaries.txt"
  if ($LASTEXITCODE -ne 0) { throw "$boundary import-boundary check failed" }
}
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
  $buildOutput = @(& lake -K 'moreLeanArgs=["-M=8192"]' build 2>&1)
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
  $sweepLines = [regex]::Matches($joinedOutput, 'ALL_CONSTANTS_OK constants=[0-9]+ modules=[0-9]+ generatedExceptions=[0-9]+ writtenExceptions=[0-9]+')
  if ($sweepLines.Count -ne 1 -or $sweepLines[0].Value.TrimEnd("`r") -notmatch
      '^ALL_CONSTANTS_OK constants=[0-9]+ modules=[0-9]+ generatedExceptions=[0-9]+ writtenExceptions=0$') {
    throw "Missing or incomplete primary exhaustive constant audit"
  }
  & $pythonCommand (Join-Path $PSScriptRoot "check-executable-constant-audits.py") --self-test
  if ($LASTEXITCODE -ne 0) { throw "executable constant-audit self-test failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-executable-constant-audits.py")
  if ($LASTEXITCODE -ne 0) { throw "executable constant-audit union failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-scientific-docs.py") --lean
  if ($LASTEXITCODE -ne 0) { throw "scientific Lean reference check failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-unified-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "compiled-code dependency check failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-agent-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "compiled agent dependency check failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-continuation-signature-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "compiled signature dependency check failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-variable-master-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "compiled variable-master sharing check failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-integrated-machine-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "compiled integrated machine sharing check failed" }
  & $pythonCommand (Join-Path $PSScriptRoot "check-independent-comparison-codegen.py")
  if ($LASTEXITCODE -ne 0) { throw "oracle-independent comparison dependency check failed" }
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
