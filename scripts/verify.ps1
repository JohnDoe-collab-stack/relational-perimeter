$ErrorActionPreference = "Stop"

$repoRoot = (Resolve-Path (Join-Path $PSScriptRoot "..")).Path
$leanFiles = Get-ChildItem -LiteralPath $repoRoot -Recurse -File -Filter "*.lean" |
  Where-Object { $_.FullName -notlike "*\.lake\*" }

$forbiddenTerms =
  '(?m)^\s*(axiom|unsafe)\s|\b(noncomputable|Classical|propext|Quot\.sound|native_decide|implemented_by|sorry|admit)\b'
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
  if ($joinedOutput -match 'depends on axioms:|sorryAx') {
    throw "axiom audit failure detected in lake build output"
  }
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

Write-Output "Verified $($leanFiles.Count) Lean files: build, constructivity, audit blocks, and migration boundaries are clean."
