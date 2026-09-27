$ErrorActionPreference = "Stop"

$repoRoot = (Resolve-Path (Join-Path $PSScriptRoot "..")).Path

function Test-ExpectedLeanFailure {
  param(
    [Parameter(Mandatory = $true)][string]$RelativeFixture,
    [Parameter(Mandatory = $true)][string]$ExpectedText
  )
  $fixture = Join-Path $repoRoot $RelativeFixture
  $output = @(& lake env lean $fixture 2>&1)
  $status = $LASTEXITCODE
  if ($status -eq 0) {
    throw "$fixture`: unexpectedly compiled"
  }
  $joined = $output -join "`n"
  if (-not $joined.Contains($ExpectedText)) {
    throw "$fixture`: failed for an unexpected reason`n$joined"
  }
}

Push-Location $repoRoot
try {
  Test-ExpectedLeanFailure `
    "Tests/ExpectedFailure/PrivateConstitutiveNormalizerCertificate.lean.fail" `
    'Unknown constant `ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerSuccinctness.mk`'
  Test-ExpectedLeanFailure `
    "Tests/ExpectedFailure/DiscoveredTransportCannotReplaceAuthoritativeInstruction.lean.fail" `
    "but is expected to have type"
  Test-ExpectedLeanFailure `
    "Tests/ExpectedFailure/InstructionIgnoringInterpreterCannotMeetSemanticSpecification.lean.fail" `
    "Not a definitional equality"
  Test-ExpectedLeanFailure `
    "Tests/ExpectedFailure/ForeignInstructionProfileCannotBeReused.lean.fail" `
    "Not a definitional equality"
} finally {
  Pop-Location
}

Write-Output "Verified expected failures: certificate privacy, instruction-indexed profiles, authoritative collision anchor, and semantic instruction use."
$global:LASTEXITCODE = 0
