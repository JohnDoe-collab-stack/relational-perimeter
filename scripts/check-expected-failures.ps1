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
    "Tests/ExpectedFailure/PrivateExecutedRoleObligationRegime.lean.fail" `
    'Unknown constant `ConstitutiveSearch.EndogenousDecomposition.ExecutedRoleObligationRegime.mk`'
  Test-ExpectedLeanFailure `
    "Tests/ExpectedFailure/PrivateConstitutiveExtensiveSeparationCertificate.lean.fail" `
    'Unknown constant `ConstitutiveSearch.EndogenousDecomposition.ConstitutiveExtensiveSeparationCertificate.mk`'
  Test-ExpectedLeanFailure `
    "Tests/ExpectedFailure/PrivateCausallyAdmittedRoleRegime.lean.fail" `
    'Unknown constant `ConstitutiveSearch.EndogenousDecomposition.CausallyAdmittedRoleRegime.mk`'
  Test-ExpectedLeanFailure `
    "Tests/ExpectedFailure/DiscoveredTransportCannotReplaceAuthoritativeInstruction.lean.fail" `
    "but is expected to have type"
  Test-ExpectedLeanFailure `
    "Tests/ExpectedFailure/InstructionIgnoringInterpreterCannotMeetSemanticSpecification.lean.fail" `
    "Not a definitional equality"
  Test-ExpectedLeanFailure `
    "Tests/ExpectedFailure/ForeignInstructionProfileCannotBeReused.lean.fail" `
    "Not a definitional equality"
  Test-ExpectedLeanFailure `
    "Tests/ExpectedFailure/RetainedDecisionCannotReplaceTransformedDecision.lean.fail" `
    "but is expected to have type"
} finally {
  Pop-Location
}

Write-Output "Verified expected failures: scientific-certificate privacy, admitted-regime privacy, causal-regime privacy, instruction-indexed profiles, authoritative collision anchor, semantic instruction use, and occurrence-indexed reduction decisions."
$global:LASTEXITCODE = 0
