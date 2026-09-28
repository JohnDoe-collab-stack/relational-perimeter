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
    "Tests/ExpectedFailure/PrivateConstitutiveExtensiveSeparationCertificate.lean.fail" `
    'Unknown constant `ConstitutiveSearch.EndogenousDecomposition.ConstitutiveExtensiveSeparationCertificate.mk`'
  Test-ExpectedLeanFailure `
    "Tests/ExpectedFailure/PrivateExecutedCausalNormalization.lean.fail" `
    'Unknown constant `ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.mk`'
  Test-ExpectedLeanFailure `
    "Tests/ExpectedFailure/PrivateExactExecutedOperationalRegime.lean.fail" `
    'Unknown constant `ConstitutiveSearch.EndogenousDecomposition.ExactExecutedOperationalRegime.mk`'
  Test-ExpectedLeanFailure `
    "Tests/ExpectedFailure/PrivateExecutedStageOperationalProduction.lean.fail" `
    'Unknown constant `ConstitutiveSearch.EndogenousDecomposition.ExecutedStageOperationalProduction.mk`'
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
  Test-ExpectedLeanFailure `
    "Tests/ExpectedFailure/SourceIgnoringNormalizationCannotSupplyTrace.lean.fail" `
    "ExecutedRoleProfileReduction reduction _source (normalization.target chosen)"
  Test-ExpectedLeanFailure `
    "Tests/ExpectedFailure/PrescribedTargetCannotRecoverTraceAfterwards.lean.fail" `
    "ExecutedRoleProfileReduction reduction source prescribed"
  Test-ExpectedLeanFailure `
    "Tests/ExpectedFailure/IndependentUnitRegimeCannotReplaceExecutedRegime.lean.fail" `
    "is not definitionally equal to the right-hand side"
  Test-ExpectedLeanFailure `
    "Tests/ExpectedFailure/PrivateActionProducedOperationalTarget.lean.fail" `
    'Unknown constant `ConstitutiveSearch.EndogenousDecomposition.ActionProducedOperationalTarget.mk`'
  Test-ExpectedLeanFailure `
    "Tests/ExpectedFailure/PrivateExactCausalExponentialTarget.lean.fail" `
    'Unknown constant `ConstitutiveSearch.EndogenousDecomposition.ExactCausalExponentialTarget.mk`'
} finally {
  Pop-Location
}

Write-Output "Verified expected failures: scientific-certificate and causal-construction privacy, instruction-indexed profiles, authoritative collision anchor, semantic instruction use, occurrence-and-target-indexed decisions, source-and-target-indexed traces, and rejection of an independent Unit regime."
$global:LASTEXITCODE = 0
