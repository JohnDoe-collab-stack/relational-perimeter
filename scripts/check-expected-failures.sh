#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

if command -v lake >/dev/null 2>&1; then
  lake_command=(lake)
elif [[ -x "$HOME/.elan/bin/lake" ]]; then
  lake_command=("$HOME/.elan/bin/lake")
elif [[ -n "${USERPROFILE:-}" ]] && command -v cygpath >/dev/null 2>&1 &&
    [[ -x "$(cygpath -u "$USERPROFILE")/.elan/bin/lake.exe" ]]; then
  lake_command=("$(cygpath -u "$USERPROFILE")/.elan/bin/lake.exe")
else
  echo 'lake was not found in PATH or in the default elan installation' >&2
  exit 1
fi

check_expected_failure() {
  local fixture="$1"
  local expected="$2"
  local output status
  set +e
  output="$("${lake_command[@]}" env lean "$fixture" 2>&1)"
  status=$?
  set -e
  if [[ "$status" == 0 ]]; then
    echo "$fixture: unexpectedly compiled" >&2
    exit 1
  fi
  if [[ "$output" != *"$expected"* ]]; then
    echo "$fixture: failed for an unexpected reason" >&2
    echo "$output" >&2
    exit 1
  fi
}

check_expected_failure \
  'Tests/ExpectedFailure/PrivateConstitutiveNormalizerCertificate.lean.fail' \
  'Unknown constant `ConstitutiveSearch.EndogenousDecomposition.ConstitutiveNormalizerSuccinctness.mk`'
check_expected_failure \
  'Tests/ExpectedFailure/PrivateConstitutiveExtensiveSeparationCertificate.lean.fail' \
  'Unknown constant `ConstitutiveSearch.EndogenousDecomposition.ConstitutiveExtensiveSeparationCertificate.mk`'
check_expected_failure \
  'Tests/ExpectedFailure/PrivateExecutedCausalNormalization.lean.fail' \
  'Unknown constant `ConstitutiveSearch.EndogenousDecomposition.ExecutedCausalNormalization.mk`'
check_expected_failure \
  'Tests/ExpectedFailure/PrivateExactExecutedOperationalRegime.lean.fail' \
  'Unknown constant `ConstitutiveSearch.EndogenousDecomposition.ExactExecutedOperationalRegime.mk`'
check_expected_failure \
  'Tests/ExpectedFailure/PrivateExecutedStageOperationalProduction.lean.fail' \
  'Unknown constant `ConstitutiveSearch.EndogenousDecomposition.ExecutedStageOperationalProduction.mk`'
check_expected_failure \
  'Tests/ExpectedFailure/DiscoveredTransportCannotReplaceAuthoritativeInstruction.lean.fail' \
  'but is expected to have type'
check_expected_failure \
  'Tests/ExpectedFailure/InstructionIgnoringInterpreterCannotMeetSemanticSpecification.lean.fail' \
  'Not a definitional equality'
check_expected_failure \
  'Tests/ExpectedFailure/ForeignInstructionProfileCannotBeReused.lean.fail' \
  'Not a definitional equality'
check_expected_failure \
  'Tests/ExpectedFailure/RetainedDecisionCannotReplaceTransformedDecision.lean.fail' \
  'but is expected to have type'
check_expected_failure \
  'Tests/ExpectedFailure/SourceIgnoringNormalizationCannotSupplyTrace.lean.fail' \
  'ExecutedRoleProfileReduction reduction _source (normalization.target chosen)'
check_expected_failure \
  'Tests/ExpectedFailure/PrescribedTargetCannotRecoverTraceAfterwards.lean.fail' \
  'ExecutedRoleProfileReduction reduction source prescribed'
check_expected_failure \
  'Tests/ExpectedFailure/IndependentUnitRegimeCannotReplaceExecutedRegime.lean.fail' \
  'is not definitionally equal to the right-hand side'
check_expected_failure \
  'Tests/ExpectedFailure/PrivateActionProducedOperationalTarget.lean.fail' \
  'Unknown constant `ConstitutiveSearch.EndogenousDecomposition.ActionProducedOperationalTarget.mk`'
check_expected_failure \
  'Tests/ExpectedFailure/PrivateExactCausalExponentialTarget.lean.fail' \
  'Unknown constant `ConstitutiveSearch.EndogenousDecomposition.ExactCausalExponentialTarget.mk`'

echo 'Verified expected failures: scientific-certificate and causal-construction privacy, instruction-indexed profiles, authoritative collision anchor, semantic instruction use, occurrence-and-target-indexed decisions, source-and-target-indexed traces, and rejection of an independent Unit regime.'
