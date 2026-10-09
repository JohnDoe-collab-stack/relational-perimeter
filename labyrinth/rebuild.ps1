param([string]$Python = 'python', [switch]$VerifyLean)
$ErrorActionPreference = 'Stop'
$taskRepoRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path

function Invoke-CheckedPython {
  param([string[]]$TaskArguments)
  & $Python -B -X utf8 @TaskArguments
  if ($LASTEXITCODE -ne 0) { throw "Python check failed: $($TaskArguments -join ' ')" }
}

Push-Location $taskRepoRoot
try {
  Invoke-CheckedPython -TaskArguments @('labyrinth/snapshot.py', '--verify')
  if ($VerifyLean) {
    & lake build *> labyrinth/evidence/roles-final-build.log
    if ($LASTEXITCODE -ne 0) { throw 'Repository build failed; see evidence/roles-final-build.log' }
    & lake env lean labyrinth/probes/FoundationalSeparators.lean.in *> labyrinth/evidence/roles-legacy-separators.log
    if ($LASTEXITCODE -ne 0) { throw 'Legacy separator probes failed' }
    & lake env lean research/agents/referee-foundations/IndependentProbes.lean.in *> labyrinth/evidence/roles-legacy-referee-probes.log
    if ($LASTEXITCODE -ne 0) { throw 'Legacy independent probes failed' }
    & lake env lean research/agents/referee-positive-foundations/IndependentProbes.lean.in *> labyrinth/evidence/roles-positive-referee-probes.log
    if ($LASTEXITCODE -ne 0) { throw 'Positive independent probes failed' }
    & lake env lean research/agents/referee-closing-boundary/IndependentProbes.lean.in *> labyrinth/evidence/roles-closing-referee-probes.log
    if ($LASTEXITCODE -ne 0) { throw 'Closing-boundary independent probes failed' }
    & lake env lean research/agents/referee-positive-generation/IndependentProbes.lean.in *> labyrinth/evidence/roles-generation-referee-probes.log
    if ($LASTEXITCODE -ne 0) { throw 'Positive-generation independent probes failed' }
    & lake env lean research/agents/referee-signature-transport/IndependentProbes.lean.in *> labyrinth/evidence/roles-signature-referee-probes.log
    if ($LASTEXITCODE -ne 0) { throw 'Full signature independent probes failed' }
    & lake env lean research/agents/referee-circular-roles/IndependentProbes.lean.in *> labyrinth/evidence/roles-referee-probes.log
    if ($LASTEXITCODE -ne 0) { throw 'Circular role independent probes failed' }
    foreach ($taskLog in @('labyrinth/evidence/roles-final-build.log','labyrinth/evidence/roles-legacy-separators.log','labyrinth/evidence/roles-legacy-referee-probes.log','labyrinth/evidence/roles-positive-referee-probes.log','labyrinth/evidence/roles-closing-referee-probes.log','labyrinth/evidence/roles-generation-referee-probes.log','labyrinth/evidence/roles-signature-referee-probes.log','labyrinth/evidence/roles-referee-probes.log')) {
      if ((Get-Content -LiteralPath $taskLog -Raw) -match 'depends on axioms:|sorryAx') {
        throw "Axiom audit failure: $taskLog"
      }
    }
  }
  Invoke-CheckedPython -TaskArguments @('labyrinth/check_foundations.py')
  Invoke-CheckedPython -TaskArguments @('labyrinth/lab.py', 'check')
  Invoke-CheckedPython -TaskArguments @('labyrinth/lab.py', 'build')
  Invoke-CheckedPython -TaskArguments @('labyrinth/render_foundations.py')
} finally { Pop-Location }
