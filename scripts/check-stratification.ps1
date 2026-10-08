$ErrorActionPreference = "Stop"

$repoRoot = (Resolve-Path (Join-Path $PSScriptRoot "..")).Path
$manifestPath = Join-Path $repoRoot "scripts/stratification.tsv"

if ($env:RELATIONAL_PERIMETER_PYTHON) {
  $pythonCommand = $env:RELATIONAL_PERIMETER_PYTHON
} elseif (Get-Command python3 -ErrorAction SilentlyContinue) {
  $pythonCommand = "python3"
} else {
  throw "Python 3 is required for stratification checks"
}

function Get-LeanImports {
  param([Parameter(Mandatory = $true)][string]$Source)
  $parsed = @($Source | & $pythonCommand (Join-Path $PSScriptRoot "lean_imports.py") --stdin)
  if ($LASTEXITCODE -ne 0) { throw "Lean import-header parsing failed" }
  return $parsed
}

if ($args.Count -gt 0 -and $args[0] -eq "--self-test") {
  $fixture = @'
/- import Forbidden.Direct
   /- import Forbidden.Nested -/
-/
-- import Forbidden.Line
import
  Allowed.Split
/- a comment between commands -/
import Allowed.Direct -- import Forbidden.Trailing
'@
  $actual = @(Get-LeanImports -Source $fixture)
  $expected = @("Allowed.Split", "Allowed.Direct")
  if (($actual -join ',') -ne ($expected -join ',')) {
    throw "stratification parser self-test failed: $($actual -join ',')"
  }
  exit 0
}

$entries = @{}
$lineNumber = 0
foreach ($line in Get-Content -LiteralPath $manifestPath) {
  $lineNumber += 1
  if ($line.Length -eq 0 -or $line.StartsWith('#')) { continue }
  $parts = $line -split "`t", 4
  if ($parts.Count -ne 4) { throw "$manifestPath`:${lineNumber}: expected four tab-separated fields" }
  $module, $stratum, $status, $responsibility = $parts
  if ($entries.ContainsKey($module)) { throw "$manifestPath`:${lineNumber}: duplicate module $module" }
  if ($stratum -notin @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','API','A0','A1','A2','A3','A4','A5','A6','A7','A8','A9','A10','A11','A12','A13','A14','A15','A16','A17') -and
      $stratum -notmatch '^T[0-7]$' -and
      $stratum -notmatch '^H([0-9]|1[0-9]|2[0-3])$' -and
      $stratum -notmatch '^M([0-9]|1[0-9])$') {
    throw "$manifestPath`:${lineNumber}: unknown stratum $stratum"
  }
  if ($status -ne 'enforced') {
    throw "$manifestPath`:${lineNumber}: every production module must be enforced, found $status"
  }
  if ([string]::IsNullOrWhiteSpace($responsibility)) {
    throw "$manifestPath`:${lineNumber}: empty responsibility"
  }
  if (($stratum -eq 'API') -ne ($module -eq 'RelationalPerimeter')) {
    throw "$manifestPath`:${lineNumber}: API is reserved for the public root"
  }
  $isNumerical = $module -eq 'RelationalPerimeter.Relativity.ExactArithmetic' -or
    $module.StartsWith('RelationalPerimeter.Relativity.Arithmetic.') -or
    $module.StartsWith('RelationalPerimeter.Relativity.Analysis.')
  if (($stratum -match '^T[0-7]$') -ne $isNumerical) {
    throw "$manifestPath`:${lineNumber}: numerical strata and numerical modules must match"
  }
  $isLocalProduction = $module -eq 'RelationalPerimeter.Relativity' -or
    $module.StartsWith('RelationalPerimeter.Relativity.Production.')
  if (($stratum -match '^H([0-9]|1[0-9]|2[0-3])$') -ne $isLocalProduction) {
    throw "$manifestPath`:${lineNumber}: local-production strata and modules must match"
  }
  $entries[$module] = [pscustomobject]@{ Stratum = $stratum; Status = $status }
}

Push-Location $repoRoot
try {
  $relativeFiles = @(& git ls-files --cached --others --exclude-standard -- '*.lean') |
    Where-Object {
      $_ -notlike 'Tests/*' -and
      (Test-Path -LiteralPath (Join-Path $repoRoot $_) -PathType Leaf)
    } | Sort-Object
  if ($LASTEXITCODE -ne 0) { throw "git ls-files failed" }
} finally {
  Pop-Location
}

$filesByModule = @{}
$imports = @{}
foreach ($relative in $relativeFiles) {
  $module = $relative.Substring(0, $relative.Length - 5).Replace('\', '.').Replace('/', '.')
  $filesByModule[$module] = $relative
  $source = Get-Content -LiteralPath (Join-Path $repoRoot $relative) -Raw
  $imports[$module] = @(Get-LeanImports -Source $source)
  foreach ($dependency in $imports[$module]) {
    if ($dependency -eq 'Tests' -or $dependency.StartsWith('Tests.')) {
      throw "production module imports a test: $module -> $dependency"
    }
  }
}

$missing = @($filesByModule.Keys | Where-Object { -not $entries.ContainsKey($_) } | Sort-Object)
$stale = @($entries.Keys | Where-Object { -not $filesByModule.ContainsKey($_) } | Sort-Object)
if ($missing.Count -gt 0) { throw "unclassified production modules: $($missing -join ', ')" }
if ($stale.Count -gt 0) { throw "manifest modules without source: $($stale -join ', ')" }

$allowed = @{
  U = @('U')
  F = @('U','F')
  G = @('U','G')
  S = @('U','G','S')
  B = @('U','F','G','S','B')
  E = @('U','G','S','B','E')
  M = @('U','G','S','B','E','M')
  R = @('U','F','G','S','B','E','R')
  X = @('U','G','S','R','X')
  P = @('U','G','S','E','R','X','P')
  K = @('U','K')
  D = @('U','G','S','E','R','X','P','K','D')
  Q = @('U','F','G','S','B','E','M','R','X','P','K','D','Q')
  N = @('U','G','S','B','E','M','R','X','P','K','D','Q','N')
  A0 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N')
  A1 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0')
  A2 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1')
  A3 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1','A2')
  A4 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1','A2','A3')
  A5 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1','A2','A3','A4')
  A6 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1','A2','A3','A4','A5')
  A7 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1','A2','A3','A4','A5','A6')
  A8 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1','A2','A3','A4','A5','A6','A7')
  A9 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1','A2','A3','A4','A5','A6','A7','A8')
  A10 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1','A2','A3','A4','A5','A6','A7','A8','A9')
  A11 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1','A2','A3','A4','A5','A6','A7','A8','A9','A10')
  A12 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1','A2','A3','A4','A5','A6','A7','A8','A9','A10','A11')
  A13 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1','A2','A3','A4','A5','A6','A7','A8','A9','A10','A11','A12')
  A14 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1','A2','A3','A4','A5','A6','A7','A8','A9','A10','A11','A12','A13')
  A15 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1','A2','A3','A4','A5','A6','A7','A8','A9','A10','A11','A12','A13','A14')
  A16 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1','A2','A3','A4','A5','A6','A7','A8','A9','A10','A11','A12','A13','A14','A15')
  A17 = @('U','F','G','S','B','E','M','R','X','P','K','D','Q','N','A0','A1','A2','A3','A4','A5','A6','A7','A8','A9','A10','A11','A12','A13','A14','A15','A16')
}

# Machine strata are strictly downstream of scientific strata. M0..M19 can
# only read an earlier machine stratum; none is an unconstrained bucket.
$scientificStrata = @($allowed.Keys)
foreach ($rank in 0..19) {
  $lowerMachine = @(0..($rank - 1) | Where-Object { $_ -ge 0 -and $_ -lt $rank } | ForEach-Object { "M$_" })
  $allowed["M$rank"] = @($scientificStrata) + $lowerMachine
}

# Numerical utilities cannot import productions, foundations or the master.
# Local physical candidates may consume foundations and numerical utilities,
# but cannot consume the computational master or machine.
foreach ($rank in 0..7) {
  $allowed["T$rank"] = @(0..($rank - 1) | Where-Object { $_ -ge 0 -and $_ -lt $rank } | ForEach-Object { "T$_" })
}
foreach ($rank in 0..23) {
  $lowerPhysical = @(0..($rank - 1) | Where-Object { $_ -ge 0 -and $_ -lt $rank } | ForEach-Object { "H$_" })
  $allowed["H$rank"] = @('U','F') + @(0..6 | ForEach-Object { "T$_" }) + $lowerPhysical
}
$allowed['API'] = @($scientificStrata) + @(0..19 | ForEach-Object { "M$_" }) +
  @(0..7 | ForEach-Object { "T$_" }) + @(0..23 | ForEach-Object { "H$_" })

foreach ($root in ($entries.Keys | Sort-Object)) {
  $queue = [Collections.Generic.Queue[string]]::new()
  $queue.Enqueue($root)
  $paths = @{ $root = $root }
  while ($queue.Count -gt 0) {
    $current = $queue.Dequeue()
    foreach ($dependency in $imports[$current]) {
      if (-not $entries.ContainsKey($dependency)) { continue }
      $path = "$($paths[$current]) -> $dependency"
      if ($entries[$dependency].Stratum -notin $allowed[$entries[$current].Stratum]) {
        throw "forbidden stratification path ($($entries[$current].Stratum) -> $($entries[$dependency].Stratum)): $path"
      }
      if (-not $paths.ContainsKey($dependency)) {
        $paths[$dependency] = $path
        $queue.Enqueue($dependency)
      }
    }
  }
}

$publicRoots = @('SegmentedResidualRole','AbstractSegmentedTurning','ExactTypeTransport','StrongPerimetralTurning','RelationalPerimeter')
$reachable = @{}
$queue = [Collections.Generic.Queue[string]]::new()
foreach ($root in $publicRoots) {
  if (-not $entries.ContainsKey($root)) { throw "missing public root in manifest: $root" }
  $reachable[$root] = $true
  $queue.Enqueue($root)
}
while ($queue.Count -gt 0) {
  $current = $queue.Dequeue()
  foreach ($dependency in $imports[$current]) {
    if ($entries.ContainsKey($dependency) -and -not $reachable.ContainsKey($dependency)) {
      $reachable[$dependency] = $true
      $queue.Enqueue($dependency)
    }
  }
}
$orphans = @($entries.Keys | Where-Object { -not $reachable.ContainsKey($_) } | Sort-Object)
if ($orphans.Count -gt 0) { throw "production modules unreachable from public Lake roots: $($orphans -join ', ')" }

Write-Output "Verified stratification inventory: $($entries.Count) production modules, all enforced, no orphan."
