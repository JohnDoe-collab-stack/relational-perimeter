$ErrorActionPreference = "Stop"

$failures = @()
Get-ChildItem -Path . -Recurse -Filter *.lean |
  Where-Object { $_.FullName -notmatch '[\\/]\.lake[\\/]' } |
  ForEach-Object {
    $text = Get-Content -Raw -LiteralPath $_.FullName
    $beginCount = ([regex]::Matches($text, 'AXIOM_AUDIT_BEGIN')).Count
    $endCount = ([regex]::Matches($text, 'AXIOM_AUDIT_END')).Count
    $isFinal = $text.TrimEnd().EndsWith('/- AXIOM_AUDIT_END -/')
    if ($beginCount -ne 1 -or $endCount -ne 1 -or -not $isFinal) {
      $relative = [IO.Path]::GetRelativePath((Get-Location).Path, $_.FullName)
      $failures += "${relative}: begin=${beginCount}, end=${endCount}, final=${isFinal}"
    }
  }

if ($failures.Count -gt 0) {
  $failures | ForEach-Object { Write-Error $_ }
  exit 1
}

$buildOutput = & lake build 2>&1
$buildStatus = $LASTEXITCODE
$buildOutput | ForEach-Object { Write-Output $_ }
if ($buildStatus -ne 0) {
  exit $buildStatus
}

$joined = $buildOutput -join "`n"
if ($joined -match 'depends on axioms:') {
  Write-Error "At least one audited declaration depends on axioms."
  exit 1
}
if ($joined -match '(?m)^warning:') {
  Write-Error "The Lean build emitted at least one warning."
  exit 1
}

Write-Output "Axiom-audit structure and warning-free build output passed."
