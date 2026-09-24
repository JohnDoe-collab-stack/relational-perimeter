$ErrorActionPreference = "Stop"

$forbidden = '(?<![A-Za-z0-9_])(noncomputable|unsafe|axiom|sorry|admit|Classical|propext|Quot\.sound)(?![A-Za-z0-9_])'
$violations = @()

Get-ChildItem -Path . -Recurse -Filter *.lean |
  Where-Object { $_.FullName -notmatch '[\\/]\.lake[\\/]' } |
  ForEach-Object {
    $matches = Select-String -LiteralPath $_.FullName -Pattern $forbidden -AllMatches -CaseSensitive
    foreach ($match in $matches) {
      $relative = [IO.Path]::GetRelativePath((Get-Location).Path, $_.FullName)
      $violations += "${relative}:$($match.LineNumber): $($match.Line.Trim())"
    }
  }

if ($violations.Count -gt 0) {
  $violations | ForEach-Object { Write-Error $_ }
  exit 1
}

Write-Output "Constructivity scan passed."
