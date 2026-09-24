$ErrorActionPreference = "Stop"

$failures = @()
Get-ChildItem -Path . -Recurse -Filter *.md |
  Where-Object { $_.FullName -notmatch '[\\/]\.lake[\\/]' } |
  ForEach-Object {
    $document = $_
    $text = Get-Content -Raw -LiteralPath $document.FullName
    $matches = [regex]::Matches($text, '\[[^\]]+\]\(([^)]+)\)')
    foreach ($match in $matches) {
      $target = $match.Groups[1].Value.Trim().Trim('<', '>')
      $pathPart = ($target -split '#', 2)[0]
      if (-not $pathPart -or $pathPart -match '^(https?://|mailto:)') {
        continue
      }
      $resolved = Join-Path $document.DirectoryName $pathPart
      if (-not (Test-Path -LiteralPath $resolved)) {
        $relative = [IO.Path]::GetRelativePath((Get-Location).Path, $document.FullName)
        $failures += "${relative}: missing local target ${target}"
      }
    }
  }

if ($failures.Count -gt 0) {
  $failures | ForEach-Object { Write-Error $_ }
  exit 1
}

Write-Output "Local Markdown links passed."
