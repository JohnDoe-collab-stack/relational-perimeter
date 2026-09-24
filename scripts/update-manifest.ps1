param([switch]$PrintOnly)

$ErrorActionPreference = "Stop"
$paths = [Collections.Generic.List[string]]::new()
& git ls-files --cached --others --exclude-standard |
  Where-Object {
    $_ -ne 'MANIFEST.sha256' -and
    $_ -notmatch '(^|/)\.lake/' -and
    $_ -notmatch '(^|/)\.git/'
  } |
  ForEach-Object { $paths.Add($_) }

# Match `LC_ALL=C sort` exactly: culture-sensitive PowerShell sorting places
# lowercase paths before some uppercase paths on Windows.
$paths.Sort([StringComparer]::Ordinal)

$lines = foreach ($path in $paths) {
  if (Test-Path -LiteralPath $path -PathType Leaf) {
    $text = [IO.File]::ReadAllText((Resolve-Path -LiteralPath $path))
    $normalizedText = $text.Replace("`r`n", "`n")
    $bytes = [Text.UTF8Encoding]::new($false).GetBytes($normalizedText)
    $hash = [Convert]::ToHexString(
      [Security.Cryptography.SHA256]::HashData($bytes)).ToLowerInvariant()
    $normalized = $path.Replace('\', '/')
    "${hash}  ${normalized}"
  }
}

if ($PrintOnly) {
  $lines
} else {
  $content = ($lines -join "`n") + "`n"
  [IO.File]::WriteAllText(
    (Join-Path (Get-Location).Path 'MANIFEST.sha256'),
    $content,
    [Text.UTF8Encoding]::new($false))
  Write-Output "Wrote MANIFEST.sha256 with $($lines.Count) entries."
}
