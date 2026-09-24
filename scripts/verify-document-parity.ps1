$ErrorActionPreference = "Stop"

$pairs = @(
  @(
    "docs/relations-primitives-constitution-perimetre.fr.md",
    "docs/primitive-relations-and-perimeter-constitution.en.md"
  ),
  @(
    "docs/decomposition-operationnelle-endogene.fr.md",
    "docs/endogenous-operational-decomposition.en.md"
  )
)

function Get-HeadingShape([string]$Path) {
  foreach ($line in Get-Content -LiteralPath $Path) {
    if ($line -match '^(#+)\s+(?:(\d+(?:\.\d+)*)\.)?') {
      $number = if ($Matches[2]) { $Matches[2] } else { "-" }
      "$($Matches[1].Length):$number"
    }
  }
}

function Get-CodeReferences([string]$Path) {
  $text = Get-Content -Raw -LiteralPath $Path
  @([regex]::Matches(
      $text,
      '`([A-Za-z][A-Za-z0-9_./:-]*(?:\.[A-Za-z0-9_]+)*)`') |
    ForEach-Object { $_.Groups[1].Value } |
    Sort-Object -Unique -CaseSensitive)
}

foreach ($pair in $pairs) {
  $leftHeadings = @(Get-HeadingShape $pair[0])
  $rightHeadings = @(Get-HeadingShape $pair[1])
  if (($leftHeadings -join "`n") -cne ($rightHeadings -join "`n")) {
    Write-Error "Heading structure differs between $($pair[0]) and $($pair[1])."
    exit 1
  }

  $leftReferences = @(Get-CodeReferences $pair[0])
  $rightReferences = @(Get-CodeReferences $pair[1])
  if (($leftReferences -join "`n") -cne ($rightReferences -join "`n")) {
    Write-Error "Lean/file references differ between $($pair[0]) and $($pair[1])."
    exit 1
  }
}

Write-Output "French/English document structure and code references passed."
