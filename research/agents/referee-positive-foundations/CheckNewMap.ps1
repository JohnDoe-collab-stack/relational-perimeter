$ErrorActionPreference = 'Stop'
$repoRoot = (Resolve-Path (Join-Path $PSScriptRoot '..\..\..')).Path
$knowledge = Get-Content -LiteralPath (Join-Path $repoRoot 'labyrinth\knowledge.json') -Raw | ConvertFrom-Json
$sota = Get-Content -LiteralPath (Join-Path $repoRoot 'labyrinth\sota.json') -Raw | ConvertFrom-Json
$ids = @('th.positive-split', 'th.circular-bridge', 'th.boundary-extraction', 'th.boundary-calculus', 'th.equipped-role', 'th.separator-closing-witness', 'th.separator-provenance-witness', 'th.separator-positive-recurrence')
$referenceCount = 0
foreach ($id in $ids) {
  $node = @($knowledge.nodes | Where-Object id -eq $id)
  if ($node.Count -ne 1) { throw "Nonunique node: $id" }
  if ($node[0].tier -ne 'T2' -or $node[0].review.state -ne 'refereed') { throw "Incorrect tier/review: $id" }
  $row = @($sota.entries | Where-Object id -eq $id)
  if ($row.Count -ne 1 -or $row[0].result -cne $node[0].statement) { throw "SOTA statement mismatch: $id" }
  foreach ($ref in $node[0].lean_refs) {
    $source = Get-Content -LiteralPath (Join-Path $repoRoot $ref.file)
    if ($source[$ref.line - 1].Trim() -cne $ref.anchor.Trim()) { throw "Reference mismatch: $id -> $($ref.file):$($ref.line)" }
    $referenceCount++
  }
  foreach ($path in $node[0].evidence) {
    if (-not (Test-Path -LiteralPath (Join-Path $repoRoot $path))) { throw "Missing evidence: $id -> $path" }
  }
  foreach ($link in $node[0].links) {
    if (@($knowledge.nodes | Where-Object id -eq $link.to).Count -ne 1) { throw "Bad link: $id -> $($link.to)" }
  }
  Write-Output "$id : source anchors, T2 review, evidence, SOTA text and link targets valid"
}
Write-Output "$($ids.Count) new T2 nodes and $referenceCount source references checked. Semantic dependency review is manual."
