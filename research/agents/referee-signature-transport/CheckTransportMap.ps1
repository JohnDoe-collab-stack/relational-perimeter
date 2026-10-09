$ErrorActionPreference = 'Stop'
$repoRoot = (Resolve-Path (Join-Path $PSScriptRoot '..\..\..')).Path
$knowledge = Get-Content -LiteralPath (Join-Path $repoRoot 'labyrinth\knowledge.json') -Raw | ConvertFrom-Json
$sota = Get-Content -LiteralPath (Join-Path $repoRoot 'labyrinth\sota.json') -Raw | ConvertFrom-Json
$nodes = @($knowledge.nodes | Where-Object {
  $_.kind -eq 'theorem' -and @($_.lean_refs | Where-Object {
    $_.file -match '/(SignatureTransport|SpineTransport|FormationTransport|ClosingTransport)[^/]*\.lean$'
  }).Count -gt 0
})
if ($nodes.Count -eq 0) { throw 'No transport theorem nodes found; map is not ready' }
$referenceCount = 0
foreach ($node in $nodes) {
  if ($node.tier -ne 'T2' -or $node.review.state -ne 'refereed') { throw "Incorrect tier/review: $($node.id)" }
  $row = @($sota.entries | Where-Object id -eq $node.id)
  if ($row.Count -ne 1 -or $row[0].result -cne $node.statement) { throw "SOTA statement mismatch: $($node.id)" }
  foreach ($ref in $node.lean_refs) {
    $source = Get-Content -LiteralPath (Join-Path $repoRoot $ref.file)
    if ($source[$ref.line - 1].Trim() -cne $ref.anchor.Trim()) { throw "Reference mismatch: $($node.id) -> $($ref.file):$($ref.line)" }
    $referenceCount++
  }
  foreach ($path in $node.evidence) {
    if (-not (Test-Path -LiteralPath (Join-Path $repoRoot $path))) { throw "Missing evidence: $($node.id) -> $path" }
  }
  foreach ($link in $node.links) {
    if (@($knowledge.nodes | Where-Object id -eq $link.to).Count -ne 1) { throw "Bad link: $($node.id) -> $($link.to)" }
  }
  Write-Output "$($node.id) : source anchors, T2 review, evidence, SOTA text and link targets valid"
}
Write-Output "$($nodes.Count) transport T2 nodes and $referenceCount source references checked. Semantic dependency review is manual."
$question = @($knowledge.nodes | Where-Object id -eq 'q.rich-transport')
$questionRow = @($sota.entries | Where-Object id -eq 'q.rich-transport')
if ($question.Count -ne 1 -or $questionRow.Count -ne 1 -or $question[0].statement -cne $questionRow[0].result) { throw 'Rich-transport question/SOTA mismatch' }
Write-Output 'Rich-transport question statement agrees with its SOTA row; scope checked manually.'
