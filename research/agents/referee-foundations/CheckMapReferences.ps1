param([string]$Repository = 'C:\Users\frederick\Documents\relational-perimeter')
$ErrorActionPreference = 'Stop'
$refereeKnowledgePath = Join-Path $Repository 'labyrinth/knowledge.json'
$refereeKnowledge = Get-Content -LiteralPath $refereeKnowledgePath -Raw | ConvertFrom-Json
$refereeIds = @($refereeKnowledge.nodes.id)
$refereeErrors = [System.Collections.Generic.List[string]]::new()
$refereeReferenceCount = 0
foreach ($refereeNode in $refereeKnowledge.nodes) {
  foreach ($refereeLink in $refereeNode.links) {
    if ($refereeLink.to -notin $refereeIds) {
      $refereeErrors.Add("Unknown link: $($refereeNode.id) -> $($refereeLink.to)")
    }
  }
  foreach ($refereeReference in $refereeNode.lean_refs) {
    $refereeReferenceCount++
    $refereeSourcePath = Join-Path $Repository $refereeReference.file
    if (-not (Test-Path -LiteralPath $refereeSourcePath)) {
      $refereeErrors.Add("Missing source: $($refereeReference.file)")
      continue
    }
    $refereeLines = Get-Content -LiteralPath $refereeSourcePath
    $refereeIndex = [int]$refereeReference.line - 1
    if ($refereeIndex -lt 0 -or $refereeIndex -ge $refereeLines.Count) {
      $refereeErrors.Add("Out-of-range line: $($refereeNode.id)")
    } elseif (-not $refereeLines[$refereeIndex].Contains($refereeReference.anchor)) {
      $refereeErrors.Add("Anchor mismatch: $($refereeNode.id) $($refereeReference.file):$($refereeReference.line)")
    }
  }
}
$refereeSota = Get-Content -LiteralPath (Join-Path $Repository 'labyrinth/sota.json') -Raw | ConvertFrom-Json
foreach ($refereeRow in $refereeSota.entries) {
  $refereeMatchedNode = @($refereeKnowledge.nodes | Where-Object id -eq $refereeRow.id)
  if ($refereeMatchedNode.Count -ne 1) {
    $refereeErrors.Add("SOTA row lacks unique node: $($refereeRow.id)")
  } elseif ($refereeRow.result -ne $refereeMatchedNode[0].statement) {
    $refereeErrors.Add("SOTA wording differs: $($refereeRow.id)")
  }
}
Write-Output "Map nodes: $($refereeIds.Count); T2 nodes: $(@($refereeKnowledge.nodes | Where-Object tier -eq 'T2').Count); exact source anchors: $refereeReferenceCount; SOTA rows: $($refereeSota.entries.Count)."
Write-Output 'This script checks source anchors, link targets and SOTA wording only; it does not prove semantic dependency or resolve namespace identity.'
if ($refereeErrors.Count -ne 0) {
  $refereeErrors | Write-Output
  exit 1
}
Write-Output 'All structural spot checks passed.'
