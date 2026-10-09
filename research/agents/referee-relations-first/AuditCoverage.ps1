param([string]$MapPath = 'labyrinth/knowledge.json', [string]$ArchivePath = 'research/agents/referee-relations-first')
$ErrorActionPreference = 'Stop'
# Independent textual coverage only: this does not run Lean or certify theorem semantics.
$root = (Get-Location).Path
$map = Get-Content -Raw -LiteralPath (Join-Path $root $MapPath) | ConvertFrom-Json
$records = @()
$snippets = @('# Independent source excerpts', '', ('Map: ' + $MapPath), '')
foreach ($node in $map.nodes) {
  $checks = @()
  foreach ($ref in @($node.lean_refs)) {
    if ($null -eq $ref) { continue }
    $path = Join-Path $root $ref.file
    $rows = @(Get-Content -LiteralPath $path)
    $index = [int]$ref.line - 1
    $present = $index -ge 0 -and $index -lt $rows.Count
    $matches = $present -and $rows[$index].Contains([string]$ref.anchor)
    $checks += [pscustomobject]@{ file=$ref.file; declaration=$ref.declaration; line=$ref.line; anchor=$ref.anchor; lineMatches=$matches; actualLine=$(if ($present) {$rows[$index]} else {'OUT OF RANGE'}) }
    $end = $index + 1
    while ($end -lt $rows.Count -and $rows[$end] -notmatch '^(def|theorem|structure|inductive|abbrev|namespace|end)\b' -and $rows[$end] -notmatch '^/- AXIOM_AUDIT_BEGIN') { $end++ }
    $snippets += @('## ' + $node.id + ' — ' + $ref.declaration, '', ($ref.file + ':' + $ref.line), '', '```lean')
    if ($present) { $snippets += $rows[$index..($end-1)] }
    $snippets += @('```', '')
  }
  $records += [pscustomobject]@{ id=$node.id; kind=$node.kind; refs=$checks; referenceCount=$checks.Count; allLineAnchorsMatch=(@($checks | Where-Object { -not $_.lineMatches }).Count -eq 0) }
}
$duplicates = @($map.nodes | Group-Object id | Where-Object Count -gt 1 | ForEach-Object Name)
$result = [pscustomobject]@{ map=$MapPath; nodeCount=@($map.nodes).Count; duplicateIds=$duplicates; referenceCount=($records | Measure-Object referenceCount -Sum).Sum; badAnchors=@($records | Where-Object { -not $_.allLineAnchorsMatch } | ForEach-Object id); nodes=$records }
$result | ConvertTo-Json -Depth 12 | Set-Content -Encoding utf8 -LiteralPath (Join-Path $root ($ArchivePath + '/coverage.json'))
$snippets | Set-Content -Encoding utf8 -LiteralPath (Join-Path $root ($ArchivePath + '/source-excerpts.md'))
$result | Select-Object map,nodeCount,duplicateIds,referenceCount,badAnchors | ConvertTo-Json -Depth 5
