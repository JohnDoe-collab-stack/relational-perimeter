param([string]$MapPath = 'labyrinth/knowledge.json')
$ErrorActionPreference = 'Stop'
# Written independently of the canonical Python checker. Textual provenance only.
# This script neither executes Lean nor decides semantic adequacy.
$root = (Get-Location).Path
$archive = Join-Path $root 'research/agents/referee-relations-first'
function Read-Json([string]$relative) {
  Get-Content -Raw -LiteralPath (Join-Path $root $relative) | ConvertFrom-Json
}
function Json-Value($value) { ConvertTo-Json -InputObject $value -Depth 100 -Compress }
$map = Read-Json $MapPath
$ownBaseline = Read-Json 'research/agents/referee-relations-first/knowledge-baseline.json'
$publishedBaseline = Read-Json 'labyrinth/evidence/iterations/roles-lot4-published-bf13840/knowledge.json'
$old = @{}
foreach ($node in $ownBaseline.nodes) { $old[$node.id] = $node }
$oldPublished = @{}
foreach ($node in $publishedBaseline.nodes) { $oldPublished[$node.id] = $node }
$current = @{}
foreach ($node in $map.nodes) { $current[$node.id] = $node }
$issues = @()
if ($current.Count -ne @($map.nodes).Count) { $issues += 'Duplicate current IDs' }
if ($current.Count -ne 93) { $issues += 'Expected 93 current IDs' }
$idDiff = @(Compare-Object @($old.Keys) @($current.Keys))
if ($idDiff.Count) { $issues += 'Current/baseline IDs differ' }
$baselineDiff = @(Compare-Object @($old.Keys) @($oldPublished.Keys))
if ($baselineDiff.Count) { $issues += 'Own/published baseline IDs differ' }
$fields = @('received', 'constructed', 'readout', 'scope', 'correction')
$frozen = @('kind', 'tier', 'status', 'statement', 'lean_refs', 'review')
$guide = [IO.File]::ReadAllText((Join-Path $root 'labyrinth/FONDATIONS.fr.md'))
$dashboard = Read-Json 'labyrinth/dashboard/data.json'
$dashboardById = @{}
foreach ($node in $dashboard.nodes) { $dashboardById[$node.id] = $node }
$records = @()
$refCount = 0
foreach ($node in $map.nodes) {
  $checks = @()
  $baseline = $old[$node.id]
  if ($node.kind -cne $baseline.kind) { $checks += 'kind changed' }
  $formal = $baseline.kind -eq 'theorem'
  if ($formal) {
    foreach ($key in $frozen) {
      if ((Json-Value $node.$key) -cne (Json-Value $baseline.$key)) { $checks += ('formal field changed: ' + $key) }
      if ((Json-Value $oldPublished[$node.id].$key) -cne (Json-Value $baseline.$key)) { $checks += ('published baseline differs: ' + $key) }
    }
  }
  foreach ($field in $fields) {
    $value = $node.constitution.$field
    if ($value -isnot [string] -or -not $value.Trim()) { $checks += ('missing constitutive field: ' + $field) }
    elseif (-not $guide.Contains($value)) { $checks += ('guide omitted constitutive field: ' + $field) }
    if ($value -cne $dashboardById[$node.id].constitution.$field) { $checks += ('dashboard field drift: ' + $field) }
  }
  if ($node.constitutive_review.human_check -cne 'pending') { $checks += 'human review no longer pending' }
  if ($node.constitutive_review.author -ceq $map.analysis_scope.referee) { $checks += 'author/referee confused' }
  if (-not $guide.Contains($node.constitutive_review.verdict)) { $checks += 'guide omitted constitutive verdict' }
  if ((Json-Value $node.constitutive_review) -cne (Json-Value $dashboardById[$node.id].constitutive_review)) { $checks += 'dashboard review drift' }
  foreach ($ref in @($node.lean_refs)) {
    if ($null -eq $ref) { continue }
    $refCount++
    $sourceRows = @([IO.File]::ReadAllLines((Join-Path $root $ref.file)))
    $index = [int]$ref.line - 1
    if ($index -lt 0 -or $index -ge $sourceRows.Count -or -not $sourceRows[$index].Contains([string]$ref.anchor)) {
      $checks += ('anchor mismatch: ' + $ref.file + ':' + $ref.line)
    }
  }
  $records += [pscustomobject]@{ id=$node.id; kind=$node.kind; baselineFormal=$formal; formalFieldsPreserved=($formal -and -not @($checks|Where-Object {$_ -like 'formal field*'}).Count); constitutionFieldsPresent=(@($fields|Where-Object {-not $node.constitution.$_}).Count -eq 0); reviewState=$node.constitutive_review.state; issues=$checks }
  foreach ($check in $checks) { $issues += ($node.id + ': ' + $check) }
}
$sota = Read-Json 'labyrinth/sota.json'
$sotaBaseline = Read-Json 'labyrinth/evidence/iterations/roles-lot4-published-bf13840/sota.json'
$oldRows = @{}
foreach ($row in $sotaBaseline.entries) { $oldRows[$row.id] = $row }
$rowDiff = @(Compare-Object @($oldRows.Keys) @($sota.entries|ForEach-Object id))
if ($rowDiff.Count) { $issues += 'SOTA IDs changed' }
if (@($sota.entries.id|Select-Object -Unique).Count -ne @($sota.entries).Count) { $issues += 'Duplicate SOTA IDs' }
if ($sota.entries[0].id -cne 'th.perimeter-exact') { $issues += 'SOTA does not start with exact interior' }
$changedRows = @()
foreach ($row in $sota.entries) {
  if ($row.result -cne $current[$row.id].statement) { $issues += ('SOTA statement drift: ' + $row.id) }
  $previousOld = @($oldRows[$row.id].previous)
  $previousNew = @($row.previous)
  for ($index=0; $index -lt $previousOld.Count; $index++) {
    if ((Json-Value $previousOld[$index]) -cne (Json-Value $previousNew[$index])) { $issues += ('SOTA old history changed: ' + $row.id) }
  }
  if ($row.result -cne $oldRows[$row.id].result) {
    $changedRows += $row.id
    if (-not @($row.previous|Where-Object {$_.was -ceq $oldRows[$row.id].result -and $_.status -ceq $oldRows[$row.id].status}).Count) { $issues += ('SOTA failed to preserve previous row: ' + $row.id) }
  }
}
$snapshot = Read-Json 'labyrinth/evidence/roles-source-snapshot.json'
$hasher = [Security.Cryptography.SHA256]::Create()
$sourceRecords = @()
foreach ($file in $snapshot.files) {
  $source = [IO.File]::ReadAllText((Join-Path $root $file.path))
  $bytes = [Text.Encoding]::UTF8.GetBytes($source.Replace("`r`n", "`n"))
  $hash = ([BitConverter]::ToString($hasher.ComputeHash($bytes))).Replace('-', '').ToLowerInvariant()
  $same = $hash -ceq $file.sha256
  if (-not $same) { $issues += ('formal source changed: ' + $file.path) }
  $sourceRecords += [pscustomobject]@{ path=$file.path; snapshotHash=$file.sha256; independentlyComputedHash=$hash; matches=$same }
}
$hasher.Dispose()
$result = [pscustomobject]@{
  map=$MapPath; method='Independent PowerShell audit; not the canonical Python checker; no Lean run';
  date=(Get-Date).ToString('o'); nodes=@($map.nodes).Count; uniqueIds=$current.Count;
  baselineFormalClaims=@($ownBaseline.nodes|Where-Object kind -eq theorem).Count;
  currentFormalClaims=@($map.nodes|Where-Object kind -eq theorem).Count;
  anchors=$refCount; formalSourceFiles=$sourceRecords.Count;
  constitutiveBlocksInGuide=([regex]::Matches($guide, '\*\*Portée constitutive\.\*\*')).Count;
  constitutiveReviewsInGuide=([regex]::Matches($guide, '\*\*Revue constitutive distincte\.\*\*')).Count;
  sotaEntries=@($sota.entries).Count; sotaChangedResults=$changedRows;
  analysisReviewState=$map.analysis_scope.review_state; issues=$issues; records=$records;
  sources=$sourceRecords
}
$result | ConvertTo-Json -Depth 100 | Set-Content -Encoding utf8 -LiteralPath (Join-Path $archive 'phase2-checks.json')
$result | Select-Object nodes,uniqueIds,baselineFormalClaims,currentFormalClaims,anchors,formalSourceFiles,constitutiveBlocksInGuide,constitutiveReviewsInGuide,sotaEntries,sotaChangedResults,analysisReviewState,issues | ConvertTo-Json -Depth 5
if ($issues.Count) { exit 1 }
