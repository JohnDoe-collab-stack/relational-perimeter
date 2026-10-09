$ErrorActionPreference = 'Stop'
$repoRoot = (Resolve-Path (Join-Path $PSScriptRoot '..\..\..')).Path
$snapshotPath = Join-Path $repoRoot 'labyrinth\evidence\transport-source-snapshot.json'
if (-not (Test-Path -LiteralPath $snapshotPath -PathType Leaf)) { throw 'Transport snapshot does not exist' }
$snapshot = Get-Content -LiteralPath $snapshotPath -Raw | ConvertFrom-Json
if (@($snapshot.files).Count -ne 38) { throw 'Expected exactly 38 snapshot files' }
if ($snapshot.branch -cne 'codex/positive-circular-foundations' -or
    $snapshot.commit -cne '8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685' -or
    $snapshot.working_tree -ne $true) { throw 'Unexpected branch/base/working-tree provenance' }
foreach ($entry in $snapshot.files) {
  $sourcePath = Join-Path $repoRoot $entry.path
  if (-not (Test-Path -LiteralPath $sourcePath -PathType Leaf)) { throw "Missing snapshot source: $($entry.path)" }
  $actual = (Get-FileHash -LiteralPath $sourcePath -Algorithm SHA256).Hash.ToLowerInvariant()
  if ($actual -cne $entry.sha256) { throw "Hash mismatch: $($entry.path)" }
}
Write-Output 'Transport snapshot explicitly exists; all 38 current SHA256 fingerprints agree; branch/base/working-tree provenance agrees.'
$moduleFiles = @($snapshot.files | Where-Object {
  $_.path -match '/(SignatureTransport|SpineTransport|FormationTransport|ClosingTransport)[^/]*\.lean$'
})
if ($moduleFiles.Count -ne 7) { throw 'Expected seven transport modules in snapshot' }
$auditCount = 0
foreach ($entry in $moduleFiles) { $auditCount += @($entry.audit_declarations).Count }
if ($auditCount -ne 162) { throw "Expected 162 audited declarations, found $auditCount" }
Write-Output 'Seven transport modules contain 162 snapshot audit declarations.'
