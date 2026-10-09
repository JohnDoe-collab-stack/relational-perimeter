param([switch]$Stop, [int]$Port = 18434)
$ErrorActionPreference = 'Stop'
$cache = Join-Path $env:LOCALAPPDATA 'relational-perimeter\local-ai'
$runtime = Join-Path $cache 'llama-b11524-vulkan'
$executable = Join-Path $runtime 'llama-server.exe'
$pidFile = Join-Path $cache 'server.pid'
if ($Stop) {
  if (Test-Path -LiteralPath $pidFile) {
    $serverProcessId = [int](Get-Content -LiteralPath $pidFile)
    $process = Get-Process -Id $serverProcessId -ErrorAction SilentlyContinue
    if ($process -and $process.Path -eq $executable) { Stop-Process -Id $serverProcessId }
  }
  exit
}
if (Get-NetTCPConnection -LocalPort $Port -State Listen -ErrorAction SilentlyContinue) {
  throw "Port $Port already in use. Inspect the existing service before starting another."
}
New-Item -ItemType Directory -Force -Path $cache | Out-Null
$zip = Join-Path $cache 'llama-b11524-bin-win-vulkan-x64.zip'
$model = Join-Path $cache 'Qwen3-4B-Q4_K_M.gguf'
if (!(Test-Path -LiteralPath $zip)) {
  Invoke-WebRequest 'https://github.com/ggml-org/llama.cpp/releases/download/b11524/llama-b11524-bin-win-vulkan-x64.zip' -OutFile $zip
}
if ((Get-FileHash -Algorithm SHA256 -LiteralPath $zip).Hash.ToLower() -ne '23cd9492275dcf653da6c72be755c5bb5af63c261c79943da71920a9c181ccf1') {
  throw 'Runtime checksum mismatch'
}
if (!(Test-Path -LiteralPath $executable)) { Expand-Archive -LiteralPath $zip -DestinationPath $runtime }
if (!(Test-Path -LiteralPath $model)) {
  $partial = $model + '.part'
  Invoke-WebRequest 'https://huggingface.co/Qwen/Qwen3-4B-GGUF/resolve/bc640142c66e1fdd12af0bd68f40445458f3869b/Qwen3-4B-Q4_K_M.gguf' -OutFile $partial
  if ((Get-FileHash -Algorithm SHA256 -LiteralPath $partial).Hash.ToLower() -ne '7485fe6f11af29433bc51cab58009521f205840f5b4ae3a32fa7f92e8534fdf5') {
    throw 'Model checksum mismatch'
  }
  Move-Item -LiteralPath $partial -Destination $model
}
if ((Get-FileHash -Algorithm SHA256 -LiteralPath $model).Hash.ToLower() -ne '7485fe6f11af29433bc51cab58009521f205840f5b4ae3a32fa7f92e8534fdf5') {
  throw 'Model checksum mismatch'
}
$server = Start-Process -FilePath $executable -ArgumentList @('-m',$model,'--host','127.0.0.1','--port',"$Port",'-c','4096','-ngl','99','-np','1','--reasoning','off','--no-webui','--offline') -WindowStyle Hidden -RedirectStandardOutput (Join-Path $cache 'server.out.log') -RedirectStandardError (Join-Path $cache 'server.err.log') -PassThru
$server.Id | Set-Content -LiteralPath $pidFile
Write-Output "Local server PID $($server.Id), listening only on 127.0.0.1:$Port after loading."
