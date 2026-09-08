param()

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
$auditEvidence = (Resolve-Path -LiteralPath $PSScriptRoot).Path
$auditProject = (Resolve-Path -LiteralPath (Join-Path $auditEvidence '../..')).Path
$auditRuntime = (Resolve-Path -LiteralPath (Join-Path $auditProject '../../tmp/lean_library_definition_audit_2026-09-05/lean-4.34.0-rc2-windows/bin')).Path
$auditLake = Join-Path $auditRuntime 'lake.exe'
$auditOldPath = $env:Path
$auditOldThreads = $env:LEAN_NUM_THREADS
$auditOldCache = $env:MATHLIB_CACHE_DIR
$auditExit = 1
$auditMutex = [Threading.Mutex]::new($false, 'Local\Codex_ComplementedSubspace_Lean_20260905')
$auditMutexHeld = $false
$auditCommandRecords = [Collections.Generic.List[object]]::new()
$auditStep = 'initialization'
$auditStatePath = Join-Path $auditEvidence 'run_status.json'

function Save-AuditState([string]$Status) {
    @{
        status = $Status
        step = $auditStep
        updatedUtc = [DateTime]::UtcNow.ToString('o')
        processId = $PID
        commands = @($auditCommandRecords.ToArray())
    } | ConvertTo-Json -Depth 8 | Set-Content -LiteralPath $auditStatePath -Encoding utf8
}

function Get-MathematicalSourceSnapshot {
    $auditSourcePaths = @(& rg --files --hidden --no-ignore -g '*.lean' -g '!.lake/**' -g '!.cache/**' -g '!verification/independent-audit-2026-09-05/**')
    if ($LASTEXITCODE -ne 0) { throw 'Could not enumerate the local Lean source tree.' }
    $auditSourcePaths += @('lakefile.toml', 'lake-manifest.json', 'lean-toolchain')
    foreach ($auditRelative in ($auditSourcePaths | Sort-Object -Unique)) {
        $auditSourcePath = Join-Path $auditProject $auditRelative
        [pscustomobject]@{
            path = $auditRelative.Replace('\', '/')
            sha256 = (Get-FileHash -LiteralPath $auditSourcePath -Algorithm SHA256).Hash.ToLowerInvariant()
            bytes = (Get-Item -LiteralPath $auditSourcePath).Length
        }
    }
}

function Invoke-AuditLake {
    param([string]$Step, [string]$LogFile, [string[]]$LakeArguments)
    $script:auditStep = $Step
    Save-AuditState 'running'
    $auditLog = Join-Path $auditEvidence $LogFile
    $auditDisplayArguments = @($LakeArguments | ForEach-Object { "'" + $_.Replace("'", "''") + "'" })
    $auditCommand = "& '" + $auditLake.Replace("'", "''") + "' " + ($auditDisplayArguments -join ' ')
    $auditStarted = [DateTime]::UtcNow.ToString('o')
    @("WORKING DIRECTORY: $auditProject", "START UTC: $auditStarted", "COMMAND: $auditCommand", 'TERMINAL OUTPUT:') |
        Set-Content -LiteralPath $auditLog -Encoding utf8
    Write-Output "$Step`: $auditCommand"
    & $auditLake @LakeArguments 2>&1 | Tee-Object -FilePath $auditLog -Append
    $auditCommandExit = $LASTEXITCODE
    $auditFinished = [DateTime]::UtcNow.ToString('o')
    @("EXIT CODE: $auditCommandExit", "END UTC: $auditFinished") |
        Tee-Object -FilePath $auditLog -Append
    $auditCommandRecords.Add([pscustomobject]@{
        step = $Step; command = $auditCommand; arguments = $LakeArguments
        exitCode = $auditCommandExit; startedUtc = $auditStarted; finishedUtc = $auditFinished; log = $LogFile
    })
    Save-AuditState 'running'
    if ($auditCommandExit -ne 0) { throw "Audit command '$Step' failed with exit code $auditCommandExit. Mathematical source has not been altered." }
}

try {
    try { $auditMutexHeld = $auditMutex.WaitOne() }
    catch [Threading.AbandonedMutexException] { $auditMutexHeld = $true }
    $env:Path = $auditRuntime + ';' + $env:Path
    $env:LEAN_NUM_THREADS = '2'
    $env:MATHLIB_CACHE_DIR = Join-Path $auditProject '.cache/mathlib'
    Push-Location -LiteralPath $auditProject
    try {
        $auditStep = 'source snapshot and clean-target validation'
        Save-AuditState 'running'
        $auditSnapshotBefore = @(Get-MathematicalSourceSnapshot)
        $auditSnapshotBefore | ConvertTo-Json -Depth 4 | Set-Content -LiteralPath (Join-Path $auditEvidence 'source_hashes_before.json') -Encoding utf8
        $auditPrefix = $auditProject.TrimEnd([char[]]@('\', '/')) + [IO.Path]::DirectorySeparatorChar
        $auditBuildTarget = [IO.Path]::GetFullPath((Join-Path $auditProject '.lake/build'))
        if (-not $auditBuildTarget.StartsWith($auditPrefix, [StringComparison]::OrdinalIgnoreCase)) { throw 'Clean target is outside the audited project.' }
        foreach ($auditCheckedPath in @((Join-Path $auditProject '.lake'), $auditBuildTarget)) {
            if (Test-Path -LiteralPath $auditCheckedPath) {
                $auditCheckedItem = Get-Item -LiteralPath $auditCheckedPath -Force
                if (($auditCheckedItem.Attributes -band [IO.FileAttributes]::ReparsePoint) -ne 0) { throw "Clean target passes through a reparse point: $auditCheckedPath" }
                if (-not (Resolve-Path -LiteralPath $auditCheckedPath).Path.StartsWith($auditPrefix, [StringComparison]::OrdinalIgnoreCase)) { throw 'Clean target resolves outside the project.' }
            }
        }
        $auditConfig = Get-Content -LiteralPath 'lakefile.toml' -Raw
        if ($auditConfig -notmatch '(?m)^name\s*=\s*"complemented_subspace_trial"\s*$' -or $auditConfig -match '(?m)^\s*buildDir\s*=') { throw 'Package name/build target needs review before cleaning.' }
        @("Validated absolute clean target: $auditBuildTarget", 'External .lake/packages dependency caches are retained; all root-project and vendored BanLat build artifacts are removed.', 'LEAN_NUM_THREADS=2; each project compiler uses -j1 -M8192 from lakefile.toml.') |
            Set-Content -LiteralPath (Join-Path $auditEvidence 'clean_state.txt') -Encoding utf8
        Invoke-AuditLake -Step 'clean' -LogFile 'clean.log' -LakeArguments @('--no-cache', 'clean', 'complemented_subspace_trial')
        $auditRemainingOleans = 0
        if (Test-Path -LiteralPath $auditBuildTarget) {
            $auditRemainingOleans = @(Get-ChildItem -LiteralPath $auditBuildTarget -Recurse -File -Filter '*.olean').Count
        } else { $auditRemainingOleans = 0 }
        "Root build .olean files after clean: $auditRemainingOleans" | Add-Content -LiteralPath (Join-Path $auditEvidence 'clean_state.txt') -Encoding utf8
        if ($auditRemainingOleans -ne 0) { throw 'The clean did not remove all local .olean files.' }
        Invoke-AuditLake -Step 'build' -LogFile 'build.log' -LakeArguments @('--no-cache', 'build', '+ComplementedSubspace:olean')
        Invoke-AuditLake -Step 'direct main source check' -LogFile 'main_source_check.log' -LakeArguments @('--no-cache', 'env', 'lean', '-j1', '-M8192', 'ComplementedSubspace/RealMainTheorem.lean')
        Invoke-AuditLake -Step 'theorem identity' -LogFile 'theorem_check.txt' -LakeArguments @('--no-cache', 'env', 'lean', '-j1', '-M8192', 'verification/independent-audit-2026-09-05/MainIdentity.lean')
        Invoke-AuditLake -Step 'exact definitions' -LogFile 'definitions.txt' -LakeArguments @('--no-cache', 'env', 'lean', '-j1', '-M8192', 'verification/independent-audit-2026-09-05/PrintDefinitions.lean')
        Invoke-AuditLake -Step 'axioms' -LogFile 'axioms.txt' -LakeArguments @('--no-cache', 'env', 'lean', '-j1', '-M8192', 'verification/independent-audit-2026-09-05/PrintAxioms.lean')
        Invoke-AuditLake -Step 'whole imported project axiom audit' -LogFile 'whole_project_axioms.txt' -LakeArguments @('--no-cache', 'env', 'lean', '-j1', '-M8192', 'WholeProjectAudit.lean')
        Invoke-AuditLake -Step 'kernel dependency traversal' -LogFile 'dependency_trace_run.txt' -LakeArguments @('--no-cache', 'env', 'lean', '-j1', '-M8192', 'verification/independent-audit-2026-09-05/TraceDependencies.lean')
        $auditSnapshotAfter = @(Get-MathematicalSourceSnapshot)
        $auditSnapshotAfter | ConvertTo-Json -Depth 4 | Set-Content -LiteralPath (Join-Path $auditEvidence 'source_hashes_after.json') -Encoding utf8
        $auditDifferences = @(Compare-Object $auditSnapshotBefore $auditSnapshotAfter -Property path,sha256,bytes)
        if ($auditDifferences.Count -ne 0) {
            $auditDifferences | ConvertTo-Json -Depth 4 | Set-Content -LiteralPath (Join-Path $auditEvidence 'source_changes.json') -Encoding utf8
            throw 'Mathematical source or pinned configuration changed during the audit.'
        }
        "PASS: all $($auditSnapshotBefore.Count) original local Lean/configuration files are unchanged by SHA256." |
            Set-Content -LiteralPath (Join-Path $auditEvidence 'source_unchanged.txt') -Encoding utf8
        $auditStep = 'all compiler checks and source immutability passed'
        Save-AuditState 'passed'
        Write-Output 'INDEPENDENT COMPILER AUDIT PASSED. Final certificate also requires source-scan and provenance review.'
        $auditExit = 0
    } finally { Pop-Location }
} catch {
    $auditFailure = $_.Exception.Message
    Save-AuditState 'failed'
    "AUDIT FAILURE at $auditStep`: $auditFailure" | Tee-Object -FilePath (Join-Path $auditEvidence 'audit_failure.txt')
} finally {
    $env:Path = $auditOldPath
    $env:LEAN_NUM_THREADS = $auditOldThreads
    $env:MATHLIB_CACHE_DIR = $auditOldCache
    if ($auditMutexHeld) { $auditMutex.ReleaseMutex() }
    $auditMutex.Dispose()
}
exit $auditExit
