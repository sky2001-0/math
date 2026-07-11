$TargetFiles = @(
    "chap1\logic.tex",
    "chap2\category.tex",
    "chap2\set.tex",
    "chap2\map.tex"
)

$counter = 1

foreach ($fileName in $TargetFiles) {
    $srcPath = Join-Path (Split-Path -Parent $PSScriptRoot) $fileName

    if (-not (Test-Path -LiteralPath $srcPath)) {
        throw "Not found: $srcPath"
    }

    $text = (Get-Content -LiteralPath $srcPath -TotalCount 10 -Encoding UTF8) -join "`n"

    if ($text -match '\\lsection\s*\{([^{}]+)\}') {
        $title = $Matches[1]
        if ($title -match '[<>:"/\\|?*\x00-\x1F._]' -or [string]::IsNullOrWhiteSpace($title)) {
            throw "Invalid title: '$title'"
        }
        $title = $title -replace '\s+', '-'
    } else {
        throw "No section is found."
    }

    $destPath = Join-Path $PSScriptRoot "$("{0:D2}" -f $counter)-$title.txt"

    if (Test-Path -LiteralPath $destPath) {
        Remove-Item -LiteralPath $destPath
    }

    Copy-Item -LiteralPath $srcPath -Destination $destPath

    Write-Host "Saved: $destPath"

    $counter++
}
