# Aeneas Verify

VSCode extension that shows the formal verification status of Rust functions extracted by [Aeneas](https://github.com/AeneasVerif/aeneas). Gutter icons indicate whether each function has been verified, specified, or just extracted, and hovering shows the Lean spec theorem.

![Gutter icons and hover tooltip](images/screenshot.png)

## Icons

| Icon | Meaning |
|------|---------|
| ![verified](images/verified.png) | **Verified** — spec theorem is proven |
| ![specified](images/specified.png) | **Specified** — spec theorem written but not yet proven |
| ![extracted](images/extracted.png) | **Extracted** — function extracted by Aeneas, no spec yet |

Hovering on the first line of a verified or specified function displays the Lean spec statement, with a link to open the spec file.

## Install

In VSCode: `Ctrl+Shift+P` → **"Extensions: Install from VSIX..."** and select the `.vsix` file.

## Build from source

```bash
cd vscode-aeneas-verify
npm install
npm run compile
npx @vscode/vsce package --allow-missing-repository
```

## Configuration

| Setting | Default | Description |
|---------|---------|-------------|
| `aeneas-verify.jsonPath` | `"functions.json"` | Path to verification status JSON (relative to workspace root) |
| `aeneas-verify.showExtractedOnly` | `true` | Show grey dot for extracted-but-unspecified functions |

## Commands

- **Aeneas Verify: Reload Verification Data** — re-read `functions.json` without reloading the window
- **Aeneas Verify: Open Lean Spec File** — available from the hover tooltip

## Future features

- Warning when Rust source has been modified since the last Aeneas extraction (stale verification)
- Auto-refresh when verification status is updated (watch for Lean build changes)
- One-click creation of a skeleton Lean spec file for extracted functions that have no spec yet
