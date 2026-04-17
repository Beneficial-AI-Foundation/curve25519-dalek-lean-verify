#!/usr/bin/env node
/**
 * Compare Lean build warnings between two commits.
 *
 * Local usage:
 *   npm run warning-diff                        # compare HEAD vs default branch (auto-detected)
 *   node scripts/warning-diff.js abc123 def456  # compare two specific commits (CI mode)
 *
 * CI usage (GitHub Actions):
 *   node scripts/warning-diff.js ${{ github.event.pull_request.base.sha }} ${{ github.sha }}
 *
 * The default branch is auto-detected from origin/HEAD (typically master or main).
 *
 * Output: prints a summary of new/fixed warnings. Exit code 0 always (informational).
 * Set WARNING_DIFF_FAIL=1 to exit 1 when new warnings are found.
 */

import { execSync } from 'child_process'
import path from 'path'
import { fileURLToPath } from 'url'

const __filename = fileURLToPath(import.meta.url)
const __dirname = path.dirname(__filename)
const REPO_ROOT = path.join(__dirname, '..')

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/** Run a command, return stdout as string. */
function run(cmd, opts = {}) {
  return execSync(cmd, {
    cwd: REPO_ROOT,
    encoding: 'utf-8',
    maxBuffer: 50 * 1024 * 1024, // 50 MB — lake build can be verbose
    ...opts,
  })
}

/** Get current git ref (branch name or SHA). */
function currentRef() {
  return run('git rev-parse HEAD').trim()
}

/** Get short description of a ref. */
function describeRef(ref) {
  try {
    return run(`git log -1 --format="%h %s" ${ref}`).trim()
  } catch {
    return ref
  }
}

/** Check for uncommitted changes. */
function hasUncommittedChanges() {
  return run('git status --porcelain').trim().length > 0
}

/**
 * Run `lake build` and collect warnings.
 * Build output is streamed to the console in real time.
 * Returns an array of { file, line, col, message } objects.
 */
function collectWarnings() {
  let output
  try {
    // Run lake build, stream to console AND capture output
    output = execSync('lake build 2>&1', {
      cwd: REPO_ROOT,
      encoding: 'utf-8',
      maxBuffer: 50 * 1024 * 1024,
      stdio: ['inherit', 'pipe', 'pipe'],
    })
    process.stdout.write(output)
  } catch (e) {
    // lake build may exit non-zero on errors — we still want the output
    output = e.stdout || e.stderr || ''
    process.stdout.write(output)
  }

  const warnings = []
  // lake build format: "warning: path/File.lean:42:5: message"
  const lines = output.split('\n')
  for (let i = 0; i < lines.length; i++) {
    const m = lines[i].match(/^warning:\s*(.+\.lean):(\d+):(\d+):\s*(.*)$/)
    if (m) {
      // Collect continuation lines
      let message = m[4]
      while (i + 1 < lines.length && !lines[i + 1].match(/^(warning:|error:|✔|ℹ)/) && lines[i + 1].trim().length > 0) {
        i++
        message += '\n' + lines[i]
      }
      warnings.push({
        file: m[1],
        line: parseInt(m[2]),
        col: parseInt(m[3]),
        message: message.trim(),
      })
    }
  }
  return warnings
}

/**
 * Create a comparable key for a warning (ignoring line numbers which may shift).
 * Uses file + first line of message for grouping.
 */
function warningKey(w) {
  const firstLine = w.message.split('\n')[0]
  return `${w.file}:${firstLine}`
}

/**
 * Create a display string for a warning.
 */
function formatWarning(w) {
  const firstLine = w.message.split('\n')[0]
  return `  ${w.file}:${w.line}: ${firstLine}`
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

/** Detect the default branch (master or main). */
function defaultBranch() {
  try {
    // Check what origin/HEAD points to
    const ref = run('git symbolic-ref refs/remotes/origin/HEAD 2>/dev/null').trim()
    return ref.replace('refs/remotes/origin/', '')
  } catch {
    // Fallback: check if master or main exists
    try { run('git rev-parse --verify master 2>/dev/null'); return 'master' } catch {}
    try { run('git rev-parse --verify main 2>/dev/null'); return 'main' } catch {}
    return 'master'
  }
}

const args = process.argv.slice(2)
const baseRef = args[0] || defaultBranch()
const headRef = args[1] || null // null means "current worktree"

console.log('=== Lean Warning Diff ===\n')

// If comparing against current worktree (no headRef), stash uncommitted changes
const needsStash = !headRef && hasUncommittedChanges()
const originalRef = currentRef()

// --- Collect HEAD warnings ---
let headWarnings
if (headRef) {
  console.log(`Checking out HEAD: ${describeRef(headRef)}`)
  run(`git checkout --quiet ${headRef}`)
  console.log('Building HEAD...')
  headWarnings = collectWarnings()
  console.log(`  ${headWarnings.length} warning(s)\n`)
} else {
  console.log(`HEAD: current worktree (${describeRef('HEAD')})`)
  console.log('Building HEAD...')
  headWarnings = collectWarnings()
  console.log(`  ${headWarnings.length} warning(s)\n`)
}

// --- Stash if needed ---
if (needsStash) {
  console.log('Stashing uncommitted changes...')
  run('git stash --quiet')
}

// --- Collect BASE warnings ---
console.log(`Checking out BASE: ${describeRef(baseRef)}`)
run(`git checkout --quiet ${baseRef}`)
console.log('Building BASE...')
const baseWarnings = collectWarnings()
console.log(`  ${baseWarnings.length} warning(s)\n`)

// --- Restore original state ---
console.log(`Restoring ${headRef || originalRef}...`)
run(`git checkout --quiet ${headRef || originalRef}`)
if (needsStash) {
  try { run('git stash pop --quiet') } catch { /* stash may be empty */ }
}

// --- Compute diff ---
const baseKeys = new Set(baseWarnings.map(warningKey))
const headKeys = new Set(headWarnings.map(warningKey))

const newWarnings = headWarnings.filter(w => !baseKeys.has(warningKey(w)))
const fixedWarnings = baseWarnings.filter(w => !headKeys.has(warningKey(w)))

// --- Report ---
console.log('=== Results ===\n')
console.log(`Base: ${baseWarnings.length} warning(s)`)
console.log(`Head: ${headWarnings.length} warning(s)`)
console.log(`New:  +${newWarnings.length}`)
console.log(`Fixed: -${fixedWarnings.length}\n`)

if (newWarnings.length > 0) {
  console.log('New warnings:')
  for (const w of newWarnings) {
    console.log(formatWarning(w))
  }
  console.log()
}

if (fixedWarnings.length > 0) {
  console.log('Fixed warnings:')
  for (const w of fixedWarnings) {
    console.log(formatWarning(w))
  }
  console.log()
}

if (newWarnings.length === 0 && fixedWarnings.length === 0) {
  console.log('No change in warnings.')
}

// --- GitHub Actions output ---
if (process.env.GITHUB_OUTPUT) {
  const fs = await import('fs')
  const outputFile = process.env.GITHUB_OUTPUT
  fs.appendFileSync(outputFile, `new_warnings=${newWarnings.length}\n`)
  fs.appendFileSync(outputFile, `fixed_warnings=${fixedWarnings.length}\n`)
  fs.appendFileSync(outputFile, `total_warnings=${headWarnings.length}\n`)
  fs.appendFileSync(outputFile, `has_diff=${newWarnings.length > 0 || fixedWarnings.length > 0}\n`)

  // Build markdown summary for PR comment
  if (newWarnings.length > 0 || fixedWarnings.length > 0) {
    let body = '## Lean Warning Diff\n\n'
    body += `| | Count |\n|---|---|\n`
    body += `| Base | ${baseWarnings.length} |\n`
    body += `| Head | ${headWarnings.length} |\n`
    body += `| **New** | **+${newWarnings.length}** |\n`
    body += `| Fixed | -${fixedWarnings.length} |\n\n`

    if (newWarnings.length > 0) {
      body += '<details><summary>New warnings</summary>\n\n```\n'
      for (const w of newWarnings) body += formatWarning(w) + '\n'
      body += '```\n</details>\n\n'
    }
    if (fixedWarnings.length > 0) {
      body += '<details><summary>Fixed warnings</summary>\n\n```\n'
      for (const w of fixedWarnings) body += formatWarning(w) + '\n'
      body += '```\n</details>\n\n'
    }

    // Write body to a file for the comment action
    fs.writeFileSync(path.join(REPO_ROOT, '.warning-diff-comment.md'), body)
    fs.appendFileSync(outputFile, `comment_body_path=.warning-diff-comment.md\n`)
  }
}

// --- Exit code ---
if (process.env.WARNING_DIFF_FAIL === '1' && newWarnings.length > 0) {
  process.exit(1)
}
