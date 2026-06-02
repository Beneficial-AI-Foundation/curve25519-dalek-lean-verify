#!/usr/bin/env tsx
/*
 * Post-processes rustdoc HTML (in target/doc/curve25519_dalek/) to inject a
 * "Lean verification" panel under each function/method that has a matching
 * record in functions.json.
 *
 * Sources:
 *   - functions.json    — per-Rust-function record (with lean_name + spec metadata)
 *   - Curve25519Dalek/  — Lean source tree; scanned at startup to build a
 *                         `lean_name → {file, line}` index for accurate links.
 *                         (Replaces the probe-lean output we used previously —
 *                         that data was stale and led to wrong line links.)
 *
 * Output: modified HTML files in-place. A single CSS file is written once
 *         at target/doc/lean-verification.css and linked from each modified
 *         page's <head>.
 *
 * Usage:
 *   tsx scripts/inject-lean-verification.ts \
 *     --rustdoc-root target/doc \
 *     --functions   functions.json \
 *     --source-root .                          # repo root (contains Curve25519Dalek/)
 *     [--repo-url   https://github.com/...]    \
 *     [--branch     master]
 */

import fs from 'node:fs'
import path from 'node:path'

// ---------- Types ----------

interface FunctionRecord {
  rust_name: string | null
  lean_name: string | null
  source: string | null
  lines: string | null
  spec_file: string | null
  spec_docstring: string | null
  spec_statement: string | null
  verified: boolean
  specified: boolean
  fully_verified: boolean
  externally_verified: boolean
  is_relevant: boolean
  is_hidden: boolean
  is_ignored: boolean
  is_extraction_artifact: boolean
}

interface LeanLocation {
  /** Path of the .lean file relative to repo root. */
  path: string
  /** 1-indexed line number where the declaration starts. */
  line: number
}

interface Config {
  rustdocRoot: string   // e.g. target/doc
  functionsJson: string
  sourceRoot: string    // e.g. . (repo root containing Curve25519Dalek/)
  repoUrl: string       // e.g. https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify
  branch: string        // e.g. master
}

// ---------- CLI ----------

function parseArgs(): Config {
  const args = new Map<string, string>()
  for (let i = 2; i < process.argv.length; i += 2) {
    const k = process.argv[i].replace(/^--/, '')
    const v = process.argv[i + 1]
    if (!v) throw new Error(`Missing value for --${k}`)
    args.set(k, v)
  }
  return {
    rustdocRoot:   args.get('rustdoc-root')  ?? 'target/doc',
    functionsJson: args.get('functions')     ?? 'functions.json',
    sourceRoot:    args.get('source-root')   ?? '.',
    repoUrl:       args.get('repo-url')      ?? 'https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify',
    branch:        args.get('branch')        ?? 'master',
  }
}

// ---------- Lean source indexer ----------

/**
 * Scan a single .lean file for declaration positions, tracking the enclosing
 * `namespace ...` blocks. Returns a list of (fully-qualified-name, line)
 * pairs.
 */
function scanLeanFile(absPath: string): Array<{ name: string; line: number }> {
  const text = fs.readFileSync(absPath, 'utf-8')
  const lines = text.split('\n')
  const nsStack: string[] = []
  const out: Array<{ name: string; line: number }> = []

  // Lean declaration prefix on the same line:
  //   def NAME ...
  //   @[reducible] def NAME ...
  //   theorem NAME ...
  // Capture group 1 = the (possibly empty) trailing name.
  const declRe = /^(?:@\[[^\]]*\]\s*)*(?:public\s+|protected\s+|private\s+)?(?:noncomputable\s+)?(def|theorem|lemma|abbrev|instance|axiom)\s+([A-Za-z_][\w.]*)?/
  // Just a binder keyword on its own line (Aeneas emits "def\n  LongName" for
  // names longer than the 100-col limit).
  const declWithoutNameRe = /^(?:@\[[^\]]*\]\s*)*(?:public\s+|protected\s+|private\s+)?(?:noncomputable\s+)?(def|theorem|lemma|abbrev|instance|axiom)\s*$/

  for (let i = 0; i < lines.length; i++) {
    const trimmed = lines[i].replace(/^\s+/, '')
    if (trimmed.length === 0 || trimmed.startsWith('--')) continue

    // namespace / end tracking.
    const nsOpen = trimmed.match(/^namespace\s+([A-Za-z_][\w.]*)/)
    if (nsOpen) { nsStack.push(nsOpen[1]); continue }
    const nsClose = trimmed.match(/^end\s+([A-Za-z_][\w.]*)/)
    if (nsClose && nsStack.length > 0 && nsStack[nsStack.length - 1] === nsClose[1]) {
      nsStack.pop()
      continue
    }

    // Inline form: `def NAME ...` or `@[attr] def NAME ...`.
    const decl = trimmed.match(declRe)
    if (decl && decl[2]) {
      const fullName = nsStack.length > 0
        ? nsStack.join('.') + '.' + decl[2]
        : decl[2]
      out.push({ name: fullName, line: i + 1 })
      continue
    }

    // Wrapped form: binder alone on line, name on next non-blank line.
    if (declWithoutNameRe.test(trimmed)) {
      for (let j = i + 1; j < lines.length && j < i + 5; j++) {
        const next = lines[j].replace(/^\s+/, '')
        if (next.length === 0) continue
        const nameMatch = next.match(/^([A-Za-z_][\w.]*)/)
        if (!nameMatch) break
        const fullName = nsStack.length > 0
          ? nsStack.join('.') + '.' + nameMatch[1]
          : nameMatch[1]
        out.push({ name: fullName, line: i + 1 })
        break
      }
    }
  }
  return out
}

/**
 * Walk Curve25519Dalek/ and produce a single `lean_name → location` index.
 */
function buildLeanIndex(sourceRoot: string): Map<string, LeanLocation> {
  const idx = new Map<string, LeanLocation>()
  const root = path.join(sourceRoot, 'Curve25519Dalek')
  if (!fs.existsSync(root)) {
    console.warn(`[inject-lean-verification] Curve25519Dalek/ not found at ${root}`)
    console.warn('  Aeneas-extracted-definition and Lean-spec links will lack line numbers.')
    return idx
  }
  function walk(dir: string) {
    for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
      const full = path.join(dir, entry.name)
      if (entry.isDirectory()) walk(full)
      else if (entry.name.endsWith('.lean')) {
        const rel = path.relative(sourceRoot, full)
        for (const d of scanLeanFile(full)) {
          // First write wins so we don't blow away earlier hits if a name
          // appears twice (rare; would indicate the same decl in two files).
          if (!idx.has(d.name)) idx.set(d.name, { path: rel, line: d.line })
        }
      }
    }
  }
  walk(root)
  return idx
}

// ---------- rust_name → rustdoc URL ----------

interface RustdocTarget {
  file: string    // path under rustdoc-root, e.g. curve25519_dalek/edwards/struct.EdwardsPoint.html
  anchor: string  // e.g. "method.identity", or "" if injecting at top of page
}

/**
 * Convert a `source` path like 'curve25519-dalek/src/backend/serial/curve_models/mod.rs'
 * into a module URL component like 'curve25519_dalek/backend/serial/curve_models'.
 */
function sourceToModulePath(source: string): string | null {
  // curve25519-dalek/src/... → curve25519_dalek/...
  const m = source.match(/^curve25519-dalek\/src\/(.*)$/)
  if (!m) return null
  let inner = m[1]
  // strip extension + /mod.rs
  inner = inner.replace(/\/mod\.rs$/, '').replace(/\.rs$/, '')
  // lib.rs at crate root has no inner module path
  if (inner === 'lib') return 'curve25519_dalek'
  return 'curve25519_dalek/' + inner
}

/**
 * Extract the receiver type and its defining module from a brace-form
 * `rust_name`. Handles two shapes:
 *
 *   curve25519_dalek::edwards::{Trait for &0 (Receiver)}::method  — trait impl
 *   curve25519_dalek::scalar::{Receiver}::method                  — inherent
 *                                                                   impl-in-block
 *
 * The inherent shape appears when a struct has multiple separate `impl T { … }`
 * blocks; the compiler tags methods with the impl block's receiver path even
 * though there's no trait involved.
 *
 * Crucially the receiver's FULLY-QUALIFIED path is embedded in the brace —
 * we use it to derive the rustdoc module directory, because rustdoc places
 * the struct's docs under the receiver's *definition* module, not under the
 * `source` (impl-block) module. Using the impl module's path produces a
 * non-existent HTML file for every trait impl whose receiver lives in a
 * different module — a frequent shape in this crate.
 *
 * Returns `{ type, modulePath }` where:
 *   - `type` is the last `::` segment of the receiver path (the struct name);
 *   - `modulePath` is a slash-joined module path like `curve25519_dalek/edwards`
 *     for the file lookup. Falls back to `null` if the brace is unrecognised
 *     or has no `::` segments at all.
 */
function receiverFromBraceForm(rustName: string): { type: string; modulePath: string } | null {
  const braceMatch = rustName.match(/\{[^{}]*\}/)
  if (!braceMatch) return null
  let inner = braceMatch[0].slice(1, -1).trim()  // strip leading '{' and trailing '}'
  // Trait impl: keep only the RHS of the last ` for `.
  const forIdx = inner.lastIndexOf(' for ')
  if (forIdx >= 0) {
    inner = inner.slice(forIdx + 5).trim()
  }
  // Drop leading '&N (' refcount wrapper and matching trailing ')'.
  inner = inner.replace(/^&\d+\s*\(/, '').replace(/\)\s*$/, '').trim()
  // Strip trailing generic param suffix `<...>` — receiver is the bare type
  // path (rustdoc page is named after the type without generics).
  inner = inner.replace(/<[^<>]*>\s*$/, '')
  const parts = inner.split('::').map(s => s.trim()).filter(s => s.length > 0)
  if (parts.length === 0) return null
  const type = parts[parts.length - 1]
  const modulePath = parts.length > 1 ? parts.slice(0, -1).join('/') : 'curve25519_dalek'
  return { type, modulePath }
}

/**
 * Last `::` segment of a Rust path.
 */
function lastSegment(rustName: string): string {
  const segs = rustName.split('::')
  return segs[segs.length - 1]
}

/**
 * Decide where in rustdoc the item lives.
 */
function rustNameToRustdoc(rustName: string, source: string): RustdocTarget | null {
  const modulePath = sourceToModulePath(source)
  if (!modulePath) return null

  // Brace form: trait impl `{T for R}::method` OR inherent impl `{R}::method`.
  // Use the receiver's OWN module path (not the impl block's `source` path)
  // since rustdoc files the struct docs under the receiver's definition.
  if (rustName.includes('{')) {
    const receiver = receiverFromBraceForm(rustName)
    const method = lastSegment(rustName)
    if (!receiver) return null
    return {
      file: `${receiver.modulePath}/struct.${receiver.type}.html`,
      anchor: `method.${method}`,
    }
  }

  // Non-trait: module::[Type::]method
  const segs = rustName.split('::')
  const name = segs[segs.length - 1]
  const parent = segs[segs.length - 2] ?? ''

  // SCREAMING_SNAKE → module-level constant
  if (/^[A-Z][A-Z0-9_]*$/.test(name) && !/[a-z]/.test(name)) {
    return { file: `${modulePath}/constant.${name}.html`, anchor: '' }
  }

  // Capitalized parent segment → method on a type (struct or enum)
  if (parent && /^[A-Z]/.test(parent)) {
    return {
      file: `${modulePath}/struct.${parent}.html`,
      anchor: `method.${name}`,
    }
  }

  // Otherwise: free function
  return { file: `${modulePath}/fn.${name}.html`, anchor: '' }
}

// ---------- Panel rendering ----------

function htmlEscape(s: string): string {
  return s
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
}

function statusBadge(fn: FunctionRecord): { text: string; cls: string } {
  if (fn.fully_verified) return { text: '✓ Verified in Lean', cls: 'verified' }
  if (fn.externally_verified) return { text: '✓ Externally verified', cls: 'verified' }
  if (fn.verified) return { text: '✓ Verified', cls: 'verified' }
  if (fn.specified) return { text: '◑ Specified (proof pending)', cls: 'specified' }
  return { text: '○ Not yet specified', cls: 'unspecified' }
}

function buildGitHubLineUrl(cfg: Config, filePath: string, startLine?: number, endLine?: number): string {
  let url = `${cfg.repoUrl}/blob/${cfg.branch}/${filePath}`
  if (startLine && endLine && startLine > 0) {
    url += `#L${startLine}-L${endLine}`
  } else if (startLine && startLine > 0) {
    url += `#L${startLine}`
  }
  return url
}

/**
 * Lightweight server-side syntax highlighter for Lean code.
 *
 * Wraps keywords / literals / strings / comments in `<span class="hl-*">`.
 * The CSS classes are styled in PANEL_CSS using the github-light Lean theme
 * (same palette as the verso-blueprint PQXDH setup).
 *
 * NOTE: regex-based — keywords appearing inside string literals will get
 * wrongly highlighted. That doesn't happen in the spec_statement values we
 * care about (mathematical theorem statements).
 */
function highlightLean(code: string): string {
  // Escape HTML first; subsequent passes operate on the escaped text.
  let h = htmlEscape(code)

  // 1. Block comments `/- ... -/`
  h = h.replace(/\/-[\s\S]*?-\//g, m => `<span class="hl-comment">${m}</span>`)
  // 2. Line comments `-- ...`
  h = h.replace(/--[^\n]*/g, m => `<span class="hl-comment">${m}</span>`)
  // 3. Strings (very basic — Lean strings can have escapes, this is best-effort)
  h = h.replace(/&quot;(?:[^&]|&(?!quot;))*?&quot;/g, m => `<span class="hl-string">${m}</span>`)
  // 4. Statement-level keywords
  h = h.replace(/\b(theorem|lemma|def|abbrev|axiom|instance|structure|inductive|class|mutual|end|namespace|section|open|variable|universe|noncomputable|protected|public|private)\b/g,
    '<span class="hl-keyword">$1</span>')
  // 5. Term / tactic keywords
  h = h.replace(/\b(by|fun|let|do|if|then|else|match|with|return|pure|try|catch|simp|rw|rewrite|exact|intro|intros|have|show|suffices|induction|cases|constructor|refine|calc|ring|omega|norm_num|linarith|aesop|trivial|contradiction|exfalso|congr|ext|funext|sorry|decide|native_decide|apply|subst|change|where)\b/g,
    '<span class="hl-keyword">$1</span>')
  // 6. Built-in constants / types
  h = h.replace(/\b(true|false|none|some|True|False|None|Some|Nat|Int|Bool|String|Type|Prop|Sort)\b/g,
    '<span class="hl-const">$1</span>')
  // 7. Numeric literals
  h = h.replace(/\b(\d+)\b/g, '<span class="hl-lit">$1</span>')
  return h
}

/**
 * Strip an Aeneas-style ":= by ..." or ":= ..." truncation suffix from a
 * spec_statement so the displayed code ends at the colon-equals.
 */
function trimSpecTail(spec: string): string {
  return spec.replace(/\s*:=\s*by\s*\.{2,}\s*$/, '')
             .replace(/\s*:=\s*\.{2,}\s*$/, '')
}

function renderPanel(
  fn: FunctionRecord,
  cfg: Config,
  specLoc: LeanLocation | null,
): string {
  const badge = statusBadge(fn)
  const parts: string[] = []
  parts.push(`<div class="lean-verification lean-${badge.cls}">`)
  parts.push(`  <div class="lean-header">`)
  parts.push(`    <span class="lean-badge lean-badge-${badge.cls}">${badge.text}</span>`)
  parts.push(`  </div>`)

  // --- Lean spec statement (collapsible) ---
  if (fn.spec_statement || fn.spec_file) {
    parts.push(`  <details class="lean-details">`)
    parts.push(`    <summary>Show Lean spec</summary>`)
    parts.push(`    <div class="lean-details-body">`)
    // Link to the spec theorem location (with line number if we found it),
    // otherwise fall back to the spec file root.
    if (specLoc) {
      const url = buildGitHubLineUrl(cfg, specLoc.path, specLoc.line)
      parts.push(`      <a class="lean-link" href="${htmlEscape(url)}" target="_blank" rel="noopener">View in <code>${htmlEscape(specLoc.path)}</code> (line ${specLoc.line}) ↗</a>`)
    } else if (fn.spec_file) {
      const url = buildGitHubLineUrl(cfg, fn.spec_file)
      parts.push(`      <a class="lean-link" href="${htmlEscape(url)}" target="_blank" rel="noopener">View in <code>${htmlEscape(fn.spec_file)}</code> ↗</a>`)
    }
    if (fn.spec_statement) {
      const trimmed = trimSpecTail(fn.spec_statement)
      parts.push(`      <pre class="lean-code"><code>${highlightLean(trimmed)}</code></pre>`)
    }
    parts.push(`    </div>`)
    parts.push(`  </details>`)
  }

  parts.push(`</div>`)
  return parts.join('\n')
}

// ---------- CSS ----------

const PANEL_CSS = `
/* Lean verification panel — injected by scripts/inject-lean-verification.ts */
.lean-verification {
  margin: 0.75rem 0 1rem 0;
  padding: 0.75rem 1rem;
  border: 1px solid var(--border-color, #d2d2d2);
  border-radius: 6px;
  background: var(--code-block-background-color, #f5f5f5);
  font-size: 0.95em;
}
.lean-header {
  display: flex;
  align-items: center;
  gap: 0.75rem;
  flex-wrap: wrap;
  margin-bottom: 0.5rem;
}
.lean-badge {
  display: inline-block;
  padding: 0.15rem 0.6rem;
  border-radius: 4px;
  font-weight: 600;
  font-size: 0.85em;
  border: 1px solid transparent;
}
.lean-badge-verified {
  background: #d4edda;
  color: #155724;
  border-color: #c3e6cb;
}
.lean-badge-specified {
  background: #fff3cd;
  color: #856404;
  border-color: #ffeeba;
}
.lean-badge-unspecified {
  background: #f8d7da;
  color: #721c24;
  border-color: #f5c6cb;
}
.lean-link {
  text-decoration: none;
  font-size: 0.9em;
}
.lean-link:hover { text-decoration: underline; }
.lean-description {
  margin: 0.4rem 0;
  color: var(--main-color, #333);
}
.lean-details {
  margin-top: 0.4rem;
}
.lean-details > summary {
  cursor: pointer;
  font-weight: 500;
  padding: 0.25rem 0;
  user-select: none;
}
.lean-details > summary:hover { color: var(--link-color, #3873ad); }
.lean-details-body {
  margin: 0.5rem 0 0.5rem 1rem;
}
.lean-meta {
  margin-bottom: 0.4rem;
  font-size: 0.85em;
  color: var(--src-line-numbers-color, #666);
}
/* Lean syntax-highlighting tokens (github-light theme) */
.lean-code .hl-keyword { color: #D73A49; }
.lean-code .hl-const   { color: #6F42C1; }
.lean-code .hl-lit     { color: #005CC5; }
.lean-code .hl-string  { color: #032F62; }
.lean-code .hl-comment { color: #6A737D; font-style: italic; }

@media (prefers-color-scheme: dark) {
  .lean-code .hl-keyword { color: #ff7b72; }
  .lean-code .hl-const   { color: #d2a8ff; }
  .lean-code .hl-lit     { color: #79c0ff; }
  .lean-code .hl-string  { color: #a5d6ff; }
  .lean-code .hl-comment { color: #8b949e; }
}
html[data-theme="dark"] .lean-code .hl-keyword,
html[data-theme="ayu"]  .lean-code .hl-keyword { color: #ff7b72; }
html[data-theme="dark"] .lean-code .hl-const,
html[data-theme="ayu"]  .lean-code .hl-const   { color: #d2a8ff; }
html[data-theme="dark"] .lean-code .hl-lit,
html[data-theme="ayu"]  .lean-code .hl-lit     { color: #79c0ff; }
html[data-theme="dark"] .lean-code .hl-string,
html[data-theme="ayu"]  .lean-code .hl-string  { color: #a5d6ff; }
html[data-theme="dark"] .lean-code .hl-comment,
html[data-theme="ayu"]  .lean-code .hl-comment { color: #8b949e; }

.lean-code {
  margin: 0.4rem 0;
  padding: 0.6rem 0.8rem;
  background: var(--code-block-background-color, #fafafa);
  border: 1px solid var(--border-color, #ddd);
  border-radius: 4px;
  overflow-x: auto;
  font-family: monospace;
  font-size: 0.88em;
  line-height: 1.5;
  white-space: pre;
}

/* Dark theme adjustments (rustdoc default vars) */
@media (prefers-color-scheme: dark) {
  .lean-badge-verified   { background: #1f3a25; color: #a3e1b5; border-color: #2c4d34; }
  .lean-badge-specified  { background: #3a3416; color: #e7d490; border-color: #4d4a22; }
  .lean-badge-unspecified{ background: #3a1f23; color: #e8a8af; border-color: #4d2c32; }
}
html[data-theme="dark"] .lean-badge-verified,
html[data-theme="ayu"] .lean-badge-verified   { background: #1f3a25; color: #a3e1b5; border-color: #2c4d34; }
html[data-theme="dark"] .lean-badge-specified,
html[data-theme="ayu"] .lean-badge-specified  { background: #3a3416; color: #e7d490; border-color: #4d4a22; }
html[data-theme="dark"] .lean-badge-unspecified,
html[data-theme="ayu"] .lean-badge-unspecified{ background: #3a1f23; color: #e8a8af; border-color: #4d2c32; }
`

// ---------- HTML injection ----------

/**
 * Walk forward from `from` to find the end of a `<div class="docblock">`
 * block, accounting for nested <div>s. Returns the index just past the
 * closing `</div>`, or null if no docblock starts within `lookahead` chars
 * of `from`.
 */
function findDocblockEnd(html: string, from: number, lookahead = 600): number | null {
  // Rustdoc uses both <div class="docblock"> (inherent methods) and
  // <div class='docblock'> (trait-impl methods). Match either.
  const docOpenRe = /<div class=['"]docblock['"][^>]*>/g
  docOpenRe.lastIndex = from
  const m = docOpenRe.exec(html)
  if (!m || m.index - from > lookahead) return null
  // Position right after the opening tag's '>'.
  let pos = m.index + m[0].length
  let depth = 1
  // Use a simple state machine — only look at <div ... > and </div>.
  // Self-closing <div /> doesn't occur in rustdoc HTML.
  while (pos < html.length && depth > 0) {
    const nextOpen = html.indexOf('<div', pos)
    const nextClose = html.indexOf('</div>', pos)
    if (nextClose === -1) return null
    if (nextOpen !== -1 && nextOpen < nextClose) {
      depth++
      const openEnd = html.indexOf('>', nextOpen)
      if (openEnd === -1) return null
      pos = openEnd + 1
    } else {
      depth--
      pos = nextClose + '</div>'.length
    }
  }
  return depth === 0 ? pos : null
}

/**
 * Inject `panelHtml` into a rustdoc page.
 *
 *  - When `anchor` is "" (free fn / constant page), insert just after the
 *    first </h1> in the body.
 *  - When `anchor` is "method.X", find <section id="method.X" class="method">
 *    and insert AFTER the function's docblock (so the rustdoc-native
 *    description "Performs the + operation. Read more" appears between the
 *    signature and our panel). Falls back to "after </section>" if no
 *    docblock follows.
 *
 * Returns the modified HTML, or null if the anchor wasn't found.
 */
function injectPanel(html: string, anchor: string, panelHtml: string): string | null {
  if (anchor === '') {
    // Insert after the first </h1> in the body
    const h1Re = /(<h1[^>]*>[\s\S]*?<\/h1>)/
    const m = h1Re.exec(html)
    if (!m) return null
    const idx = m.index + m[0].length
    return html.slice(0, idx) + '\n' + panelHtml + '\n' + html.slice(idx)
  }

  // Find the full <section id="ANCHOR" ...> ... </section>
  const escAnchor = anchor.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')
  const sectionRe = new RegExp(
    `<section\\s+id="${escAnchor}"[^>]*>[\\s\\S]*?<\\/section>`,
    'm',
  )
  const m = sectionRe.exec(html)
  if (!m) return null
  const sectionEnd = m.index + m[0].length

  // Prefer to inject AFTER the docblock that follows (so the rustdoc
  // description appears between the signature and our panel).
  const docEnd = findDocblockEnd(html, sectionEnd)
  const insertAt = docEnd ?? sectionEnd
  return html.slice(0, insertAt) + '\n' + panelHtml + '\n' + html.slice(insertAt)
}

/** Inject a <link> for the panel stylesheet into <head> if not already present. */
function injectStylesheetLink(html: string, relCssPath: string): string {
  if (html.includes(`href="${relCssPath}"`)) return html
  return html.replace(
    /(<\/head>)/,
    `  <link rel="stylesheet" href="${relCssPath}">\n$1`,
  )
}

/**
 * Strip every <div class="lean-verification ...">...</div> previously
 * injected into the page (matched by balanced <div> counting). Makes the
 * post-processor idempotent: re-running it on an already-augmented HTML
 * file replaces the panels instead of stacking new ones.
 *
 * `cargo rustdoc` is incremental and will skip rewriting HTML for files
 * whose source didn't change, so stale panels persist across runs without
 * this pass.
 */
function stripExistingPanels(html: string): string {
  let out = html
  const openRe = /<div\s+class="lean-verification[^"]*"[^>]*>/g
  while (true) {
    openRe.lastIndex = 0
    const m = openRe.exec(out)
    if (!m) break
    const start = m.index
    let pos = m.index + m[0].length
    let depth = 1
    while (pos < out.length && depth > 0) {
      const nextOpen = out.indexOf('<div', pos)
      const nextClose = out.indexOf('</div>', pos)
      if (nextClose === -1) break
      if (nextOpen !== -1 && nextOpen < nextClose) {
        depth++
        const openEnd = out.indexOf('>', nextOpen)
        if (openEnd === -1) break
        pos = openEnd + 1
      } else {
        depth--
        pos = nextClose + '</div>'.length
      }
    }
    if (depth !== 0) break  // malformed; bail out to avoid an infinite loop
    // Also swallow the preceding/following lone newlines we inserted.
    let cleanStart = start
    let cleanEnd = pos
    if (out[cleanStart - 1] === '\n') cleanStart--
    if (out[cleanEnd] === '\n') cleanEnd++
    out = out.slice(0, cleanStart) + out.slice(cleanEnd)
  }
  return out
}

/** How many `..` segments are needed to step from `htmlFile` up to rustdoc-root. */
function relCssPathFor(htmlFile: string): string {
  // htmlFile is something like 'curve25519_dalek/edwards/struct.X.html'.
  const depth = htmlFile.split('/').length - 1
  return depth > 0 ? '../'.repeat(depth) + 'lean-verification.css' : 'lean-verification.css'
}

// ---------- Main ----------

interface Stats {
  panelsInjected: number
  filesModified: number
  htmlNotFound: number
  anchorNotFound: number
  skippedHidden: number
  noRustName: number
  noSource: number
  duplicatesMerged: number
}

/**
 * Precedence for picking the "best" record when multiple functions.json
 * entries map to the same rustdoc anchor. Higher = preferred.
 */
function statusRank(fn: FunctionRecord): number {
  if (fn.fully_verified) return 5
  if (fn.externally_verified) return 4
  if (fn.verified) return 3
  if (fn.specified) return 2
  return 1
}

function main() {
  const cfg = parseArgs()
  const stats: Stats = {
    panelsInjected: 0,
    filesModified: 0,
    htmlNotFound: 0,
    anchorNotFound: 0,
    skippedHidden: 0,
    noRustName: 0,
    noSource: 0,
    duplicatesMerged: 0,
  }

  // Load functions.json
  const fnsData = JSON.parse(fs.readFileSync(cfg.functionsJson, 'utf-8')) as {
    functions: FunctionRecord[]
  }

  // Build the Lean source index by scanning Curve25519Dalek/**/*.lean for
  // declarations. The index maps a fully-qualified Lean name to (file, line).
  const leanByName = buildLeanIndex(cfg.sourceRoot)
  console.log(`[inject-lean-verification] indexed ${leanByName.size} Lean declarations from ${cfg.sourceRoot}/Curve25519Dalek/`)

  // Group function records by target HTML file. Each (file, anchor) tuple
  // keeps only ONE record — the one with the highest status rank. This
  // prevents multiple panels from stacking when several functions.json
  // entries (e.g. Add<&T1> and Add<&T2>) map to the same rustdoc method
  // anchor.
  const bestByAnchor = new Map<string, { fn: FunctionRecord; target: RustdocTarget }>()

  for (const fn of fnsData.functions) {
    // We still want to show panels for `is_extraction_artifact`-flagged
    // functions: those are real Rust functions Aeneas couldn't extract
    // cleanly, and surfacing them as yellow/red is exactly the point.
    if (!fn.is_relevant || fn.is_hidden || fn.is_ignored) {
      stats.skippedHidden++
      continue
    }
    if (!fn.rust_name) { stats.noRustName++; continue }
    if (!fn.source)    { stats.noSource++;    continue }

    const target = rustNameToRustdoc(fn.rust_name, fn.source)
    if (!target) continue

    const key = `${target.file}#${target.anchor}`
    const prev = bestByAnchor.get(key)
    if (!prev) {
      bestByAnchor.set(key, { fn, target })
    } else {
      stats.duplicatesMerged++
      if (statusRank(fn) > statusRank(prev.fn)) {
        bestByAnchor.set(key, { fn, target })
      }
    }
  }

  // Build byFile from the deduped best-records and look up Lean spec locations.
  const byFile = new Map<string, {
    fn: FunctionRecord
    target: RustdocTarget
    spec: LeanLocation | null
  }[]>()
  for (const { fn, target } of bestByAnchor.values()) {
    // Convention: the spec theorem for an Aeneas-extracted function `X` is
    // named `X_spec` in the same namespace.
    const spec = fn.lean_name ? leanByName.get(fn.lean_name + '_spec') ?? null : null
    const arr = byFile.get(target.file) ?? []
    arr.push({ fn, target, spec })
    byFile.set(target.file, arr)
  }

  // Write the CSS file once into rustdoc root.
  const cssAbs = path.join(cfg.rustdocRoot, 'lean-verification.css')
  fs.writeFileSync(cssAbs, PANEL_CSS, 'utf-8')

  // Walk each file, inject all panels for it.
  for (const [file, entries] of byFile) {
    const abs = path.join(cfg.rustdocRoot, file)
    if (!fs.existsSync(abs)) {
      stats.htmlNotFound += entries.length
      continue
    }
    const originalHtml = fs.readFileSync(abs, 'utf-8')
    // Strip any panels already injected by a previous run, so this run is
    // idempotent (cargo rustdoc is incremental and may not have rewritten
    // this page even though we did).
    let html = stripExistingPanels(originalHtml)
    const before = html

    // Sort entries: "top of page" (anchor === '') first so subsequent
    // anchored injections aren't disturbed.
    const sortedTop = entries.filter(e => e.target.anchor === '')
    const sortedAnchored = entries.filter(e => e.target.anchor !== '')

    for (const e of sortedTop) {
      const panel = renderPanel(e.fn, cfg, e.spec)
      const next = injectPanel(html, e.target.anchor, panel)
      if (next) {
        html = next
        stats.panelsInjected++
      } else {
        stats.anchorNotFound++
      }
    }
    for (const e of sortedAnchored) {
      const panel = renderPanel(e.fn, cfg, e.spec)
      const next = injectPanel(html, e.target.anchor, panel)
      if (next) {
        html = next
        stats.panelsInjected++
      } else {
        stats.anchorNotFound++
      }
    }

    // Write if either (a) we stripped old panels, or (b) we injected new ones.
    if (html !== originalHtml) {
      html = injectStylesheetLink(html, relCssPathFor(file))
      fs.writeFileSync(abs, html, 'utf-8')
      stats.filesModified++
    }
  }

  console.log('[inject-lean-verification] done')
  console.log(`  Panels injected:               ${stats.panelsInjected}`)
  console.log(`  Files modified:                ${stats.filesModified}`)
  console.log(`  Duplicates merged per anchor:  ${stats.duplicatesMerged}`)
  console.log(`  Skipped (hidden/ignored):      ${stats.skippedHidden}`)
  console.log(`  Anchor not found in HTML:      ${stats.anchorNotFound}`)
  console.log(`  HTML file not found:           ${stats.htmlNotFound}`)
  console.log(`  No rust_name:                  ${stats.noRustName}`)
  console.log(`  No source path:                ${stats.noSource}`)
}

main()
