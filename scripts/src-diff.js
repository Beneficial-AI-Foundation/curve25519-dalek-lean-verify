#!/usr/bin/env node
/**
 * Generate diff between original curve25519-dalek source and modified version
 *
 * This script:
 * 1. Clones the original curve25519-dalek repo
 * 2. Checks out the specific commit used in this project
 * 3. Compares curve25519-dalek/src from original with local version
 * 4. Saves the diff to MODIFICATIONS.diff
 */

const { execSync } = require('child_process');
const fs = require('fs');
const path = require('path');

// Configuration from CONTRIBUTING.md
const UPSTREAM_REPO = 'https://github.com/dalek-cryptography/curve25519-dalek';
const UPSTREAM_COMMIT = '8016d6d9b9cdbaa681f24147e0b9377cc8cef934';
const UPSTREAM_TAG = 'curve25519-4.2.0';

// Paths
const SCRIPT_DIR = __dirname;
const REPO_ROOT = path.join(SCRIPT_DIR, '..');
const TEMP_DIR = path.join(REPO_ROOT, '.tmp');
const UPSTREAM_CLONE = path.join(TEMP_DIR, 'curve25519-dalek-upstream');
const LOCAL_SRC = path.join(REPO_ROOT, 'curve25519-dalek', 'src');
const OUTPUT_DIFF = path.join(REPO_ROOT, 'src-modifications.diff');

function run(cmd, options = {}) {
    console.log(`  $ ${cmd}`);
    try {
        return execSync(cmd, {
            encoding: 'utf8',
            stdio: options.quiet ? 'pipe' : 'inherit',
            ...options
        });
    } catch (error) {
        if (!options.allowFail) {
            throw error;
        }
        // If allowFail is true, return stdout/stderr from the error
        // (e.g., diff returns exit code 1 when there are differences, but we still want the output)
        return error.stdout || error.stderr || null;
    }
}

function ensureUpstreamRepo() {
    console.log('\n📦 Cloning upstream repository...');

    // Remove existing clone if present
    if (fs.existsSync(UPSTREAM_CLONE)) {
        console.log('  Removing existing clone...');
        fs.rmSync(UPSTREAM_CLONE, { recursive: true, force: true });
    }

    if (!fs.existsSync(TEMP_DIR)) {
        fs.mkdirSync(TEMP_DIR, { recursive: true });
    }

    console.log(`  Cloning ${UPSTREAM_REPO}...`);
    run(`git clone --bare "${UPSTREAM_REPO}" "${UPSTREAM_CLONE}"`, { quiet: true });
    console.log('  ✓ Cloned successfully');
}

function extractUpstreamSource() {
    console.log(`\n📋 Extracting source at commit ${UPSTREAM_COMMIT.substring(0, 8)}...`);

    const extractDir = path.join(TEMP_DIR, 'extracted-src');

    // Remove old extraction
    if (fs.existsSync(extractDir)) {
        fs.rmSync(extractDir, { recursive: true, force: true });
    }
    fs.mkdirSync(extractDir, { recursive: true });

    // Extract the curve25519-dalek/src directory at the specific commit using git archive
    console.log('  Extracting curve25519-dalek/src/ directory...');
    run(`git -C "${UPSTREAM_CLONE}" archive ${UPSTREAM_COMMIT} curve25519-dalek/src | tar -x -C "${extractDir}"`,
        { quiet: true, shell: '/bin/bash' });

    console.log('  ✓ Extracted successfully');

    return path.join(extractDir, 'curve25519-dalek', 'src');
}

function generateDiff(upstreamSrc, localSrc) {
    console.log('\n🔍 Generating diff...');

    // Generate unified diff
    const diffOutput = run(
        `diff -Naur "${upstreamSrc}" "${localSrc}"`,
        { quiet: true, allowFail: true, stdio: 'pipe' }
    );

    if (!diffOutput || diffOutput.trim() === '') {
        console.log('  ℹ️  No differences found');
        return null;
    }

    // Replace absolute paths with relative paths to make diff machine-independent
    // This ensures the diff is the same regardless of where the repo is cloned
    const upstreamPattern = new RegExp(upstreamSrc.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'), 'g');
    const localPattern = new RegExp(localSrc.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'), 'g');

    const normalizedDiff = diffOutput
        .replace(upstreamPattern, 'a/curve25519-dalek/src')
        .replace(localPattern, 'b/curve25519-dalek/src');

    // Add header to diff
    const header = `# Modifications to curve25519-dalek source code

This file contains the diff between the original curve25519-dalek source
and the modified version used in this verification project.

- **Upstream Repository**: ${UPSTREAM_REPO}
- **Upstream Commit**: ${UPSTREAM_COMMIT}
- **Upstream Tag**: ${UPSTREAM_TAG}

---

`;

    return header + normalizedDiff;
}

function saveDiff(diff) {
    if (!diff) {
        console.log('\n✨ No modifications detected - source matches upstream');

        // Create a note file instead
        const note = `# No Modifications

The curve25519-dalek/src directory matches the upstream source exactly.

- **Upstream Commit**: ${UPSTREAM_COMMIT}
- **Checked**: ${new Date().toISOString()}
`;
        fs.writeFileSync(OUTPUT_DIFF, note);
        console.log(`  ✓ Note saved to ${path.basename(OUTPUT_DIFF)}`);
        return;
    }

    fs.writeFileSync(OUTPUT_DIFF, diff);
    console.log(`\n✅ Diff saved to ${path.basename(OUTPUT_DIFF)}`);

    // Count lines of changes
    const lines = diff.split('\n');
    const added = lines.filter(l => l.startsWith('+')).length;
    const removed = lines.filter(l => l.startsWith('-')).length;

    console.log(`   Lines added:   ${added}`);
    console.log(`   Lines removed: ${removed}`);
}

function cleanup() {
    console.log('\n🧹 Cleaning up...');
    const extractDir = path.join(TEMP_DIR, 'extracted-src');
    if (fs.existsSync(extractDir)) {
        fs.rmSync(extractDir, { recursive: true, force: true });
        console.log('  ✓ Cleaned up temporary files');
    }
}

function main() {
    console.log('═══════════════════════════════════════════════════════');
    console.log('  curve25519-dalek Modification Diff Generator');
    console.log('═══════════════════════════════════════════════════════');

    try {
        ensureUpstreamRepo();
        const upstreamSrc = extractUpstreamSource();
        const diff = generateDiff(upstreamSrc, LOCAL_SRC);
        saveDiff(diff);
        cleanup();

        console.log('\n✨ Done!');
        console.log(`\nTo view the diff: cat ${path.basename(OUTPUT_DIFF)}`);
    } catch (error) {
        console.error('\n❌ Error:', error.message);
        cleanup();
        process.exit(1);
    }
}

if (require.main === module) {
    main();
}

module.exports = { main };
