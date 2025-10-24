---
title: Verification Status
---

<script setup lang="ts">
import { data } from './.vitepress/data/status.data'
import { data as progressData } from './.vitepress/data/progress.data'
import ProgressChart from './.vitepress/components/ProgressChart.vue'

const { entries, stats } = data
const { dataPoints } = progressData

// Helper function to extract function name from full path
function getFunctionName(fullPath: string): string {
  const parts = fullPath.split('::')
  return parts[parts.length - 1]
}

// Helper function to create GitHub link to Rust source
function getRustSourceLink(source: string, lines: string): { text: string, url: string } {
  const baseUrl = 'https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/blob/master'
  const shortName = source.replace('curve25519-dalek/src/', '')

  // Parse line range (e.g., "L364-L372" or "L364")
  const lineMatch = lines.match(/L(\d+)(?:-L(\d+))?/)
  if (lineMatch) {
    const start = lineMatch[1]
    const end = lineMatch[2]
    const lineFragment = end ? `#L${start}-L${end}` : `#L${start}`
    return {
      text: shortName,
      url: `${baseUrl}/${source}${lineFragment}`
    }
  }

  return {
    text: shortName,
    url: `${baseUrl}/${source}`
  }
}

// Helper function to create GitHub link to Lean spec
function getLeanSpecLink(specPath: string): { text: string, url: string } | null {
  if (!specPath) return null

  const baseUrl = 'https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/blob/master'
  const fileName = specPath.split('/').pop() || specPath

  return {
    text: fileName,
    url: `${baseUrl}/${specPath}`
  }
}

// Helper function to render extracted status icon
function getExtractedIcon(status: string): string {
  return status === 'extracted' ? '✓' : '☐'
}

// Helper function to render verified status icon
function getVerifiedIcon(status: string): string {
  if (status === 'verified') return '✓'
  if (status === 'specified') return '📋'
  if (status === 'draft spec') return '✏️'
  return '☐'
}
</script>

# Verification Status

## Current Status

<div class="stats-grid">
  <div class="stat-card">
    <div class="stat-value">{{ stats.total }}</div>
    <div class="stat-label">Total Functions</div>
  </div>
  <div class="stat-card">
    <div class="stat-value">{{ stats.extracted }}</div>
    <div class="stat-label">Extracted</div>
  </div>
  <div class="stat-card">
    <div class="stat-value">{{ stats.specified }}</div>
    <div class="stat-label">Specified</div>
  </div>
  <div class="stat-card">
    <div class="stat-value">{{ stats.verified }}</div>
    <div class="stat-label">Verified</div>
  </div>
</div>

## Progress

<ProgressChart :dataPoints="dataPoints" />

## Detailed Status

<div class="status-table">
  <table>
    <thead>
      <tr>
        <th>Function</th>
        <th>Rust Source</th>
        <th>Lean Spec</th>
        <th class="status-col" title="Extracted">Extr.</th>
        <th class="status-col" title="Verified">Veri.</th>
      </tr>
    </thead>
    <tbody>
      <tr v-for="entry in entries" :key="entry.function">
        <td class="function-name">
          <code :title="entry.function">{{ getFunctionName(entry.function) }}</code>
        </td>
        <td class="rust-source">
          <a v-if="entry.source" :href="getRustSourceLink(entry.source, entry.lines).url" target="_blank" class="source-link" :title="getRustSourceLink(entry.source, entry.lines).text">
            {{ getRustSourceLink(entry.source, entry.lines).text }}
          </a>
        </td>
        <td class="lean-spec">
          <a v-if="getLeanSpecLink(entry.spec_theorem)" :href="getLeanSpecLink(entry.spec_theorem).url" target="_blank" class="spec-link" :title="getLeanSpecLink(entry.spec_theorem).text">
            {{ getLeanSpecLink(entry.spec_theorem).text }}
          </a>
          <span v-else class="empty">—</span>
        </td>
        <td class="status-col">
          <span :class="['status-icon', entry.extracted === 'extracted' ? 'checked' : 'unchecked']">
            {{ getExtractedIcon(entry.extracted) }}
          </span>
        </td>
        <td class="status-col">
          <span :class="['status-icon', entry.verified === 'verified' ? 'verified' : entry.verified === 'specified' ? 'specified' : entry.verified === 'draft spec' ? 'draft' : 'unchecked']">
            {{ getVerifiedIcon(entry.verified) }}
          </span>
        </td>
      </tr>
    </tbody>
  </table>
</div>

### Legend

<div class="legend">
  <div class="legend-section">
    <h4>Extracted</h4>
    <div class="legend-item">
      <span class="status-icon checked">✓</span>
      <span>Rust code has been extracted to Lean</span>
    </div>
    <div class="legend-item">
      <span class="status-icon unchecked">☐</span>
      <span>Extraction pending</span>
    </div>
  </div>

  <div class="legend-section">
    <h4>Verified</h4>
    <div class="legend-item">
      <span class="status-icon verified">✓</span>
      <span>Function has been formally verified</span>
    </div>
    <div class="legend-item">
      <span class="status-icon specified">📋</span>
      <span>Formal specifications but no proofs</span>
    </div>
    <div class="legend-item">
      <span class="status-icon draft">✏️</span>
      <span>Natural language specifications</span>
    </div>
    <div class="legend-item">
      <span class="status-icon unchecked">☐</span>
      <span>No verification work completed yet</span>
    </div>
  </div>
</div>

<style scoped>
.stats-grid {
  display: grid;
  grid-template-columns: repeat(auto-fit, minmax(150px, 1fr));
  gap: 1rem;
  margin: 2rem 0;
}

.stat-card {
  background: var(--vp-c-bg-soft);
  padding: 1.5rem;
  border-radius: 8px;
  text-align: center;
}

.stat-value {
  font-size: 2.5rem;
  font-weight: bold;
  color: var(--vp-c-brand-1);
}

.stat-label {
  margin-top: 0.5rem;
  color: var(--vp-c-text-2);
  font-size: 0.9rem;
}

.status-table {
  margin: 2rem 0;
}

.function-name {
  max-width: 202px;
}

.function-name code {
  display: block;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
  cursor: help;
  background: transparent;
  padding: 0;
}

.rust-source {
  max-width: 202px;
}

.rust-source .source-link {
  display: block;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
  direction: rtl;
  text-align: left;
}

.lean-spec {
  max-width: 180px;
}

.lean-spec .spec-link {
  display: block;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
}

.status-col {
  text-align: center;
  max-width: 50px;
}

.status-icon {
  font-size: 1.2rem;
  font-weight: bold;
}

.status-icon.checked {
  color: #10b981;
}

.status-icon.verified {
  color: #10b981;
}

.status-icon.specified {
  color: #3b82f6;
}

.status-icon.draft {
  color: #f59e0b;
}

.status-icon.unchecked {
  color: var(--vp-c-text-3);
}

.legend {
  display: grid;
  grid-template-columns: repeat(auto-fit, minmax(300px, 1fr));
  gap: 2rem;
  margin: 2rem 0;
  padding: 1.5rem;
  background: var(--vp-c-bg-soft);
  border-radius: 8px;
}

.legend-section h4 {
  margin: 0 0 1rem 0;
  color: var(--vp-c-text-1);
  font-size: 1rem;
}

.legend-item {
  display: flex;
  align-items: center;
  gap: 0.75rem;
  margin-bottom: 0.75rem;
  font-size: 0.9rem;
}

.legend-item .status-icon {
  font-size: 1.1rem;
  min-width: 1.5rem;
}

.legend-item span:last-child {
  color: var(--vp-c-text-2);
}

code {
  font-size: 0.85rem;
}
</style>