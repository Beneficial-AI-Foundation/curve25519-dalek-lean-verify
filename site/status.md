---
title: Verification Status
---

<script setup lang="ts">
import { data } from './.vitepress/data/status.data'

const { entries, stats } = data
</script>

# Verification Status

## Progress Overview

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

## Detailed Status

<div class="status-table">
  <table>
    <thead>
      <tr>
        <th>Function</th>
        <th>Source</th>
        <th>Status</th>
        <th>Notes</th>
      </tr>
    </thead>
    <tbody>
      <tr v-for="entry in entries" :key="entry.function">
        <td><code>{{ entry.function }}</code></td>
        <td>
          <div class="source-info">
            <div>{{ entry.source.split('/').pop() }}</div>
            <div class="lines">{{ entry.lines }}</div>
          </div>
        </td>
        <td>
          <span v-if="entry.verified === 'verified'" class="badge verified">✓ Verified</span>
          <span v-else-if="entry.verified === 'specified' || entry.verified === 'draft spec'" class="badge specified">Specified</span>
          <span v-else-if="entry.extracted === 'extracted'" class="badge extracted">Extracted</span>
          <span v-else class="badge pending">Pending</span>
        </td>
        <td class="notes">{{ entry.notes }}</td>
      </tr>
    </tbody>
  </table>
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
  overflow-x: auto;
  margin: 2rem 0;
}

table {
  width: 100%;
  border-collapse: collapse;
}

th, td {
  padding: 0.75rem;
  text-align: left;
  border-bottom: 1px solid var(--vp-c-divider);
}

th {
  background: var(--vp-c-bg-soft);
  font-weight: 600;
}

.source-info {
  font-size: 0.85rem;
}

.lines {
  color: var(--vp-c-text-2);
  font-size: 0.75rem;
}

.badge {
  display: inline-block;
  padding: 0.25rem 0.75rem;
  border-radius: 12px;
  font-size: 0.75rem;
  font-weight: 600;
}

.badge.verified {
  background: #10b98120;
  color: #10b981;
}

.badge.specified {
  background: #3b82f620;
  color: #3b82f6;
}

.badge.extracted {
  background: #f59e0b20;
  color: #f59e0b;
}

.badge.pending {
  background: #6b728020;
  color: #6b7280;
}

.notes {
  font-size: 0.85rem;
  color: var(--vp-c-text-2);
}

code {
  font-size: 0.85rem;
}
</style>