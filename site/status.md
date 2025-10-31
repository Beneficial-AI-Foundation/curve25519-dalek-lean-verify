---
title: Verification Status
---

<script setup lang="ts">
import { data } from './.vitepress/data/status.data'
import { data as progressData } from './.vitepress/data/progress.data'
import ProgressChart from './.vitepress/components/ProgressChart.vue'
import StatusTable from './.vitepress/components/StatusTable.vue'

const { entries, stats } = data
const { dataPoints } = progressData
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
    <div class="stat-value">{{ stats.specified + stats.verified }}</div>
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

<StatusTable :data="{ functions: entries }" />

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
</style>