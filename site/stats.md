---
title: Stats
layout: home
---

<script setup lang="ts">
import { defineAsyncComponent } from 'vue'
import { data } from './.vitepress/data/status.data'
import { data as progressData } from './.vitepress/data/progress.data'

const ProgressChart = defineAsyncComponent(() =>
  import('./.vitepress/components/ProgressChart.vue')
)

const { stats } = data
const { dataPoints } = progressData
</script>

## Current Status

<div class="stats-grid">
  <div class="stat-card">
    <div class="stat-value">{{ stats.total }}</div>
    <div class="stat-label">Total Functions</div>
  </div>
  <div class="stat-card">
    <div class="stat-value">{{ stats.extracted }}</div>
    <div class="stat-label">Extracted</div>
    <div class="stat-percent">{{ Math.round(stats.extracted / stats.total * 100) }}%</div>
  </div>
  <div class="stat-card">
    <div class="stat-value">{{ stats.specified + stats.verified }}</div>
    <div class="stat-label">Specified</div>
    <div class="stat-percent">{{ Math.round((stats.specified + stats.verified) / stats.total * 100) }}%</div>
  </div>
  <div class="stat-card">
    <div class="stat-value">{{ stats.verified }}</div>
    <div class="stat-label">Verified</div>
    <div class="stat-percent">{{ Math.round(stats.verified / stats.total * 100) }}%</div>
  </div>
</div>

## Verification Progress

<ProgressChart :dataPoints="dataPoints" />

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

.stat-percent {
  font-size: 0.85rem;
  font-weight: normal;
  color: var(--vp-c-brand-1);
  margin-top: 0.25rem;
}
</style>
