---
# https://vitepress.dev/reference/default-theme-home-page
layout: home

hero:
  name: "Formally verifying"
  text: "Dalek elliptic curve cryptography"
  tagline: Project to formally verify the Rust code of curve25519-dalek using Lean
  image:
    src: https://cdn.jsdelivr.net/gh/dalek-cryptography/curve25519-dalek/docs/assets/dalek-logo-clear.png
    alt: dalek-cryptography logo
---

<script setup lang="ts">
import { data } from './.vitepress/data/status.data'
import { data as progressData } from './.vitepress/data/progress.data'
import { data as issuesData } from './.vitepress/data/issues.data'
import ProgressChart from './.vitepress/components/ProgressChart.vue'
import StatusTable from './.vitepress/components/StatusTable.vue'

const { entries, stats } = data
const { dataPoints } = progressData

// Function to match issues to functions
function findIssueForFunction(functionName, issues) {
  // Remove "curve25519_dalek::" prefix to get the function path we want to match
  const functionPath = functionName.replace(/^curve25519_dalek::/, '')

  // Search for function path in issue title or body
  const issue = issues.find(issue => {
    const titleLower = issue.title.toLowerCase()
    const bodyLower = issue.body ? issue.body.toLowerCase() : ''

    // Check if the function path (without curve25519_dalek prefix) appears in title or body
    return titleLower.includes(functionPath.toLowerCase()) ||
           bodyLower.includes(functionPath.toLowerCase())
  })

  return issue
}
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

## Function Status

<StatusTable
  :data="{ functions: entries }"
  :issues="issuesData"
  :findIssueForFunction="findIssueForFunction"
/>

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
