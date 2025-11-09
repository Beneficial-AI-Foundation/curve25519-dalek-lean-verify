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
import { data as githubData } from './.vitepress/data/github.data'
import ProgressChart from './.vitepress/components/ProgressChart.vue'
import StatusTable from './.vitepress/components/StatusTable.vue'
import { useGitHubMatching } from './.vitepress/composables/useGitHubMatching'

const { entries, stats } = data
const { dataPoints } = progressData

// Use the GitHub matching composable
const { findItemsForFunction } = useGitHubMatching()
</script>

This project aims to formally verify the [curve25519-dalek](https://github.com/dalek-cryptography/curve25519-dalek) Rust library using the [Lean theorem prover](https://lean-lang.org). We use [Aeneas](https://github.com/AeneasVerif/aeneas) to automatically extract Rust code into Lean, then we write formal specifications and proofs to ensure the cryptographic implementations are mathematically correct and free from bugs. 

We aim to:
Demonstrate the viability of verifying Rust cryptographic code using Lean;
Develop techniques to make Rust-to-Lean verification more accessible;
Create a resource for learning verification of real-world Rust code.

See the [project repo](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify) or [project description](details.md) for further details. See below for the latest status and links to the individual spec theorems.

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
  :issues="githubData"
  :findIssuesForFunction="findItemsForFunction"
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
