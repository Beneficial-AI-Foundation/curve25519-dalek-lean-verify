---
title: Dependencies
layout: home
---

<script setup lang="ts">
import { defineAsyncComponent } from 'vue'
import { data as depsData } from './.vitepress/data/deps.data'
import { data } from './.vitepress/data/status.data'

const DependencyGraph = defineAsyncComponent(() =>
  import('./.vitepress/components/DependencyGraph.vue')
)

const { entries } = data
</script>

## Dependency Graph

Visualization of function dependencies. Each node represents a function, with edges showing dependencies between them.

<DependencyGraph :functions="depsData.functions" :statusEntries="entries" />
