---
title: Stats (2D)
layout: home
---

<script setup>
import { data } from './.vitepress/data/deps.data'
import DependencyGraph from './.vitepress/components/DependencyGraph.vue'
</script>

<DependencyGraph :functions="data.functions" />
