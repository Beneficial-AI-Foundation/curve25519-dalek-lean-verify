---
title: Status
layout: home
---

<script setup lang="ts">
import { defineAsyncComponent } from 'vue'
import { data } from './.vitepress/data/status.data'
import { data as githubData } from './.vitepress/data/github.data'
import { useGitHubMatching } from './.vitepress/composables/useGitHubMatching'

const StatusTable = defineAsyncComponent(() =>
  import('./.vitepress/components/StatusTable.vue')
)

const { entries } = data
const { findItemsForFunction } = useGitHubMatching()
</script>

## Function Status

This table shows the verification status of all functions in the project. Click on a function to see more details.

<StatusTable
  :data="{ functions: entries }"
  :issues="githubData"
  :findIssuesForFunction="findItemsForFunction"
/>
