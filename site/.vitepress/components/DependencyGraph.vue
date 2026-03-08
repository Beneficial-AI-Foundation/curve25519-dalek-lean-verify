<script setup lang="ts">
/**
 * DependencyGraph.vue
 *
 * This is a thin wrapper around the new modular graph visualization system.
 * The actual implementation is in the graph/ subfolder with:
 * - GraphController.vue: Orchestrates data processing and visualization
 * - GraphCanvas.vue: Wraps the visualization adapter (Cytoscape, etc.)
 * - GraphControls.vue: Filter and view controls
 * - InfoPanels.vue: Selected function info display
 *
 * The architecture is designed to be modular:
 * - Data processing is in composables (useGraphData, useGraphFiltering, etc.)
 * - Visualization is abstracted via IVisualizationAdapter interface
 * - Components are separated by concern for easy maintenance
 */
import type { StatusEntry } from '../types'
import type { FunctionRecord } from '../data/deps.data'
import { GraphController } from './graph'

// Accept FunctionRecord[] directly since that's what deps.data.ts provides
const props = defineProps<{
  functions: FunctionRecord[]
  statusEntries?: StatusEntry[]
}>()
</script>

<template>
  <GraphController
    :functions="functions"
    :status-entries="statusEntries || []"
  />
</template>
