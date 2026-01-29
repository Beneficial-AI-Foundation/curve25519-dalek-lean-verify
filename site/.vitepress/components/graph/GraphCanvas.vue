<script setup lang="ts">
import { ref, onMounted, onUnmounted, watch, type PropType } from 'vue'
import type { IVisualizationAdapter } from '../../adapters/types'
import { createVisualizationAdapter, type AdapterType } from '../../adapters/types'
import type { GraphNode, GraphEdge, FileGroup, NodeClickEvent, NodeHoverEvent } from '../../types/graph'
import { useThemeWatcher, isDarkMode } from '../../composables/useThemeWatcher'

const props = defineProps({
  nodes: {
    type: Array as PropType<GraphNode[]>,
    required: true
  },
  edges: {
    type: Array as PropType<GraphEdge[]>,
    required: true
  },
  groups: {
    type: Array as PropType<FileGroup[]>,
    default: () => []
  },
  showGroups: {
    type: Boolean,
    default: false
  },
  adapterType: {
    type: String as PropType<AdapterType>,
    default: 'cytoscape'
  },
  selectedNodeIds: {
    type: Array as PropType<string[]>,
    default: () => []
  }
})

const emit = defineEmits<{
  (e: 'nodeClick', event: NodeClickEvent): void
  (e: 'nodeDoubleClick', event: NodeClickEvent): void
  (e: 'nodeHover', event: NodeHoverEvent): void
  (e: 'backgroundClick'): void
  (e: 'groupClick', groupId: string): void
  (e: 'initialized'): void
}>()

const container = ref<HTMLElement | null>(null)
const isLoading = ref(true)
let adapter: IVisualizationAdapter | null = null

// Cleanup functions for event handlers
const cleanupFns: (() => void)[] = []

async function initializeAdapter() {
  if (!container.value) return

  isLoading.value = true

  // Clean up existing adapter
  if (adapter) {
    cleanupFns.forEach(fn => fn())
    cleanupFns.length = 0
    adapter.destroy()
  }

  // Create new adapter
  adapter = await createVisualizationAdapter(props.adapterType)

  await adapter.initialize(container.value, {
    theme: isDarkMode() ? 'dark' : 'light',
    minZoom: 0.1,
    maxZoom: 4
  })

  // Set up event handlers
  cleanupFns.push(
    adapter.onNodeClick((event) => emit('nodeClick', event)),
    adapter.onNodeDoubleClick((event) => emit('nodeDoubleClick', event)),
    adapter.onNodeHover((event) => emit('nodeHover', event)),
    adapter.onBackgroundClick(() => emit('backgroundClick')),
    adapter.onGroupClick((groupId) => emit('groupClick', groupId))
  )

  // Set initial data
  adapter.setData(props.nodes, props.edges)

  // Set groups if enabled
  if (props.showGroups && props.groups.length > 0) {
    adapter.setGroupsVisible(true)
    adapter.setGroups(props.groups)
  }

  // Highlight selected nodes
  if (props.selectedNodeIds.length > 0) {
    adapter.highlightNodes(props.selectedNodeIds)
  }

  isLoading.value = false
  emit('initialized')
}

// Watch for theme changes
useThemeWatcher(() => {
  if (adapter?.isInitialized()) {
    adapter.setTheme(isDarkMode())
  }
})

// Watch for data changes
watch([() => props.nodes, () => props.edges], () => {
  if (adapter?.isInitialized()) {
    adapter.setData(props.nodes, props.edges)
  }
}, { deep: true })

// Watch for group changes
watch([() => props.groups, () => props.showGroups], () => {
  if (adapter?.isInitialized()) {
    adapter.setGroupsVisible(props.showGroups)
    // Always call setGroups - it handles hiding/showing internally
    adapter.setGroups(props.groups)
  }
}, { deep: true })

// Watch for selection changes
watch(() => props.selectedNodeIds, (newIds) => {
  if (adapter?.isInitialized()) {
    adapter.highlightNodes(newIds)
  }
}, { deep: true })

// Expose adapter methods for parent component
function fitToView(padding?: number) {
  adapter?.fitToView(padding)
}

function centerOnNode(nodeId: string, zoom?: number) {
  adapter?.centerOnNode(nodeId, zoom)
}

function highlightConnections(nodeId: string) {
  adapter?.highlightConnections(nodeId)
}

function resetHighlight() {
  adapter?.resetHighlight()
}

async function runLayout() {
  await adapter?.runLayout()
}

async function setLayout(layoutType: string) {
  await adapter?.setLayout(layoutType)
}

function getNodeScreenPosition(nodeId: string): { x: number; y: number } | null {
  return adapter?.getNodeScreenPosition(nodeId) ?? null
}

defineExpose({
  fitToView,
  centerOnNode,
  highlightConnections,
  resetHighlight,
  runLayout,
  setLayout,
  getNodeScreenPosition
})

onMounted(() => {
  initializeAdapter()
})

onUnmounted(() => {
  cleanupFns.forEach(fn => fn())
  cleanupFns.length = 0
  adapter?.destroy()
  adapter = null
})
</script>

<template>
  <div class="graph-canvas-wrapper">
    <div ref="container" class="graph-canvas">
      <div v-if="isLoading" class="loading-overlay">
        <span>Loading graph...</span>
      </div>
    </div>
  </div>
</template>

<style scoped>
.graph-canvas-wrapper {
  position: relative;
  width: 100%;
  height: 100%;
}

.graph-canvas {
  width: 100%;
  height: 100%;
  background: var(--vp-c-bg);
}

.loading-overlay {
  position: absolute;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  display: flex;
  align-items: center;
  justify-content: center;
  background: var(--vp-c-bg);
  color: var(--vp-c-text-2);
}
</style>
