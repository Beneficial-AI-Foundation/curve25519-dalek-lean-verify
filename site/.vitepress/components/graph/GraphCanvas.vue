<script setup lang="ts">
import { ref, computed, onMounted, onUnmounted, watch, type PropType } from 'vue'
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

// For loading indicator
const nodeCount = computed(() => props.nodes.length)

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
        <div class="loading-content">
          <div class="loading-graph-animation">
            <svg viewBox="0 0 120 80" class="loading-svg">
              <!-- Nodes -->
              <circle cx="20" cy="40" r="8" class="loading-node node-1" />
              <circle cx="60" cy="20" r="8" class="loading-node node-2" />
              <circle cx="60" cy="60" r="8" class="loading-node node-3" />
              <circle cx="100" cy="40" r="8" class="loading-node node-4" />
              <!-- Edges -->
              <line x1="28" y1="37" x2="52" y2="23" class="loading-edge edge-1" />
              <line x1="28" y1="43" x2="52" y2="57" class="loading-edge edge-2" />
              <line x1="68" y1="23" x2="92" y2="37" class="loading-edge edge-3" />
              <line x1="68" y1="57" x2="92" y2="43" class="loading-edge edge-4" />
            </svg>
          </div>
          <div class="loading-text">
            <span class="loading-title">Building dependency graph</span>
            <span class="loading-subtitle">Preparing {{ nodeCount }} functions...</span>
          </div>
        </div>
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

.loading-content {
  display: flex;
  flex-direction: column;
  align-items: center;
  gap: 1.5rem;
}

.loading-graph-animation {
  width: 160px;
  height: 110px;
}

.loading-svg {
  width: 100%;
  height: 100%;
}

.loading-node {
  fill: var(--vp-c-brand-1);
  opacity: 0.3;
  animation: pulse-node 1.5s ease-in-out infinite;
}

.loading-node.node-1 { animation-delay: 0s; }
.loading-node.node-2 { animation-delay: 0.2s; }
.loading-node.node-3 { animation-delay: 0.4s; }
.loading-node.node-4 { animation-delay: 0.6s; }

.loading-edge {
  stroke: var(--vp-c-text-3);
  stroke-width: 2;
  stroke-linecap: round;
  opacity: 0.2;
  animation: pulse-edge 1.5s ease-in-out infinite;
}

.loading-edge.edge-1 { animation-delay: 0.1s; }
.loading-edge.edge-2 { animation-delay: 0.3s; }
.loading-edge.edge-3 { animation-delay: 0.5s; }
.loading-edge.edge-4 { animation-delay: 0.7s; }

@keyframes pulse-node {
  0%, 100% {
    opacity: 0.3;
    transform: scale(1);
  }
  50% {
    opacity: 1;
    transform: scale(1.1);
  }
}

@keyframes pulse-edge {
  0%, 100% { opacity: 0.2; }
  50% { opacity: 0.7; }
}

.loading-text {
  display: flex;
  flex-direction: column;
  align-items: center;
  gap: 0.25rem;
}

.loading-title {
  font-size: 1rem;
  font-weight: 600;
  color: var(--vp-c-text-1);
}

.loading-subtitle {
  font-size: 0.875rem;
  color: var(--vp-c-text-3);
  font-family: var(--vp-font-family-mono);
}
</style>
