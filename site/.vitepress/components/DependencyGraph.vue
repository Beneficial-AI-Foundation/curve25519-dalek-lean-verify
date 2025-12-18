<script setup lang="ts">
import { ref, onMounted, onUnmounted, watch, computed } from 'vue'
import FunctionDetailModal from './FunctionDetailModal.vue'
import FunctionSearch from './FunctionSearch.vue'
import { useThemeWatcher, isDarkMode } from '../composables/useThemeWatcher'
import { getShortLabel, getMediumLabel } from '../utils/labelUtils'
import {
  nodeColors,
  edgeColors,
  getNodeColor,
  createCytoscapeStyles,
  elkLayoutConfig,
  cytoscapeOptions
} from '../config/cytoscapeConfig'
import type { FunctionDep, StatusEntry } from '../types'

const props = defineProps<{
  functions: FunctionDep[]
  statusEntries?: StatusEntry[]
}>()

// Modal state
const isModalOpen = ref(false)
const selectedFunction = ref<StatusEntry | undefined>(undefined)

// DOM refs
const container = ref<HTMLElement | null>(null)
const tooltip = ref<HTMLElement | null>(null)
const wrapper = ref<HTMLElement | null>(null)

// State
const isClient = ref(false)
const isLoading = ref(true)
const isFullscreen = ref(false)

let cyInstance: any = null

// Teleport target for modal - use wrapper when fullscreen, body otherwise
const modalTeleportTarget = computed(() => {
  return isFullscreen.value && wrapper.value ? wrapper.value : 'body'
})

// Theme change handler
useThemeWatcher(() => {
  if (isClient.value) {
    initGraph()
  }
})

async function initGraph() {
  if (!container.value || !isClient.value) return

  isLoading.value = true

  // Dynamic import - only load on client
  const cytoscape = (await import('cytoscape')).default
  // @ts-ignore - no types for cytoscape-elk
  const elk = (await import('cytoscape-elk')).default

  // Register ELK layout
  cytoscape.use(elk)

  // Clean up existing instance
  if (cyInstance) {
    cyInstance.destroy()
    cyInstance = null
  }

  // Create a map for quick lookup
  const funcMap = new Map(props.functions.map(f => [f.lean_name, f]))

  // Border color based on theme
  const borderColor = isDarkMode() ? '#ffffff' : '#374151'

  // Build nodes
  const nodes = props.functions.map(func => ({
    data: {
      id: func.lean_name,
      label: getShortLabel(func.lean_name),
      mediumLabel: getMediumLabel(func.lean_name),
      color: getNodeColor(func),
      fullName: func.lean_name,
      specified: func.specified,
      verified: func.verified,
      fullyVerified: func.fully_verified
    }
  }))

  // Build edges
  const edges: any[] = []
  props.functions.forEach(func => {
    func.dependencies.forEach(dep => {
      if (funcMap.has(dep)) {
        const targetFunc = funcMap.get(dep)!
        const isTargetVerified = targetFunc.verified || targetFunc.fully_verified
        edges.push({
          data: {
            id: `${func.lean_name}->${dep}`,
            source: func.lean_name,
            target: dep,
            color: isTargetVerified ? edgeColors.verified : edgeColors.default
          }
        })
      }
    })
  })

  // Create cytoscape instance
  cyInstance = cytoscape({
    container: container.value,
    elements: { nodes, edges },
    style: createCytoscapeStyles(borderColor) as any,
    layout: elkLayoutConfig as any,
    ...cytoscapeOptions
  })

  // Add hover behavior
  cyInstance.on('mouseover', 'node', (e: any) => {
    const node = e.target
    highlightConnections(node)
    showTooltip(node, e.originalEvent)
  })

  cyInstance.on('mouseout', 'node', () => {
    resetHighlight()
    hideTooltip()
  })

  // Add click handler to open modal
  cyInstance.on('tap', 'node', (e: any) => {
    const node = e.target
    handleNodeClick(node)
  })

  // Fit graph to container
  cyInstance.fit(undefined, 30)

  isLoading.value = false
}

function highlightConnections(node: any) {
  if (!cyInstance) return

  // Get connected nodes and edges
  const connectedEdges = node.connectedEdges()
  const connectedNodes = connectedEdges.connectedNodes().add(node)

  // Fade everything
  cyInstance.elements().addClass('faded')

  // Highlight connected elements
  connectedNodes.removeClass('faded').addClass('highlighted')
  connectedEdges.removeClass('faded').addClass('highlighted')
}

function resetHighlight() {
  if (!cyInstance) return
  cyInstance.elements().removeClass('faded').removeClass('highlighted')
}

function showTooltip(node: any, event: MouseEvent) {
  if (!tooltip.value) return
  tooltip.value.textContent = node.data('mediumLabel')
  tooltip.value.style.display = 'block'
  tooltip.value.style.left = `${event.clientX + 10}px`
  tooltip.value.style.top = `${event.clientY + 10}px`
}

function hideTooltip() {
  if (!tooltip.value) return
  tooltip.value.style.display = 'none'
}

// Handle node click to open modal
function handleNodeClick(node: any) {
  if (!props.statusEntries) return

  const leanName = node.data('id')
  // Find the matching status entry by lean_name
  const statusEntry = props.statusEntries.find(
    entry => entry.lean_name === leanName || entry.function?.replace(/::/g, '.') === leanName
  )

  if (statusEntry) {
    selectedFunction.value = statusEntry
    isModalOpen.value = true
  }
}

function closeModal() {
  isModalOpen.value = false
  selectedFunction.value = undefined
}

// Fullscreen toggle
function toggleFullscreen() {
  if (!wrapper.value) return

  if (!document.fullscreenElement) {
    wrapper.value.requestFullscreen().catch(err => {
      console.error('Error attempting to enable fullscreen:', err)
    })
  } else {
    document.exitFullscreen()
  }
}

function handleFullscreenChange() {
  isFullscreen.value = !!document.fullscreenElement
  // Resize graph when fullscreen changes
  if (cyInstance) {
    setTimeout(() => {
      cyInstance.resize()
      cyInstance.fit(undefined, 30)
    }, 100)
  }
}

// Recenter the graph
function recenterGraph() {
  if (cyInstance) {
    cyInstance.fit(undefined, 30)
  }
}

// Focus on a specific node (called by FunctionSearch component)
function focusOnNode(leanName: string) {
  if (!cyInstance) return

  const node = cyInstance.getElementById(leanName)
  if (node && node.length > 0) {
    // Center and zoom on the node
    cyInstance.animate({
      center: { eles: node },
      zoom: 1.5
    }, {
      duration: 300
    })

    // Highlight the node and its connections
    node.select()
    highlightConnections(node)
  }
}

// Legend items (simplified: verified includes fully_verified)
const legendItems = computed(() => [
  { color: nodeColors.fully_verified, label: 'Verified' },
  { color: nodeColors.specified, label: 'Specified' },
  { color: nodeColors.nothing, label: 'Not Specified' }
])

// Stats
const stats = computed(() => {
  const total = props.functions.length
  const specified = props.functions.filter(f => f.specified && !f.verified && !f.fully_verified).length
  const verified = props.functions.filter(f => f.verified || f.fully_verified).length
  const notSpecified = props.functions.filter(f => !f.specified && !f.verified && !f.fully_verified).length
  return { total, specified, verified, notSpecified }
})

onMounted(() => {
  isClient.value = true
  initGraph()

  // Listen for fullscreen changes
  document.addEventListener('fullscreenchange', handleFullscreenChange)
})

onUnmounted(() => {
  if (cyInstance) {
    cyInstance.destroy()
    cyInstance = null
  }
  document.removeEventListener('fullscreenchange', handleFullscreenChange)
})

watch(() => props.functions, () => {
  if (isClient.value) {
    initGraph()
  }
}, { deep: true })
</script>

<template>
  <div ref="wrapper" class="dependency-graph-wrapper" :class="{ fullscreen: isFullscreen }">
    <div ref="tooltip" class="tooltip"></div>
    <div class="graph-controls">
      <button @click="recenterGraph" class="graph-btn" title="Recenter graph">
        <svg xmlns="http://www.w3.org/2000/svg" width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
          <circle cx="12" cy="12" r="3"/>
          <path d="M12 2v4m0 12v4M2 12h4m12 0h4"/>
        </svg>
      </button>
      <button @click="toggleFullscreen" class="graph-btn" :title="isFullscreen ? 'Exit fullscreen' : 'Enter fullscreen'">
        <svg v-if="!isFullscreen" xmlns="http://www.w3.org/2000/svg" width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
          <path d="M8 3H5a2 2 0 0 0-2 2v3m18 0V5a2 2 0 0 0-2-2h-3m0 18h3a2 2 0 0 0 2-2v-3M3 16v3a2 2 0 0 0 2 2h3"/>
        </svg>
        <svg v-else xmlns="http://www.w3.org/2000/svg" width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
          <path d="M8 3v3a2 2 0 0 1-2 2H3m18 0h-3a2 2 0 0 1-2-2V3m0 18v-3a2 2 0 0 1 2-2h3M3 16h3a2 2 0 0 1 2 2v3"/>
        </svg>
      </button>
    </div>
    <div ref="container" class="graph-container">
      <div v-if="isLoading" class="loading-overlay">
        <span>Loading graph...</span>
      </div>
    </div>
    <div class="graph-footer">
      <div class="footer-content">
        <div class="legend">
          <div v-for="item in legendItems" :key="item.label" class="legend-item">
            <span class="legend-dot" :style="{ backgroundColor: item.color }"></span>
            <span>{{ item.label }}</span>
          </div>
        </div>
        <FunctionSearch :functions="functions" @select="focusOnNode" />
        <div class="stats">
          <span>{{ stats.total }} functions</span>
          <span class="stat-divider">|</span>
          <span>{{ stats.verified }} verified</span>
          <span class="stat-divider">|</span>
          <span>{{ stats.specified }} specified</span>
          <span class="stat-divider">|</span>
          <span>{{ stats.notSpecified }} not specified</span>
        </div>
        <div class="hint-wrapper">
          <svg class="hint-icon" xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
            <circle cx="12" cy="12" r="10"/>
            <path d="M12 16v-4m0-4h.01"/>
          </svg>
          <span class="hint-text">Hover over nodes to highlight connections. Click a node for details. Arrows point from function to its dependencies. Scroll to zoom, drag to pan.</span>
        </div>
      </div>
    </div>

    <!-- Function detail modal -->
    <FunctionDetailModal
      :isOpen="isModalOpen"
      :func="selectedFunction"
      :teleportTo="modalTeleportTarget"
      @close="closeModal"
    />
  </div>
</template>

<style scoped>
.dependency-graph-wrapper {
  margin: 2rem 0;
  background: var(--vp-c-bg-soft);
  border-radius: 8px;
  overflow: hidden;
  position: relative;
}

.tooltip {
  display: none;
  position: fixed;
  background: var(--vp-c-bg-elv);
  border: 1px solid var(--vp-c-divider);
  border-radius: 4px;
  padding: 6px 10px;
  font-size: 12px;
  font-family: monospace;
  color: var(--vp-c-text-1);
  z-index: 1000;
  pointer-events: none;
  box-shadow: 0 2px 8px rgba(0, 0, 0, 0.15);
  white-space: nowrap;
}

.legend {
  display: flex;
  gap: 1rem;
  flex-wrap: wrap;
}

.legend-item {
  display: flex;
  align-items: center;
  gap: 0.5rem;
  font-size: 0.875rem;
}

.legend-dot {
  width: 12px;
  height: 12px;
  border-radius: 50%;
}

.stats {
  font-size: 0.875rem;
  color: var(--vp-c-text-2);
}

.stat-divider {
  margin: 0 0.5rem;
  opacity: 0.5;
}

.graph-container {
  width: 100%;
  height: 600px;
  background: var(--vp-c-bg);
  position: relative;
  border: 1px solid var(--vp-c-divider);
  border-radius: 4px;
  margin: 0.5rem;
  width: calc(100% - 1rem);
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

.graph-footer {
  padding: 1rem;
  border-top: 1px solid var(--vp-c-divider);
}

.footer-content {
  display: flex;
  justify-content: space-between;
  align-items: center;
  flex-wrap: wrap;
  gap: 1rem;
}

.hint-wrapper {
  position: relative;
  display: flex;
  align-items: center;
}

.hint-icon {
  color: var(--vp-c-text-3);
  cursor: help;
}

.hint-text {
  display: none;
  position: absolute;
  bottom: 100%;
  right: 0;
  margin-bottom: 0.5rem;
  padding: 0.5rem 0.75rem;
  background: var(--vp-c-bg-elv);
  border: 1px solid var(--vp-c-divider);
  border-radius: 6px;
  font-size: 0.75rem;
  color: var(--vp-c-text-2);
  white-space: nowrap;
  box-shadow: 0 2px 8px rgba(0, 0, 0, 0.1);
  z-index: 100;
}

.hint-wrapper:hover .hint-text {
  display: block;
}

.graph-controls {
  position: absolute;
  top: 1rem;
  right: 1rem;
  z-index: 10;
  display: flex;
  gap: 0.25rem;
}

.graph-btn {
  background: var(--vp-c-bg);
  border: 1px solid var(--vp-c-divider);
  border-radius: 6px;
  padding: 0.5rem;
  cursor: pointer;
  color: var(--vp-c-text-2);
  display: flex;
  align-items: center;
  justify-content: center;
  transition: all 0.2s;
}

.graph-btn:hover {
  background: var(--vp-c-bg-soft);
  color: var(--vp-c-text-1);
  border-color: var(--vp-c-brand-1);
}

/* Fullscreen mode styles */
.dependency-graph-wrapper.fullscreen {
  position: fixed;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  margin: 0;
  border-radius: 0;
  z-index: 9999;
  display: flex;
  flex-direction: column;
}

.dependency-graph-wrapper.fullscreen .graph-container {
  flex: 1;
  height: auto;
}
</style>
