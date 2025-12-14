<script setup lang="ts">
import { ref, onMounted, onUnmounted, watch, computed } from 'vue'

interface FunctionDep {
  lean_name: string
  dependencies: string[]
  specified: boolean
  verified: boolean
  fully_verified: boolean
}

const props = defineProps<{
  functions: FunctionDep[]
}>()

const container = ref<HTMLElement | null>(null)
const tooltip = ref<HTMLElement | null>(null)
const isClient = ref(false)
const isLoading = ref(true)

let cyInstance: any = null
let themeObserver: MutationObserver | null = null

// Check if dark mode is active
function isDarkMode(): boolean {
  if (typeof document === 'undefined') return false
  return document.documentElement.classList.contains('dark')
}

// Node colors based on verification status
const nodeColors = {
  nothing: '#9ca3af',       // gray-400 - not specified
  specified: '#f59e0b',     // amber-500 - has spec but not verified
  verified: '#86efac',      // green-300 - verified (lighter green)
  fully_verified: '#22c55e' // green-500 - fully verified
}

// Get color for a function based on its status
function getNodeColor(func: FunctionDep): string {
  if (func.fully_verified) return nodeColors.fully_verified
  if (func.verified) return nodeColors.verified
  if (func.specified) return nodeColors.specified
  return nodeColors.nothing
}

// Get short label from lean_name (last component only)
function getShortLabel(lean_name: string): string {
  const parts = lean_name.split('.')
  return parts[parts.length - 1]
}

// Get medium label (strip common prefixes, show on hover)
function getMediumLabel(lean_name: string): string {
  return lean_name
    .replace(/^curve25519_dalek\./, '')
    .replace(/^backend\.serial\.(u64\.)?/, '')
}

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
  const edgeColorDefault = '#94a3b8'  // slate-400
  const edgeColorVerified = '#4ade80' // green-400 (softer than node green)
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
            color: isTargetVerified ? edgeColorVerified : edgeColorDefault
          }
        })
      }
    })
  })

  // Create cytoscape instance
  cyInstance = cytoscape({
    container: container.value,
    elements: { nodes, edges },
    style: [
      {
        selector: 'node',
        style: {
          'background-color': 'data(color)',
          'label': 'data(label)',
          'font-size': '9px',
          'font-weight': 'bold',
          'font-family': 'monospace',
          'text-valign': 'center',
          'text-halign': 'center',
          'text-wrap': 'ellipsis',
          'text-max-width': '64px',
          'width': 70,
          'height': 30,
          'shape': 'round-rectangle',
          'color': '#1f2937',
          'text-background-color': '#ffffff',
          'text-background-opacity': 0.85,
          'text-background-shape': 'roundrectangle',
          'text-background-padding': '2px',
          'border-width': 2,
          'border-color': borderColor
        }
      },
      {
        selector: 'edge',
        style: {
          'width': 1.5,
          'line-color': 'data(color)',
          'target-arrow-color': 'data(color)',
          'target-arrow-shape': 'triangle',
          'curve-style': 'taxi',
          'taxi-direction': 'rightward',
          'arrow-scale': 0.8
        }
      },
      {
        selector: 'node:selected',
        style: {
          'border-width': 3,
          'border-color': '#1e40af'
        }
      },
      {
        selector: '.highlighted',
        style: {
          'background-color': 'data(color)',
          'line-color': 'data(color)',
          'target-arrow-color': 'data(color)',
          'opacity': 1,
          'z-index': 10
        }
      },
      {
        selector: '.faded',
        style: {
          'opacity': 0.15
        }
      }
    ],
    layout: {
      name: 'elk',
      elk: {
        algorithm: 'layered',
        'elk.direction': 'RIGHT',
        'elk.spacing.nodeNode': 100,
        'elk.layered.spacing.nodeNodeBetweenLayers': 120,
        'elk.layered.spacing.edgeEdgeBetweenLayers': 20,
        'elk.layered.crossingMinimization.strategy': 'LAYER_SWEEP',
        'elk.layered.nodePlacement.strategy': 'NETWORK_SIMPLEX'
      },
      animate: false,
      fit: true,
      padding: 30
    } as any,
    minZoom: 0.2,
    maxZoom: 3
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

  // Watch for theme changes
  themeObserver = new MutationObserver((mutations) => {
    for (const mutation of mutations) {
      if (mutation.attributeName === 'class') {
        initGraph()
        break
      }
    }
  })
  themeObserver.observe(document.documentElement, { attributes: true })
})

onUnmounted(() => {
  if (cyInstance) {
    cyInstance.destroy()
    cyInstance = null
  }
  if (themeObserver) {
    themeObserver.disconnect()
    themeObserver = null
  }
})

watch(() => props.functions, () => {
  if (isClient.value) {
    initGraph()
  }
}, { deep: true })
</script>

<template>
  <div class="dependency-graph-wrapper">
    <div ref="tooltip" class="tooltip"></div>
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
        <div class="stats">
          <span>{{ stats.total }} functions</span>
          <span class="stat-divider">|</span>
          <span>{{ stats.verified }} verified</span>
          <span class="stat-divider">|</span>
          <span>{{ stats.specified }} specified</span>
          <span class="stat-divider">|</span>
          <span>{{ stats.notSpecified }} not specified</span>
        </div>
      </div>
      <p class="hint">Hover over nodes to highlight connections. Arrows point from function to its dependencies. Scroll to zoom, drag to pan.</p>
    </div>
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
  margin-bottom: 0.75rem;
}

.hint {
  margin: 0;
  font-size: 0.75rem;
  color: var(--vp-c-text-3);
}
</style>
