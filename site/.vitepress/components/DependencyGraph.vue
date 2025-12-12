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
const isClient = ref(false)
const isLoading = ref(true)

let cyInstance: any = null

// Node colors based on verification status
const nodeColors = {
  nothing: '#9ca3af',       // gray-400 - not specified
  specified: '#f59e0b',     // amber-500 - has spec but not verified
  verified: '#22c55e',      // green-500 - verified
  fully_verified: '#3b82f6' // blue-500 - fully verified
}

// Get color for a function based on its status
function getNodeColor(func: FunctionDep): string {
  if (func.fully_verified) return nodeColors.fully_verified
  if (func.verified) return nodeColors.verified
  if (func.specified) return nodeColors.specified
  return nodeColors.nothing
}

// Get short label from lean_name (last component)
function getShortLabel(lean_name: string): string {
  const parts = lean_name.split('.')
  return parts.slice(-2).join('.')
}

async function initGraph() {
  if (!container.value || !isClient.value) return

  isLoading.value = true

  // Dynamic import - only load on client
  const cytoscape = (await import('cytoscape')).default
  const dagre = (await import('cytoscape-dagre')).default

  // Register dagre layout
  cytoscape.use(dagre)

  // Clean up existing instance
  if (cyInstance) {
    cyInstance.destroy()
    cyInstance = null
  }

  // Create a map for quick lookup
  const funcMap = new Map(props.functions.map(f => [f.lean_name, f]))

  // Build nodes
  const nodes = props.functions.map(func => ({
    data: {
      id: func.lean_name,
      label: getShortLabel(func.lean_name),
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
        edges.push({
          data: {
            id: `${func.lean_name}->${dep}`,
            source: func.lean_name,
            target: dep
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
          'font-size': '10px',
          'font-family': 'monospace',
          'text-valign': 'bottom',
          'text-halign': 'center',
          'text-margin-y': 5,
          'width': 20,
          'height': 20,
          'color': '#374151'
        }
      },
      {
        selector: 'edge',
        style: {
          'width': 1.5,
          'line-color': '#94a3b8',
          'target-arrow-color': '#94a3b8',
          'target-arrow-shape': 'triangle',
          'curve-style': 'bezier',
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
          'line-color': '#475569',
          'target-arrow-color': '#475569',
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
      name: 'dagre',
      rankDir: 'TB',        // Top to bottom (TB), or try 'LR' for left-to-right
      nodeSep: 50,          // Separation between nodes in same rank
      rankSep: 80,          // Separation between ranks
      edgeSep: 10,          // Separation between edges
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
  })

  cyInstance.on('mouseout', 'node', () => {
    resetHighlight()
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

// Legend items
const legendItems = computed(() => [
  { color: nodeColors.fully_verified, label: 'Fully Verified' },
  { color: nodeColors.verified, label: 'Verified' },
  { color: nodeColors.specified, label: 'Specified' },
  { color: nodeColors.nothing, label: 'Not Specified' }
])

// Stats
const stats = computed(() => {
  const total = props.functions.length
  const specified = props.functions.filter(f => f.specified).length
  const verified = props.functions.filter(f => f.verified).length
  const fullyVerified = props.functions.filter(f => f.fully_verified).length
  return { total, specified, verified, fullyVerified }
})

onMounted(() => {
  isClient.value = true
  initGraph()
})

onUnmounted(() => {
  if (cyInstance) {
    cyInstance.destroy()
    cyInstance = null
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
    <div class="graph-header">
      <div class="legend">
        <div v-for="item in legendItems" :key="item.label" class="legend-item">
          <span class="legend-dot" :style="{ backgroundColor: item.color }"></span>
          <span>{{ item.label }}</span>
        </div>
      </div>
      <div class="stats">
        <span>{{ stats.total }} functions</span>
        <span class="stat-divider">|</span>
        <span>{{ stats.fullyVerified }} fully verified</span>
        <span class="stat-divider">|</span>
        <span>{{ stats.verified }} verified</span>
      </div>
    </div>
    <div ref="container" class="graph-container">
      <div v-if="isLoading" class="loading-overlay">
        <span>Loading graph...</span>
      </div>
    </div>
    <div class="graph-footer">
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
}

.graph-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 1rem;
  border-bottom: 1px solid var(--vp-c-divider);
  flex-wrap: wrap;
  gap: 1rem;
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
  padding: 0.75rem 1rem;
  border-top: 1px solid var(--vp-c-divider);
}

.hint {
  margin: 0;
  font-size: 0.75rem;
  color: var(--vp-c-text-3);
}
</style>
