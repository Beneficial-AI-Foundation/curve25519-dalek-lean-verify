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

// Store sigma and graph instances
let sigmaInstance: any = null
let graphInstance: any = null

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
  // Return last 2 components for better identification
  return parts.slice(-2).join('.')
}

async function initGraph() {
  if (!container.value || !isClient.value) return

  isLoading.value = true

  // Dynamic imports - only load on client
  const [
    { default: Graph },
    Sigma,
    forceAtlas2Module,
    edgeArrowProgram
  ] = await Promise.all([
    import('graphology'),
    import('sigma'),
    import('graphology-layout-forceatlas2'),
    import('sigma/rendering')
  ])

  const SigmaClass = Sigma.default || Sigma
  const forceAtlas2 = forceAtlas2Module.default || forceAtlas2Module
  const EdgeArrowProgram = edgeArrowProgram.EdgeArrowProgram

  // Clean up existing sigma instance
  if (sigmaInstance) {
    sigmaInstance.kill()
    sigmaInstance = null
  }

  // Create directed graph
  graphInstance = new Graph({ type: 'directed' })

  // Create a map for quick lookup
  const funcMap = new Map(props.functions.map(f => [f.lean_name, f]))

  // Add nodes
  props.functions.forEach((func) => {
    graphInstance.addNode(func.lean_name, {
      label: getShortLabel(func.lean_name),
      x: Math.random() * 100,
      y: Math.random() * 100,
      size: 10,
      color: getNodeColor(func)
    })
  })

  // Add edges (dependencies)
  props.functions.forEach(func => {
    func.dependencies.forEach(dep => {
      // Only add edge if target exists in our function set
      if (funcMap.has(dep)) {
        // Check if edge already exists
        if (!graphInstance.hasEdge(func.lean_name, dep)) {
          graphInstance.addEdge(func.lean_name, dep, {
            size: 2,
            color: '#94a3b8'
          })
        }
      }
    })
  })

  // Apply ForceAtlas2 layout
  forceAtlas2.assign(graphInstance, {
    iterations: 100,
    settings: {
      gravity: 1,
      scalingRatio: 10,
      strongGravityMode: false,
      barnesHutOptimize: true
    }
  })

  // Create sigma instance with edge arrows
  sigmaInstance = new SigmaClass(graphInstance, container.value, {
    defaultEdgeType: 'arrow',
    edgeProgramClasses: {
      arrow: EdgeArrowProgram
    },
    labelRenderedSizeThreshold: 8,
    labelFont: 'monospace',
    labelSize: 11,
    labelColor: { color: '#374151' },
    allowInvalidContainer: true,
    renderEdgeLabels: false
  })

  // Add hover behavior for highlighting connections
  sigmaInstance.on('enterNode', ({ node }: { node: string }) => {
    highlightConnections(node)
  })

  sigmaInstance.on('leaveNode', () => {
    resetHighlight()
  })

  isLoading.value = false
}

function highlightConnections(node: string) {
  if (!graphInstance || !sigmaInstance) return

  const connectedNodes = new Set<string>([node])

  // Get all connected nodes (both directions)
  graphInstance.forEachEdge(node, (edge: string, attrs: any, source: string, target: string) => {
    connectedNodes.add(source)
    connectedNodes.add(target)
  })

  // Dim non-connected nodes
  graphInstance.forEachNode((n: string) => {
    graphInstance.setNodeAttribute(n, 'hidden', !connectedNodes.has(n))
  })

  sigmaInstance.refresh()
}

function resetHighlight() {
  if (!graphInstance || !sigmaInstance) return

  graphInstance.forEachNode((n: string) => {
    graphInstance.setNodeAttribute(n, 'hidden', false)
  })

  sigmaInstance.refresh()
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
  if (sigmaInstance) {
    sigmaInstance.kill()
    sigmaInstance = null
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
      <p class="hint">Hover over nodes to highlight connections. Arrows point from function to its dependencies.</p>
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
