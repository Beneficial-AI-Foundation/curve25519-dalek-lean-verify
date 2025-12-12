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

// Get short label from lean_name (last 2 components)
function getShortLabel(lean_name: string): string {
  const parts = lean_name.split('.')
  return parts.slice(-2).join('.')
}

function loadScript(src: string): Promise<void> {
  return new Promise((resolve, reject) => {
    if ((window as any).ForceGraph3D) {
      resolve()
      return
    }
    const script = document.createElement('script')
    script.src = src
    script.onload = () => resolve()
    script.onerror = reject
    document.head.appendChild(script)
  })
}

async function initGraph() {
  if (!container.value || !isClient.value) return

  isLoading.value = true

  // Load from CDN to avoid Vite bundling issues with WebGPU
  await loadScript('https://unpkg.com/3d-force-graph@1.73.3/dist/3d-force-graph.min.js')
  const ForceGraph3D = (window as any).ForceGraph3D

  // Clean up existing instance
  if (graphInstance) {
    graphInstance._destructor?.()
    graphInstance = null
  }

  // Create a map for quick lookup
  const funcMap = new Map(props.functions.map(f => [f.lean_name, f]))

  // Build nodes with labels
  const nodes = props.functions.map(func => ({
    id: func.lean_name,
    label: getShortLabel(func.lean_name),
    color: getNodeColor(func),
    specified: func.specified,
    verified: func.verified,
    fullyVerified: func.fully_verified
  }))

  // Build links
  const links: any[] = []
  props.functions.forEach(func => {
    func.dependencies.forEach(dep => {
      if (funcMap.has(dep)) {
        links.push({
          source: func.lean_name,
          target: dep
        })
      }
    })
  })

  // Create 3D force graph
  graphInstance = ForceGraph3D()(container.value)
    .graphData({ nodes, links })
    .nodeLabel((node: any) => `<div style="color: #374151; font-size: 12px; font-family: monospace; background: rgba(255,255,255,0.9); padding: 2px 6px; border-radius: 4px;">${node.label}</div>`)
    .nodeColor((node: any) => node.color)
    .nodeVal(10)
    .nodeOpacity(0.95)
    .nodeResolution(24)
    .linkColor(() => '#94a3b8')
    .linkOpacity(0.5)
    .linkWidth(1.5)
    .linkDirectionalArrowLength(6)
    .linkDirectionalArrowRelPos(1)
    .linkDirectionalArrowColor(() => '#64748b')
    .backgroundColor('#ffffff')
    .showNavInfo(false)
    .onNodeHover((node: any) => {
      container.value!.style.cursor = node ? 'pointer' : 'default'
    })
    .onNodeClick((node: any) => {
      // Focus on node
      const distance = 120
      const distRatio = 1 + distance / Math.hypot(node.x, node.y, node.z)
      graphInstance.cameraPosition(
        { x: node.x * distRatio, y: node.y * distRatio, z: node.z * distRatio },
        node,
        1000
      )
    })

  // Adjust forces for better layout
  graphInstance.d3Force('charge')?.strength(-100)
  graphInstance.d3Force('link')?.distance(50)

  isLoading.value = false
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
  if (graphInstance) {
    graphInstance._destructor?.()
    graphInstance = null
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
        <span>Loading 3D graph...</span>
      </div>
    </div>
    <div class="graph-footer">
      <p class="hint">Click and drag to rotate. Scroll to zoom. Click a node to focus on it. Arrows point from function to its dependencies.</p>
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
  height: 700px;
  background: #ffffff;
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
  background: #ffffff;
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
