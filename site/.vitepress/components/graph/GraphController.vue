<script setup lang="ts">
import { ref, computed, watch, onMounted, onUnmounted, type PropType } from 'vue'
import type { FunctionRecord } from '../../data/deps.data'
import type { StatusEntry, FileGroup, NodeClickEvent, NodeHoverEvent, SubgraphMode } from '../../types'
import { useGraphData } from '../../composables/useGraphData'
import { useGraphFiltering } from '../../composables/useGraphFiltering'
import { useGraphStats } from '../../composables/useGraphStats'
import { useGraphSelection } from '../../composables/useGraphSelection'
import { getGroupColor, type LayoutType } from '../../config/cytoscapeConfig'
import GraphCanvas from './GraphCanvas.vue'
import GraphControls from './GraphControls.vue'
import InfoPanels from './InfoPanels.vue'

const props = defineProps({
  functions: {
    type: Array as PropType<FunctionRecord[]>,
    required: true
  },
  statusEntries: {
    type: Array as PropType<StatusEntry[]>,
    default: () => []
  }
})

// Convert to ref for composables
const functionsRef = computed(() => props.functions)

// Process graph data (filter hidden and artifacts, compute transitive deps)
const { processedData } = useGraphData(functionsRef)

// Filtering
const {
  filterState,
  filteredData,
  toggleSourceFile,
  enableAllSourceFiles,
  disableAllSourceFiles,
  soloSourceFile,
  setFocusedFunction,
  setSubgraphMode,
  setSubgraphDepth
} = useGraphFiltering(processedData)

// Stats
const {
  globalStats,
  fileStatsSorted,
  filteredStats,
  filteredSummaryText
} = useGraphStats(processedData, filteredData)

// Selection
const nodeMapRef = computed(() => processedData.value.nodeMap)
const {
  selectNode,
  deselectNode,
  clearSelection,
  selectedNodeIds,
  selectedNodesData,
  setHoveredNode
} = useGraphSelection(nodeMapRef, { maxSelections: 5 })

// View state
const showGroups = ref(false)
const isFullscreen = ref(false)
const layoutType = ref<LayoutType>('cose-bilkent')

// Refs
const canvasRef = ref<InstanceType<typeof GraphCanvas> | null>(null)
const wrapperRef = ref<HTMLElement | null>(null)

// Tooltip state
const tooltip = ref<{ visible: boolean; text: string; x: number; y: number }>({
  visible: false,
  text: '',
  x: 0,
  y: 0
})

// Connector line state (links info panel to its node)
const hoveredPanelNodeId = ref<string | null>(null)
const connectorLine = ref<{ x1: number; y1: number; x2: number; y2: number } | null>(null)

// Update connector line when panel is hovered
function updateConnectorLine() {
  if (!hoveredPanelNodeId.value) {
    connectorLine.value = null
    return
  }

  // Get node position from cytoscape adapter
  const nodePos = canvasRef.value?.getNodeScreenPosition(hoveredPanelNodeId.value)
  if (!nodePos) {
    connectorLine.value = null
    return
  }

  // Find the hovered panel element to get its exact position
  const panelElements = document.querySelectorAll('.info-panel')
  const panelIndex = selectedNodesData.value.findIndex(n => n.id === hoveredPanelNodeId.value)
  const panelEl = panelElements[panelIndex] as HTMLElement | undefined

  if (!panelEl) {
    connectorLine.value = null
    return
  }

  const panelRect = panelEl.getBoundingClientRect()

  // Draw line from node to left edge of panel, vertically centered on panel
  connectorLine.value = {
    x1: nodePos.x,
    y1: nodePos.y,
    x2: panelRect.left,
    y2: panelRect.top + panelRect.height / 2
  }
}

function handlePanelHover(nodeId: string | null) {
  hoveredPanelNodeId.value = nodeId
  updateConnectorLine()
}

// Check if filters are active (affects whether we show stats on groups)
// Only focused function hides stats - file filtering still shows stats
const hasActiveFilters = computed(() => {
  // Check if a function is focused (subgraph mode)
  return !!filterState.focusedFunction
})

// Build file groups for compound nodes
const fileGroups = computed<FileGroup[]>(() => {
  if (!showGroups.value) return []

  const groups: FileGroup[] = []
  const nodesByFile = new Map<string, string[]>()

  // Group nodes by source file
  for (const node of filteredData.value.nodes) {
    const file = node.sourceFile || 'unknown'
    if (!nodesByFile.has(file)) {
      nodesByFile.set(file, [])
    }
    nodesByFile.get(file)!.push(node.id)
  }

  // Build groups - only show stats when no filters are active
  const canShowStats = !hasActiveFilters.value
  let index = 0
  for (const [file, nodeIds] of nodesByFile) {
    const stats = globalStats.value.bySourceFile.get(file)
    if (stats && nodeIds.length > 0) {
      const pct = stats.total > 0 ? Math.round((stats.verified / stats.total) * 100) : 0
      groups.push({
        id: `file-${index}`,
        label: getFileName(file) + (canShowStats ? ` (${stats.verified}/${stats.total}, ${pct}%)` : ''),
        sourceFile: file,
        nodeIds,
        stats,
        color: getGroupColor(index),
        collapsed: false
      })
      index++
    }
  }

  return groups
})

// Helper to get filename from path
function getFileName(path: string): string {
  if (path === 'unknown') return 'Unknown'
  const parts = path.split('/')
  return parts[parts.length - 1]
}

// Event handlers
function handleNodeClick(event: NodeClickEvent) {
  selectNode(event.nodeId, event.isCtrlKey)
}

function handleNodeHover(event: NodeHoverEvent) {
  setHoveredNode(event.nodeId)

  if (event.nodeId && event.position) {
    const node = processedData.value.nodeMap.get(event.nodeId)
    if (node) {
      tooltip.value = {
        visible: true,
        text: node.fullLabel,
        x: event.position.x + 10,
        y: event.position.y + 10
      }
      // Highlight connections
      canvasRef.value?.highlightConnections(event.nodeId)
    }
  } else {
    tooltip.value.visible = false
    canvasRef.value?.resetHighlight()
  }
}

function handleBackgroundClick() {
  clearSelection()
}

function handleFocusOn(nodeId: string) {
  setFocusedFunction(nodeId)
  setSubgraphMode('both')
  // Note: Don't call centerOnNode here - the subsequent layout will fitToView automatically
  // which is better since it shows the entire filtered subgraph
}

function handleClearFocus() {
  setFocusedFunction(null)
  setSubgraphMode('all')
}

function handleDeselect(nodeId: string) {
  deselectNode(nodeId)
}

function handleCloseAllPanels() {
  clearSelection()
}

function handleFitToView() {
  canvasRef.value?.fitToView()
}

function handleRecenter() {
  canvasRef.value?.fitToView(30)
}

function handleReset() {
  // Reset all filters
  enableAllSourceFiles()
  setFocusedFunction(null)
  setSubgraphMode('all')
  // Reset view options
  showGroups.value = false
  layoutType.value = 'cose-bilkent'
  // Clear selection
  clearSelection()
  // Reset layout and fit to view
  setTimeout(async () => {
    await canvasRef.value?.setLayout('cose-bilkent')
    canvasRef.value?.fitToView(30)
  }, 100)
}

function handleToggleFullscreen() {
  if (!wrapperRef.value) return

  if (!document.fullscreenElement) {
    wrapperRef.value.requestFullscreen().catch(err => {
      console.error('Error attempting to enable fullscreen:', err)
    })
  } else {
    document.exitFullscreen()
  }
}

async function handleSetLayout(newLayout: LayoutType) {
  layoutType.value = newLayout
  await canvasRef.value?.setLayout(newLayout)
}

function handlePreloadElk() {
  canvasRef.value?.preloadElk()
}

async function handleToggleShowGroups() {
  showGroups.value = !showGroups.value
  // Auto-switch to hierarchical layout when enabling groups
  if (showGroups.value && layoutType.value !== 'elk') {
    layoutType.value = 'elk'
    await canvasRef.value?.setLayout('elk')
  }
}

// Helper to enable groups view with hierarchical layout
async function enableGroupsView() {
  if (!showGroups.value) {
    showGroups.value = true
    if (layoutType.value !== 'elk') {
      layoutType.value = 'elk'
      await canvasRef.value?.setLayout('elk')
    }
  }
}

// Wrapper handlers for source file filtering that auto-enable groups
async function handleToggleSourceFile(file: string) {
  toggleSourceFile(file)
  // Check if we're now filtering (not all files enabled)
  if (filterState.enabledSourceFiles.size !== processedData.value.sourceFiles.length) {
    await enableGroupsView()
  }
}

async function handleSoloSourceFile(file: string) {
  soloSourceFile(file)
  // Solo always results in filtering, so enable groups
  await enableGroupsView()
}

function handleFullscreenChange() {
  isFullscreen.value = !!document.fullscreenElement
  // Resize graph when fullscreen changes
  setTimeout(() => {
    canvasRef.value?.fitToView(30)
  }, 100)
}

onMounted(() => {
  document.addEventListener('fullscreenchange', handleFullscreenChange)
})

onUnmounted(() => {
  document.removeEventListener('fullscreenchange', handleFullscreenChange)
})
</script>

<template>
  <div ref="wrapperRef" class="graph-controller" :class="{ fullscreen: isFullscreen }">
    <GraphControls
      :source-files="processedData.sourceFiles"
      :enabled-source-files="filterState.enabledSourceFiles"
      :file-stats="fileStatsSorted"
      :focused-function="filterState.focusedFunction"
      :subgraph-mode="filterState.subgraphMode"
      :show-groups="showGroups"
      :summary-text="filteredSummaryText"
      :is-fullscreen="isFullscreen"
      :all-nodes="processedData.nodes"
      :layout-type="layoutType"
      @toggle-source-file="handleToggleSourceFile"
      @enable-all-source-files="enableAllSourceFiles"
      @solo-source-file="handleSoloSourceFile"
      @set-subgraph-mode="setSubgraphMode"
      @clear-focus="handleClearFocus"
      @toggle-show-groups="handleToggleShowGroups"
      @fit-to-view="handleFitToView"
      @recenter="handleRecenter"
      @reset="handleReset"
      @toggle-fullscreen="handleToggleFullscreen"
      @focus-on-function="handleFocusOn"
      @set-layout="handleSetLayout"
      @preload-elk="handlePreloadElk"
    />

    <div class="graph-main">
      <GraphCanvas
        ref="canvasRef"
        :nodes="filteredData.nodes"
        :edges="filteredData.edges"
        :groups="fileGroups"
        :show-groups="showGroups"
        :selected-node-ids="selectedNodeIds"
        @node-click="handleNodeClick"
        @node-double-click="(e) => handleFocusOn(e.nodeId)"
        @node-hover="handleNodeHover"
        @background-click="handleBackgroundClick"
      />

      <InfoPanels
        :selected-nodes="selectedNodesData"
        @deselect="handleDeselect"
        @focus-on="handleFocusOn"
        @close="handleCloseAllPanels"
        @panel-hover="handlePanelHover"
      />

      <!-- Tooltip -->
      <div
        v-if="tooltip.visible"
        class="graph-tooltip"
        :style="{ left: tooltip.x + 'px', top: tooltip.y + 'px' }"
      >
        {{ tooltip.text }}
      </div>

      <!-- Connector line from info panel to node -->
      <svg
        v-if="connectorLine"
        class="connector-svg"
        :style="{
          position: 'fixed',
          top: 0,
          left: 0,
          width: '100vw',
          height: '100vh',
          pointerEvents: 'none',
          zIndex: 40
        }"
      >
        <line
          :x1="connectorLine.x1"
          :y1="connectorLine.y1"
          :x2="connectorLine.x2"
          :y2="connectorLine.y2"
          stroke="var(--vp-c-brand-1)"
          stroke-width="2"
          stroke-dasharray="6 4"
          stroke-opacity="0.6"
        />
        <!-- Small circle at the node end -->
        <circle
          :cx="connectorLine.x1"
          :cy="connectorLine.y1"
          r="5"
          fill="var(--vp-c-brand-1)"
          fill-opacity="0.7"
        />
      </svg>
    </div>

    <!-- Legend -->
    <div class="graph-legend">
      <div class="legend-item">
        <span class="legend-dot" style="background-color: #22c55e;"></span>
        <span>Verified</span>
      </div>
      <div class="legend-item">
        <span class="legend-dot" style="background-color: #f59e0b;"></span>
        <span>Specified</span>
      </div>
      <div class="legend-item">
        <span class="legend-dot" style="background-color: #9ca3af;"></span>
        <span>Not Specified</span>
      </div>
      <div class="legend-divider"></div>
      <div class="legend-hint">
        Click to select | Ctrl+Click for multi-select | Hover to highlight connections
      </div>
    </div>
  </div>
</template>

<style scoped>
.graph-controller {
  display: flex;
  flex-direction: column;
  background: var(--vp-c-bg-soft);
  border-radius: 8px;
  overflow: hidden;
  margin: 2rem 0;
}

.graph-main {
  position: relative;
  height: 600px;
  border: 1px solid var(--vp-c-divider);
  margin: 0.5rem;
  border-radius: 4px;
  overflow: hidden;
}

.graph-tooltip {
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

.graph-legend {
  display: flex;
  align-items: center;
  gap: 1rem;
  padding: 0.75rem 1rem;
  border-top: 1px solid var(--vp-c-divider);
  flex-wrap: wrap;
}

.legend-item {
  display: flex;
  align-items: center;
  gap: 0.375rem;
  font-size: 0.8125rem;
  color: var(--vp-c-text-2);
}

.legend-dot {
  width: 10px;
  height: 10px;
  border-radius: 50%;
}

.legend-divider {
  width: 1px;
  height: 1rem;
  background: var(--vp-c-divider);
}

.legend-hint {
  font-size: 0.75rem;
  color: var(--vp-c-text-3);
  margin-left: auto;
}

/* Fullscreen mode */
.graph-controller.fullscreen {
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

.graph-controller.fullscreen .graph-main {
  flex: 1;
  height: auto;
  margin: 0.5rem;
}

@media (max-width: 768px) {
  .graph-main {
    height: 400px;
  }

  .legend-hint {
    width: 100%;
    margin-left: 0;
    text-align: center;
  }
}
</style>
