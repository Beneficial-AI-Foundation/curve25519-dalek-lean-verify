<script setup lang="ts">
import { reactive, watch, onMounted, nextTick, type PropType } from 'vue'
import type { GraphNode } from '../../types/graph'
import InfoPanel from './InfoPanel.vue'

const props = defineProps({
  selectedNodes: {
    type: Array as PropType<GraphNode[]>,
    required: true
  },
  containerRef: {
    type: Object as PropType<HTMLElement | null>,
    default: null
  },
  getNodeScreenPosition: {
    type: Function as PropType<(nodeId: string) => { x: number; y: number } | null>,
    default: null
  }
})

const emit = defineEmits<{
  (e: 'deselect', nodeId: string): void
  (e: 'focusOn', nodeId: string): void
  (e: 'close'): void
  (e: 'panelPositions', positions: Map<string, { x: number; y: number; width: number; height: number }>): void
}>()

// Panel sizing
const PANEL_MIN_WIDTH = 320
const PANEL_MAX_WIDTH = 700
const PANEL_MIN_HEIGHT = 100
const PANEL_MARGIN = 10

// Compute panel width from longest line in spec statement
function getPanelWidth(node: GraphNode): number {
  if (!node.specStatement) return PANEL_MIN_WIDTH
  const maxLen = Math.max(...node.specStatement.split('\n').map(line => line.length))
  const needed = maxLen * 6.6 + 34
  return Math.max(PANEL_MIN_WIDTH, Math.min(Math.ceil(needed), PANEL_MAX_WIDTH))
}

// Track initial positions and current rects for connector lines
const initialPositions = reactive<Map<string, { x: number; y: number }>>(new Map())
const panelRects = reactive<Map<string, { x: number; y: number; width: number; height: number }>>(new Map())

// Calculate initial position for a new panel
function calculateInitialPosition(nodeId: string, existingPanels: string[]): { x: number; y: number } {
  if (!props.containerRef || !props.getNodeScreenPosition) {
    return { x: 20, y: 60 + existingPanels.length * (PANEL_MIN_HEIGHT + PANEL_MARGIN) }
  }

  const containerRect = props.containerRef.getBoundingClientRect()
  const nodePos = props.getNodeScreenPosition(nodeId)

  if (!nodePos) {
    return { x: 20, y: 60 + existingPanels.length * (PANEL_MIN_HEIGHT + PANEL_MARGIN) }
  }

  const nodeX = nodePos.x - containerRect.left
  const nodeY = nodePos.y - containerRect.top

  const distToLeft = nodeX
  const distToRight = containerRect.width - nodeX

  let x: number
  if (distToRight < distToLeft) {
    x = containerRect.width - PANEL_MAX_WIDTH - PANEL_MARGIN
  } else {
    x = PANEL_MARGIN
  }

  let y = Math.max(PANEL_MARGIN, Math.min(nodeY - 50, containerRect.height - PANEL_MIN_HEIGHT - PANEL_MARGIN))

  // Avoid overlapping with existing panels
  const occupiedRanges: { top: number; bottom: number }[] = []
  for (const existingId of existingPanels) {
    const existingRect = panelRects.get(existingId)
    if (existingRect) {
      const existingOnRight = existingRect.x > containerRect.width / 2
      const newOnRight = x > containerRect.width / 2
      if (existingOnRight === newOnRight) {
        occupiedRanges.push({ top: existingRect.y, bottom: existingRect.y + existingRect.height })
      }
    }
  }

  occupiedRanges.sort((a, b) => a.top - b.top)

  for (const range of occupiedRanges) {
    if (y < range.bottom && y + PANEL_MIN_HEIGHT > range.top) {
      y = range.bottom + PANEL_MARGIN
    }
  }

  y = Math.max(PANEL_MARGIN, Math.min(y, containerRect.height - PANEL_MIN_HEIGHT - PANEL_MARGIN))

  return { x, y }
}

// Watch for nodes being added/removed
watch(() => props.selectedNodes, (newNodes, oldNodes) => {
  const oldIds = new Set((oldNodes || []).map(n => n.id))
  const newIds = newNodes.map(n => n.id)

  // Clean up removed panels
  let removedAny = false
  for (const [id] of initialPositions) {
    if (!newIds.includes(id)) {
      initialPositions.delete(id)
      panelRects.delete(id)
      removedAny = true
    }
  }

  if (removedAny) {
    nextTick(emitPanelPositions)
  }

  // Set initial positions for new panels
  const existingIds = newIds.filter(id => oldIds.has(id))
  for (const node of newNodes) {
    if (!oldIds.has(node.id) && !initialPositions.has(node.id)) {
      nextTick(() => {
        const pos = calculateInitialPosition(node.id, existingIds)
        initialPositions.set(node.id, pos)
        existingIds.push(node.id)
      })
    }
  }
}, { immediate: true })

// Handle position updates from child panels
function onPositionUpdate(nodeId: string, rect: { x: number; y: number; width: number; height: number }) {
  panelRects.set(nodeId, rect)
  emitPanelPositions()
}

function emitPanelPositions() {
  emit('panelPositions', new Map(panelRects))
}

function getInitialPosition(nodeId: string): { x: number; y: number } {
  return initialPositions.get(nodeId) || { x: 20, y: 60 }
}

onMounted(() => {
  nextTick(emitPanelPositions)
})
</script>

<template>
  <div class="info-panels-container" v-if="selectedNodes.length > 0">
    <!-- Close all button -->
    <div class="close-all-floating">
      <span class="panels-count">{{ selectedNodes.length }} selected</span>
      <button class="close-all-btn" @click="emit('close')" title="Close all">
        <svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
          <line x1="18" y1="6" x2="6" y2="18"/>
          <line x1="6" y1="6" x2="18" y2="18"/>
        </svg>
      </button>
    </div>

    <!-- Individual panels -->
    <InfoPanel
      v-for="node in selectedNodes"
      :key="node.id"
      :node="node"
      :initial-position="getInitialPosition(node.id)"
      :container-ref="containerRef"
      :width="getPanelWidth(node)"
      @deselect="emit('deselect', node.id)"
      @focus-on="emit('focusOn', node.id)"
      @position-update="(rect) => onPositionUpdate(node.id, rect)"
    />
  </div>
</template>

<style scoped>
.info-panels-container {
  position: absolute;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  pointer-events: none;
  z-index: 50;
}

.close-all-floating {
  position: absolute;
  right: 1rem;
  top: 0.5rem;
  display: flex;
  align-items: center;
  gap: 0.5rem;
  padding: 0.25rem 0.5rem;
  background: var(--vp-c-bg-elv);
  border: 1px solid var(--vp-c-divider);
  border-radius: 6px;
  pointer-events: auto;
  z-index: 60;
}

.panels-count {
  font-size: 0.75rem;
  color: var(--vp-c-text-2);
}

.close-all-btn {
  display: flex;
  align-items: center;
  justify-content: center;
  padding: 0.25rem;
  background: none;
  border: none;
  color: var(--vp-c-text-2);
  cursor: pointer;
  border-radius: 4px;
}

.close-all-btn:hover {
  background: var(--vp-c-bg-soft);
  color: var(--vp-c-text-1);
}
</style>
