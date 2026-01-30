import { computed, reactive, type Ref } from 'vue'
import type { GraphNode, SelectionState } from '../types/graph'

/**
 * Composable for managing multi-node selection in the graph.
 * Supports additive selection (Ctrl+click) and hover state.
 */
export function useGraphSelection(
  nodeMap: Ref<Map<string, GraphNode>>,
  options?: { maxSelections?: number }
) {
  const state = reactive<SelectionState>({
    selectedNodes: new Set(),
    hoveredNode: null,
    maxSelections: options?.maxSelections ?? 5
  })

  // Select a node (optionally additive with Ctrl key)
  function selectNode(nodeId: string, additive: boolean = false): void {
    if (!nodeMap.value.has(nodeId)) return

    if (additive) {
      // Toggle selection in additive mode
      if (state.selectedNodes.has(nodeId)) {
        state.selectedNodes.delete(nodeId)
      } else if (state.selectedNodes.size < state.maxSelections) {
        state.selectedNodes.add(nodeId)
      }
    } else {
      // Replace selection
      state.selectedNodes.clear()
      state.selectedNodes.add(nodeId)
    }
  }

  // Deselect a specific node
  function deselectNode(nodeId: string): void {
    state.selectedNodes.delete(nodeId)
  }

  // Clear all selections
  function clearSelection(): void {
    state.selectedNodes.clear()
  }

  // Toggle a node's selection
  function toggleNode(nodeId: string): void {
    if (state.selectedNodes.has(nodeId)) {
      state.selectedNodes.delete(nodeId)
    } else if (state.selectedNodes.size < state.maxSelections) {
      state.selectedNodes.add(nodeId)
    }
  }

  // Set hover state
  function setHoveredNode(nodeId: string | null): void {
    state.hoveredNode = nodeId
  }

  // Check if a node is selected
  function isSelected(nodeId: string): boolean {
    return state.selectedNodes.has(nodeId)
  }

  // Get array of selected node IDs
  const selectedNodeIds = computed(() => Array.from(state.selectedNodes))

  // Get array of selected GraphNode objects
  const selectedNodesData = computed(() => {
    return selectedNodeIds.value
      .map(id => nodeMap.value.get(id))
      .filter((node): node is GraphNode => node !== undefined)
  })

  // Get the hovered node data
  const hoveredNodeData = computed(() => {
    if (!state.hoveredNode) return null
    return nodeMap.value.get(state.hoveredNode) ?? null
  })

  // Check if we can select more nodes
  const canSelectMore = computed(() => state.selectedNodes.size < state.maxSelections)

  // Selection count
  const selectionCount = computed(() => state.selectedNodes.size)

  return {
    state,
    selectNode,
    deselectNode,
    clearSelection,
    toggleNode,
    setHoveredNode,
    isSelected,
    selectedNodeIds,
    selectedNodesData,
    hoveredNodeData,
    canSelectMore,
    selectionCount
  }
}
