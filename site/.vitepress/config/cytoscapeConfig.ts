import type { NodeStatus } from '../types/graph'

// Node colors based on verification status
export const nodeColors = {
  nothing: '#9ca3af',       // gray-400 - not specified
  specified: '#f59e0b',     // amber-500 - has spec but not verified
  verified: '#86efac',      // green-300 - verified (lighter green)
  fully_verified: '#22c55e' // green-500 - fully verified
}

// Edge colors
export const edgeColors = {
  default: '#94a3b8',  // slate-400
  verified: '#4ade80', // green-400 (softer than node green)
  transitive: '#cbd5e1' // slate-300 - for transitive edges
}

// Group/file colors for compound nodes
export const groupColors = [
  '#3b82f6', // blue-500
  '#8b5cf6', // violet-500
  '#ec4899', // pink-500
  '#f97316', // orange-500
  '#14b8a6', // teal-500
  '#84cc16', // lime-500
  '#ef4444', // red-500
  '#06b6d4', // cyan-500
  '#a855f7', // purple-500
  '#f59e0b', // amber-500
  '#10b981', // emerald-500
  '#6366f1', // indigo-500
  '#f43f5e', // rose-500
  '#0ea5e9', // sky-500
  '#22c55e', // green-500
  '#eab308'  // yellow-500
]

// Get color by NodeStatus type (for adapter use)
export function getNodeColorByStatus(status: NodeStatus): string {
  switch (status) {
    case 'fully_verified':
      return nodeColors.fully_verified
    case 'verified':
      return nodeColors.verified
    case 'specified':
      return nodeColors.specified
    default:
      return nodeColors.nothing
  }
}

// Get a consistent color for a file based on its index
export function getGroupColor(index: number): string {
  return groupColors[index % groupColors.length]
}

// Create cytoscape styles array for regular nodes
export function createCytoscapeStyles(borderColor: string) {
  return [
    {
      selector: 'node',
      style: {
        'background-color': 'data(color)',
        'label': 'data(label)',
        'font-size': '10px',
        'font-weight': 'bold',
        'font-family': 'monospace',
        'text-valign': 'center',
        'text-halign': 'center',
        'text-wrap': 'ellipsis',
        'text-max-width': '80px',
        'width': 90,
        'height': 40,
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
      selector: 'node:active',
      style: {
        'overlay-opacity': 0.1
      }
    },
    {
      selector: 'edge',
      style: {
        'width': 1.5,
        'line-color': 'data(color)',
        'target-arrow-color': 'data(color)',
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
      // Multi-select style
      selector: 'node.selected',
      style: {
        'border-width': 3,
        'border-color': '#7c3aed', // violet-600
        'border-style': 'double'
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
  ]
}

// Create compound node styles for file grouping
export function createCompoundNodeStyles(borderColor: string) {
  const textColor = borderColor === '#ffffff' ? '#e5e7eb' : '#374151'
  const bgColor = borderColor === '#ffffff' ? '#1f2937' : '#ffffff'

  return [
    {
      // Parent/group nodes
      selector: 'node[?isGroup]',
      style: {
        'background-color': 'data(color)',
        'background-opacity': 0.08,
        'border-width': 2,
        'border-color': 'data(color)',
        'border-opacity': 0.5,
        'border-style': 'solid',
        'shape': 'round-rectangle',
        'padding': 25,
        'label': 'data(label)',
        'font-size': '11px',
        'font-weight': 'bold',
        'text-valign': 'top',
        'text-halign': 'center',
        'text-margin-y': 8,
        'text-wrap': 'none',
        'text-max-width': '300px',
        'color': textColor,
        'text-background-color': bgColor,
        'text-background-opacity': 0.9,
        'text-background-shape': 'roundrectangle',
        'text-background-padding': '6px',
        'min-width': 100,
        'min-height': 60
      }
    },
    {
      // Group hover
      selector: 'node[?isGroup]:active',
      style: {
        'background-opacity': 0.15,
        'border-opacity': 0.8
      }
    }
  ]
}

// Layout type for selection
export type LayoutType = 'elk' | 'fcose'

// ELK layout configuration - for grouped view (wider spacing for compound nodes)
export const elkLayoutConfig = {
  name: 'elk',
  elk: {
    algorithm: 'layered',
    'elk.direction': 'RIGHT',
    'elk.spacing.nodeNode': 50,
    'elk.layered.spacing.nodeNodeBetweenLayers': 160,
    'elk.layered.spacing.edgeEdgeBetweenLayers': 25,
    'elk.layered.crossingMinimization.strategy': 'LAYER_SWEEP',
    'elk.layered.nodePlacement.strategy': 'NETWORK_SIMPLEX',
    'elk.layered.compaction.postCompaction.strategy': 'EDGE_LENGTH'
  },
  animate: false,
  fit: true,
  padding: 50
}

// fCoSE layout - fast force-directed with smooth animation support
export const fcoseLayoutConfig = {
  name: 'fcose',
  quality: 'default',
  nodeDimensionsIncludeLabels: true,
  fit: true,
  padding: 30,
  // Animation settings - fcose has native support for smooth scatter → converge
  randomize: true,
  animate: true,
  animationDuration: 800,
  animationEasing: 'ease-out',
  // Force-directed parameters
  nodeRepulsion: 6500,
  idealEdgeLength: 80,
  edgeElasticity: 0.45,
  nestingFactor: 0.1,
  gravity: 0.4,
  gravityRange: 4.5,
  gravityRangeCompound: 1.5,
  gravityCompound: 1.0,
  numIter: 2500,
  tile: true,
  tilingPaddingVertical: 10,
  tilingPaddingHorizontal: 10
}

// Get layout config by type
export function getLayoutConfig(type: LayoutType) {
  switch (type) {
    case 'elk':
      return elkLayoutConfig
    case 'fcose':
      return fcoseLayoutConfig
    default:
      return fcoseLayoutConfig
  }
}

// Layout display names
export const layoutOptions: { value: LayoutType; label: string }[] = [
  { value: 'fcose', label: 'Force-Directed' },
  { value: 'elk', label: 'Hierarchical' }
]

// Cytoscape instance options
export const cytoscapeOptions = {
  minZoom: 0.1,
  maxZoom: 4
}
