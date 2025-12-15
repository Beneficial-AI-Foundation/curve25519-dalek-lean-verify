import type { FunctionDep } from '../types'

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
  verified: '#4ade80'  // green-400 (softer than node green)
}

// Get color for a function based on its status
export function getNodeColor(func: FunctionDep): string {
  if (func.fully_verified) return nodeColors.fully_verified
  if (func.verified) return nodeColors.verified
  if (func.specified) return nodeColors.specified
  return nodeColors.nothing
}

// Create cytoscape styles array
export function createCytoscapeStyles(borderColor: string) {
  return [
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
  ]
}

// ELK layout configuration
export const elkLayoutConfig = {
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
}

// Cytoscape instance options
export const cytoscapeOptions = {
  minZoom: 0.2,
  maxZoom: 3
}
