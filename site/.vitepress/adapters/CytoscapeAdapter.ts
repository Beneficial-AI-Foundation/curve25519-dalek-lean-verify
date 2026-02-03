import type {
  IVisualizationAdapter,
  InitOptions
} from './types'
import { defaultInitOptions } from './types'
import type {
  GraphNode,
  GraphEdge,
  FileGroup,
  NodeStyle,
  EdgeStyle,
  GroupStyle,
  LayoutOptions,
  NodeClickEvent,
  NodeHoverEvent
} from '../types/graph'
import {
  edgeColors,
  getNodeColorByStatus,
  createCytoscapeStyles,
  createCompoundNodeStyles,
  getLayoutConfig,
  type LayoutType
} from '../config/cytoscapeConfig'

type CytoscapeInstance = any
type CytoscapeNode = any
type CytoscapeEdge = any

/**
 * Cytoscape.js adapter implementing the IVisualizationAdapter interface.
 * Provides graph visualization with ELK layout and compound nodes for file grouping.
 */
export class CytoscapeAdapter implements IVisualizationAdapter {
  private cy: CytoscapeInstance | null = null
  private cytoscape: any = null  // Store cytoscape constructor for lazy extension registration
  private container: HTMLElement | null = null
  private options: InitOptions = defaultInitOptions
  private groupsVisible: boolean = false
  private currentTheme: 'light' | 'dark' = 'light'
  private currentLayoutType: LayoutType = 'fcose'
  private elkLoaded: boolean = false  // Track if ELK extension is loaded

  // Event handler cleanup functions
  private cleanupFunctions: (() => void)[] = []

  // Elastic drag state (only active in force-directed layout)
  private elasticDragEnabled: boolean = true

  // Layout state - prevent concurrent layouts
  private layoutRunning: boolean = false
  private pendingLayoutResolve: (() => void) | null = null

  // ============ Lifecycle ============

  async initialize(container: HTMLElement, options?: Partial<InitOptions>): Promise<void> {
    this.container = container
    this.options = { ...defaultInitOptions, ...options }
    this.currentTheme = this.options.theme

    // Dynamic import - only load cytoscape core and the default layout
    // ELK (~1.4MB) is loaded lazily when user switches to hierarchical layout
    this.cytoscape = (await import('cytoscape')).default
    // @ts-ignore - no types for cytoscape-fcose
    const fcose = (await import('cytoscape-fcose')).default

    // Register only the default layout (fcose) on init
    this.cytoscape.use(fcose)

    // Create cytoscape instance
    const borderColor = this.currentTheme === 'dark' ? '#ffffff' : '#374151'

    this.cy = this.cytoscape({
      container,
      elements: [],
      style: [
        ...createCytoscapeStyles(borderColor),
        ...createCompoundNodeStyles(borderColor)
      ],
      minZoom: this.options.minZoom,
      maxZoom: this.options.maxZoom
    })

    // Set up elastic drag behavior
    this.setupElasticDrag()
  }

  /**
   * Set up elastic drag behavior - connected nodes move proportionally when dragging.
   * Only active in force-directed layout (fcose), not hierarchical (elk).
   */
  private setupElasticDrag(): void {
    if (!this.cy || !this.elasticDragEnabled) return

    let draggedNode: CytoscapeNode | null = null
    // Map of nodeId -> { position, distance } where distance is graph distance (hops)
    let connectedNodes: Map<string, { pos: { x: number; y: number }; hops: number }> = new Map()
    let dragStartPos: { x: number; y: number } | null = null

    const onGrab = (e: any) => {
      // Only enable elastic drag in force-directed layout
      if (this.currentLayoutType !== 'fcose') return

      const node = e.target
      if (!node.isNode() || node.data('isGroup')) return

      draggedNode = node
      dragStartPos = { ...node.position() }
      connectedNodes.clear()

      // Find connected nodes up to 2 hops away using BFS
      const visited = new Set<string>([node.id()])
      const queue: Array<{ node: CytoscapeNode; hops: number }> = [{ node, hops: 0 }]

      while (queue.length > 0) {
        const { node: currentNode, hops } = queue.shift()!
        if (hops >= 2) continue  // Max 2 hops

        // Get all neighbors (both incoming and outgoing edges)
        const neighbors = currentNode.neighborhood('node[!isGroup]')
        neighbors.forEach((neighbor: CytoscapeNode) => {
          if (!visited.has(neighbor.id())) {
            visited.add(neighbor.id())
            const neighborHops = hops + 1
            connectedNodes.set(neighbor.id(), {
              pos: { ...neighbor.position() },
              hops: neighborHops
            })
            queue.push({ node: neighbor, hops: neighborHops })
          }
        })
      }
    }

    const onDrag = () => {
      if (!draggedNode || !dragStartPos || this.currentLayoutType !== 'fcose') return

      const currentPos = draggedNode.position()
      const dx = currentPos.x - dragStartPos.x
      const dy = currentPos.y - dragStartPos.y

      // Move connected nodes based on graph distance (hops)
      connectedNodes.forEach(({ pos, hops }, nodeId) => {
        const node = this.cy!.getElementById(nodeId)
        if (node.length === 0) return

        // Influence decreases with hops: 1 hop = 0.5, 2 hops = 0.25
        const influence = Math.pow(0.5, hops)

        node.position({
          x: pos.x + dx * influence,
          y: pos.y + dy * influence
        })
      })
    }

    const onFree = () => {
      draggedNode = null
      dragStartPos = null
      connectedNodes.clear()
    }

    this.cy.on('grab', 'node', onGrab)
    this.cy.on('drag', 'node', onDrag)
    this.cy.on('free', 'node', onFree)

    this.cleanupFunctions.push(() => {
      this.cy?.off('grab', 'node', onGrab)
      this.cy?.off('drag', 'node', onDrag)
      this.cy?.off('free', 'node', onFree)
    })
  }

  /**
   * Lazily load the ELK layout extension when needed.
   * ELK is ~1.4MB so we defer loading until user actually needs hierarchical layout.
   */
  private async ensureElkLoaded(): Promise<void> {
    if (this.elkLoaded || !this.cytoscape) return

    // @ts-ignore - no types for cytoscape-elk
    const elk = (await import('cytoscape-elk')).default
    this.cytoscape.use(elk)
    this.elkLoaded = true
  }

  /**
   * Preload ELK in the background during idle time.
   * Call this after the graph is displayed to have ELK ready when user needs it.
   */
  preloadElk(): void {
    if (this.elkLoaded || !this.cytoscape) return

    // Use requestIdleCallback if available, otherwise setTimeout
    const schedulePreload = (window as any).requestIdleCallback || ((cb: () => void) => setTimeout(cb, 1000))

    schedulePreload(() => {
      // Don't await - let it load in background
      this.ensureElkLoaded()
    })
  }

  destroy(): void {
    // Clean up event handlers
    this.cleanupFunctions.forEach(fn => fn())
    this.cleanupFunctions = []

    if (this.cy) {
      this.cy.destroy()
      this.cy = null
    }
    this.container = null
  }

  isInitialized(): boolean {
    return this.cy !== null
  }

  // ============ Data Management ============

  setData(nodes: GraphNode[], edges: GraphEdge[]): void {
    if (!this.cy || !this.container) return

    // Build cytoscape elements (positions will be set by layout)
    const cyNodes = nodes.map(node => ({
      data: {
        id: node.id,
        label: node.label,
        fullLabel: node.fullLabel,
        color: getNodeColorByStatus(node.status),
        status: node.status,
        sourceFile: node.sourceFile,
        isTransitive: node.isTransitiveTarget
      }
    }))

    const cyEdges = edges.map(edge => ({
      data: {
        id: edge.id,
        source: edge.source,
        target: edge.target,
        color: this.getEdgeColor(nodes, edge.target),
        isTransitive: edge.isTransitive
      }
    }))

    // Replace all elements
    this.cy.elements().remove()
    this.cy.add([...cyNodes, ...cyEdges])

    // Run layout with scatter animation
    this.runLayoutWithScatterAnimation()
  }

  /**
   * Run initial layout with scatter-to-converge animation.
   * We manually scatter nodes across the viewport first, then run fcose
   * with randomize:false to animate from our scattered positions.
   */
  private async runLayoutWithScatterAnimation(): Promise<void> {
    if (!this.cy) return

    // If a layout is already running, stop it first
    if (this.layoutRunning) {
      this.cy.stop()
      if (this.pendingLayoutResolve) {
        this.pendingLayoutResolve()
        this.pendingLayoutResolve = null
      }
    }

    this.layoutRunning = true

    // Lazy-load ELK if needed
    if (this.currentLayoutType === 'elk') {
      await this.ensureElkLoaded()
    }

    // Update edge curve style based on layout type
    this.updateEdgeCurveStyle()

    // Get layout config
    const baseConfig = getLayoutConfig(this.currentLayoutType)

    // For fcose: manually scatter nodes across viewport, then animate to final positions
    if (this.currentLayoutType === 'fcose' && this.container) {
      const rect = this.container.getBoundingClientRect()
      const width = rect.width || 800
      const height = rect.height || 600
      const padding = 50

      // Scatter nodes randomly across the viewport area
      const nonGroupNodes = this.cy.nodes('[!isGroup]')
      nonGroupNodes.forEach((node: CytoscapeNode) => {
        node.position({
          x: padding + Math.random() * (width - 2 * padding),
          y: padding + Math.random() * (height - 2 * padding)
        })
      })

      // Run fcose with randomize:false so it uses our scattered positions
      // Disable fit to prevent viewport jump at end - we'll fit smoothly after
      const layoutConfig = {
        ...baseConfig,
        randomize: false,  // Use our manually scattered positions
        fit: false         // Don't snap viewport at end
      }

      return new Promise((resolve) => {
        this.pendingLayoutResolve = resolve
        const layout = this.cy!.layout(layoutConfig)
        layout.on('layoutstop', () => {
          this.layoutRunning = false
          this.pendingLayoutResolve = null
          // Smoothly animate to fit the final layout
          this.cy!.animate({
            fit: { eles: this.cy!.elements(), padding: 30 }
          }, {
            duration: 300,
            easing: 'ease-out',
            complete: () => resolve()
          })
        })
        layout.run()
      })
    }

    // For ELK or other layouts, run normally
    return new Promise((resolve) => {
      this.pendingLayoutResolve = resolve
      const layout = this.cy!.layout(baseConfig)
      layout.on('layoutstop', () => {
        this.layoutRunning = false
        this.pendingLayoutResolve = null
        if (this.currentLayoutType === 'elk') {
          this.fitToView()
        }
        resolve()
      })
      layout.run()
    })
  }

  private getEdgeColor(nodes: GraphNode[], targetId: string): string {
    const target = nodes.find(n => n.id === targetId)
    if (target && (target.status === 'verified' || target.status === 'fully_verified')) {
      return edgeColors.verified
    }
    return edgeColors.default
  }

  updateNodes(nodes: GraphNode[]): void {
    if (!this.cy) return

    for (const node of nodes) {
      const cyNode = this.cy.getElementById(node.id)
      if (cyNode.length > 0) {
        cyNode.data('label', node.label)
        cyNode.data('fullLabel', node.fullLabel)
        cyNode.data('color', getNodeColorByStatus(node.status))
        cyNode.data('status', node.status)
      }
    }
  }

  setGroups(groups: FileGroup[]): void {
    if (!this.cy) return

    // Get current group IDs
    const currentGroupIds = new Set<string>()
    this.cy.nodes('[?isGroup]').forEach((node: CytoscapeNode) => {
      currentGroupIds.add(node.id())
    })

    // If groups should be hidden or empty, remove all groups
    if (!this.groupsVisible || groups.length === 0) {
      // First, orphan all child nodes (remove parent reference)
      this.cy.nodes().forEach((node: CytoscapeNode) => {
        if (!node.data('isGroup') && node.parent().length > 0) {
          node.move({ parent: null })
        }
      })
      // Then remove group nodes
      this.cy.nodes('[?isGroup]').remove()
      return
    }

    // Build new group map
    const newGroupMap = new Map<string, FileGroup>()
    for (const group of groups) {
      newGroupMap.set(`group-${group.id}`, group)
    }

    // Check if this is just a label update (same groups, same nodes)
    const isLabelOnlyUpdate = currentGroupIds.size === groups.length &&
      groups.every(g => currentGroupIds.has(`group-${g.id}`))

    if (isLabelOnlyUpdate) {
      // Just update labels for existing groups
      for (const group of groups) {
        const groupNode = this.cy.getElementById(`group-${group.id}`)
        if (groupNode.length > 0) {
          groupNode.data('label', group.label)
          groupNode.data('color', group.color)
          groupNode.data('stats', group.stats)
        }
      }
      return
    }

    // Full rebuild needed - first orphan all children
    this.cy.nodes().forEach((node: CytoscapeNode) => {
      if (!node.data('isGroup') && node.parent().length > 0) {
        node.move({ parent: null })
      }
    })

    // Remove all existing groups
    this.cy.nodes('[?isGroup]').remove()

    // Add new parent nodes for each group
    for (const group of groups) {
      // Add parent node
      this.cy.add({
        data: {
          id: `group-${group.id}`,
          label: group.label,
          isGroup: true,
          color: group.color,
          stats: group.stats
        }
      })

      // Set parent for child nodes
      for (const nodeId of group.nodeIds) {
        const node = this.cy.getElementById(nodeId)
        if (node.length > 0) {
          node.move({ parent: `group-${group.id}` })
        }
      }
    }

    // Re-run layout to accommodate groups
    this.runLayout()
  }

  setGroupsVisible(visible: boolean): void {
    this.groupsVisible = visible
    // Groups will be re-rendered on next setGroups call
  }

  // ============ Interaction Handlers ============

  onNodeClick(handler: (event: NodeClickEvent) => void): () => void {
    if (!this.cy) return () => {}

    const listener = (e: any) => {
      const node = e.target
      if (node.isNode() && !node.data('isGroup')) {
        handler({
          nodeId: node.id(),
          originalEvent: e.originalEvent,
          isCtrlKey: e.originalEvent?.ctrlKey || e.originalEvent?.metaKey || false,
          isShiftKey: e.originalEvent?.shiftKey || false
        })
      }
    }

    this.cy.on('tap', 'node', listener)

    const cleanup = () => {
      this.cy?.off('tap', 'node', listener)
    }
    this.cleanupFunctions.push(cleanup)
    return cleanup
  }

  onNodeHover(handler: (event: NodeHoverEvent) => void): () => void {
    if (!this.cy) return () => {}

    const mouseoverListener = (e: any) => {
      const node = e.target
      if (node.isNode() && !node.data('isGroup')) {
        handler({
          nodeId: node.id(),
          position: {
            x: e.originalEvent?.clientX || 0,
            y: e.originalEvent?.clientY || 0
          }
        })
      }
    }

    const mouseoutListener = () => {
      handler({ nodeId: null, position: null })
    }

    this.cy.on('mouseover', 'node', mouseoverListener)
    this.cy.on('mouseout', 'node', mouseoutListener)

    const cleanup = () => {
      this.cy?.off('mouseover', 'node', mouseoverListener)
      this.cy?.off('mouseout', 'node', mouseoutListener)
    }
    this.cleanupFunctions.push(cleanup)
    return cleanup
  }

  onBackgroundClick(handler: () => void): () => void {
    if (!this.cy) return () => {}

    const listener = (e: any) => {
      if (e.target === this.cy) {
        handler()
      }
    }

    this.cy.on('tap', listener)

    const cleanup = () => {
      this.cy?.off('tap', listener)
    }
    this.cleanupFunctions.push(cleanup)
    return cleanup
  }

  onGroupClick(handler: (groupId: string) => void): () => void {
    if (!this.cy) return () => {}

    const listener = (e: any) => {
      const node = e.target
      if (node.isNode() && node.data('isGroup')) {
        const groupId = node.id().replace('group-', '')
        handler(groupId)
      }
    }

    this.cy.on('tap', 'node[?isGroup]', listener)

    const cleanup = () => {
      this.cy?.off('tap', 'node[?isGroup]', listener)
    }
    this.cleanupFunctions.push(cleanup)
    return cleanup
  }

  onNodeDoubleClick(handler: (event: NodeClickEvent) => void): () => void {
    if (!this.cy) return () => {}

    const listener = (e: any) => {
      const node = e.target
      if (node.isNode() && !node.data('isGroup')) {
        handler({
          nodeId: node.id(),
          originalEvent: e.originalEvent,
          isCtrlKey: e.originalEvent?.ctrlKey || e.originalEvent?.metaKey || false,
          isShiftKey: e.originalEvent?.shiftKey || false
        })
      }
    }

    this.cy.on('dbltap', 'node', listener)

    const cleanup = () => {
      this.cy?.off('dbltap', 'node', listener)
    }
    this.cleanupFunctions.push(cleanup)
    return cleanup
  }

  // ============ View Control ============

  fitToView(padding: number = 30, animate: boolean = false): void {
    if (!this.cy) return
    if (animate) {
      this.cy.animate({
        fit: { eles: this.cy.elements(), padding }
      }, {
        duration: 300,
        easing: 'ease-out'
      })
    } else {
      this.cy.fit(undefined, padding)
    }
  }

  centerOnNode(nodeId: string, zoom?: number): void {
    if (!this.cy) return

    const node = this.cy.getElementById(nodeId)
    if (node.length > 0) {
      this.cy.animate({
        center: { eles: node },
        zoom: zoom ?? this.cy.zoom()
      }, {
        duration: 300
      })
    }
  }

  animateTo(options: { center?: string; zoom?: number; duration?: number }): void {
    if (!this.cy) return

    const animateOpts: any = {}
    if (options.center) {
      const node = this.cy.getElementById(options.center)
      if (node.length > 0) {
        animateOpts.center = { eles: node }
      }
    }
    if (options.zoom !== undefined) {
      animateOpts.zoom = options.zoom
    }

    this.cy.animate(animateOpts, { duration: options.duration ?? 300 })
  }

  getViewport(): { zoom: number; pan: { x: number; y: number } } {
    if (!this.cy) return { zoom: 1, pan: { x: 0, y: 0 } }
    return {
      zoom: this.cy.zoom(),
      pan: this.cy.pan()
    }
  }

  setViewport(viewport: { zoom?: number; pan?: { x: number; y: number } }): void {
    if (!this.cy) return
    if (viewport.zoom !== undefined) {
      this.cy.zoom(viewport.zoom)
    }
    if (viewport.pan) {
      this.cy.pan(viewport.pan)
    }
  }

  getNodeScreenPosition(nodeId: string): { x: number; y: number } | null {
    if (!this.cy || !this.container) return null

    const node = this.cy.getElementById(nodeId)
    if (node.length === 0) return null

    // Get node's rendered position (in model coordinates)
    const pos = node.renderedPosition()

    // Get container's bounding rect to convert to screen coordinates
    const rect = this.container.getBoundingClientRect()

    return {
      x: rect.left + pos.x,
      y: rect.top + pos.y
    }
  }

  // ============ Highlighting ============

  highlightNodes(nodeIds: string[]): void {
    if (!this.cy) return

    // Remove existing selection highlighting
    this.cy.nodes().removeClass('selected')

    // Add selection class to specified nodes
    for (const id of nodeIds) {
      const node = this.cy.getElementById(id)
      if (node.length > 0) {
        node.addClass('selected')
      }
    }
  }

  highlightConnections(nodeId: string): void {
    if (!this.cy) return

    const node = this.cy.getElementById(nodeId)
    if (node.length === 0) return

    // Get connected edges and nodes
    const connectedEdges = node.connectedEdges()
    const connectedNodes = connectedEdges.connectedNodes().add(node)

    // Fade everything
    this.cy.elements().addClass('faded')

    // Highlight connected elements
    connectedNodes.removeClass('faded').addClass('highlighted')
    connectedEdges.removeClass('faded').addClass('highlighted')
  }

  fadeElements(excludeNodeIds: string[]): void {
    if (!this.cy) return

    const excludeSet = new Set(excludeNodeIds)

    this.cy.nodes().forEach((node: CytoscapeNode) => {
      if (!excludeSet.has(node.id())) {
        node.addClass('faded')
      }
    })

    this.cy.edges().forEach((edge: CytoscapeEdge) => {
      const source = edge.source().id()
      const target = edge.target().id()
      if (!excludeSet.has(source) || !excludeSet.has(target)) {
        edge.addClass('faded')
      }
    })
  }

  resetHighlight(): void {
    if (!this.cy) return
    this.cy.elements().removeClass('faded').removeClass('highlighted')
  }

  // ============ Layout ============

  async setLayout(layoutType: string, options?: { scatter?: boolean }): Promise<void> {
    if (!this.cy) return

    this.currentLayoutType = layoutType as LayoutType

    // If scatter animation requested, use the scatter animation method
    if (options?.scatter && this.currentLayoutType === 'fcose') {
      return this.runLayoutWithScatterAnimation()
    }

    // Lazy-load ELK if needed (saves ~1.4MB on initial load)
    if (this.currentLayoutType === 'elk') {
      await this.ensureElkLoaded()
    }

    const layoutConfig = getLayoutConfig(this.currentLayoutType)

    // Update edge curve style based on layout type
    this.updateEdgeCurveStyle()

    return new Promise((resolve) => {
      const layout = this.cy!.layout(layoutConfig)
      layout.on('layoutstop', () => {
        // fcose with fit:true already fits, only call for elk
        if (this.currentLayoutType === 'elk') {
          this.fitToView()
        }
        resolve()
      })
      layout.run()
    })
  }

  async runLayout(options?: Partial<LayoutOptions>): Promise<void> {
    if (!this.cy) return

    // Lazy-load ELK if needed
    if (this.currentLayoutType === 'elk') {
      await this.ensureElkLoaded()
    }

    // Use current layout type's config
    const baseConfig = getLayoutConfig(this.currentLayoutType)
    const layoutConfig = {
      ...baseConfig,
      animate: options?.animate ?? false
    }

    // Update edge curve style based on layout type
    this.updateEdgeCurveStyle()

    return new Promise((resolve) => {
      const layout = this.cy!.layout(layoutConfig)
      layout.on('layoutstop', () => {
        // fcose with fit:true already fits, only call for elk
        if (this.currentLayoutType === 'elk') {
          this.fitToView()
        }
        resolve()
      })
      layout.run()
    })
  }

  private updateEdgeCurveStyle(): void {
    if (!this.cy) return

    // Use bezier curves for force-directed, taxi for hierarchical
    const curveStyle = this.currentLayoutType === 'fcose' ? 'bezier' : 'taxi'
    const taxiDirection = this.currentLayoutType === 'fcose' ? undefined : 'rightward'

    this.cy.edges().style({
      'curve-style': curveStyle,
      'taxi-direction': taxiDirection
    })
  }

  getAvailableLayouts(): string[] {
    return ['fcose', 'elk']
  }

  // ============ Styling ============

  setTheme(dark: boolean): void {
    if (!this.cy) return

    this.currentTheme = dark ? 'dark' : 'light'
    const borderColor = dark ? '#ffffff' : '#374151'

    // Update styles
    this.cy.style([
      ...createCytoscapeStyles(borderColor),
      ...createCompoundNodeStyles(borderColor)
    ])
  }

  setNodeStyle(nodeId: string, style: Partial<NodeStyle>): void {
    if (!this.cy) return

    const node = this.cy.getElementById(nodeId)
    if (node.length === 0) return

    const cyStyle: any = {}
    if (style.backgroundColor) cyStyle['background-color'] = style.backgroundColor
    if (style.borderColor) cyStyle['border-color'] = style.borderColor
    if (style.borderWidth) cyStyle['border-width'] = style.borderWidth
    if (style.width) cyStyle['width'] = style.width
    if (style.height) cyStyle['height'] = style.height
    if (style.opacity !== undefined) cyStyle['opacity'] = style.opacity

    node.style(cyStyle)
  }

  setEdgeStyle(edgeId: string, style: Partial<EdgeStyle>): void {
    if (!this.cy) return

    const edge = this.cy.getElementById(edgeId)
    if (edge.length === 0) return

    const cyStyle: any = {}
    if (style.lineColor) {
      cyStyle['line-color'] = style.lineColor
      cyStyle['target-arrow-color'] = style.lineColor
    }
    if (style.width) cyStyle['width'] = style.width
    if (style.opacity !== undefined) cyStyle['opacity'] = style.opacity
    if (style.lineStyle) cyStyle['line-style'] = style.lineStyle
    if (style.curveStyle) cyStyle['curve-style'] = style.curveStyle

    edge.style(cyStyle)
  }

  setGroupStyle(groupId: string, style: Partial<GroupStyle>): void {
    if (!this.cy) return

    const group = this.cy.getElementById(`group-${groupId}`)
    if (group.length === 0) return

    const cyStyle: any = {}
    if (style.backgroundColor) cyStyle['background-color'] = style.backgroundColor
    if (style.borderColor) cyStyle['border-color'] = style.borderColor
    if (style.borderWidth) cyStyle['border-width'] = style.borderWidth
    if (style.padding) cyStyle['padding'] = style.padding

    group.style(cyStyle)
  }

  // ============ Export ============

  async exportPNG(options?: { scale?: number; backgroundColor?: string }): Promise<Blob> {
    if (!this.cy) throw new Error('Adapter not initialized')

    const dataUrl = this.cy.png({
      scale: options?.scale ?? 2,
      bg: options?.backgroundColor ?? '#ffffff',
      full: true
    })

    // Convert data URL to Blob
    const response = await fetch(dataUrl)
    return response.blob()
  }

  exportSVG(): string {
    if (!this.cy) throw new Error('Adapter not initialized')
    return this.cy.svg({ full: true })
  }
}
