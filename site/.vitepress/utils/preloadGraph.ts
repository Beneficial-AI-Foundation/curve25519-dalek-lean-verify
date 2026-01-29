/**
 * Preload graph visualization dependencies in the background.
 * Call this on any page to have the deps page load faster.
 */

let preloadStarted = false
let cytoscapeLoaded = false

/**
 * Preload Cytoscape core and default layout.
 * Uses dynamic import which will be cached by the browser.
 */
async function preloadCytoscapeCore(): Promise<void> {
  if (cytoscapeLoaded) return

  try {
    // These imports will be cached by the browser for when deps page loads
    await Promise.all([
      import('cytoscape'),
      import('cytoscape-fcose')
    ])
    cytoscapeLoaded = true
  } catch (e) {
    // Silently fail - this is just optimization
    console.debug('Graph preload skipped:', e)
  }
}

/**
 * Schedule preloading for idle time.
 * Waits for the specified delay, then uses requestIdleCallback.
 */
export function scheduleGraphPreload(delayMs: number = 3000): void {
  if (preloadStarted || typeof window === 'undefined') return
  preloadStarted = true

  // Wait for initial page to settle, then preload during idle time
  setTimeout(() => {
    const scheduleIdle = (window as any).requestIdleCallback ||
      ((cb: () => void) => setTimeout(cb, 100))

    scheduleIdle(() => {
      preloadCytoscapeCore()
    }, { timeout: 5000 }) // Max wait 5s before forcing preload
  }, delayMs)
}

/**
 * Immediately start preloading (e.g., on hover over Deps link).
 */
export function preloadGraphNow(): void {
  if (cytoscapeLoaded) return
  preloadCytoscapeCore()
}

/**
 * Check if graph dependencies are already loaded.
 */
export function isGraphPreloaded(): boolean {
  return cytoscapeLoaded
}
