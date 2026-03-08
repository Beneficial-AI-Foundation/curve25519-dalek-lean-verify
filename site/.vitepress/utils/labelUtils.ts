// Utility functions for formatting function names/labels

/**
 * Get short label from lean_name (last component only)
 * e.g., "curve25519_dalek.backend.serial.u64.field.FieldElement51.add" -> "add"
 */
export function getShortLabel(lean_name: string): string {
  const parts = lean_name.split('.')
  return parts[parts.length - 1]
}

/**
 * Get medium label (strip common prefixes, show on hover)
 * e.g., "curve25519_dalek.backend.serial.u64.field.FieldElement51.add" -> "field.FieldElement51.add"
 */
export function getMediumLabel(lean_name: string): string {
  return lean_name
    .replace(/^curve25519_dalek\./, '')
    .replace(/^backend\.serial\.(u64\.)?/, '')
}

/**
 * Get function name from Rust path (last component after ::)
 * e.g., "curve25519_dalek::backend::serial::add" -> "add"
 */
export function getRustFunctionName(rustPath: string): string {
  const parts = rustPath.split('::')
  return parts[parts.length - 1]
}

/**
 * Shorten source file path by removing common prefix
 * e.g., "curve25519-dalek/src/backend/serial.rs" -> "backend/serial.rs"
 */
export function shortenSourcePath(source: string | null): string {
  if (!source) return '-'
  return source.replace('curve25519-dalek/src/', '')
}
