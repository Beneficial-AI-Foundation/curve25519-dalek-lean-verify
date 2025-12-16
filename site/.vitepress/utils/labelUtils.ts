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
 * Convert Rust path to Lean notation
 * e.g., "curve25519_dalek::backend::serial" -> "curve25519_dalek.backend.serial"
 */
export function rustPathToLean(rustPath: string): string {
  return rustPath.replace(/::/g, '.')
}
