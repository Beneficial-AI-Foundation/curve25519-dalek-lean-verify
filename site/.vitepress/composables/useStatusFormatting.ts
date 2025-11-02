/**
 * Composable for consistent status formatting across components
 */

export interface StatusConfig {
  icon: string
  label: string
  cssClass: string
}

export function useStatusFormatting() {
  /**
   * Get formatted configuration for extraction status
   */
  function getExtractedStatus(extracted: string): StatusConfig {
    if (extracted === 'extracted') {
      return {
        icon: '✓',
        label: 'Extracted',
        cssClass: 'checked'
      }
    }
    return {
      icon: '☐',
      label: 'Not Extracted',
      cssClass: 'unchecked'
    }
  }

  /**
   * Get formatted configuration for verification status
   */
  function getVerifiedStatus(verified: string): StatusConfig {
    switch (verified) {
      case 'verified':
        return {
          icon: '✓',
          label: 'Verified',
          cssClass: 'verified'
        }
      case 'specified':
        return {
          icon: '📋',
          label: 'Specified',
          cssClass: 'specified'
        }
      case 'draft spec':
        return {
          icon: '✏️',
          label: 'Draft',
          cssClass: 'draft'
        }
      default:
        return {
          icon: '☐',
          label: 'Not Started',
          cssClass: 'unchecked'
        }
    }
  }

  return {
    getExtractedStatus,
    getVerifiedStatus
  }
}
