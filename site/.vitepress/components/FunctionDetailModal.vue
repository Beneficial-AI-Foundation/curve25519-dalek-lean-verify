<script setup>
import { ref, watch, onMounted, onUnmounted } from 'vue'
import { useStatusFormatting } from '../composables/useStatusFormatting'
import { useGitHubLinks } from '../composables/useGitHubLinks'

const { getExtractedStatus, getVerifiedStatus, getAiProveableStatus } = useStatusFormatting()
const { getSourceLink, getSpecLink } = useGitHubLinks()

const props = defineProps({
  isOpen: {
    type: Boolean,
    required: true
  },
  func: {
    type: Object,
    default: null
  }
})

const emit = defineEmits(['close'])

// Handle ESC key to close modal
function handleEscape(event) {
  if (event.key === 'Escape' && props.isOpen) {
    emit('close')
  }
}

// Handle click outside modal to close
function handleBackdropClick(event) {
  if (event.target === event.currentTarget) {
    emit('close')
  }
}

// Copy state
const copySuccess = ref(false)

// Copy function name to clipboard
async function copyFunctionName() {
  if (!props.func) return

  try {
    await navigator.clipboard.writeText(props.func.function)
    copySuccess.value = true
    setTimeout(() => {
      copySuccess.value = false
    }, 2000)
  } catch (err) {
    console.error('Failed to copy:', err)
  }
}

// Lifecycle hooks for keyboard listener
onMounted(() => {
  document.addEventListener('keydown', handleEscape)
})

onUnmounted(() => {
  document.removeEventListener('keydown', handleEscape)
})

// Lock body scroll when modal is open
watch(() => props.isOpen, (isOpen) => {
  if (isOpen) {
    document.body.style.overflow = 'hidden'
  } else {
    document.body.style.overflow = ''
  }
})
</script>

<template>
  <Teleport to="body">
    <Transition name="modal">
      <div v-if="isOpen && func" class="modal-backdrop" @click="handleBackdropClick">
        <div class="modal-content" role="dialog" aria-modal="true">
          <div class="modal-header">
            <h2>Function Details</h2>
            <button @click="emit('close')" class="close-button" aria-label="Close modal">
              ×
            </button>
          </div>

          <div class="modal-body">
            <div class="detail-section">
              <h3>Full Name</h3>
              <div class="code-block-wrapper">
                <code class="full-name">{{ func.function }}</code>
                <button
                  @click="copyFunctionName"
                  class="copy-icon-button"
                  :class="{ copied: copySuccess }"
                  :title="copySuccess ? 'Copied!' : 'Copy to clipboard'"
                >
                  <span v-if="copySuccess">✓</span>
                  <span v-else>
                    <svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
                      <rect x="9" y="9" width="13" height="13" rx="2" ry="2"></rect>
                      <path d="M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1"></path>
                    </svg>
                  </span>
                </button>
              </div>
            </div>

            <div class="detail-section" v-if="func.source">
              <h3>Source</h3>
              <p>
                <a
                  v-if="getSourceLink(func.source, func.lines)"
                  :href="getSourceLink(func.source, func.lines)"
                  target="_blank"
                  rel="noopener noreferrer"
                  class="vp-external-link-icon"
                >
                  {{ func.source }}
                </a>
                <span v-else>{{ func.source }}</span>
              </p>
              <p v-if="func.lines" class="lines-info">Lines: {{ func.lines }}</p>
            </div>

            <div class="detail-section" v-if="func.spec_theorem">
              <h3>Specification</h3>
              <p>
                <a
                  v-if="getSpecLink(func.spec_theorem)"
                  :href="getSpecLink(func.spec_theorem)"
                  target="_blank"
                  rel="noopener noreferrer"
                  class="vp-external-link-icon"
                >
                  {{ func.spec_theorem }}
                </a>
                <span v-else>{{ func.spec_theorem }}</span>
              </p>
            </div>

            <div class="detail-section">
              <h3>Status</h3>
              <div class="status-grid">
                <div class="status-item">
                  <span class="status-label">Extracted:</span>
                  <span :class="['status-badge', getExtractedStatus(func.extracted).cssClass === 'checked' ? 'success' : 'pending']">
                    {{ getExtractedStatus(func.extracted).icon }} {{ getExtractedStatus(func.extracted).label }}
                  </span>
                </div>
                <div class="status-item">
                  <span class="status-label">Verified:</span>
                  <span :class="['status-badge',
                    getVerifiedStatus(func.verified).cssClass === 'verified' ? 'success' :
                    getVerifiedStatus(func.verified).cssClass === 'specified' ? 'info' :
                    getVerifiedStatus(func.verified).cssClass === 'draft' ? 'warning' : 'pending']">
                    {{ getVerifiedStatus(func.verified).icon }} {{ getVerifiedStatus(func.verified).label }}
                  </span>
                </div>
                <div class="status-item">
                  <span class="status-label">AI-Verifiable:</span>
                  <span :class="['status-badge', getAiProveableStatus(func['ai-proveable']).cssClass]">
                    {{ getAiProveableStatus(func['ai-proveable']).icon }} {{ getAiProveableStatus(func['ai-proveable']).label }}
                  </span>
                </div>
              </div>
            </div>

            <div class="detail-section" v-if="func.notes">
              <h3>Notes</h3>
              <p class="notes-text">{{ func.notes }}</p>
            </div>
          </div>

          <div class="modal-footer">
            <button @click="emit('close')" class="button-primary">Close</button>
          </div>
        </div>
      </div>
    </Transition>
  </Teleport>
</template>

<style scoped>
.modal-backdrop {
  position: fixed;
  top: 0;
  left: 0;
  width: 100%;
  height: 100%;
  background: rgba(0, 0, 0, 0.5);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 9999;
  padding: 1rem;
}

.modal-content {
  background: var(--vp-c-bg);
  border-radius: 12px;
  max-width: 700px;
  width: 100%;
  max-height: 90vh;
  overflow: hidden;
  display: flex;
  flex-direction: column;
  box-shadow: 0 20px 60px rgba(0, 0, 0, 0.3);
}

.modal-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 1.5rem;
  border-bottom: 1px solid var(--vp-c-divider);
}

.modal-header h2 {
  margin: 0;
  font-size: 1.5rem;
}

.close-button {
  background: none;
  border: none;
  font-size: 2rem;
  line-height: 1;
  cursor: pointer;
  color: var(--vp-c-text-2);
  padding: 0;
  width: 2rem;
  height: 2rem;
  display: flex;
  align-items: center;
  justify-content: center;
  border-radius: 4px;
}

.close-button:hover {
  background: var(--vp-c-bg-soft);
  color: var(--vp-c-text-1);
}

.modal-body {
  padding: 1.5rem;
  overflow-y: auto;
  flex: 1;
}

.detail-section {
  margin-bottom: 1.5rem;
}

.detail-section:last-child {
  margin-bottom: 0;
}

.detail-section h3 {
  margin: 0 0 0.75rem 0;
  font-size: 1rem;
  color: var(--vp-c-text-2);
  text-transform: uppercase;
  letter-spacing: 0.05em;
  font-weight: 600;
}

.code-block-wrapper {
  position: relative;
}

.full-name {
  display: block;
  padding: 0.75rem;
  padding-right: 3rem;
  background: var(--vp-c-bg-soft);
  border-radius: 6px;
  word-break: break-all;
  font-size: 0.9rem;
  line-height: 1.6;
  user-select: all;
}

.copy-icon-button {
  position: absolute;
  top: 0.5rem;
  right: 0.5rem;
  width: 2rem;
  height: 2rem;
  padding: 0;
  background: transparent;
  border: none;
  cursor: pointer;
  color: var(--vp-c-text-2);
  display: flex;
  align-items: center;
  justify-content: center;
  border-radius: 4px;
  transition: all 0.2s;
}

.copy-icon-button:hover {
  background: var(--vp-c-bg);
  color: var(--vp-c-text-1);
}

.copy-icon-button.copied {
  color: #10b981;
}

.copy-icon-button svg {
  width: 16px;
  height: 16px;
}

.vp-external-link-icon {
  color: var(--vp-c-brand-1);
  text-decoration: none;
  transition: color 0.2s;
}

.vp-external-link-icon:hover {
  color: var(--vp-c-brand-2);
  text-decoration: underline;
}

.lines-info {
  color: var(--vp-c-text-2);
  font-size: 0.9rem;
  margin-top: 0.5rem;
}

.status-grid {
  display: grid;
  grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
  gap: 1rem;
}

.status-item {
  display: flex;
  flex-direction: column;
  gap: 0.5rem;
}

.status-label {
  font-size: 0.85rem;
  color: var(--vp-c-text-2);
}

.status-badge {
  display: inline-flex;
  align-items: center;
  padding: 0.4rem 0.75rem;
  border-radius: 6px;
  font-size: 0.9rem;
  font-weight: 500;
  width: fit-content;
}

.status-badge.success {
  background: rgba(16, 185, 129, 0.1);
  color: #10b981;
}

.status-badge.info {
  background: rgba(59, 130, 246, 0.1);
  color: #3b82f6;
}

.status-badge.warning {
  background: rgba(245, 158, 11, 0.1);
  color: #f59e0b;
}

.status-badge.pending {
  background: var(--vp-c-bg-soft);
  color: var(--vp-c-text-3);
}

.status-badge.ai-proveable {
  background: rgba(139, 92, 246, 0.1);
  color: #8b5cf6;
}

.notes-text {
  margin: 0;
  padding: 0.75rem;
  background: var(--vp-c-bg-soft);
  border-radius: 6px;
  line-height: 1.6;
}

.modal-footer {
  padding: 1rem 1.5rem;
  border-top: 1px solid var(--vp-c-divider);
  display: flex;
  justify-content: flex-end;
}

.button-primary {
  padding: 0.5rem 1.5rem;
  background: var(--vp-c-brand-1);
  color: white;
  border: none;
  border-radius: 6px;
  cursor: pointer;
  font-size: 1rem;
}

.button-primary:hover {
  background: var(--vp-c-brand-2);
}

/* Modal transitions */
.modal-enter-active,
.modal-leave-active {
  transition: opacity 0.2s ease;
}

.modal-enter-from,
.modal-leave-to {
  opacity: 0;
}

.modal-enter-active .modal-content,
.modal-leave-active .modal-content {
  transition: transform 0.2s ease;
}

.modal-enter-from .modal-content,
.modal-leave-to .modal-content {
  transform: scale(0.95);
}

/* Responsive */
@media (max-width: 768px) {
  .modal-content {
    max-height: 95vh;
  }

  .status-grid {
    grid-template-columns: 1fr;
  }
}
</style>
