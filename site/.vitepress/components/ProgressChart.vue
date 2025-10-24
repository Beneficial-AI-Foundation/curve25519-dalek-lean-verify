<script setup lang="ts">
import { computed } from 'vue'
import { Line } from 'vue-chartjs'
import {
  Chart as ChartJS,
  CategoryScale,
  LinearScale,
  PointElement,
  LineElement,
  Title,
  Tooltip,
  Legend,
  Filler,
  type ChartOptions
} from 'chart.js'

// Register Chart.js components
ChartJS.register(
  CategoryScale,
  LinearScale,
  PointElement,
  LineElement,
  Title,
  Tooltip,
  Legend,
  Filler
)

interface ProgressDataPoint {
  date: string
  timestamp: number
  total: number
  verified: number
  specified: number
  draftSpec: number
  extracted: number
}

const props = defineProps<{
  dataPoints: ProgressDataPoint[]
}>()

const chartData = computed(() => {
  const labels = props.dataPoints.map(dp => {
    const date = new Date(dp.date)
    return date.toLocaleDateString('en-GB', { day: '2-digit', month: '2-digit', year: '2-digit' })
  })

  const verified = props.dataPoints.map(dp => dp.verified)
  const specified = props.dataPoints.map(dp => dp.specified)
  const draftSpec = props.dataPoints.map(dp => dp.draftSpec)
  const total = props.dataPoints.map(dp => dp.total)
  const extracted = props.dataPoints.map(dp => dp.extracted)

  // Calculate "not started" (everything else)
  const notStarted = props.dataPoints.map(dp =>
    dp.total - dp.verified - dp.specified - dp.draftSpec
  )

  return {
    labels,
    datasets: [
      {
        label: 'Verified',
        data: verified,
        borderColor: '#10b981',
        backgroundColor: 'rgba(16, 185, 129, 0.85)',
        fill: true,
        stepped: 'after',
        borderWidth: 2,
        pointRadius: 0,
        order: 1
      },
      {
        label: 'Specified',
        data: specified.map((val, idx) => val + verified[idx]),
        borderColor: '#fdba74',
        backgroundColor: 'rgba(253, 186, 116, 0.6)',
        fill: true,
        stepped: 'after',
        borderWidth: 0,
        pointRadius: 0,
        order: 2
      },
      {
        label: 'Draft',
        data: draftSpec.map((val, idx) => val + specified[idx] + verified[idx]),
        borderColor: '#cbd5e1',
        backgroundColor: 'rgba(203, 213, 225, 0.5)',
        fill: true,
        stepped: 'after',
        borderWidth: 0,
        pointRadius: 0,
        order: 3
      },
      {
        label: 'Not started',
        data: total,
        borderColor: '#e5e7eb',
        backgroundColor: 'rgba(229, 231, 235, 0.4)',
        fill: true,
        stepped: 'after',
        borderWidth: 0,
        pointRadius: 0,
        order: 4
      },
      {
        label: 'Total Functions',
        data: total,
        borderColor: '#374151',
        backgroundColor: 'transparent',
        fill: false,
        stepped: 'after',
        borderWidth: 2,
        pointRadius: 0,
        order: 0
      },
      {
        label: 'Extracted',
        data: extracted,
        borderColor: '#9ca3af',
        backgroundColor: 'transparent',
        fill: false,
        stepped: 'after',
        borderWidth: 1.5,
        borderDash: [3, 3],
        pointRadius: 0,
        order: 0
      }
    ]
  }
})

const chartOptions: ChartOptions<'line'> = {
  responsive: true,
  maintainAspectRatio: true,
  aspectRatio: 2,
  interaction: {
    mode: 'index',
    intersect: false
  },
  plugins: {
    title: {
      display: false
    },
    legend: {
      position: 'bottom',
      labels: {
        usePointStyle: true,
        padding: 15,
        filter: function(item, chart) {
          // Only show Verified, Specified, and Draft in legend
          return item.text === 'Verified' || item.text === 'Specified' || item.text === 'Draft'
        }
      }
    },
    tooltip: {
      callbacks: {
        label: function(context) {
          const label = context.dataset.label || ''
          const value = context.parsed.y

          // For stacked areas, show the actual count, not cumulative
          if (label === 'Specified' && context.dataIndex !== undefined) {
            const verified = props.dataPoints[context.dataIndex].verified
            const specified = props.dataPoints[context.dataIndex].specified
            return `${label}: ${specified}`
          } else if (label === 'Draft' && context.dataIndex !== undefined) {
            const draftSpec = props.dataPoints[context.dataIndex].draftSpec
            return `${label}: ${draftSpec}`
          } else if (label === 'Not started' && context.dataIndex !== undefined) {
            const dp = props.dataPoints[context.dataIndex]
            const notStarted = dp.total - dp.verified - dp.specified - dp.draftSpec
            return `${label}: ${notStarted}`
          }

          return `${label}: ${value}`
        }
      }
    }
  },
  scales: {
    y: {
      beginAtZero: true,
      stacked: false,
      title: {
        display: false
      },
      grid: {
        color: 'rgba(0, 0, 0, 0.1)'
      }
    },
    x: {
      grid: {
        display: false
      }
    }
  }
}
</script>

<template>
  <div class="chart-container">
    <Line :data="chartData" :options="chartOptions" />
  </div>
</template>

<style scoped>
.chart-container {
  position: relative;
  margin: 2rem 0;
  padding: 1rem;
  background: var(--vp-c-bg-soft);
  border-radius: 8px;
}
</style>
