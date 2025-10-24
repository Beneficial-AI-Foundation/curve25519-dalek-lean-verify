<script setup lang="ts">
import { computed } from 'vue'
import { Line } from 'vue-chartjs'
import {
  Chart as ChartJS,
  TimeScale,
  LinearScale,
  PointElement,
  LineElement,
  Title,
  Tooltip,
  Legend,
  Filler,
  type ChartOptions
} from 'chart.js'
import 'chartjs-adapter-date-fns'

// Register Chart.js components
ChartJS.register(
  TimeScale,
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
  // For TimeScale, we need to provide data as {x, y} objects
  const verified = props.dataPoints.map(dp => ({ x: dp.timestamp * 1000, y: dp.verified }))
  const specified = props.dataPoints.map((dp, idx) => ({
    x: dp.timestamp * 1000,
    y: dp.specified + props.dataPoints[idx].verified
  }))
  const draftSpec = props.dataPoints.map((dp, idx) => ({
    x: dp.timestamp * 1000,
    y: dp.draftSpec + props.dataPoints[idx].specified + props.dataPoints[idx].verified
  }))
  const total = props.dataPoints.map(dp => ({ x: dp.timestamp * 1000, y: dp.total }))
  const extracted = props.dataPoints.map(dp => ({ x: dp.timestamp * 1000, y: dp.extracted }))

  return {
    datasets: [
      {
        label: 'Verified',
        data: verified,
        borderColor: '#10b981',
        backgroundColor: 'rgba(16, 185, 129, 0.85)',
        fill: true,
        stepped: 'after' as const,
        borderWidth: 2,
        pointRadius: 0,
        order: 1
      },
      {
        label: 'Specified',
        data: specified,
        borderColor: '#fdba74',
        backgroundColor: 'rgba(253, 186, 116, 0.6)',
        fill: true,
        stepped: 'after' as const,
        borderWidth: 0,
        pointRadius: 0,
        order: 2
      },
      {
        label: 'Draft',
        data: draftSpec,
        borderColor: '#cbd5e1',
        backgroundColor: 'rgba(203, 213, 225, 0.5)',
        fill: true,
        stepped: 'after' as const,
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
        stepped: 'after' as const,
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
        stepped: 'after' as const,
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
        stepped: 'after' as const,
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
      type: 'time',
      time: {
        unit: 'day',
        displayFormats: {
          day: 'dd/MM/yy'
        },
        tooltipFormat: 'PPP'
      },
      grid: {
        display: false
      },
      ticks: {
        maxRotation: 45,
        minRotation: 45
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
