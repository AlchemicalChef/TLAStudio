import SwiftUI
import Charts

// MARK: - Progress Chart View

/// Live line chart showing model checking progress over time
struct ProgressChartView: View {
    let history: [ProgressDataPoint]

    enum ChartMode: String, CaseIterable {
        case states = "States"
        case rate = "Rate"
        case memory = "Memory"
    }

    @State private var chartMode: ChartMode = .states

    var body: some View {
        VStack(alignment: .leading, spacing: 8) {
            Picker("Chart", selection: $chartMode) {
                ForEach(ChartMode.allCases, id: \.self) { mode in
                    Text(mode.rawValue).tag(mode)
                }
            }
            .pickerStyle(.segmented)
            .frame(maxWidth: 240)

            switch chartMode {
            case .states:
                statesChart
            case .rate:
                rateChart
            case .memory:
                memoryChart
            }
        }
    }

    // MARK: - States Chart

    private var statesChart: some View {
        Chart {
            ForEach(history) { point in
                LineMark(
                    x: .value("Time", point.timestamp),
                    y: .value("States Found", point.statesFound)
                )
                .foregroundStyle(by: .value("Series", "Found"))
                .interpolationMethod(.monotone)

                AreaMark(
                    x: .value("Time", point.timestamp),
                    y: .value("States Found", point.statesFound)
                )
                .foregroundStyle(
                    .linearGradient(
                        colors: [.blue.opacity(0.15), .blue.opacity(0.02)],
                        startPoint: .top,
                        endPoint: .bottom
                    )
                )
            }

            ForEach(history) { point in
                LineMark(
                    x: .value("Time", point.timestamp),
                    y: .value("Distinct States", point.distinctStates)
                )
                .foregroundStyle(by: .value("Series", "Distinct"))
                .interpolationMethod(.monotone)

                AreaMark(
                    x: .value("Time", point.timestamp),
                    y: .value("Distinct States", point.distinctStates)
                )
                .foregroundStyle(
                    .linearGradient(
                        colors: [.green.opacity(0.15), .green.opacity(0.02)],
                        startPoint: .top,
                        endPoint: .bottom
                    )
                )
            }
        }
        .chartForegroundStyleScale([
            "Found": Color.blue,
            "Distinct": Color.green
        ])
        .chartXAxis {
            AxisMarks { value in
                AxisGridLine()
                AxisValueLabel {
                    if let seconds = value.as(Double.self) {
                        Text(formatTimeAxis(seconds))
                    }
                }
            }
        }
        .chartYAxis {
            AxisMarks { value in
                AxisGridLine()
                AxisValueLabel {
                    if let count = value.as(Double.self) {
                        Text(formatCountAxis(count))
                    }
                }
            }
        }
        .chartXAxisLabel("Time")
        .chartYAxisLabel("States")
        .frame(height: 180)
        .chartLegend(position: .top, alignment: .leading)
    }

    // MARK: - Rate Chart

    private var rateChart: some View {
        Chart {
            ForEach(history) { point in
                LineMark(
                    x: .value("Time", point.timestamp),
                    y: .value("Rate", point.statesPerSecond)
                )
                .foregroundStyle(Color.orange)
                .interpolationMethod(.monotone)

                AreaMark(
                    x: .value("Time", point.timestamp),
                    y: .value("Rate", point.statesPerSecond)
                )
                .foregroundStyle(
                    .linearGradient(
                        colors: [.orange.opacity(0.15), .orange.opacity(0.02)],
                        startPoint: .top,
                        endPoint: .bottom
                    )
                )
            }
        }
        .chartXAxis {
            AxisMarks { value in
                AxisGridLine()
                AxisValueLabel {
                    if let seconds = value.as(Double.self) {
                        Text(formatTimeAxis(seconds))
                    }
                }
            }
        }
        .chartYAxis {
            AxisMarks { value in
                AxisGridLine()
                AxisValueLabel {
                    if let count = value.as(Double.self) {
                        Text(formatCountAxis(count) + "/s")
                    }
                }
            }
        }
        .chartXAxisLabel("Time")
        .chartYAxisLabel("States/sec")
        .frame(height: 180)
    }

    // MARK: - Memory Chart

    private var memoryChart: some View {
        Chart {
            ForEach(history) { point in
                LineMark(
                    x: .value("Time", point.timestamp),
                    y: .value("Memory", Double(point.memoryUsed) / 1_048_576.0) // MB
                )
                .foregroundStyle(Color.purple)
                .interpolationMethod(.monotone)

                AreaMark(
                    x: .value("Time", point.timestamp),
                    y: .value("Memory", Double(point.memoryUsed) / 1_048_576.0)
                )
                .foregroundStyle(
                    .linearGradient(
                        colors: [.purple.opacity(0.15), .purple.opacity(0.02)],
                        startPoint: .top,
                        endPoint: .bottom
                    )
                )
            }
        }
        .chartXAxis {
            AxisMarks { value in
                AxisGridLine()
                AxisValueLabel {
                    if let seconds = value.as(Double.self) {
                        Text(formatTimeAxis(seconds))
                    }
                }
            }
        }
        .chartYAxis {
            AxisMarks { value in
                AxisGridLine()
                AxisValueLabel {
                    if let mb = value.as(Double.self) {
                        Text(formatMemoryAxis(mb))
                    }
                }
            }
        }
        .chartXAxisLabel("Time")
        .chartYAxisLabel("Memory")
        .frame(height: 180)
    }

    // MARK: - Axis Formatting

    private func formatTimeAxis(_ seconds: Double) -> String {
        if seconds < 60 {
            return "\(Int(seconds))s"
        } else if seconds < 3600 {
            let mins = Int(seconds / 60)
            let secs = Int(seconds.truncatingRemainder(dividingBy: 60))
            return secs == 0 ? "\(mins)m" : "\(mins):\(String(format: "%02d", secs))"
        } else {
            let hours = Int(seconds / 3600)
            let mins = Int((seconds.truncatingRemainder(dividingBy: 3600)) / 60)
            return "\(hours)h\(mins)m"
        }
    }

    private func formatCountAxis(_ count: Double) -> String {
        if count >= 1_000_000_000 {
            return String(format: "%.0fB", count / 1_000_000_000)
        } else if count >= 1_000_000 {
            return String(format: "%.0fM", count / 1_000_000)
        } else if count >= 1_000 {
            return String(format: "%.0fK", count / 1_000)
        }
        return "\(Int(count))"
    }

    private func formatMemoryAxis(_ mb: Double) -> String {
        if mb >= 1024 {
            return String(format: "%.1f GB", mb / 1024)
        }
        return String(format: "%.0f MB", mb)
    }
}
