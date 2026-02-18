import SwiftUI
import Charts

// MARK: - Model Check Progress View

/// Shows real-time progress during model checking
struct ModelCheckProgressView: View {
    @ObservedObject var session: TLCSession

    var body: some View {
        VStack(alignment: .leading, spacing: 16) {
            // Header
            HStack {
                if session.isRunning {
                    ProgressView()
                        .controlSize(.small)
                        .padding(.trailing, 4)
                }

                Text(statusTitle)
                    .font(.headline)

                Spacer()

                if session.isRunning {
                    Button("Stop") {
                        session.stop()
                    }
                    .buttonStyle(.bordered)
                }
            }

            // Progress info
            if let progress = session.progress {
                ProgressDetailsView(progress: progress)
            }

            // Progress chart
            if session.progressHistory.count >= 2 {
                ProgressChartView(history: session.progressHistory)
            }

            // Error display
            if let error = session.error {
                ErrorBanner(error: error)
            }

            // Result summary
            if let result = session.result {
                ResultSummaryView(result: result)
            }
        }
        .padding()
        .frame(maxWidth: .infinity, alignment: .leading)
    }

    var statusTitle: String {
        if let progress = session.progress {
            switch progress.phase {
            case .parsing:
                return "Parsing specification..."
            case .computing:
                return "Computing reachable states..."
            case .checkingLiveness:
                return "Checking liveness properties..."
            case .done:
                return "Model checking complete"
            case .error:
                return "Error found"
            }
        }

        if session.isRunning {
            return "Starting TLC..."
        }

        if session.result != nil {
            return "Model checking complete"
        }

        return "Ready to check"
    }
}

// MARK: - Progress Details

struct ProgressDetailsView: View, Equatable {
    let progress: ModelCheckProgress

    static func == (lhs: ProgressDetailsView, rhs: ProgressDetailsView) -> Bool {
        lhs.progress.sessionId == rhs.progress.sessionId &&
        lhs.progress.phase == rhs.progress.phase &&
        lhs.progress.statesFound == rhs.progress.statesFound &&
        lhs.progress.distinctStates == rhs.progress.distinctStates &&
        lhs.progress.statesLeft == rhs.progress.statesLeft &&
        lhs.progress.statesPerSecond == rhs.progress.statesPerSecond &&
        lhs.progress.memoryUsed == rhs.progress.memoryUsed &&
        lhs.progress.currentAction == rhs.progress.currentAction
    }

    var body: some View {
        VStack(alignment: .leading, spacing: 8) {
            // State counts
            HStack(spacing: 24) {
                StatBox(title: "States Found", value: formatNumber(progress.statesFound))
                StatBox(title: "Distinct", value: formatNumber(progress.distinctStates))
                StatBox(title: "Queue", value: formatNumber(progress.statesLeft))
            }

            // Performance
            HStack(spacing: 24) {
                StatBox(title: "Rate", value: "\(formatNumber(UInt64(progress.statesPerSecond)))/s")
                StatBox(title: "Duration", value: formatDuration(progress.duration))
                if progress.memoryUsed > 0 {
                    StatBox(title: "Memory", value: formatBytes(progress.memoryUsed))
                }
            }

            // Current action
            if let action = progress.currentAction {
                HStack {
                    Text("Current action:")
                        .foregroundColor(.secondary)
                    Text(action)
                        .font(.system(.body, design: .monospaced))
                }
            }

            // Progress bar (indeterminate when queue unknown)
            if progress.statesLeft > 0 && progress.distinctStates > 0 {
                let completed = Double(progress.distinctStates - progress.statesLeft) / Double(progress.distinctStates)
                ProgressView(value: completed)
                    .progressViewStyle(.linear)
            } else if progress.phase == .computing {
                ProgressView()
                    .progressViewStyle(.linear)
            }
        }
    }

    func formatNumber(_ n: UInt64) -> String {
        if n >= 1_000_000_000 {
            return String(format: "%.1fB", Double(n) / 1_000_000_000)
        } else if n >= 1_000_000 {
            return String(format: "%.1fM", Double(n) / 1_000_000)
        } else if n >= 1_000 {
            return String(format: "%.1fK", Double(n) / 1_000)
        }
        return "\(n)"
    }

    func formatDuration(_ seconds: TimeInterval) -> String {
        if seconds < 60 {
            return String(format: "%.1fs", seconds)
        } else if seconds < 3600 {
            let mins = Int(seconds / 60)
            let secs = Int(seconds.truncatingRemainder(dividingBy: 60))
            return "\(mins)m \(secs)s"
        } else {
            let hours = Int(seconds / 3600)
            let mins = Int((seconds.truncatingRemainder(dividingBy: 3600)) / 60)
            return "\(hours)h \(mins)m"
        }
    }

    func formatBytes(_ bytes: UInt64) -> String {
        if bytes >= 1_073_741_824 {
            return String(format: "%.1f GB", Double(bytes) / 1_073_741_824)
        } else if bytes >= 1_048_576 {
            return String(format: "%.1f MB", Double(bytes) / 1_048_576)
        } else if bytes >= 1024 {
            return String(format: "%.1f KB", Double(bytes) / 1024)
        }
        return "\(bytes) B"
    }
}

// MARK: - Stat Box

struct StatBox: View, Equatable {
    let title: String
    let value: String

    var body: some View {
        VStack(alignment: .leading, spacing: 2) {
            Text(title)
                .font(.caption)
                .foregroundColor(.secondary)
            Text(value)
                .font(.system(.body, design: .monospaced))
                .fontWeight(.medium)
        }
    }

    static func == (lhs: StatBox, rhs: StatBox) -> Bool {
        lhs.title == rhs.title && lhs.value == rhs.value
    }
}

// MARK: - Result Summary

struct ResultSummaryView: View {
    let result: ModelCheckResult

    var body: some View {
        VStack(alignment: .leading, spacing: 12) {
            // Success/Failure indicator
            HStack {
                Image(systemName: result.success ? "checkmark.circle.fill" : "xmark.circle.fill")
                    .foregroundColor(result.success ? .green : .red)
                    .font(.title2)

                Text(result.success ? "No errors found" : "Error found")
                    .font(.headline)
            }

            // Stats
            HStack(spacing: 24) {
                StatBox(title: "Total States", value: "\(result.statesFound)")
                StatBox(title: "Distinct States", value: "\(result.distinctStates)")
                StatBox(title: "Duration", value: formatDuration(result.duration))
            }

            // Message
            if let message = result.message {
                Text(message)
                    .font(.callout)
                    .foregroundColor(.secondary)
            }
        }
        .padding()
        .background(result.success ? Color.green.opacity(0.1) : Color.red.opacity(0.1))
        .cornerRadius(8)
    }

    func formatDuration(_ seconds: TimeInterval) -> String {
        if seconds < 60 {
            return String(format: "%.2fs", seconds)
        } else if seconds < 3600 {
            let mins = Int(seconds / 60)
            let secs = Int(seconds.truncatingRemainder(dividingBy: 60))
            return "\(mins)m \(secs)s"
        } else {
            let hours = Int(seconds / 3600)
            let mins = Int((seconds.truncatingRemainder(dividingBy: 3600)) / 60)
            return "\(hours)h \(mins)m"
        }
    }
}

// MARK: - Error Banner

struct ErrorBanner: View {
    let error: Error

    var body: some View {
        HStack {
            Image(systemName: "exclamationmark.triangle.fill")
                .foregroundColor(.yellow)

            Text(error.localizedDescription)
                .font(.callout)

            Spacer()
        }
        .padding()
        .background(Color.yellow.opacity(0.1))
        .cornerRadius(8)
    }
}

// MARK: - Compact Progress View

/// Smaller progress view for toolbar or status bar
struct CompactProgressView: View {
    let progress: ModelCheckProgress?
    let isRunning: Bool

    var body: some View {
        HStack(spacing: 8) {
            if isRunning {
                ProgressView()
                    .controlSize(.small)
            }

            if let progress = progress {
                Text("\(progress.distinctStates) states")
                    .font(.caption)
                    .foregroundColor(.secondary)

                if progress.statesPerSecond > 0 {
                    Text("(\(Int(progress.statesPerSecond))/s)")
                        .font(.caption)
                        .foregroundColor(.secondary)
                }
            }
        }
    }
}
