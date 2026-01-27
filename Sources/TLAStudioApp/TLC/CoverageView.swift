import SwiftUI

// MARK: - Coverage View

/// Displays action coverage statistics from model checking
struct CoverageView: View {
    let coverage: [ActionCoverage]
    let totalStates: UInt64

    @State private var sortOrder = [KeyPathComparator(\ActionCoverage.count, order: .reverse)]

    var sortedCoverage: [ActionCoverage] {
        coverage.sorted(using: sortOrder)
    }

    var body: some View {
        VStack(alignment: .leading, spacing: 0) {
            // Summary header
            HStack {
                VStack(alignment: .leading) {
                    Text("Action Coverage")
                        .font(.headline)
                    Text("\(coverage.count) actions, \(totalStates) total states")
                        .font(.caption)
                        .foregroundColor(.secondary)
                }

                Spacer()

                // Overall coverage indicator
                if !coverage.isEmpty {
                    VStack(alignment: .trailing) {
                        Text("\(overallCoveragePercent)%")
                            .font(.title2)
                            .fontWeight(.semibold)
                        Text("coverage")
                            .font(.caption)
                            .foregroundColor(.secondary)
                    }
                }
            }
            .padding()
            .background(Color(NSColor.controlBackgroundColor))

            Divider()

            // Coverage table
            Table(sortedCoverage, sortOrder: $sortOrder) {
                TableColumn("Action", value: \.actionName) { action in
                    Text(action.actionName)
                        .font(.system(.body, design: .monospaced))
                }
                .width(min: 150, ideal: 200)

                TableColumn("Executions", value: \.count) { action in
                    Text(formatNumber(action.count))
                        .monospacedDigit()
                }
                .width(min: 80, ideal: 100)

                TableColumn("States", value: \.distinctStates) { action in
                    Text(formatNumber(action.distinctStates))
                        .monospacedDigit()
                }
                .width(min: 80, ideal: 100)

                TableColumn("Coverage") { action in
                    CoverageBar(
                        value: Double(action.distinctStates),
                        total: Double(totalStates)
                    )
                }
                .width(min: 100, ideal: 150)
            }
        }
    }

    var overallCoveragePercent: Int {
        guard totalStates > 0 else { return 0 }
        let coveredStates = coverage.reduce(0) { $0 + $1.distinctStates }
        // Each state might be covered by multiple actions, so cap at 100%
        return min(100, Int((Double(coveredStates) / Double(totalStates)) * 100))
    }

    func formatNumber(_ n: UInt64) -> String {
        let formatter = NumberFormatter()
        formatter.numberStyle = .decimal
        return formatter.string(from: NSNumber(value: n)) ?? "\(n)"
    }
}

// MARK: - Coverage Bar

struct CoverageBar: View {
    let value: Double
    let total: Double

    var percentage: Double {
        guard total > 0 else { return 0 }
        return min(1.0, value / total)
    }

    var body: some View {
        GeometryReader { geometry in
            ZStack(alignment: .leading) {
                // Background
                RoundedRectangle(cornerRadius: 3)
                    .fill(Color.secondary.opacity(0.2))

                // Fill
                RoundedRectangle(cornerRadius: 3)
                    .fill(coverageColor)
                    .frame(width: geometry.size.width * percentage)

                // Percentage text
                Text(String(format: "%.1f%%", percentage * 100))
                    .font(.caption2)
                    .foregroundColor(.secondary)
                    .frame(maxWidth: .infinity, alignment: .trailing)
                    .padding(.trailing, 4)
            }
        }
        .frame(height: 16)
    }

    var coverageColor: Color {
        if percentage >= 0.8 {
            return .green
        } else if percentage >= 0.5 {
            return .yellow
        } else if percentage >= 0.2 {
            return .orange
        } else {
            return .red
        }
    }
}

// MARK: - Coverage Summary Card

/// Compact coverage summary for embedding
struct CoverageSummaryCard: View {
    let coverage: [ActionCoverage]
    let totalStates: UInt64
    var onExpand: (() -> Void)?

    var body: some View {
        VStack(alignment: .leading, spacing: 8) {
            HStack {
                Image(systemName: "chart.bar.fill")
                    .foregroundColor(.blue)

                Text("Coverage")
                    .font(.headline)

                Spacer()

                if let onExpand = onExpand {
                    Button("Details") {
                        onExpand()
                    }
                    .buttonStyle(.link)
                }
            }

            // Top actions
            ForEach(topActions.prefix(3)) { action in
                HStack {
                    Text(action.actionName)
                        .font(.system(.caption, design: .monospaced))
                        .lineLimit(1)

                    Spacer()

                    Text("\(action.count)")
                        .font(.caption)
                        .foregroundColor(.secondary)
                }
            }

            if coverage.count > 3 {
                Text("+ \(coverage.count - 3) more actions")
                    .font(.caption)
                    .foregroundColor(.secondary)
            }
        }
        .padding()
        .background(Color(NSColor.controlBackgroundColor))
        .cornerRadius(8)
    }

    var topActions: [ActionCoverage] {
        coverage.sorted { $0.count > $1.count }
    }
}

// MARK: - Coverage Heatmap

/// Visual heatmap of action coverage
struct CoverageHeatmap: View {
    let coverage: [ActionCoverage]
    let totalStates: UInt64

    private let columns = [
        GridItem(.adaptive(minimum: 80, maximum: 120), spacing: 8)
    ]

    var body: some View {
        LazyVGrid(columns: columns, spacing: 8) {
            ForEach(coverage.sorted { $0.count > $1.count }) { action in
                CoverageCell(action: action, totalStates: totalStates)
            }
        }
        .padding()
    }
}

struct CoverageCell: View {
    let action: ActionCoverage
    let totalStates: UInt64

    var percentage: Double {
        guard totalStates > 0 else { return 0 }
        return min(1.0, Double(action.distinctStates) / Double(totalStates))
    }

    var body: some View {
        VStack(spacing: 4) {
            Text(action.actionName)
                .font(.system(.caption, design: .monospaced))
                .lineLimit(1)
                .truncationMode(.middle)

            Text("\(action.count)")
                .font(.caption2)
                .fontWeight(.semibold)
        }
        .frame(maxWidth: .infinity)
        .padding(8)
        .background(cellColor.opacity(0.3 + percentage * 0.7))
        .cornerRadius(8)
    }

    var cellColor: Color {
        if percentage >= 0.5 {
            return .green
        } else if percentage >= 0.2 {
            return .yellow
        } else {
            return .orange
        }
    }
}

// MARK: - No Coverage View

struct NoCoverageView: View {
    var body: some View {
        VStack(spacing: 16) {
            Image(systemName: "chart.bar")
                .font(.largeTitle)
                .foregroundColor(.secondary)

            Text("No Coverage Data")
                .font(.headline)

            Text("Run model checking to see action coverage statistics.")
                .font(.callout)
                .foregroundColor(.secondary)
                .multilineTextAlignment(.center)
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
        .padding()
    }
}
