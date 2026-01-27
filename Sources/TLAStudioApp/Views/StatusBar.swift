import SwiftUI

// MARK: - Status Bar

/// Bottom status bar showing editor information
struct StatusBar: View {
    @ObservedObject var document: TLADocument
    let cursorLine: Int
    let cursorColumn: Int

    var body: some View {
        HStack(spacing: 0) {
            // Left section: Line/Column position
            HStack(spacing: 4) {
                Text("Ln \(cursorLine), Col \(cursorColumn)")
                    .font(.system(size: 11, design: .monospaced))
            }
            .padding(.horizontal, 8)

            Divider()
                .frame(height: 12)

            // Encoding
            Text(document.encoding == .utf8 ? "UTF-8" : "UTF-16")
                .font(.system(size: 11))
                .padding(.horizontal, 8)

            Divider()
                .frame(height: 12)

            // Line ending
            Text(document.lineEnding.displayName)
                .font(.system(size: 11))
                .padding(.horizontal, 8)

            Spacer()

            // Parse status
            HStack(spacing: 4) {
                parseStatusIcon
                Text(parseStatusText)
                    .font(.system(size: 11))
            }
            .padding(.horizontal, 8)

            Divider()
                .frame(height: 12)

            // TLC status
            if let session = document.tlcSession, session.isRunning {
                HStack(spacing: 4) {
                    ProgressView()
                        .controlSize(.mini)
                        .scaleEffect(0.7)
                    Text("TLC Running")
                        .font(.system(size: 11))
                }
                .padding(.horizontal, 8)

                Divider()
                    .frame(height: 12)
            }

            // Proof status
            if let session = document.proofSession, session.isRunning {
                HStack(spacing: 4) {
                    ProgressView()
                        .controlSize(.mini)
                        .scaleEffect(0.7)
                    Text("TLAPM Running")
                        .font(.system(size: 11))
                }
                .padding(.horizontal, 8)

                Divider()
                    .frame(height: 12)
            }

            // File type
            Text("TLA+")
                .font(.system(size: 11))
                .padding(.horizontal, 8)
        }
        .frame(height: 22)
        .background(Color(NSColor.controlBackgroundColor))
    }

    // MARK: - Parse Status

    @ViewBuilder
    private var parseStatusIcon: some View {
        let errorCount = document.diagnostics.filter { $0.severity == .error }.count
        let warningCount = document.diagnostics.filter { $0.severity == .warning }.count

        if errorCount > 0 {
            Image(systemName: "xmark.circle.fill")
                .font(.system(size: 10))
                .foregroundColor(.red)
        } else if warningCount > 0 {
            Image(systemName: "exclamationmark.triangle.fill")
                .font(.system(size: 10))
                .foregroundColor(.orange)
        } else {
            Image(systemName: "checkmark.circle.fill")
                .font(.system(size: 10))
                .foregroundColor(.green)
        }
    }

    private var parseStatusText: String {
        let errorCount = document.diagnostics.filter { $0.severity == .error }.count
        let warningCount = document.diagnostics.filter { $0.severity == .warning }.count

        if errorCount > 0 && warningCount > 0 {
            return "\(errorCount) errors, \(warningCount) warnings"
        } else if errorCount > 0 {
            return "\(errorCount) error\(errorCount == 1 ? "" : "s")"
        } else if warningCount > 0 {
            return "\(warningCount) warning\(warningCount == 1 ? "" : "s")"
        } else {
            return "No issues"
        }
    }
}

// MARK: - Line Ending Display

extension LineEnding {
    var displayName: String {
        switch self {
        case .lf: return "LF"
        case .crlf: return "CRLF"
        case .cr: return "CR"
        }
    }
}

// MARK: - Preview

#if DEBUG
struct StatusBar_Previews: PreviewProvider {
    static var previews: some View {
        StatusBar(
            document: TLADocument(),
            cursorLine: 42,
            cursorColumn: 15
        )
    }
}
#endif
