import SwiftUI

// MARK: - Checkpoint Settings View

/// UI for checkpoint configuration and management
struct CheckpointSettingsView: View {
    @Binding var config: ModelConfig
    let specURL: URL?

    @State private var checkpoints: [CheckpointInfo] = []
    @State private var isLoading = false
    @State private var error: Error?
    @State private var showDeleteConfirmation = false
    @State private var checkpointToDelete: CheckpointInfo?

    var onResume: ((CheckpointInfo) -> Void)?

    var body: some View {
        VStack(alignment: .leading, spacing: 16) {
            // Settings section
            settingsSection

            Divider()

            // Available checkpoints section
            checkpointsSection
        }
        .padding()
        .task {
            await loadCheckpoints()
        }
        .alert("Delete Checkpoint", isPresented: $showDeleteConfirmation) {
            Button("Cancel", role: .cancel) { }
            Button("Delete", role: .destructive) {
                if let checkpoint = checkpointToDelete {
                    Task { await deleteCheckpoint(checkpoint) }
                }
            }
        } message: {
            if let checkpoint = checkpointToDelete {
                Text("Are you sure you want to delete the checkpoint from \(checkpoint.ageDescription)?")
            }
        }
    }

    // MARK: - Settings Section

    var settingsSection: some View {
        VStack(alignment: .leading, spacing: 12) {
            Text("Checkpoint Settings")
                .font(.headline)

            Toggle("Enable Checkpointing", isOn: $config.checkpointEnabled)

            if config.checkpointEnabled {
                HStack {
                    Text("Checkpoint Interval:")
                    Stepper(
                        "\(Int(config.checkpointInterval / 60)) min",
                        value: Binding(
                            get: { Int(config.checkpointInterval / 60) },
                            set: { config.checkpointInterval = TimeInterval($0 * 60) }
                        ),
                        in: 1...60
                    )
                }

                Toggle("Auto-cleanup Old Checkpoints", isOn: $config.autoCleanupCheckpoints)

                HStack {
                    Text("Checkpoint Directory:")
                    Text(checkpointDirDisplay)
                        .foregroundColor(.secondary)
                        .lineLimit(1)
                        .truncationMode(.middle)

                    Spacer()

                    Button("Choose...") {
                        chooseCheckpointDirectory()
                    }
                    .buttonStyle(.bordered)
                    .controlSize(.small)
                }
            }
        }
    }

    var checkpointDirDisplay: String {
        if let dir = config.checkpointDir {
            return dir.path
        }
        if let specURL = specURL {
            let defaultDir = specURL.deletingPathExtension().lastPathComponent + ".toolbox"
            return defaultDir + " (default)"
        }
        return "Default"
    }

    func chooseCheckpointDirectory() {
        let panel = NSOpenPanel()
        panel.canChooseFiles = false
        panel.canChooseDirectories = true
        panel.canCreateDirectories = true
        panel.message = "Choose a directory for TLC checkpoints"

        if panel.runModal() == .OK {
            config.checkpointDir = panel.url
        }
    }

    // MARK: - Checkpoints Section

    var checkpointsSection: some View {
        VStack(alignment: .leading, spacing: 12) {
            HStack {
                Text("Available Checkpoints")
                    .font(.headline)

                Spacer()

                if isLoading {
                    ProgressView()
                        .controlSize(.small)
                } else {
                    Button {
                        Task { await loadCheckpoints() }
                    } label: {
                        Image(systemName: "arrow.clockwise")
                    }
                    .buttonStyle(.borderless)
                    .help("Refresh checkpoints")
                }
            }

            if let error = error {
                HStack {
                    Image(systemName: "exclamationmark.triangle")
                        .foregroundColor(.orange)
                    Text(error.localizedDescription)
                        .foregroundColor(.secondary)
                        .font(.caption)
                }
            } else if checkpoints.isEmpty {
                Text("No checkpoints found")
                    .foregroundColor(.secondary)
                    .font(.callout)
            } else {
                checkpointsList
            }
        }
    }

    var checkpointsList: some View {
        VStack(spacing: 8) {
            ForEach(checkpoints) { checkpoint in
                CheckpointRow(
                    checkpoint: checkpoint,
                    onResume: {
                        onResume?(checkpoint)
                    },
                    onDelete: {
                        checkpointToDelete = checkpoint
                        showDeleteConfirmation = true
                    }
                )
            }
        }
    }

    // MARK: - Actions

    func loadCheckpoints() async {
        guard let specURL = specURL else { return }

        await MainActor.run { isLoading = true }

        do {
            let discovered = try await CheckpointManager.shared.discoverCheckpoints(forSpec: specURL)
            await MainActor.run {
                checkpoints = discovered
                isLoading = false
                error = nil
            }
        } catch {
            await MainActor.run {
                self.error = error
                isLoading = false
            }
        }
    }

    func deleteCheckpoint(_ checkpoint: CheckpointInfo) async {
        do {
            try await CheckpointManager.shared.deleteCheckpoint(checkpoint)
            await loadCheckpoints()
        } catch {
            await MainActor.run {
                self.error = error
            }
        }
    }
}

// MARK: - Checkpoint Row

struct CheckpointRow: View {
    let checkpoint: CheckpointInfo
    var onResume: (() -> Void)?
    var onDelete: (() -> Void)?

    var body: some View {
        HStack {
            VStack(alignment: .leading, spacing: 4) {
                Text(checkpoint.displayName)
                    .font(.callout)

                HStack(spacing: 8) {
                    Text(checkpoint.ageDescription)
                        .font(.caption)
                        .foregroundColor(.secondary)

                    Text(checkpoint.formattedDiskSize)
                        .font(.caption)
                        .foregroundColor(.secondary)

                    if let states = checkpoint.distinctStates {
                        Text("\(states) states")
                            .font(.caption)
                            .foregroundColor(.secondary)
                    }
                }
            }

            Spacer()

            Button("Resume") {
                onResume?()
            }
            .buttonStyle(.borderedProminent)
            .controlSize(.small)

            Button {
                onDelete?()
            } label: {
                Image(systemName: "trash")
            }
            .buttonStyle(.borderless)
            .foregroundColor(.red)
            .help("Delete checkpoint")
        }
        .padding(8)
        .background(Color(NSColor.controlBackgroundColor))
        .cornerRadius(6)
    }
}

// MARK: - Compact Checkpoint View

/// Compact view for showing checkpoint status inline
struct CheckpointStatusView: View {
    let status: CheckpointStatus

    var body: some View {
        if status != .none {
            HStack(spacing: 4) {
                if status.isActive {
                    ProgressView()
                        .controlSize(.small)
                } else {
                    Image(systemName: statusIcon)
                        .foregroundColor(statusColor)
                }

                Text(status.displayMessage)
                    .font(.caption)
                    .foregroundColor(.secondary)
            }
        }
    }

    var statusIcon: String {
        switch status {
        case .saved:
            return "checkmark.circle.fill"
        case .restored:
            return "arrow.counterclockwise.circle.fill"
        case .failed:
            return "exclamationmark.circle.fill"
        default:
            return "circle"
        }
    }

    var statusColor: Color {
        switch status {
        case .saved, .restored:
            return .green
        case .failed:
            return .red
        default:
            return .secondary
        }
    }
}
