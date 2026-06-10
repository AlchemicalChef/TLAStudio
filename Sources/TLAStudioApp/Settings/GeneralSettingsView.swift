import AppKit
import SwiftUI

// MARK: - General Settings View

/// A SwiftUI settings view for general application preferences.
///
/// This view provides controls for document handling, application behavior,
/// and data management. It uses `@AppStorage` for persistent storage of
/// user preferences.
struct GeneralSettingsView: View {

    // MARK: - Application Settings

    @AppStorage(UserSettings.Keys.showWelcomeOnLaunch) private var showWelcomeOnLaunch = true

    // MARK: - Module Library Settings

    @State private var moduleLibraryFolders = UserSettings.shared.moduleLibraryFolders

    // MARK: - Alert State

    @State private var showClearRecentsAlert = false
    @State private var showResetSettingsAlert = false

    // MARK: - Body

    var body: some View {
        Form {
            moduleLibrariesSection
            applicationSection
            dataManagementSection
        }
        .formStyle(.grouped)
        .padding()
    }

    // MARK: - Application Section

    private var moduleLibrariesSection: some View {
        Section("Module Libraries") {
            if moduleLibraryFolders.isEmpty {
                Text("No extra library folders configured.")
                    .foregroundStyle(.secondary)
            } else {
                ForEach(moduleLibraryFolders, id: \.self) { folder in
                    HStack(spacing: 12) {
                        VStack(alignment: .leading, spacing: 2) {
                            Text((folder as NSString).lastPathComponent)
                            Text(folder)
                                .font(.caption)
                                .foregroundStyle(.secondary)
                                .textSelection(.enabled)
                        }

                        Spacer()

                        Button(role: .destructive) {
                            removeModuleLibraryFolder(folder)
                        } label: {
                            Image(systemName: "minus.circle")
                        }
                        .buttonStyle(.plain)
                        .help("Remove folder")
                    }
                }
            }

            HStack {
                Button("Add Folder…") {
                    addModuleLibraryFolder()
                }

                if !moduleLibraryFolders.isEmpty {
                    Button("Clear All", role: .destructive) {
                        moduleLibraryFolders = []
                        persistModuleLibraryFolders()
                    }
                }
            }

            Text("Folders are searched in order after the current spec directory and before bundled or system modules.")
                .font(.caption)
                .foregroundStyle(.secondary)
        }
    }

    private var applicationSection: some View {
        Section("Application") {
            Toggle("Show welcome screen on launch", isOn: $showWelcomeOnLaunch)
        }
    }

    // MARK: - Data Management Section

    private var dataManagementSection: some View {
        Section("Data Management") {
            HStack {
                Button("Clear Recent Documents") {
                    showClearRecentsAlert = true
                }
                .alert("Clear Recent Documents", isPresented: $showClearRecentsAlert) {
                    Button("Cancel", role: .cancel) { }
                    Button("Clear", role: .destructive) {
                        clearRecentDocuments()
                    }
                } message: {
                    Text("This will remove all items from the recent documents list. This action cannot be undone.")
                }

                Spacer()
            }

            HStack {
                Button("Reset All Settings") {
                    showResetSettingsAlert = true
                }
                .alert("Reset All Settings", isPresented: $showResetSettingsAlert) {
                    Button("Cancel", role: .cancel) { }
                    Button("Reset", role: .destructive) {
                        resetAllSettings()
                    }
                } message: {
                    Text("This will restore all settings to their default values. This action cannot be undone.")
                }

                Spacer()
            }

            versionInfoView
        }
    }

    // MARK: - Version Info

    private var versionInfoView: some View {
        HStack {
            Spacer()
            VStack(alignment: .trailing, spacing: 2) {
                Text("TLA+ Studio \(appVersion)")
                    .font(.footnote)
                    .foregroundStyle(.secondary)
                Text("Build \(buildNumber)")
                    .font(.caption2)
                    .foregroundStyle(.tertiary)
            }
        }
        .padding(.top, 8)
    }

    // MARK: - Computed Properties

    private var appVersion: String {
        Bundle.main.infoDictionary?["CFBundleShortVersionString"] as? String ?? "1.0"
    }

    private var buildNumber: String {
        Bundle.main.infoDictionary?["CFBundleVersion"] as? String ?? "1"
    }

    // MARK: - Actions

    private func clearRecentDocuments() {
        NSDocumentController.shared.clearRecentDocuments(nil)
    }

    private func resetAllSettings() {
        moduleLibraryFolders = []
        persistModuleLibraryFolders()

        // Application
        showWelcomeOnLaunch = true
    }

    private func persistModuleLibraryFolders() {
        moduleLibraryFolders = UserSettings.normalizedModuleLibraryFolders(moduleLibraryFolders)
        UserSettings.shared.moduleLibraryFolders = moduleLibraryFolders
    }

    private func addModuleLibraryFolder() {
        let panel = NSOpenPanel()
        panel.title = "Choose Module Library Folder"
        panel.prompt = "Add Folder"
        panel.allowsMultipleSelection = true
        panel.canChooseDirectories = true
        panel.canChooseFiles = false
        panel.canCreateDirectories = true

        guard panel.runModal() == .OK else { return }

        moduleLibraryFolders.append(contentsOf: panel.urls.map(\.path))
        persistModuleLibraryFolders()
    }

    private func removeModuleLibraryFolder(_ folder: String) {
        moduleLibraryFolders.removeAll { $0 == folder }
        persistModuleLibraryFolders()
    }
}

// MARK: - Preview

#Preview {
    GeneralSettingsView()
        .frame(width: 500, height: 400)
}
