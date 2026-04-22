import AppKit
import SwiftUI

// MARK: - Text Encoding

/// Supported text encodings for document handling.
enum TextEncoding: String, CaseIterable, Identifiable {
    case utf8 = "UTF-8"
    case windows1252 = "Windows-1252"
    case ascii = "ASCII"

    var id: String { rawValue }

    var stringEncoding: String.Encoding {
        switch self {
        case .utf8:
            return .utf8
        case .windows1252:
            return .windowsCP1252
        case .ascii:
            return .ascii
        }
    }
}

// MARK: - Autosave Interval

/// Available intervals for document autosave.
enum AutosaveInterval: Int, CaseIterable, Identifiable {
    case tenSeconds = 10
    case fifteenSeconds = 15
    case thirtySeconds = 30
    case sixtySeconds = 60

    var id: Int { rawValue }

    var displayName: String {
        switch self {
        case .tenSeconds:
            return "10 seconds"
        case .fifteenSeconds:
            return "15 seconds"
        case .thirtySeconds:
            return "30 seconds"
        case .sixtySeconds:
            return "60 seconds"
        }
    }
}

// MARK: - General Settings View

/// A SwiftUI settings view for general application preferences.
///
/// This view provides controls for document handling, application behavior,
/// and data management. It uses `@AppStorage` for persistent storage of
/// user preferences.
struct GeneralSettingsView: View {

    // MARK: - Document Handling Settings

    @AppStorage(UserSettings.Keys.autosaveEnabled) private var autosaveEnabled = true
    @AppStorage(UserSettings.Keys.autosaveInterval) private var autosaveInterval = 30
    @AppStorage(UserSettings.Keys.reopenLastDocument) private var reopenLastDocument = true
    @AppStorage(UserSettings.Keys.defaultEncoding) private var defaultTextEncoding = TextEncoding.utf8.rawValue

    // MARK: - Application Settings

    @AppStorage(UserSettings.Keys.checkForUpdates) private var checkForUpdates = true
    @AppStorage(UserSettings.Keys.showWelcomeOnLaunch) private var showWelcomeOnLaunch = true

    // MARK: - Module Library Settings

    @State private var moduleLibraryFolders = UserSettings.shared.moduleLibraryFolders

    // MARK: - Alert State

    @State private var showClearRecentsAlert = false
    @State private var showResetSettingsAlert = false

    // MARK: - Body

    var body: some View {
        Form {
            documentHandlingSection
            moduleLibrariesSection
            applicationSection
            dataManagementSection
        }
        .formStyle(.grouped)
        .padding()
    }

    // MARK: - Document Handling Section

    private var documentHandlingSection: some View {
        Section("Document Handling") {
            Toggle("Automatically save documents", isOn: $autosaveEnabled)

            if autosaveEnabled {
                Picker("Save interval", selection: $autosaveInterval) {
                    ForEach(AutosaveInterval.allCases) { interval in
                        Text(interval.displayName).tag(interval.rawValue)
                    }
                }
            }

            Toggle("Reopen last document on launch", isOn: $reopenLastDocument)

            Picker("Default text encoding", selection: $defaultTextEncoding) {
                ForEach(TextEncoding.allCases) { encoding in
                    Text(encoding.rawValue).tag(encoding.rawValue)
                }
            }
        }
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
                Button("Add Folder...") {
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
            Toggle("Check for updates automatically", isOn: $checkForUpdates)
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
                Text("TLA Studio \(appVersion)")
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
        // Document Handling
        autosaveEnabled = true
        autosaveInterval = 30
        reopenLastDocument = true
        defaultTextEncoding = TextEncoding.utf8.rawValue
        moduleLibraryFolders = []
        persistModuleLibraryFolders()

        // Application
        checkForUpdates = true
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
