import AppKit
import Combine
import Foundation
import SwiftUI

// MARK: - UserSettings

/// Central settings model for TLA Studio that persists user preferences using @AppStorage.
///
/// Access the shared instance via `UserSettings.shared`. All properties are automatically
/// persisted to UserDefaults and trigger SwiftUI view updates when changed.
///
/// Settings are organized into three categories:
/// - **General**: Application-wide behavior settings
/// - **Editor**: Text editor appearance and behavior
/// - **Prover**: TLC and TLAPM tool configuration
final class UserSettings: ObservableObject {

    // MARK: - Singleton

    /// The shared settings instance used throughout the application.
    static let shared = UserSettings()

    // MARK: - Storage Keys

    enum Keys {
        // General
        static let autosaveEnabled = "settings.general.autosaveEnabled"
        static let autosaveInterval = "settings.general.autosaveInterval"
        static let defaultEncoding = "settings.general.defaultEncoding"
        static let reopenLastDocument = "settings.general.reopenLastDocument"
        static let checkForUpdates = "settings.general.checkForUpdates"
        static let showWelcomeOnLaunch = "settings.general.showWelcomeOnLaunch"
        static let moduleLibraryFolders = "settings.general.moduleLibraryFolders"

        // Editor
        static let fontName = "settings.editor.fontName"
        static let fontSize = "settings.editor.fontSize"
        static let lineHeight = "settings.editor.lineHeight"
        static let showLineNumbers = "settings.editor.showLineNumbers"
        static let showMinimap = "settings.editor.showMinimap"
        static let highlightCurrentLine = "settings.editor.highlightCurrentLine"
        static let tabWidth = "settings.editor.tabWidth"
        static let insertSpacesForTabs = "settings.editor.insertSpacesForTabs"
        static let wordWrap = "settings.editor.wordWrap"
        static let colorScheme = "settings.editor.colorScheme"
        static let appearance = "settings.editor.appearance"
        static let matchBrackets = "settings.editor.matchBrackets"

        // Prover
        static let tlcPath = "settings.prover.tlcPath"
        static let tlapmPath = "settings.prover.tlapmPath"
        static let z3Path = "settings.prover.z3Path"
        static let zenonPath = "settings.prover.zenonPath"
        static let isabellePath = "settings.prover.isabellePath"
        static let cvc5Path = "settings.prover.cvc5Path"
        static let spassPath = "settings.prover.spassPath"
        static let defaultProverBackend = "settings.prover.defaultProverBackend"
        static let defaultProverTimeout = "settings.prover.defaultProverTimeout"
        static let tlcWorkers = "settings.prover.tlcWorkers"
        static let tlcCheckpointEnabled = "settings.prover.tlcCheckpointEnabled"
        static let tlcCheckpointInterval = "settings.prover.tlcCheckpointInterval"
    }

    /// Legacy keys that older builds used. Migrated once on first launch of this build and then removed.
    /// Never read these directly; all reads go through the canonical `Keys` via `@AppStorage`.
    private enum LegacyKeys {
        static let cvc5Path = "prover.cvc5.path"
        static let spassPath = "prover.spass.path"
        static let tlcCheckpointEnabled = "prover.tlc.checkpointEnabled"
        static let migrationMarker = "settings.internal.migrated.v1"

        static let prover: [(String, String)] = [
            ("prover.tlc.path", Keys.tlcPath),
            ("prover.tlapm.path", Keys.tlapmPath),
            ("prover.z3.path", Keys.z3Path),
            ("prover.zenon.path", Keys.zenonPath),
            ("prover.isabelle.path", Keys.isabellePath),
            (cvc5Path, Keys.cvc5Path),
            (spassPath, Keys.spassPath),
            ("prover.tlc.workerThreads", Keys.tlcWorkers),
            (tlcCheckpointEnabled, Keys.tlcCheckpointEnabled),
            ("prover.tlc.checkpointInterval", Keys.tlcCheckpointInterval),
            ("prover.defaultBackend", Keys.defaultProverBackend),
            ("prover.defaultTimeout", Keys.defaultProverTimeout)
        ]
    }

    // MARK: - General Settings

    /// Enables automatic saving of documents at regular intervals.
    @AppStorage(Keys.autosaveEnabled)
    var autosaveEnabled: Bool = true

    /// The interval in seconds between automatic saves when autosave is enabled.
    @AppStorage(Keys.autosaveInterval)
    var autosaveInterval: Int = 30

    /// The default text encoding used when reading and writing files.
    @AppStorage(Keys.defaultEncoding)
    var defaultEncoding: String = "UTF-8"

    /// Whether to reopen the last edited document when launching the application.
    @AppStorage(Keys.reopenLastDocument)
    var reopenLastDocument: Bool = true

    /// Whether to automatically check for application updates on launch.
    @AppStorage(Keys.checkForUpdates)
    var checkForUpdates: Bool = true

    /// Whether to show the welcome screen when launching the application.
    @AppStorage(Keys.showWelcomeOnLaunch)
    var showWelcomeOnLaunch: Bool = true

    /// User-configured library folders searched for EXTENDS'd modules.
    var moduleLibraryFolders: [String] {
        get {
            Self.normalizedModuleLibraryFolders(
                UserDefaults.standard.stringArray(forKey: Keys.moduleLibraryFolders) ?? []
            )
        }
        set {
            let normalized = Self.normalizedModuleLibraryFolders(newValue)
            objectWillChange.send()
            if normalized.isEmpty {
                UserDefaults.standard.removeObject(forKey: Keys.moduleLibraryFolders)
            } else {
                UserDefaults.standard.set(normalized, forKey: Keys.moduleLibraryFolders)
            }
        }
    }

    /// Existing library folders that should be passed to TLC/TLAPM and module lookup.
    var resolvedModuleLibraryFolders: [String] {
        Self.existingModuleLibraryFolders(from: moduleLibraryFolders)
    }

    // MARK: - Editor Settings

    /// The name of the font used in the editor.
    @AppStorage(Keys.fontName)
    var fontName: String = "SF Mono"

    /// The font size in points used in the editor.
    @AppStorage(Keys.fontSize)
    var fontSize: Double = 13

    /// The line height multiplier for editor text.
    @AppStorage(Keys.lineHeight)
    var lineHeight: Double = 1.4

    /// Whether to display line numbers in the editor gutter.
    @AppStorage(Keys.showLineNumbers)
    var showLineNumbers: Bool = true

    /// Whether to display a minimap overview of the document.
    @AppStorage(Keys.showMinimap)
    var showMinimap: Bool = false

    /// Whether to highlight the line containing the cursor.
    @AppStorage(Keys.highlightCurrentLine)
    var highlightCurrentLine: Bool = true

    /// The number of spaces that a tab character represents.
    @AppStorage(Keys.tabWidth)
    var tabWidth: Int = 4

    /// Whether to insert spaces instead of tab characters when pressing Tab.
    @AppStorage(Keys.insertSpacesForTabs)
    var insertSpacesForTabs: Bool = true

    /// Whether to wrap long lines to fit the editor width.
    @AppStorage(Keys.wordWrap)
    var wordWrap: Bool = false

    /// The name of the syntax highlighting color scheme.
    @AppStorage(Keys.colorScheme)
    var colorScheme: String = "Default"

    /// The appearance mode: "system", "light", or "dark".
    @AppStorage(Keys.appearance)
    var appearance: String = "system"

    /// Whether to highlight matching brackets.
    @AppStorage(Keys.matchBrackets)
    var matchBrackets: Bool = true

    // MARK: - Prover Settings

    /// Custom path to the TLC model checker. Empty string uses the bundled version.
    @AppStorage(Keys.tlcPath)
    var tlcPath: String = ""

    /// Custom path to the TLAPM proof manager. Empty string uses the bundled version.
    @AppStorage(Keys.tlapmPath)
    var tlapmPath: String = ""

    /// Custom path to the Z3 SMT solver. Empty string uses the bundled version.
    @AppStorage(Keys.z3Path)
    var z3Path: String = ""

    /// Custom path to the Zenon automated theorem prover. Empty string uses the bundled version.
    @AppStorage(Keys.zenonPath)
    var zenonPath: String = ""

    /// Path to the Isabelle proof assistant installation.
    @AppStorage(Keys.isabellePath)
    var isabellePath: String = ""

    /// Custom path to the CVC5 SMT solver. Empty string uses the bundled version.
    @AppStorage(Keys.cvc5Path)
    var cvc5Path: String = ""

    /// Custom path to the SPASS automated theorem prover. Empty string uses the bundled version.
    @AppStorage(Keys.spassPath)
    var spassPath: String = ""

    /// The default backend to use for proof obligations ("auto", "zenon", "z3", "isabelle", "smt").
    @AppStorage(Keys.defaultProverBackend)
    var defaultProverBackend: String = "auto"

    /// The default timeout in seconds for proof attempts.
    @AppStorage(Keys.defaultProverTimeout)
    var defaultProverTimeout: Int = 30

    /// The number of worker threads TLC uses for model checking.
    /// Defaults to the number of available CPU cores.
    @AppStorage(Keys.tlcWorkers)
    var tlcWorkers: Int = ProcessInfo.processInfo.activeProcessorCount

    /// Whether TLC checkpointing is enabled by default for new models.
    @AppStorage(Keys.tlcCheckpointEnabled)
    var tlcCheckpointEnabled: Bool = true

    /// The interval in minutes between TLC checkpoint saves during model checking.
    @AppStorage(Keys.tlcCheckpointInterval)
    var tlcCheckpointInterval: Int = 30

    // MARK: - Computed Properties

    /// Returns the path to the TLC executable, using the bundled version if no custom path is set.
    var resolvedTLCPath: String {
        if tlcPath.isEmpty {
            return bundledToolPath(named: "tlc-native") ?? bundledToolPath(named: "tlc-native-fast") ?? ""
        }
        return tlcPath
    }

    /// Returns the path to the TLAPM executable, using the bundled version if no custom path is set.
    var resolvedTLAPMPath: String {
        if tlapmPath.isEmpty {
            return bundledToolPath(named: "tlapm", subdirectories: ["bin", "Provers"]) ?? ""
        }
        return tlapmPath
    }

    /// Returns the path to the Z3 executable, using the bundled version if no custom path is set.
    var resolvedZ3Path: String {
        if z3Path.isEmpty {
            return bundledToolPath(named: "z3", subdirectories: ["Provers", "lib/tlapm/backends/bin"]) ?? ""
        }
        return z3Path
    }

    /// Returns the path to the Zenon executable, using the bundled version if no custom path is set.
    var resolvedZenonPath: String {
        if zenonPath.isEmpty {
            return bundledToolPath(named: "zenon", subdirectories: ["Provers", "lib/tlapm/backends/bin"]) ?? ""
        }
        return zenonPath
    }

    /// Returns the path to the CVC5 executable, using the bundled version if no custom path is set.
    var resolvedCvc5Path: String {
        if cvc5Path.isEmpty {
            return bundledToolPath(named: "cvc5", subdirectories: ["Provers"]) ?? ""
        }
        return cvc5Path
    }

    /// Returns the path to the SPASS executable, using the bundled version if no custom path is set.
    var resolvedSpassPath: String {
        if spassPath.isEmpty {
            return bundledToolPath(named: "SPASS", subdirectories: ["Provers"]) ?? ""
        }
        return spassPath
    }

    /// The list of available syntax highlighting color schemes.
    var availableColorSchemes: [String] {
        [
            "Default",
            "Solarized Light",
            "Solarized Dark",
            "Monokai",
            "Dracula",
            "GitHub Light",
            "GitHub Dark",
            "One Light",
            "One Dark",
            "Nord",
            "Gruvbox Light",
            "Gruvbox Dark",
            "Tomorrow",
            "Tomorrow Night"
        ]
    }

    /// The list of available appearance modes.
    var availableAppearances: [String] {
        ["system", "light", "dark"]
    }

    /// Display name for an appearance mode.
    func appearanceDisplayName(_ mode: String) -> String {
        switch mode {
        case "system": return "System"
        case "light": return "Light"
        case "dark": return "Dark"
        default: return mode.capitalized
        }
    }

    /// The list of available monospace fonts suitable for code editing.
    var availableFonts: [String] {
        let monospaceFonts = [
            "SF Mono",
            "Menlo",
            "Monaco",
            "Courier New",
            "Andale Mono",
            "Source Code Pro",
            "Fira Code",
            "JetBrains Mono",
            "Cascadia Code",
            "IBM Plex Mono",
            "Inconsolata",
            "Hack",
            "Ubuntu Mono",
            "Roboto Mono",
            "Input Mono",
            "Dank Mono",
            "Operator Mono",
            "Berkeley Mono"
        ]

        // Filter to only fonts that are actually installed on this system
        let fontManager = NSFontManager.shared
        return monospaceFonts.filter { fontName in
            fontManager.font(withFamily: fontName, traits: [], weight: 5, size: 12) != nil
        }
    }

    /// The list of available prover backends.
    var availableProverBackends: [String] {
        [
            "auto",
            "zenon",
            "z3",
            "isabelle",
            "smt",
            "cvc4",
            "yices"
        ]
    }

    /// The list of supported text encodings.
    var availableEncodings: [String] {
        [
            "UTF-8",
            "UTF-16",
            "UTF-16BE",
            "UTF-16LE",
            "ASCII",
            "ISO-8859-1",
            "Windows-1252",
            "macOS Roman"
        ]
    }

    // MARK: - Initialization

    private init() {
        migrateLegacyKeysIfNeeded()
    }

    /// One-shot migration: copy any values stored under legacy key names into the canonical
    /// `Keys.*` identifiers, then remove the legacy entries. Idempotent — the marker key
    /// keeps it from running on every launch.
    private func migrateLegacyKeysIfNeeded() {
        let defaults = UserDefaults.standard
        guard !defaults.bool(forKey: LegacyKeys.migrationMarker) else { return }

        for (legacy, canonical) in LegacyKeys.prover {
            guard let legacyValue = defaults.object(forKey: legacy) else { continue }
            if defaults.object(forKey: canonical) == nil {
                defaults.set(legacyValue, forKey: canonical)
            }
            defaults.removeObject(forKey: legacy)
        }

        defaults.set(true, forKey: LegacyKeys.migrationMarker)
    }

    static func normalizedModuleLibraryFolders(_ folders: [String]) -> [String] {
        var normalized: [String] = []
        var seen = Set<String>()

        for folder in folders {
            let trimmed = folder.trimmingCharacters(in: .whitespacesAndNewlines)
            guard !trimmed.isEmpty else { continue }

            let expanded = (trimmed as NSString).expandingTildeInPath
            let path = URL(fileURLWithPath: expanded).standardizedFileURL.path
            guard !seen.contains(path) else { continue }

            seen.insert(path)
            normalized.append(path)
        }

        return normalized
    }

    static func existingModuleLibraryFolders(from folders: [String]) -> [String] {
        let fileManager = FileManager.default

        return normalizedModuleLibraryFolders(folders).compactMap { path in
            var isDirectory: ObjCBool = false
            guard fileManager.fileExists(atPath: path, isDirectory: &isDirectory), isDirectory.boolValue else {
                return nil
            }
            return path
        }
    }

    // MARK: - Helper Methods

    /// Returns the path to a bundled tool within the application bundle.
    /// - Parameter named: The name of the tool file.
    /// - Returns: The full path to the bundled tool, or an empty string if not found.
    private func bundledToolPath(named name: String, subdirectories: [String] = []) -> String? {
        BinaryDiscovery.find(
            named: name,
            options: .init(
                bundleSubdirectories: subdirectories,
                systemPaths: ["/usr/local/bin", "/opt/homebrew/bin"],
                homeRelativePaths: [".tla", ".tla/provers"]
            )
        )?.path
    }

    /// Returns the resolved font to use in the editor.
    /// Falls back to Menlo if the configured font is not available.
    var resolvedFont: NSFont {
        if let font = NSFont(name: fontName, size: CGFloat(fontSize)) {
            return font
        }
        // Fallback to Menlo if configured font is unavailable
        return NSFont(name: "Menlo", size: CGFloat(fontSize))
            ?? NSFont.monospacedSystemFont(ofSize: CGFloat(fontSize), weight: .regular)
    }

    /// Returns the tab string based on current settings.
    /// Either a tab character or the configured number of spaces.
    var tabString: String {
        if insertSpacesForTabs {
            return String(repeating: " ", count: tabWidth)
        }
        return "\t"
    }

    // MARK: - Reset Methods

    /// Resets all general settings to their default values.
    func resetGeneralSettings() {
        autosaveEnabled = true
        autosaveInterval = 30
        defaultEncoding = "UTF-8"
        reopenLastDocument = true
        checkForUpdates = true
        showWelcomeOnLaunch = true
        moduleLibraryFolders = []
    }

    /// Resets all editor settings to their default values.
    func resetEditorSettings() {
        fontName = "SF Mono"
        fontSize = 13
        lineHeight = 1.4
        showLineNumbers = true
        showMinimap = false
        highlightCurrentLine = true
        tabWidth = 4
        insertSpacesForTabs = true
        wordWrap = false
        colorScheme = "Default"
        appearance = "system"
        matchBrackets = true
    }

    /// Resets all prover settings to their default values.
    func resetProverSettings() {
        tlcPath = ""
        tlapmPath = ""
        z3Path = ""
        zenonPath = ""
        isabellePath = ""
        cvc5Path = ""
        spassPath = ""
        defaultProverBackend = "auto"
        defaultProverTimeout = 30
        tlcWorkers = ProcessInfo.processInfo.activeProcessorCount
        tlcCheckpointEnabled = true
        tlcCheckpointInterval = 30
    }

    /// Resets all settings to their default values.
    func resetAllSettings() {
        resetGeneralSettings()
        resetEditorSettings()
        resetProverSettings()
    }
}

// MARK: - SwiftUI Environment Support

/// Environment key for accessing UserSettings in SwiftUI views.
private struct UserSettingsKey: EnvironmentKey {
    static let defaultValue = UserSettings.shared
}

extension EnvironmentValues {
    /// Access to the shared UserSettings instance from the SwiftUI environment.
    var userSettings: UserSettings {
        get { self[UserSettingsKey.self] }
        set { self[UserSettingsKey.self] = newValue }
    }
}
