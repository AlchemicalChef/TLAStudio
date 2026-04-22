import XCTest
@testable import TLAStudioApp

// MARK: - UserSettings Tests

/// Tests for UserSettings computed properties, reset methods, and available lists.
/// Note: @AppStorage persistence is not directly testable in unit tests,
/// but we can test all computed properties and reset behaviors.
final class UserSettingsTests: XCTestCase {

    var settings: UserSettings!

    override func setUp() {
        super.setUp()
        settings = UserSettings.shared
    }

    override func tearDown() {
        // Reset all settings after each test to avoid test pollution
        settings.resetAllSettings()
        settings = nil
        super.tearDown()
    }

    // MARK: - Default Values Tests

    func testDefaultGeneralSettings() {
        settings.resetGeneralSettings()

        XCTAssertTrue(settings.autosaveEnabled)
        XCTAssertEqual(settings.autosaveInterval, 30)
        XCTAssertEqual(settings.defaultEncoding, "UTF-8")
        XCTAssertTrue(settings.reopenLastDocument)
        XCTAssertTrue(settings.checkForUpdates)
        XCTAssertTrue(settings.showWelcomeOnLaunch)
        XCTAssertTrue(settings.moduleLibraryFolders.isEmpty)
    }

    func testDefaultEditorSettings() {
        settings.resetEditorSettings()

        XCTAssertEqual(settings.fontName, "SF Mono")
        XCTAssertEqual(settings.fontSize, 13)
        XCTAssertEqual(settings.lineHeight, 1.4)
        XCTAssertTrue(settings.showLineNumbers)
        XCTAssertFalse(settings.showMinimap)
        XCTAssertTrue(settings.highlightCurrentLine)
        XCTAssertEqual(settings.tabWidth, 4)
        XCTAssertTrue(settings.insertSpacesForTabs)
        XCTAssertFalse(settings.wordWrap)
        XCTAssertEqual(settings.colorScheme, "Default")
    }

    func testDefaultProverSettings() {
        settings.resetProverSettings()

        XCTAssertEqual(settings.tlcPath, "")
        XCTAssertEqual(settings.tlapmPath, "")
        XCTAssertEqual(settings.z3Path, "")
        XCTAssertEqual(settings.zenonPath, "")
        XCTAssertEqual(settings.isabellePath, "")
        XCTAssertEqual(settings.defaultProverBackend, "auto")
        XCTAssertEqual(settings.defaultProverTimeout, 30)
        // tlcWorkers defaults to activeProcessorCount, which varies by system
        XCTAssertGreaterThan(settings.tlcWorkers, 0)
        XCTAssertTrue(settings.tlcCheckpointEnabled)
        XCTAssertEqual(settings.tlcCheckpointInterval, 30)
    }

    // MARK: - Tab String Tests

    func testTabStringWithSpaces() {
        settings.insertSpacesForTabs = true
        settings.tabWidth = 4
        XCTAssertEqual(settings.tabString, "    ")
    }

    func testTabStringWithSpaces2() {
        settings.insertSpacesForTabs = true
        settings.tabWidth = 2
        XCTAssertEqual(settings.tabString, "  ")
    }

    func testTabStringWithSpaces8() {
        settings.insertSpacesForTabs = true
        settings.tabWidth = 8
        XCTAssertEqual(settings.tabString, "        ")
    }

    func testTabStringWithActualTab() {
        settings.insertSpacesForTabs = false
        settings.tabWidth = 4 // Should be ignored
        XCTAssertEqual(settings.tabString, "\t")
    }

    // MARK: - Resolved Path Tests

    func testResolvedTLCPathCustom() {
        settings.tlcPath = "/custom/path/tlc.jar"
        XCTAssertEqual(settings.resolvedTLCPath, "/custom/path/tlc.jar")
    }

    func testResolvedTLCPathDefault() {
        settings.tlcPath = ""
        // When no custom path, returns bundled path or empty string
        // In test context, bundled tools may resolve from the checked-out repo.
        let resolved = settings.resolvedTLCPath
        XCTAssertTrue(
            resolved.isEmpty ||
            resolved.contains("tlc-native") ||
            resolved.contains("tlc-native-fast")
        )
    }

    func testResolvedTLAPMPathCustom() {
        settings.tlapmPath = "/custom/path/tlapm"
        XCTAssertEqual(settings.resolvedTLAPMPath, "/custom/path/tlapm")
    }

    func testResolvedZ3PathCustom() {
        settings.z3Path = "/custom/path/z3"
        XCTAssertEqual(settings.resolvedZ3Path, "/custom/path/z3")
    }

    func testResolvedZenonPathCustom() {
        settings.zenonPath = "/custom/path/zenon"
        XCTAssertEqual(settings.resolvedZenonPath, "/custom/path/zenon")
    }

    // MARK: - Resolved Font Tests

    func testResolvedFontDefaultMonospace() {
        settings.fontName = "SF Mono"
        settings.fontSize = 13
        let font = settings.resolvedFont
        XCTAssertNotNil(font)
        XCTAssertEqual(font.pointSize, 13)
    }

    func testResolvedFontCustomSize() {
        settings.fontName = "Menlo"
        settings.fontSize = 16
        let font = settings.resolvedFont
        XCTAssertNotNil(font)
        XCTAssertEqual(font.pointSize, 16)
    }

    func testResolvedFontFallback() {
        settings.fontName = "NonExistentFont12345"
        settings.fontSize = 14
        let font = settings.resolvedFont
        XCTAssertNotNil(font)
        XCTAssertEqual(font.pointSize, 14)
        // Should fall back to Menlo or system monospace
    }

    // MARK: - Available Lists Tests

    func testAvailableColorSchemesNotEmpty() {
        let schemes = settings.availableColorSchemes
        XCTAssertFalse(schemes.isEmpty)
        XCTAssertTrue(schemes.contains("Default"))
    }

    func testAvailableColorSchemesContainsExpected() {
        let schemes = settings.availableColorSchemes
        XCTAssertTrue(schemes.contains("Solarized Light"))
        XCTAssertTrue(schemes.contains("Solarized Dark"))
        XCTAssertTrue(schemes.contains("Monokai"))
        XCTAssertTrue(schemes.contains("Dracula"))
        XCTAssertTrue(schemes.contains("GitHub Light"))
        XCTAssertTrue(schemes.contains("GitHub Dark"))
    }

    func testAvailableFontsNotEmpty() {
        let fonts = settings.availableFonts
        XCTAssertFalse(fonts.isEmpty)
        // Should contain at least Menlo, which is always available on macOS
        XCTAssertTrue(fonts.contains("Menlo"))
    }

    func testAvailableProverBackendsNotEmpty() {
        let backends = settings.availableProverBackends
        XCTAssertFalse(backends.isEmpty)
        XCTAssertTrue(backends.contains("auto"))
        XCTAssertTrue(backends.contains("zenon"))
        XCTAssertTrue(backends.contains("z3"))
        XCTAssertTrue(backends.contains("isabelle"))
    }

    func testAvailableEncodingsNotEmpty() {
        let encodings = settings.availableEncodings
        XCTAssertFalse(encodings.isEmpty)
        XCTAssertTrue(encodings.contains("UTF-8"))
        XCTAssertTrue(encodings.contains("ASCII"))
        XCTAssertTrue(encodings.contains("UTF-16"))
    }

    // MARK: - Reset Methods Tests

    func testResetGeneralSettings() {
        // Modify settings
        settings.autosaveEnabled = false
        settings.autosaveInterval = 60
        settings.defaultEncoding = "ASCII"
        settings.moduleLibraryFolders = ["/tmp/library"]

        // Reset
        settings.resetGeneralSettings()

        // Verify defaults restored
        XCTAssertTrue(settings.autosaveEnabled)
        XCTAssertEqual(settings.autosaveInterval, 30)
        XCTAssertEqual(settings.defaultEncoding, "UTF-8")
        XCTAssertTrue(settings.moduleLibraryFolders.isEmpty)
    }

    func testModuleLibraryFoldersNormalizedAndDeduplicated() {
        let libraryPath = FileManager.default.temporaryDirectory
            .appendingPathComponent("UserSettingsTests-Library")
            .path

        settings.moduleLibraryFolders = [
            " \(libraryPath) ",
            libraryPath,
            ""
        ]

        XCTAssertEqual(
            settings.moduleLibraryFolders,
            [URL(fileURLWithPath: libraryPath).standardizedFileURL.path]
        )
    }

    func testResolvedModuleLibraryFoldersIgnoresMissingDirectories() throws {
        let existingDirectory = FileManager.default.temporaryDirectory
            .appendingPathComponent("UserSettingsTests-\(UUID().uuidString)")
        try FileManager.default.createDirectory(at: existingDirectory, withIntermediateDirectories: true)
        defer { try? FileManager.default.removeItem(at: existingDirectory) }

        let missingDirectory = existingDirectory.appendingPathComponent("missing")
        settings.moduleLibraryFolders = [existingDirectory.path, missingDirectory.path]

        XCTAssertEqual(settings.resolvedModuleLibraryFolders, [existingDirectory.standardizedFileURL.path])
    }

    func testResetEditorSettings() {
        // Modify settings
        settings.fontName = "Monaco"
        settings.fontSize = 20
        settings.tabWidth = 8
        settings.insertSpacesForTabs = false

        // Reset
        settings.resetEditorSettings()

        // Verify defaults restored
        XCTAssertEqual(settings.fontName, "SF Mono")
        XCTAssertEqual(settings.fontSize, 13)
        XCTAssertEqual(settings.tabWidth, 4)
        XCTAssertTrue(settings.insertSpacesForTabs)
    }

    func testResetProverSettings() {
        // Modify settings
        settings.tlcPath = "/custom/tlc"
        settings.defaultProverTimeout = 120
        settings.defaultProverBackend = "z3"
        settings.tlcCheckpointEnabled = false

        // Reset
        settings.resetProverSettings()

        // Verify defaults restored
        XCTAssertEqual(settings.tlcPath, "")
        XCTAssertEqual(settings.defaultProverTimeout, 30)
        XCTAssertEqual(settings.defaultProverBackend, "auto")
        XCTAssertTrue(settings.tlcCheckpointEnabled)
    }

    func testResetAllSettings() {
        // Modify settings in each category
        settings.autosaveEnabled = false
        settings.fontName = "Monaco"
        settings.tlcPath = "/custom/tlc"

        // Reset all
        settings.resetAllSettings()

        // Verify all defaults restored
        XCTAssertTrue(settings.autosaveEnabled)
        XCTAssertEqual(settings.fontName, "SF Mono")
        XCTAssertEqual(settings.tlcPath, "")
    }

    // MARK: - Settings Modification Tests

    func testModifyAutosaveInterval() {
        settings.autosaveInterval = 60
        XCTAssertEqual(settings.autosaveInterval, 60)

        settings.autosaveInterval = 15
        XCTAssertEqual(settings.autosaveInterval, 15)
    }

    func testModifyFontSize() {
        settings.fontSize = 18
        XCTAssertEqual(settings.fontSize, 18)

        settings.fontSize = 10
        XCTAssertEqual(settings.fontSize, 10)
    }

    func testModifyLineHeight() {
        settings.lineHeight = 1.8
        XCTAssertEqual(settings.lineHeight, 1.8, accuracy: 0.01)

        settings.lineHeight = 1.2
        XCTAssertEqual(settings.lineHeight, 1.2, accuracy: 0.01)
    }

    func testModifyColorScheme() {
        settings.colorScheme = "Monokai"
        XCTAssertEqual(settings.colorScheme, "Monokai")

        settings.colorScheme = "Dracula"
        XCTAssertEqual(settings.colorScheme, "Dracula")
    }

    func testModifyTLCWorkers() {
        settings.tlcWorkers = 4
        XCTAssertEqual(settings.tlcWorkers, 4)

        settings.tlcWorkers = 8
        XCTAssertEqual(settings.tlcWorkers, 8)
    }

    func testModifyCheckpointInterval() {
        settings.tlcCheckpointInterval = 60
        XCTAssertEqual(settings.tlcCheckpointInterval, 60)

        settings.tlcCheckpointInterval = 15
        XCTAssertEqual(settings.tlcCheckpointInterval, 15)
    }

    // MARK: - Boolean Toggle Tests

    func testToggleAutosave() {
        let original = settings.autosaveEnabled
        settings.autosaveEnabled = !original
        XCTAssertEqual(settings.autosaveEnabled, !original)
    }

    func testToggleShowLineNumbers() {
        let original = settings.showLineNumbers
        settings.showLineNumbers = !original
        XCTAssertEqual(settings.showLineNumbers, !original)
    }

    func testToggleShowMinimap() {
        let original = settings.showMinimap
        settings.showMinimap = !original
        XCTAssertEqual(settings.showMinimap, !original)
    }

    func testToggleHighlightCurrentLine() {
        let original = settings.highlightCurrentLine
        settings.highlightCurrentLine = !original
        XCTAssertEqual(settings.highlightCurrentLine, !original)
    }

    func testToggleWordWrap() {
        let original = settings.wordWrap
        settings.wordWrap = !original
        XCTAssertEqual(settings.wordWrap, !original)
    }
}
