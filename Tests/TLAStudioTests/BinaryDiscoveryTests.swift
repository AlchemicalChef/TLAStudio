import XCTest
@testable import TLAStudioApp

final class BinaryDiscoveryTests: TempDirectoryTestCase {

    private var originalLibraryFolders: [String]?

    override func setUp() async throws {
        try await super.setUp()
        originalLibraryFolders = UserDefaults.standard.stringArray(forKey: UserSettings.Keys.moduleLibraryFolders)
    }

    override func tearDown() async throws {
        if let originalLibraryFolders {
            UserDefaults.standard.set(originalLibraryFolders, forKey: UserSettings.Keys.moduleLibraryFolders)
        } else {
            UserDefaults.standard.removeObject(forKey: UserSettings.Keys.moduleLibraryFolders)
        }
        try await super.tearDown()
    }

    func testFindModuleUsesConfiguredLibraryFolders() throws {
        let libraryDirectory = tempDirectory.appendingPathComponent("library")
        try FileManager.default.createDirectory(at: libraryDirectory, withIntermediateDirectories: true)

        let moduleURL = libraryDirectory.appendingPathComponent("CustomLib.tla")
        try """
        ---- MODULE CustomLib ----
        Foo == TRUE
        ====
        """.write(to: moduleURL, atomically: true, encoding: .utf8)

        UserDefaults.standard.set([libraryDirectory.path], forKey: UserSettings.Keys.moduleLibraryFolders)

        let foundModule = BinaryDiscovery.findModule(named: "CustomLib")

        XCTAssertEqual(foundModule?.standardizedFileURL.path, moduleURL.standardizedFileURL.path)
    }

    func testConfiguredTLALibraryPropertyValuePreservesOrderAndSkipsMissingDirectories() throws {
        let firstDirectory = tempDirectory.appendingPathComponent("library-a")
        let secondDirectory = tempDirectory.appendingPathComponent("library-b")
        try FileManager.default.createDirectory(at: firstDirectory, withIntermediateDirectories: true)
        try FileManager.default.createDirectory(at: secondDirectory, withIntermediateDirectories: true)

        let missingDirectory = tempDirectory.appendingPathComponent("missing")
        UserDefaults.standard.set(
            [firstDirectory.path, missingDirectory.path, secondDirectory.path, firstDirectory.path],
            forKey: UserSettings.Keys.moduleLibraryFolders
        )

        XCTAssertEqual(
            BinaryDiscovery.configuredTLALibraryPropertyValue(),
            [firstDirectory.standardizedFileURL.path, secondDirectory.standardizedFileURL.path].joined(separator: ":")
        )
    }
}
