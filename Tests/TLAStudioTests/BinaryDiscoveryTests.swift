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

    func testResourceFilesystemSearchFindsNestedBundleSubdirectoryExecutables() throws {
        let nestedBin = tempDirectory
            .appendingPathComponent("TLAStudio_TLAStudioApp.bundle")
            .appendingPathComponent("bin")
        try FileManager.default.createDirectory(at: nestedBin, withIntermediateDirectories: true)

        let tlapm = nestedBin.appendingPathComponent("tlapm")
        try makeFile(tlapm, executable: true)

        let found = BinaryDiscovery.findUsableFileInResourceRoot(
            tempDirectory,
            fullName: "tlapm",
            bundleSubdirectories: ["bin", "Provers"],
            checkNestedBundle: true,
            requiresExecutable: true
        )

        XCTAssertEqual(found?.standardizedFileURL.path, tlapm.standardizedFileURL.path)
    }

    func testResourceFilesystemSearchSkipsNonExecutableTools() throws {
        let direct = tempDirectory.appendingPathComponent("tlapm")
        try makeFile(direct, executable: false)

        let bin = tempDirectory.appendingPathComponent("bin")
        try FileManager.default.createDirectory(at: bin, withIntermediateDirectories: true)
        let executable = bin.appendingPathComponent("tlapm")
        try makeFile(executable, executable: true)

        let found = BinaryDiscovery.findUsableFileInResourceRoot(
            tempDirectory,
            fullName: "tlapm",
            bundleSubdirectories: ["bin"],
            checkNestedBundle: false,
            requiresExecutable: true
        )

        XCTAssertEqual(found?.standardizedFileURL.path, executable.standardizedFileURL.path)
    }

    func testResourceFilesystemSearchAllowsNonExecutableJarResources() throws {
        let jar = tempDirectory.appendingPathComponent("tla2tools.jar")
        try makeFile(jar, executable: false)

        let found = BinaryDiscovery.findUsableFileInResourceRoot(
            tempDirectory,
            fullName: "tla2tools.jar",
            bundleSubdirectories: [],
            checkNestedBundle: false,
            requiresExecutable: false
        )

        XCTAssertEqual(found?.standardizedFileURL.path, jar.standardizedFileURL.path)
    }

    private func makeFile(_ url: URL, executable: Bool) throws {
        try "#!/bin/sh\nexit 0\n".write(to: url, atomically: true, encoding: .utf8)
        try FileManager.default.setAttributes(
            [.posixPermissions: executable ? 0o755 : 0o644],
            ofItemAtPath: url.path
        )
    }
}
