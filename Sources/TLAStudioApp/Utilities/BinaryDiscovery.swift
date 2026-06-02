import Foundation
import os

private let logger = Log.logger(category: "BinaryDiscovery")

/// Centralized binary discovery for TLC, TLAPM, and prover executables.
///
/// Consolidates the duplicated filesystem search logic from TLCProcessManager,
/// TLAPMProcessManager, and GraphvizProcessManager into a single utility.
enum BinaryDiscovery {

    private static let spmBundleName = "TLAStudio_TLAStudioApp.bundle"

    private static var developmentProjectRoot: URL? {
        let fileURL = URL(fileURLWithPath: #filePath)
        let root = fileURL
            .deletingLastPathComponent()
            .deletingLastPathComponent()
            .deletingLastPathComponent()
            .deletingLastPathComponent()
        guard FileManager.default.fileExists(atPath: root.appendingPathComponent("Package.swift").path) else {
            return nil
        }
        return root
    }

    static func findDevelopmentFile(relativePath: String) -> URL? {
        guard let root = developmentProjectRoot else {
            return nil
        }
        let candidate = root.appendingPathComponent(relativePath)
        return FileManager.default.fileExists(atPath: candidate.path) ? candidate : nil
    }

    static func configuredModuleLibraryDirectories() -> [URL] {
        UserSettings.existingModuleLibraryFolders(
            from: UserDefaults.standard.stringArray(forKey: UserSettings.Keys.moduleLibraryFolders) ?? []
        )
        .map { URL(fileURLWithPath: $0) }
    }

    static func configuredTLALibraryPropertyValue() -> String? {
        let paths = configuredModuleLibraryDirectories().map(\.path)
        guard !paths.isEmpty else {
            return nil
        }
        return paths.joined(separator: ":")
    }

    static func fullResourceName(for name: String, extension ext: String?) -> String {
        ext != nil ? "\(name).\(ext!)" : name
    }

    static func requiresExecutablePermission(extension ext: String?) -> Bool {
        ext?.lowercased() != "jar"
    }

    static func isUsableDiscoveredFile(_ url: URL, requiresExecutable: Bool) -> Bool {
        var isDirectory: ObjCBool = false
        guard FileManager.default.fileExists(atPath: url.path, isDirectory: &isDirectory),
              !isDirectory.boolValue else {
            return false
        }
        if requiresExecutable && !FileManager.default.isExecutableFile(atPath: url.path) {
            // F-Sdiff-recent-002: a bundled tool exists but lacks the exec bit.
            // This is almost always a packaging mistake (build-app.sh chmod,
            // archive-extract umask). Emit a notice so the discovery fallthrough
            // doesn't look like a generic "not found".
            logger.notice(
                "Bundled binary at \(url.path, privacy: .public) is not executable; falling through to PATH search"
            )
            return false
        }
        return true
    }

    static func findUsableFileInResourceRoot(
        _ root: URL,
        fullName: String,
        bundleSubdirectories: [String],
        checkNestedBundle: Bool,
        requiresExecutable: Bool
    ) -> URL? {
        var roots = [root]
        if checkNestedBundle {
            roots.append(root.appendingPathComponent(spmBundleName))
        }

        for root in roots {
            let directPath = root.appendingPathComponent(fullName)
            if isUsableDiscoveredFile(directPath, requiresExecutable: requiresExecutable) {
                return directPath
            }

            for subdir in bundleSubdirectories {
                let subdirPath = root
                    .appendingPathComponent(subdir)
                    .appendingPathComponent(fullName)
                if isUsableDiscoveredFile(subdirPath, requiresExecutable: requiresExecutable) {
                    return subdirPath
                }
            }
        }

        return nil
    }

    /// Options controlling where to search for binaries.
    struct SearchOptions {
        /// Subdirectories to check within bundle resource paths (e.g., `["bin", "Provers"]`).
        var bundleSubdirectories: [String] = []

        /// System paths to search (e.g., `["/usr/local/bin", "/opt/homebrew/bin"]`).
        var systemPaths: [String] = [
            "/usr/local/bin",
            "/opt/homebrew/bin"
        ]

        /// Paths relative to the user's home directory (e.g., `[".tla"]`).
        var homeRelativePaths: [String] = [".tla"]

        /// Whether to search in bundle resources at all.
        var searchBundles: Bool = true

        /// Whether to check the nested SPM resource bundle (TLAStudio_TLAStudioApp.bundle).
        var checkNestedBundle: Bool = true

        /// System-only search (no bundle search).
        static func systemOnly(paths: [String]) -> SearchOptions {
            SearchOptions(
                systemPaths: paths,
                homeRelativePaths: [],
                searchBundles: false,
                checkNestedBundle: false
            )
        }
    }

    /// Search for a binary by name across bundle resources, system paths, and home directory.
    ///
    /// Search order:
    /// 1. `Bundle.module` (with optional subdirectories)
    /// 2. `Bundle.main` (with optional subdirectories)
    /// 3. App bundle `Resources` directory (direct and nested bundle)
    /// 4. `Bundle.module.resourcePath` direct filesystem check
    /// 5. System paths
    /// 6. Home-relative paths
    ///
    /// - Parameters:
    ///   - name: Binary name (without extension), e.g. `"tlapm"` or `"tlc-native"`
    ///   - extension: Optional file extension, e.g. `"jar"`
    ///   - options: Search options controlling which locations to check
    /// - Returns: URL to the binary if found, nil otherwise
    static func find(
        named name: String,
        extension ext: String? = nil,
        options: SearchOptions = SearchOptions()
    ) -> URL? {
        let fullName = fullResourceName(for: name, extension: ext)
        let requiresExecutable = requiresExecutablePermission(extension: ext)

        if options.searchBundles {
            // 1. Bundle.module with subdirectories
            for subdir in options.bundleSubdirectories {
                if let url = Bundle.module.url(forResource: name, withExtension: ext, subdirectory: subdir),
                   isUsableDiscoveredFile(url, requiresExecutable: requiresExecutable) {
                    logger.debug("Found \(name) in Bundle.module/\(subdir): \(url.path)")
                    return url
                }
            }

            // Bundle.module at root
            if let url = Bundle.module.url(forResource: name, withExtension: ext),
               isUsableDiscoveredFile(url, requiresExecutable: requiresExecutable) {
                logger.debug("Found \(name) in Bundle.module: \(url.path)")
                return url
            }

            // 2. Bundle.main with subdirectories
            for subdir in options.bundleSubdirectories {
                if let url = Bundle.main.url(forResource: name, withExtension: ext, subdirectory: subdir),
                   isUsableDiscoveredFile(url, requiresExecutable: requiresExecutable) {
                    logger.debug("Found \(name) in Bundle.main/\(subdir): \(url.path)")
                    return url
                }
            }

            // Bundle.main at root
            if let url = Bundle.main.url(forResource: name, withExtension: ext),
               isUsableDiscoveredFile(url, requiresExecutable: requiresExecutable) {
                logger.debug("Found \(name) in Bundle.main: \(url.path)")
                return url
            }

            // 3. App bundle Resources directory (direct filesystem check)
            if let resourcePath = Bundle.main.resourcePath {
                let root = URL(fileURLWithPath: resourcePath)
                if let found = findUsableFileInResourceRoot(
                    root,
                    fullName: fullName,
                    bundleSubdirectories: options.bundleSubdirectories,
                    checkNestedBundle: options.checkNestedBundle,
                    requiresExecutable: requiresExecutable
                ) {
                    logger.debug("Found \(name) in resource filesystem: \(found.path)")
                    return found
                }
            }

            // 4. SPM debug bundle (next to executable)
            if options.checkNestedBundle {
                if let debugBundleRoot = Bundle.main.executableURL?.deletingLastPathComponent()
                    .appendingPathComponent(spmBundleName),
                   let found = findUsableFileInResourceRoot(
                    debugBundleRoot,
                    fullName: fullName,
                    bundleSubdirectories: options.bundleSubdirectories,
                    checkNestedBundle: false,
                    requiresExecutable: requiresExecutable
                   ) {
                    logger.debug("Found \(name) in debug bundle: \(found.path)")
                    return found
                }
            }

            // 5. Bundle.module.resourcePath direct filesystem check
            if let modulePath = Bundle.module.resourcePath {
                let root = URL(fileURLWithPath: modulePath)
                if let found = findUsableFileInResourceRoot(
                    root,
                    fullName: fullName,
                    bundleSubdirectories: options.bundleSubdirectories,
                    checkNestedBundle: false,
                    requiresExecutable: requiresExecutable
                ) {
                    logger.debug("Found \(name) in module resourcePath: \(found.path)")
                    return found
                }
            }
        }

        // 6. System paths
        for systemPath in options.systemPaths {
            let fullPath = "\(systemPath)/\(fullName)"
            let url = URL(fileURLWithPath: fullPath)
            if isUsableDiscoveredFile(url, requiresExecutable: requiresExecutable) {
                logger.debug("Found \(name) at system path: \(fullPath)")
                return url
            }
        }

        // 7. Home-relative paths
        let home = FileManager.default.homeDirectoryForCurrentUser
        for homePath in options.homeRelativePaths {
            let fullPath = home.appendingPathComponent(homePath).appendingPathComponent(fullName)
            if isUsableDiscoveredFile(fullPath, requiresExecutable: requiresExecutable) {
                logger.debug("Found \(name) at home path: \(fullPath.path)")
                return fullPath
            }
        }

        logger.warning("Binary '\(name)' not found in any location")
        return nil
    }

    /// Search for a TLA+ module file by name.
    ///
    /// Search order:
    /// 1. Same directory as the current spec file
    /// 2. Standard library locations (TLC resource bundle)
    /// 3. User-installed modules (`~/.tlaplus/`, `~/.tla/`)
    /// 4. System paths (`/usr/local/share/tla+/`)
    ///
    /// - Parameters:
    ///   - name: Module name (without `.tla` extension)
    ///   - specDirectory: The directory of the current spec file (searched first)
    /// - Returns: URL to the module file if found
    static func findModule(named name: String, specDirectory: URL? = nil) -> URL? {
        // Validate module name: TLA+ identifiers are alphanumeric + underscore.
        // Reject anything else to prevent path traversal via crafted EXTENDS lines.
        let validPattern = #"^[A-Za-z_][A-Za-z0-9_]*$"#
        guard name.range(of: validPattern, options: .regularExpression) != nil else {
            logger.warning("Rejecting invalid module name: \(name)")
            return nil
        }

        let fileName = "\(name).tla"
        let fm = FileManager.default

        // 1. Same directory as current spec
        if let specDir = specDirectory {
            let localPath = specDir.appendingPathComponent(fileName)
            if fm.fileExists(atPath: localPath.path) {
                logger.debug("Found module \(name) in spec directory: \(localPath.path)")
                return localPath
            }
        }

        // 2. User-configured library folders
        for directory in configuredModuleLibraryDirectories() {
            let libraryPath = directory.appendingPathComponent(fileName)
            if fm.fileExists(atPath: libraryPath.path) {
                logger.debug("Found module \(name) in configured library: \(libraryPath.path)")
                return libraryPath
            }
        }

        // 3. Bundle resources (standard library modules)
        if let url = Bundle.main.url(forResource: name, withExtension: "tla") {
            logger.debug("Found module \(name) in bundle: \(url.path)")
            return url
        }

        // Check known resource subdirectories used by the app bundle.
        if let resourcePath = Bundle.main.resourcePath {
            let resourceDirectories = [
                "modules",
                "StandardModules",
                "lib/tlapm/stdlib"
            ]
            for directory in resourceDirectories {
                let modulesPath = URL(fileURLWithPath: resourcePath)
                    .appendingPathComponent(directory)
                    .appendingPathComponent(fileName)
                if fm.fileExists(atPath: modulesPath.path) {
                    logger.debug("Found module \(name) in Resources/\(directory): \(modulesPath.path)")
                    return modulesPath
                }
            }
        }

        // Development checkout fallback for `swift run` / test builds.
        let developmentPaths = [
            "Resources/StandardModules/\(fileName)",
            "Scripts/tlapm/library/\(fileName)"
        ]
        for relativePath in developmentPaths {
            if let path = findDevelopmentFile(relativePath: relativePath) {
                logger.debug("Found module \(name) in development path: \(path.path)")
                return path
            }
        }

        // 4. User-installed locations
        let home = fm.homeDirectoryForCurrentUser
        let userPaths = [
            home.appendingPathComponent(".tlaplus").appendingPathComponent(fileName),
            home.appendingPathComponent(".tla").appendingPathComponent(fileName),
            home.appendingPathComponent(".tlaplus/modules").appendingPathComponent(fileName),
        ]

        for path in userPaths {
            if fm.fileExists(atPath: path.path) {
                logger.debug("Found module \(name) at user path: \(path.path)")
                return path
            }
        }

        // 5. System paths
        let systemPaths = [
            "/usr/local/share/tla+/\(fileName)",
            "/usr/local/share/tla+/modules/\(fileName)",
            "/opt/homebrew/share/tla+/\(fileName)",
            "/opt/homebrew/share/tla+/modules/\(fileName)"
        ]

        for path in systemPaths {
            if fm.fileExists(atPath: path) {
                logger.debug("Found module \(name) at system path: \(path)")
                return URL(fileURLWithPath: path)
            }
        }

        logger.debug("Module '\(name)' not found in any location")
        return nil
    }
}
