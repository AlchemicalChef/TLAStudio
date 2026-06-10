import Foundation
import os

private let logger = Log.logger(category: "BinaryDiscovery")

/// Centralized binary discovery for TLC, TLAPM, and prover executables.
///
/// Consolidates the duplicated filesystem search logic from TLCProcessManager,
/// TLAPMProcessManager, and GraphvizProcessManager into a single utility.
enum BinaryDiscovery {

    private static let spmBundleName = "TLAStudio_TLAStudioApp.bundle"

    /// Safe replacement for SPM's generated `Bundle.module`.
    ///
    /// SPM's `Bundle.module` accessor only checks two paths — `Bundle.main.bundleURL`
    /// (the `.app` root, *not* `Contents/Resources/`) and a build-time-absolute
    /// `.build/.../<config>/` path — and calls `fatalError` if neither resolves. In a
    /// distributed `.app`, `build-app.sh` stages the SPM bundle under
    /// `Contents/Resources/`, so *both* of those paths miss and merely *touching*
    /// `Bundle.module` traps the process (SIGTRAP). This never reproduces on a developer
    /// machine because the hardcoded `.build/` path still exists there.
    ///
    /// This accessor probes the locations where the bundle actually lives and returns
    /// `nil` instead of trapping, so callers can fall through to other search paths.
    static let resourceBundle: Bundle? = {
        let fm = FileManager.default
        var candidates: [URL] = []
        if let resources = Bundle.main.resourceURL {
            // Contents/Resources/TLAStudio_TLAStudioApp.bundle (where build-app.sh stages it)
            candidates.append(resources.appendingPathComponent(spmBundleName))
            // Contents/Resources itself (flat resource layout)
            candidates.append(resources)
        }
        if let execDir = Bundle.main.executableURL?.deletingLastPathComponent() {
            // Raw `swift build` output: bundle sits next to the executable.
            candidates.append(execDir.appendingPathComponent(spmBundleName))
        }
        // The .app root — the first path SPM's own accessor checks.
        candidates.append(Bundle.main.bundleURL.appendingPathComponent(spmBundleName))

        for url in candidates where fm.fileExists(atPath: url.path) {
            if let bundle = Bundle(url: url) {
                return bundle
            }
        }
        return nil
    }()

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
            // 1. SPM resource bundle (safe accessor; never traps like Bundle.module)
            if let moduleBundle = resourceBundle {
                for subdir in options.bundleSubdirectories {
                    if let url = moduleBundle.url(forResource: name, withExtension: ext, subdirectory: subdir),
                       isUsableDiscoveredFile(url, requiresExecutable: requiresExecutable) {
                        logger.debug("Found \(name) in resourceBundle/\(subdir): \(url.path)")
                        return url
                    }
                }

                // resource bundle at root
                if let url = moduleBundle.url(forResource: name, withExtension: ext),
                   isUsableDiscoveredFile(url, requiresExecutable: requiresExecutable) {
                    logger.debug("Found \(name) in resourceBundle: \(url.path)")
                    return url
                }
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

            // 5. SPM resource bundle resourcePath direct filesystem check
            if let modulePath = resourceBundle?.resourcePath {
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

    /// On-disk directories that may contain TLA+ standard-library (or user-installed)
    /// modules, for tools that take a module *search path* rather than a per-file lookup
    /// (e.g. SANY's `TLA-Library` property).
    ///
    /// Mirrors the candidate roots `findModule` probes per file. Note the standard
    /// library is also baked into `tla2tools.jar`, so `EXTENDS Naturals` resolves even
    /// when this list is empty — these directories only add tooling parity for modules
    /// installed outside the jar.
    static func standardModulesDirectories() -> [URL] {
        let fm = FileManager.default
        var candidates: [URL] = []

        if let resourcePath = Bundle.main.resourcePath {
            let root = URL(fileURLWithPath: resourcePath)
            for directory in ["modules", "StandardModules", "lib/tlapm/stdlib"] {
                candidates.append(root.appendingPathComponent(directory))
            }
        }

        // Development checkout fallback for `swift run` / test builds.
        if let root = developmentProjectRoot {
            candidates.append(root.appendingPathComponent("Resources/StandardModules"))
            candidates.append(root.appendingPathComponent("Scripts/tlapm/library"))
        }

        let home = fm.homeDirectoryForCurrentUser
        candidates.append(home.appendingPathComponent(".tlaplus"))
        candidates.append(home.appendingPathComponent(".tla"))
        candidates.append(home.appendingPathComponent(".tlaplus/modules"))

        candidates.append(contentsOf: [
            "/usr/local/share/tla+",
            "/usr/local/share/tla+/modules",
            "/opt/homebrew/share/tla+",
            "/opt/homebrew/share/tla+/modules"
        ].map { URL(fileURLWithPath: $0) })

        return candidates.filter { url in
            var isDirectory: ObjCBool = false
            return fm.fileExists(atPath: url.path, isDirectory: &isDirectory) && isDirectory.boolValue
        }
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
