import Foundation
import os

private let logger = Log.logger(category: "BinaryDiscovery")

/// Centralized binary discovery for TLC, TLAPM, and prover executables.
///
/// Consolidates the duplicated filesystem search logic from TLCProcessManager,
/// TLAPMProcessManager, and GraphvizProcessManager into a single utility.
enum BinaryDiscovery {

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
        if options.searchBundles {
            // 1. Bundle.module with subdirectories
            for subdir in options.bundleSubdirectories {
                if let url = Bundle.module.url(forResource: name, withExtension: ext, subdirectory: subdir) {
                    logger.debug("Found \(name) in Bundle.module/\(subdir): \(url.path)")
                    return url
                }
            }

            // Bundle.module at root
            if let url = Bundle.module.url(forResource: name, withExtension: ext) {
                logger.debug("Found \(name) in Bundle.module: \(url.path)")
                return url
            }

            // 2. Bundle.main with subdirectories
            for subdir in options.bundleSubdirectories {
                if let url = Bundle.main.url(forResource: name, withExtension: ext, subdirectory: subdir) {
                    logger.debug("Found \(name) in Bundle.main/\(subdir): \(url.path)")
                    return url
                }
            }

            // Bundle.main at root
            if let url = Bundle.main.url(forResource: name, withExtension: ext) {
                logger.debug("Found \(name) in Bundle.main: \(url.path)")
                return url
            }

            // 3. App bundle Resources directory (direct filesystem check)
            if let resourcePath = Bundle.main.resourcePath {
                let fullName = ext != nil ? "\(name).\(ext!)" : name

                // Direct in Resources
                let directPath = URL(fileURLWithPath: resourcePath).appendingPathComponent(fullName)
                if FileManager.default.fileExists(atPath: directPath.path) {
                    logger.debug("Found \(name) in Resources directly: \(directPath.path)")
                    return directPath
                }

                // Check subdirectories within Resources
                for subdir in options.bundleSubdirectories {
                    let subdirPath = URL(fileURLWithPath: resourcePath)
                        .appendingPathComponent(subdir)
                        .appendingPathComponent(fullName)
                    if FileManager.default.fileExists(atPath: subdirPath.path) {
                        logger.debug("Found \(name) in Resources/\(subdir): \(subdirPath.path)")
                        return subdirPath
                    }
                }

                // Nested SPM bundle
                if options.checkNestedBundle {
                    let nestedPath = URL(fileURLWithPath: resourcePath)
                        .appendingPathComponent("TLAStudio_TLAStudioApp.bundle")
                        .appendingPathComponent(fullName)
                    if FileManager.default.fileExists(atPath: nestedPath.path) {
                        logger.debug("Found \(name) in nested bundle: \(nestedPath.path)")
                        return nestedPath
                    }
                }
            }

            // 4. SPM debug bundle (next to executable)
            if options.checkNestedBundle {
                let fullName = ext != nil ? "\(name).\(ext!)" : name
                if let debugBundlePath = Bundle.main.executableURL?.deletingLastPathComponent()
                    .appendingPathComponent("TLAStudio_TLAStudioApp.bundle")
                    .appendingPathComponent(fullName) {
                    if FileManager.default.fileExists(atPath: debugBundlePath.path) {
                        logger.debug("Found \(name) in debug bundle: \(debugBundlePath.path)")
                        return debugBundlePath
                    }
                }
            }

            // 5. Bundle.module.resourcePath direct filesystem check
            if let modulePath = Bundle.module.resourcePath {
                let fullName = ext != nil ? "\(name).\(ext!)" : name
                for subdir in options.bundleSubdirectories {
                    let path = URL(fileURLWithPath: modulePath)
                        .appendingPathComponent(subdir)
                        .appendingPathComponent(fullName)
                    if FileManager.default.fileExists(atPath: path.path) {
                        logger.debug("Found \(name) in module resourcePath/\(subdir): \(path.path)")
                        return path
                    }
                }
            }
        }

        let fullName = ext != nil ? "\(name).\(ext!)" : name

        // 6. System paths
        for systemPath in options.systemPaths {
            let fullPath = "\(systemPath)/\(fullName)"
            if FileManager.default.fileExists(atPath: fullPath) {
                logger.debug("Found \(name) at system path: \(fullPath)")
                return URL(fileURLWithPath: fullPath)
            }
        }

        // 7. Home-relative paths
        let home = FileManager.default.homeDirectoryForCurrentUser
        for homePath in options.homeRelativePaths {
            let fullPath = home.appendingPathComponent(homePath).appendingPathComponent(fullName)
            if FileManager.default.fileExists(atPath: fullPath.path) {
                logger.debug("Found \(name) at home path: \(fullPath.path)")
                return fullPath
            }
        }

        logger.warning("Binary '\(name)' not found in any location")
        return nil
    }
}
