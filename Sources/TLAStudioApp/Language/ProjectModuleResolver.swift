import Foundation

/// Lightweight project/module-resolution model for multi-file TLA+ specs.
///
/// Produces the ordered module search path handed to tools that resolve
/// `EXTENDS` / `INSTANCE` across files (currently SANY). Order matters: the
/// spec's own directory wins, then user-configured library folders (the same
/// `moduleLibraryFolders` setting TLC and TLAPM consume), then on-disk
/// standard-library locations.
enum ProjectModuleResolver {

    /// Build the ordered, de-duplicated module search path for a spec.
    ///
    /// - Parameters:
    ///   - specURL: The spec being analyzed (possibly a managed temp copy of a
    ///     dirty buffer).
    ///   - extraDirectories: High-priority extra directories — pass the document's
    ///     `originalDirectoryLibraryPaths(forToolingSpecURL:)` so a temp-buffer
    ///     spec still resolves siblings of the real on-disk file.
    static func searchPaths(for specURL: URL, extraDirectories: [URL] = []) -> [URL] {
        var ordered: [URL] = []
        var seen = Set<String>()

        func add(_ url: URL) {
            let key = url.standardizedFileURL.path
            guard !key.isEmpty, seen.insert(key).inserted else { return }
            ordered.append(url)
        }

        // 1. The spec's own directory. For a dirty buffer this is the temp
        //    container; `extraDirectories` carries the real spec directory.
        add(specURL.deletingLastPathComponent())
        extraDirectories.forEach(add)

        // 2. User-configured module library folders.
        BinaryDiscovery.configuredModuleLibraryDirectories().forEach(add)

        // 3. On-disk standard modules (the stdlib is also baked into
        //    tla2tools.jar, so these only add parity for external installs).
        BinaryDiscovery.standardModulesDirectories().forEach(add)

        return ordered
    }
}
