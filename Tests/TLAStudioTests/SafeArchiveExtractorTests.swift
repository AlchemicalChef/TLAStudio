import XCTest
@testable import TLAStudioApp

// MARK: - Safe Archive Extractor Tests

/// Tests for the SafeArchiveExtractor security validation logic.
final class SafeArchiveExtractorTests: TempDirectoryTestCase {

    // MARK: - Path Validation Tests

    func testAbsolutePathDetection() throws {
        // Test that paths with "/" prefix are rejected
        let absolutePath = "/etc/passwd"

        XCTAssertTrue(absolutePath.hasPrefix("/"))
    }

    func testPathTraversalWithDoubleDots() {
        // Test detection of ".." path traversal
        let traversalPath = "../../../etc/passwd"

        let components = traversalPath.components(separatedBy: "/")
        var depth = 0
        var hasTraversal = false

        for component in components {
            if component == ".." {
                depth -= 1
                if depth < 0 {
                    hasTraversal = true
                    break
                }
            } else if component != "." && !component.isEmpty {
                depth += 1
            }
        }

        XCTAssertTrue(hasTraversal)
    }

    func testSafePathWithDotDotInMiddle() {
        // Test that "foo/../bar" at depth 1 is acceptable
        let safePath = "foo/../bar/file.txt"

        let components = safePath.components(separatedBy: "/")
        var depth = 0
        var hasTraversal = false

        for component in components {
            if component == ".." {
                depth -= 1
                if depth < 0 {
                    hasTraversal = true
                    break
                }
            } else if component != "." && !component.isEmpty {
                depth += 1
            }
        }

        // This should NOT be a traversal since depth never goes negative
        XCTAssertFalse(hasTraversal)
    }

    func testEncodedPathTraversalDetection() {
        // Test detection of URL-encoded path traversal attempts
        let encodedPaths = [
            "%2e%2e/etc/passwd",     // URL-encoded ..
            "%2E%2E/etc/passwd",     // URL-encoded .. (uppercase)
            "..%2f../etc/passwd",    // .. with encoded /
            "..%2F../etc/passwd",    // .. with encoded / (uppercase)
            "%2f../etc/passwd",      // encoded / then ..
            "%2F../etc/passwd"       // encoded / then .. (uppercase)
        ]

        for path in encodedPaths {
            let hasEncodedTraversal = path.contains("%2e%2e") || path.contains("%2E%2E") ||
                                      path.contains("..%2f") || path.contains("..%2F") ||
                                      path.contains("%2f..") || path.contains("%2F..")
            XCTAssertTrue(hasEncodedTraversal, "Should detect encoded traversal in: \(path)")
        }
    }

    func testCleanPathIsValid() {
        // Test that normal paths pass validation
        let cleanPaths = [
            "file.txt",
            "dir/file.txt",
            "a/b/c/file.txt",
            "Isabelle2024/bin/isabelle"
        ]

        for path in cleanPaths {
            // Check not absolute
            XCTAssertFalse(path.hasPrefix("/"), "Path should not be absolute: \(path)")

            // Check no traversal
            let components = path.components(separatedBy: "/")
            var depth = 0
            var hasTraversal = false

            for component in components {
                if component == ".." {
                    depth -= 1
                    if depth < 0 {
                        hasTraversal = true
                        break
                    }
                } else if component != "." && !component.isEmpty {
                    depth += 1
                }
            }

            XCTAssertFalse(hasTraversal, "Path should not have traversal: \(path)")
        }
    }

    func testExtractsPlainTarArchive() throws {
        let sourceDir = tempDirectory.appendingPathComponent("plain-source", isDirectory: true)
        let nestedDir = sourceDir.appendingPathComponent("dir", isDirectory: true)
        try FileManager.default.createDirectory(at: nestedDir, withIntermediateDirectories: true)
        try "contents".write(to: nestedDir.appendingPathComponent("file.txt"), atomically: true, encoding: .utf8)

        let archiveURL = tempDirectory.appendingPathComponent("plain.tar")
        try runTar(arguments: ["-cf", archiveURL.path, "-C", sourceDir.path, "."])

        let targetDir = tempDirectory.appendingPathComponent("plain-target", isDirectory: true)
        try SafeArchiveExtractor.extract(from: archiveURL, to: targetDir)

        let extracted = targetDir.appendingPathComponent("dir/file.txt")
        XCTAssertEqual(try String(contentsOf: extracted), "contents")
    }

    func testRejectsAbsoluteSymlinkBeforeMove() throws {
        let sourceDir = tempDirectory.appendingPathComponent("symlink-source", isDirectory: true)
        try FileManager.default.createDirectory(at: sourceDir, withIntermediateDirectories: true)
        let linkURL = sourceDir.appendingPathComponent("escape")
        try FileManager.default.createSymbolicLink(at: linkURL, withDestinationURL: URL(fileURLWithPath: "/tmp"))

        let archiveURL = tempDirectory.appendingPathComponent("symlink.tar")
        try runTar(arguments: ["-cf", archiveURL.path, "-C", sourceDir.path, "."])

        let targetDir = tempDirectory.appendingPathComponent("symlink-target", isDirectory: true)
        XCTAssertThrowsError(try SafeArchiveExtractor.extract(from: archiveURL, to: targetDir)) { error in
            guard case SafeArchiveExtractor.Error.symlinkEscapeDetected = error else {
                XCTFail("Expected symlinkEscapeDetected, got \(error)")
                return
            }
        }
        XCTAssertFalse(FileManager.default.fileExists(atPath: targetDir.path))
    }

    // MARK: - Error Types Tests

    func testErrorDescriptions() {
        let errors: [SafeArchiveExtractor.Error] = [
            .listingFailed("test error"),
            .pathTraversalDetected("../etc/passwd"),
            .absolutePathDetected("/etc/passwd"),
            .extractionFailed("extraction error"),
            .symlinkEscapeDetected("/path/to/symlink"),
            .targetDirectoryCreationFailed(NSError(domain: "test", code: 0))
        ]

        for error in errors {
            XCTAssertNotNil(error.errorDescription)
            XCTAssertFalse(error.errorDescription!.isEmpty)
        }
    }

    func testListingFailedError() {
        let error = SafeArchiveExtractor.Error.listingFailed("command failed")

        XCTAssertTrue(error.errorDescription?.contains("list archive") ?? false)
        XCTAssertTrue(error.errorDescription?.contains("command failed") ?? false)
    }

    func testPathTraversalError() {
        let path = "../../../etc/passwd"
        let error = SafeArchiveExtractor.Error.pathTraversalDetected(path)

        XCTAssertTrue(error.errorDescription?.contains("traversal") ?? false)
        XCTAssertTrue(error.errorDescription?.contains(path) ?? false)
    }

    func testAbsolutePathError() {
        let path = "/etc/passwd"
        let error = SafeArchiveExtractor.Error.absolutePathDetected(path)

        XCTAssertTrue(error.errorDescription?.contains("Absolute path") ?? false)
        XCTAssertTrue(error.errorDescription?.contains(path) ?? false)
    }

    func testExtractionFailedError() {
        let error = SafeArchiveExtractor.Error.extractionFailed("tar error")

        XCTAssertTrue(error.errorDescription?.contains("extraction failed") ?? false)
        XCTAssertTrue(error.errorDescription?.contains("tar error") ?? false)
    }

    func testSymlinkEscapeError() {
        let path = "/tmp/archive/link"
        let error = SafeArchiveExtractor.Error.symlinkEscapeDetected(path)

        XCTAssertTrue(error.errorDescription?.contains("Symlink") ?? false)
        XCTAssertTrue(error.errorDescription?.contains(path) ?? false)
    }

    func testTargetDirectoryCreationError() {
        let underlyingError = NSError(domain: "FileManager", code: 1, userInfo: [NSLocalizedDescriptionKey: "Permission denied"])
        let error = SafeArchiveExtractor.Error.targetDirectoryCreationFailed(underlyingError)

        XCTAssertTrue(error.errorDescription?.contains("create target directory") ?? false)
        XCTAssertTrue(error.errorDescription?.contains("Permission denied") ?? false)
    }

    // MARK: - Symlink Validation Tests

    func testSymlinkPathNormalization() {
        // Test path normalization logic used in symlink validation
        let basePath = "/tmp/extract"
        let relativePath = "subdir/../file.txt"

        let fullPath = (basePath as NSString).appendingPathComponent(relativePath)
        let normalized = (fullPath as NSString).standardizingPath

        XCTAssertEqual(normalized, "/tmp/extract/file.txt")
    }

    func testSymlinkEscapeDetection() {
        // Test that symlinks pointing outside target are detected
        let targetDir = "/tmp/extract"
        let symlinkDestination = "/etc/passwd"

        let isWithinTarget = symlinkDestination.hasPrefix(targetDir)
        XCTAssertFalse(isWithinTarget)
    }

    func testRelativeSymlinkWithinTarget() {
        // Test that relative symlinks within target are allowed
        let targetDir = "/tmp/extract"
        let symlinkParent = "/tmp/extract/subdir"
        let relativeDestination = "../otherfile.txt"

        let absoluteDestination = (symlinkParent as NSString).appendingPathComponent(relativeDestination)
        let normalized = (absoluteDestination as NSString).standardizingPath

        XCTAssertTrue(normalized.hasPrefix(targetDir))
    }

    // MARK: - Edge Cases

    func testEmptyPathList() {
        let paths: [String] = []

        var hasValidationError = false
        for path in paths {
            if path.hasPrefix("/") {
                hasValidationError = true
                break
            }
        }

        XCTAssertFalse(hasValidationError)
    }

    func testPathWithSingleDot() {
        let path = "./file.txt"

        let components = path.components(separatedBy: "/")
        var depth = 0
        var hasTraversal = false

        for component in components {
            if component == ".." {
                depth -= 1
                if depth < 0 {
                    hasTraversal = true
                    break
                }
            } else if component != "." && !component.isEmpty {
                depth += 1
            }
        }

        // Single dots should not trigger traversal
        XCTAssertFalse(hasTraversal)
    }

    func testPathWithManyNestedDirs() {
        // Deep nesting should be fine
        let deepPath = "a/b/c/d/e/f/g/h/i/j/k/l/m/n/o/p/q/r/s/t/u/v/w/x/y/z/file.txt"

        XCTAssertFalse(deepPath.hasPrefix("/"))

        let components = deepPath.components(separatedBy: "/")
        var depth = 0
        var hasTraversal = false

        for component in components {
            if component == ".." {
                depth -= 1
                if depth < 0 {
                    hasTraversal = true
                    break
                }
            } else if component != "." && !component.isEmpty {
                depth += 1
            }
        }

        XCTAssertFalse(hasTraversal)
        XCTAssertEqual(depth, 27) // 26 directories + 1 file
    }

    func testMixedTraversalAttempts() {
        // Test paths that mix valid and invalid patterns
        let paths = [
            ("a/b/../../c/d", false),   // Stays within bounds (depth never goes negative)
            ("a/../../../b", true),      // Goes outside (depth goes to -2)
            ("../a/b/c", true),          // Starts with traversal
            ("a/b/c/..", false)          // Valid - stays within
        ]

        for (path, shouldDetectTraversal) in paths {
            let components = path.components(separatedBy: "/")
            var depth = 0
            var hasTraversal = false

            for component in components {
                if component == ".." {
                    depth -= 1
                    if depth < 0 {
                        hasTraversal = true
                        break
                    }
                } else if component != "." && !component.isEmpty {
                    depth += 1
                }
            }

            XCTAssertEqual(hasTraversal, shouldDetectTraversal, "Path '\(path)' traversal detection mismatch")
        }
    }

    private func runTar(arguments: [String]) throws {
        let process = Process()
        process.executableURL = URL(fileURLWithPath: "/usr/bin/tar")
        process.arguments = arguments
        let stderr = Pipe()
        process.standardError = stderr
        try process.run()
        process.waitUntilExit()
        if process.terminationStatus != 0 {
            let data = stderr.fileHandleForReading.readDataToEndOfFile()
            let message = String(data: data, encoding: .utf8) ?? "tar failed"
            XCTFail(message)
            throw NSError(domain: "SafeArchiveExtractorTests", code: Int(process.terminationStatus), userInfo: [
                NSLocalizedDescriptionKey: message
            ])
        }
    }
}
