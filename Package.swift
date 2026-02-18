// swift-tools-version: 5.9

import PackageDescription

// Path to the TLACore Rust library
let tlaCoreLibPath = "Sources/TLACore/target/release"

let package = Package(
    name: "TLAStudio",
    platforms: [
        .macOS(.v14)
    ],
    products: [
        .executable(name: "TLAStudio", targets: ["TLAStudioApp"]),
    ],
    dependencies: [
        // Sparkle for auto-updates (optional)
        // .package(url: "https://github.com/sparkle-project/Sparkle", from: "2.0.0"),
    ],
    targets: [
        // System library for the Rust TLACore FFI
        .systemLibrary(
            name: "tla_coreFFI",
            path: "Sources/tla_coreFFI",
            pkgConfig: nil,
            providers: nil
        ),

        // Main application
        .executableTarget(
            name: "TLAStudioApp",
            dependencies: [
                "SourceEditor",
                "TLAService",
                "tla_coreFFI",
            ],
            path: "Sources/TLAStudioApp",
            exclude: [
                "Resources/Assets.xcassets",
            ],
            resources: [
                .copy("Resources/tlc-native"),
                .copy("Resources/tlc-native-fast"),
                .copy("Resources/AppIcon.icns"),
                .copy("Resources/bin"),      // TLAPM binary
                .copy("Resources/lib"),      // TLAPM stdlib
                .copy("Resources/Provers"),  // Backend provers (Z3, CVC5, Zenon, Isabelle, SPASS)
            ],
            swiftSettings: [
                .unsafeFlags(["-I", "Sources/tla_coreFFI"]),
            ],
            linkerSettings: [
                .unsafeFlags([
                    "-L", tlaCoreLibPath,
                    "-ltla_core",
                    "-Xlinker", "-rpath", "-Xlinker", "@executable_path/../Frameworks",
                ]),
            ]
        ),

        // CoreText-based source editor
        .target(
            name: "SourceEditor",
            dependencies: [],
            path: "Sources/SourceEditor"
        ),

        // XPC service for TLC/TLAPS
        .target(
            name: "TLAService",
            dependencies: [],
            path: "Sources/TLAService"
        ),

        // Tests
        .testTarget(
            name: "TLAStudioTests",
            dependencies: ["TLAStudioApp"],
            path: "Tests"
        ),
    ]
)

// Note: TLACore (Rust) is built separately via Cargo.
// Run: cd Sources/TLACore && cargo build --release
// Then: swift build
// See Scripts/build-rust-core.sh for full build automation
