import SwiftUI
import SourceEditor

// MARK: - Notifications

extension Notification.Name {
    static let editorColorSchemeDidChange = Notification.Name("editorColorSchemeDidChange")
}

// MARK: - Color Scheme Definition

/// Available color schemes for the TLA+ editor
enum EditorColorScheme: String, CaseIterable, Identifiable {
    case `default` = "Default"
    case light = "Light"
    case dark = "Dark"
    case solarizedLight = "Solarized Light"
    case solarizedDark = "Solarized Dark"
    case monokai = "Monokai"

    var id: String { rawValue }

    /// Background color for the editor
    var backgroundColor: Color {
        switch self {
        case .default:
            return Color(nsColor: .textBackgroundColor)
        case .light:
            return Color(white: 1.0)
        case .dark:
            return Color(red: 0.12, green: 0.12, blue: 0.14)
        case .solarizedLight:
            return Color(red: 0.99, green: 0.96, blue: 0.89)
        case .solarizedDark:
            return Color(red: 0.0, green: 0.17, blue: 0.21)
        case .monokai:
            return Color(red: 0.15, green: 0.16, blue: 0.13)
        }
    }

    /// Default text color
    var textColor: Color {
        switch self {
        case .default:
            return Color(nsColor: .textColor)
        case .light:
            return Color(white: 0.1)
        case .dark:
            return Color(white: 0.9)
        case .solarizedLight:
            return Color(red: 0.4, green: 0.48, blue: 0.51)
        case .solarizedDark:
            return Color(red: 0.51, green: 0.58, blue: 0.59)
        case .monokai:
            return Color(red: 0.97, green: 0.97, blue: 0.95)
        }
    }

    /// Keyword color (MODULE, EXTENDS, VARIABLE, etc.)
    var keywordColor: Color {
        switch self {
        case .default:
            return Color.purple
        case .light:
            return Color(red: 0.61, green: 0.15, blue: 0.69)
        case .dark:
            return Color(red: 0.78, green: 0.56, blue: 0.89)
        case .solarizedLight, .solarizedDark:
            return Color(red: 0.52, green: 0.6, blue: 0.0)
        case .monokai:
            return Color(red: 0.98, green: 0.15, blue: 0.45)
        }
    }

    /// Operator color (==, ', etc.)
    var operatorColor: Color {
        switch self {
        case .default:
            return Color.orange
        case .light:
            return Color(red: 0.8, green: 0.4, blue: 0.0)
        case .dark:
            return Color(red: 1.0, green: 0.6, blue: 0.2)
        case .solarizedLight, .solarizedDark:
            return Color(red: 0.8, green: 0.29, blue: 0.09)
        case .monokai:
            return Color(red: 0.98, green: 0.15, blue: 0.45)
        }
    }

    /// Number color
    var numberColor: Color {
        switch self {
        case .default:
            return Color.blue
        case .light:
            return Color(red: 0.11, green: 0.0, blue: 0.81)
        case .dark:
            return Color(red: 0.51, green: 0.68, blue: 0.99)
        case .solarizedLight, .solarizedDark:
            return Color(red: 0.16, green: 0.63, blue: 0.6)
        case .monokai:
            return Color(red: 0.68, green: 0.51, blue: 1.0)
        }
    }

    /// Comment color
    var commentColor: Color {
        switch self {
        case .default:
            return Color.gray
        case .light:
            return Color(white: 0.5)
        case .dark:
            return Color(white: 0.55)
        case .solarizedLight:
            return Color(red: 0.58, green: 0.63, blue: 0.63)
        case .solarizedDark:
            return Color(red: 0.4, green: 0.48, blue: 0.51)
        case .monokai:
            return Color(red: 0.46, green: 0.44, blue: 0.37)
        }
    }

    /// Delimiter color (---- and ====)
    var delimiterColor: Color {
        switch self {
        case .default:
            return Color.green
        case .light:
            return Color(red: 0.0, green: 0.5, blue: 0.0)
        case .dark:
            return Color(red: 0.4, green: 0.8, blue: 0.4)
        case .solarizedLight, .solarizedDark:
            return Color(red: 0.71, green: 0.54, blue: 0.0)
        case .monokai:
            return Color(red: 0.9, green: 0.86, blue: 0.45)
        }
    }

    /// Identifier color (custom names)
    var identifierColor: Color {
        switch self {
        case .default:
            return Color(nsColor: .textColor)
        case .light:
            return Color(white: 0.2)
        case .dark:
            return Color(white: 0.85)
        case .solarizedLight:
            return Color(red: 0.15, green: 0.55, blue: 0.82)
        case .solarizedDark:
            return Color(red: 0.15, green: 0.55, blue: 0.82)
        case .monokai:
            return Color(red: 0.4, green: 0.85, blue: 0.94)
        }
    }

    /// Convert to SyntaxTheme for the highlighter
    var syntaxTheme: SyntaxTheme {
        switch self {
        case .default:
            return .default
        case .light:
            return .light
        case .dark:
            return .dark
        case .solarizedLight:
            return .solarizedLight
        case .solarizedDark:
            return .solarizedDark
        case .monokai:
            return .monokai
        }
    }
}

// MARK: - Monospace Font Definition

/// Available monospace fonts for the editor
enum MonospaceFont: String, CaseIterable, Identifiable {
    case sfMono = "SF Mono"
    case menlo = "Menlo"
    case monaco = "Monaco"
    case courierNew = "Courier New"
    case sourceCodePro = "Source Code Pro"
    case jetBrainsMono = "JetBrains Mono"
    case firaCode = "Fira Code"

    var id: String { rawValue }

    /// The actual font family name to use with NSFont/Font
    var fontName: String {
        switch self {
        case .sfMono:
            return "SFMono-Regular"
        case .menlo:
            return "Menlo"
        case .monaco:
            return "Monaco"
        case .courierNew:
            return "Courier New"
        case .sourceCodePro:
            return "SourceCodePro-Regular"
        case .jetBrainsMono:
            return "JetBrainsMono-Regular"
        case .firaCode:
            return "FiraCode-Regular"
        }
    }

    /// Check if the font is available on this system
    var isAvailable: Bool {
        NSFont(name: fontName, size: 12) != nil
    }

    /// Returns a fallback font if this one is not available
    func fontWithFallback(size: CGFloat) -> NSFont {
        if let font = NSFont(name: fontName, size: size) {
            return font
        }
        // Fallback to Menlo which is always available on macOS
        return NSFont(name: "Menlo", size: size) ?? NSFont.monospacedSystemFont(ofSize: size, weight: .regular)
    }
}

// MARK: - Editor Settings View

/// Settings view for editor preferences including font, display, indentation, and color scheme
struct EditorSettingsView: View {

    // MARK: - Font & Text Settings

    @AppStorage("editorFontName") private var fontName: String = MonospaceFont.sfMono.rawValue
    @AppStorage("editorFontSize") private var fontSize: Double = 13
    @AppStorage("editorLineHeight") private var lineHeight: Double = 1.4

    // MARK: - Display Settings

    @AppStorage("showLineNumbers") private var showLineNumbers: Bool = true
    @AppStorage("showMinimap") private var showMinimap: Bool = false
    @AppStorage("highlightCurrentLine") private var highlightCurrentLine: Bool = true
    @AppStorage("wordWrap") private var wordWrap: Bool = true

    // MARK: - Indentation Settings

    @AppStorage("tabWidth") private var tabWidth: Int = 4
    @AppStorage("insertSpacesForTabs") private var insertSpacesForTabs: Bool = true

    // MARK: - Appearance Settings

    @AppStorage("settings.editor.appearance") private var appearance: String = "system"
    @AppStorage("settings.editor.matchBrackets") private var matchBrackets: Bool = true

    // MARK: - Color Scheme Settings

    @AppStorage("editorColorScheme") private var colorSchemeName: String = EditorColorScheme.default.rawValue

    // MARK: - Computed Properties

    private var selectedFont: MonospaceFont {
        MonospaceFont(rawValue: fontName) ?? .sfMono
    }

    private var selectedColorScheme: EditorColorScheme {
        EditorColorScheme(rawValue: colorSchemeName) ?? .default
    }

    // MARK: - Body

    var body: some View {
        Form {
            fontAndTextSection
            displaySection
            indentationSection
            appearanceSection
            colorSchemeSection
        }
        .formStyle(.grouped)
        .frame(minWidth: 480, minHeight: 600)
    }

    // MARK: - Appearance Section

    private var appearanceSection: some View {
        Section {
            Picker("Appearance", selection: $appearance) {
                Text("System").tag("system")
                Text("Light").tag("light")
                Text("Dark").tag("dark")
            }
            .onChange(of: appearance) { _, newValue in
                applyAppearance(newValue)
            }

            Toggle("Match brackets", isOn: $matchBrackets)
        } header: {
            Text("Appearance")
        }
    }

    private func applyAppearance(_ mode: String) {
        let appearance: NSAppearance?
        switch mode {
        case "light":
            appearance = NSAppearance(named: .aqua)
        case "dark":
            appearance = NSAppearance(named: .darkAqua)
        default:
            appearance = nil // System default
        }

        // Apply to all windows
        for window in NSApp.windows {
            window.appearance = appearance
        }
    }

    // MARK: - Font & Text Section

    private var fontAndTextSection: some View {
        Section {
            // Font picker
            Picker("Font", selection: $fontName) {
                ForEach(MonospaceFont.allCases) { font in
                    HStack {
                        Text(font.rawValue)
                            .font(.custom(font.fontName, size: 13))
                        if !font.isAvailable {
                            Text("(not installed)")
                                .foregroundColor(.secondary)
                                .font(.caption)
                        }
                    }
                    .tag(font.rawValue)
                }
            }

            // Font size stepper
            HStack {
                Text("Size")
                Spacer()
                Text("\(Int(fontSize)) pt")
                    .foregroundColor(.secondary)
                    .monospacedDigit()
                Stepper("", value: $fontSize, in: 9...24, step: 1)
                    .labelsHidden()
            }

            // Line height slider
            VStack(alignment: .leading, spacing: 4) {
                HStack {
                    Text("Line Height")
                    Spacer()
                    Text(String(format: "%.1f", lineHeight))
                        .foregroundColor(.secondary)
                        .monospacedDigit()
                }
                Slider(value: $lineHeight, in: 1.0...2.0, step: 0.1)
            }

            // Font preview
            fontPreview
        } header: {
            Text("Font & Text")
        }
    }

    private var fontPreview: some View {
        VStack(alignment: .leading, spacing: 4) {
            Text("Preview")
                .font(.caption)
                .foregroundColor(.secondary)

            Text("---- MODULE Example ----")
                .font(.custom(selectedFont.fontName, size: fontSize))
                .lineSpacing((lineHeight - 1.0) * fontSize)
                .padding(8)
                .frame(maxWidth: .infinity, alignment: .leading)
                .background(Color(nsColor: .textBackgroundColor))
                .cornerRadius(6)
                .overlay(
                    RoundedRectangle(cornerRadius: 6)
                        .stroke(Color(nsColor: .separatorColor), lineWidth: 1)
                )
        }
    }

    // MARK: - Display Section

    private var displaySection: some View {
        Section {
            Toggle("Show line numbers", isOn: $showLineNumbers)
            Toggle("Show minimap", isOn: $showMinimap)
            Toggle("Highlight current line", isOn: $highlightCurrentLine)
            Toggle("Word wrap", isOn: $wordWrap)
        } header: {
            Text("Display")
        }
    }

    // MARK: - Indentation Section

    private var indentationSection: some View {
        Section {
            HStack {
                Text("Tab width")
                Spacer()
                Text("\(tabWidth) spaces")
                    .foregroundColor(.secondary)
                    .monospacedDigit()
                DiscreteValueStepper(value: $tabWidth, values: [2, 4, 8])
            }

            Toggle("Insert spaces instead of tabs", isOn: $insertSpacesForTabs)
        } header: {
            Text("Indentation")
        }
    }

    // MARK: - Color Scheme Section

    private var colorSchemeSection: some View {
        Section {
            Picker("Color scheme", selection: $colorSchemeName) {
                ForEach(EditorColorScheme.allCases) { scheme in
                    Text(scheme.rawValue)
                        .tag(scheme.rawValue)
                }
            }
            .onChange(of: colorSchemeName) { _, newValue in
                // Notify editors to update their theme
                NotificationCenter.default.post(
                    name: .editorColorSchemeDidChange,
                    object: nil,
                    userInfo: ["colorScheme": newValue]
                )
            }

            // Color scheme preview
            colorSchemePreview
        } header: {
            Text("Color Scheme")
        }
    }

    private var colorSchemePreview: some View {
        VStack(alignment: .leading, spacing: 4) {
            Text("Preview")
                .font(.caption)
                .foregroundColor(.secondary)

            VStack(alignment: .leading, spacing: 2) {
                syntaxHighlightedLine("---- MODULE Example ----", tokens: [
                    (.delimiter, "----"),
                    (.text, " "),
                    (.keyword, "MODULE"),
                    (.text, " "),
                    (.identifier, "Example"),
                    (.text, " "),
                    (.delimiter, "----")
                ])

                syntaxHighlightedLine("EXTENDS Naturals", tokens: [
                    (.keyword, "EXTENDS"),
                    (.text, " "),
                    (.identifier, "Naturals")
                ])

                syntaxHighlightedLine("VARIABLE x", tokens: [
                    (.keyword, "VARIABLE"),
                    (.text, " "),
                    (.identifier, "x")
                ])

                syntaxHighlightedLine("", tokens: [])

                syntaxHighlightedLine("Init == x = 0", tokens: [
                    (.identifier, "Init"),
                    (.text, " "),
                    (.operator, "=="),
                    (.text, " "),
                    (.identifier, "x"),
                    (.text, " "),
                    (.operator, "="),
                    (.text, " "),
                    (.number, "0")
                ])

                syntaxHighlightedLine("Next == x' = x + 1", tokens: [
                    (.identifier, "Next"),
                    (.text, " "),
                    (.operator, "=="),
                    (.text, " "),
                    (.identifier, "x"),
                    (.operator, "'"),
                    (.text, " "),
                    (.operator, "="),
                    (.text, " "),
                    (.identifier, "x"),
                    (.text, " "),
                    (.operator, "+"),
                    (.text, " "),
                    (.number, "1")
                ])

                syntaxHighlightedLine("====", tokens: [
                    (.delimiter, "====")
                ])
            }
            .font(.custom(selectedFont.fontName, size: fontSize))
            .lineSpacing((lineHeight - 1.0) * fontSize)
            .padding(8)
            .frame(maxWidth: .infinity, alignment: .leading)
            .background(selectedColorScheme.backgroundColor)
            .cornerRadius(6)
            .overlay(
                RoundedRectangle(cornerRadius: 6)
                    .stroke(Color(nsColor: .separatorColor), lineWidth: 1)
            )
        }
    }

    // MARK: - Syntax Highlighting Helpers

    private enum TokenType {
        case text
        case keyword
        case identifier
        case `operator`
        case number
        case comment
        case delimiter
    }

    private func colorForToken(_ type: TokenType) -> Color {
        let scheme = selectedColorScheme
        switch type {
        case .text:
            return scheme.textColor
        case .keyword:
            return scheme.keywordColor
        case .identifier:
            return scheme.identifierColor
        case .operator:
            return scheme.operatorColor
        case .number:
            return scheme.numberColor
        case .comment:
            return scheme.commentColor
        case .delimiter:
            return scheme.delimiterColor
        }
    }

    @ViewBuilder
    private func syntaxHighlightedLine(_ line: String, tokens: [(TokenType, String)]) -> some View {
        if tokens.isEmpty {
            Text(" ")
                .foregroundColor(selectedColorScheme.textColor)
        } else {
            HStack(spacing: 0) {
                ForEach(Array(tokens.enumerated()), id: \.offset) { _, token in
                    Text(token.1)
                        .foregroundColor(colorForToken(token.0))
                }
            }
        }
    }
}

// MARK: - Discrete Value Stepper

/// A stepper that cycles through a set of discrete values
struct DiscreteValueStepper: View {
    @Binding var value: Int
    let values: [Int]

    private var sortedValues: [Int] {
        values.sorted()
    }

    var body: some View {
        Stepper(
            "",
            onIncrement: {
                if let currentIndex = sortedValues.firstIndex(of: value),
                   currentIndex < sortedValues.count - 1 {
                    value = sortedValues[currentIndex + 1]
                }
            },
            onDecrement: {
                if let currentIndex = sortedValues.firstIndex(of: value),
                   currentIndex > 0 {
                    value = sortedValues[currentIndex - 1]
                }
            }
        )
        .labelsHidden()
    }
}

// MARK: - Preview

#Preview {
    EditorSettingsView()
        .frame(width: 500, height: 700)
}
