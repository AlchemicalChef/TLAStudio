# Document Management Architecture

## Overview

TLA+ Studio uses macOS's `NSDocument` architecture for complete file lifecycle management with native behaviors for New, Open, Save, Save As, Close, auto-save, and version history.

## File Types

| Extension | UTI | Description |
|-----------|-----|-------------|
| `.tla` | `com.tlaplus.specification` | TLA+ specification |
| `.cfg` | `com.tlaplus.configuration` | TLC model configuration |

## Info.plist Configuration

```xml
<key>CFBundleDocumentTypes</key>
<array>
    <dict>
        <key>CFBundleTypeName</key>
        <string>TLA+ Specification</string>
        <key>CFBundleTypeRole</key>
        <string>Editor</string>
        <key>LSHandlerRank</key>
        <string>Owner</string>
        <key>LSItemContentTypes</key>
        <array>
            <string>com.tlaplus.specification</string>
        </array>
        <key>NSDocumentClass</key>
        <string>$(PRODUCT_MODULE_NAME).TLADocument</string>
    </dict>
    <dict>
        <key>CFBundleTypeName</key>
        <string>TLA+ Configuration</string>
        <key>CFBundleTypeRole</key>
        <string>Editor</string>
        <key>LSHandlerRank</key>
        <string>Owner</string>
        <key>LSItemContentTypes</key>
        <array>
            <string>com.tlaplus.configuration</string>
        </array>
        <key>NSDocumentClass</key>
        <string>$(PRODUCT_MODULE_NAME).TLAConfigDocument</string>
    </dict>
</array>

<key>UTImportedTypeDeclarations</key>
<array>
    <dict>
        <key>UTTypeIdentifier</key>
        <string>com.tlaplus.specification</string>
        <key>UTTypeDescription</key>
        <string>TLA+ Specification</string>
        <key>UTTypeConformsTo</key>
        <array>
            <string>public.plain-text</string>
            <string>public.source-code</string>
        </array>
        <key>UTTypeTagSpecification</key>
        <dict>
            <key>public.filename-extension</key>
            <array><string>tla</string></array>
        </dict>
    </dict>
</array>
```

## Key Classes

### TLADocument

Primary document class for `.tla` files.

**Responsibilities:**
- Store document content as String
- Handle encoding detection (UTF-8, Windows-1252)
- Preserve line endings (LF, CRLF, CR)
- Trigger parsing on content change
- Coordinate with editor view

**NSDocument Overrides:**
```swift
override class var autosavesInPlace: Bool { true }
override class var autosavesDrafts: Bool { true }
override class var preservesVersions: Bool { true }
```

**File Operations:**
- `read(from:ofType:)` — Load file, detect encoding
- `data(ofType:)` — Encode content for save
- `makeWindowControllers()` — Create window with editor

### TLADocumentController

Custom document controller for TLA+-specific behaviors.

**Responsibilities:**
- Handle "New from Template" menu
- Filter open panel to `.tla`/`.cfg` files
- Manage recent documents

### TLAWindowController

Window controller binding document to editor.

**Responsibilities:**
- Set up toolbar (Run, Stop, Prove buttons)
- Bind window title to document name
- Bind dirty indicator to `hasUnautosavedChanges`

## File Operation Flows

### New (⌘N)
```
User: ⌘N
  → TLADocumentController.newDocument(_:)
  → TLADocument.init()
  → content = template
  → makeWindowControllers()
  → Window displayed with "Untitled"
```

### Open (⌘O)
```
User: ⌘O
  → NSOpenPanel (filtered to .tla/.cfg)
  → User selects file
  → TLADocumentController.openDocument(withContentsOf:)
  → TLADocument.read(from:ofType:)
  → Detect encoding, normalize line endings
  → Parse content
  → makeWindowControllers()
  → Window displayed with filename
```

### Save (⌘S)
```
User: ⌘S
  → NSDocument.save(_:)
  → Has fileURL? 
    → NO: Show NSSavePanel
    → YES: Continue
  → TLADocument.data(ofType:)
  → Apply line ending style
  → Write to disk
  → Clear dirty flag
```

### Save As (⇧⌘S)
```
User: ⇧⌘S
  → NSDocument.saveAs(_:)
  → NSSavePanel
  → User chooses location
  → TLADocument.write(to:ofType:for:)
  → Update MODULE name to match filename
  → Write to disk
```

### Close (⌘W)
```
User: ⌘W
  → canClose(withDelegate:)
  → Is dirty?
    → YES: "Save changes?" alert
      → Save: save, then close
      → Don't Save: close
      → Cancel: abort
    → NO: Continue
  → cancelActiveOperations() — stop model checking
  → close() — release resources
```

## Templates

```swift
enum DocumentTemplate {
    case empty          // Basic MODULE structure
    case specification  // Full spec with VARIABLES, Init, Next
    case plusCal        // PlusCal algorithm template
    case refinement     // Refinement mapping template
}
```

## Keyboard Shortcuts

| Operation | Shortcut |
|-----------|----------|
| New | ⌘N |
| New from Template | — (submenu) |
| Open | ⌘O |
| Save | ⌘S |
| Save As | ⇧⌘S |
| Save All | ⌥⌘S |
| Revert | — |
| Close | ⌘W |
| Close All | ⌥⌘W |

## Implementation Checklist

- [ ] Create `TLADocument.swift` with full NSDocument implementation
- [ ] Create `TLADocumentController.swift` with template support
- [ ] Create `TLAWindowController.swift` with toolbar
- [ ] Add `FileCommands.swift` for SwiftUI menu integration
- [ ] Configure Info.plist with UTIs and document types
- [ ] Test all file operations
- [ ] Verify auto-save and version history work
