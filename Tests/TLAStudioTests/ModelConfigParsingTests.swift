import XCTest
@testable import TLAStudioApp

final class ModelConfigParsingTests: XCTestCase {

    func testGenerateAndParseConfigPreservesConstantTypes() {
        let config = ModelConfig(
            name: "RoundTrip",
            specFile: URL(fileURLWithPath: "/tmp/RoundTrip.tla"),
            constants: [
                "Count": .int(3),
                "Enabled": .bool(true),
                "Greeting": .string("hello \"world\""),
                "Node": .modelValue("NodeA"),
                "Members": .set([
                    .modelValue("n1"),
                    .modelValue("n2"),
                    .string("quoted"),
                    .set([.int(1), .int(2)])
                ])
            ],
            symmetrySets: ["Members": []]
        )

        let parsed = ModelConfig.parse(content: config.generateConfigFile())

        XCTAssertEqual(parsed.constants["Count"], .int(3))
        XCTAssertEqual(parsed.constants["Enabled"], .bool(true))
        XCTAssertEqual(parsed.constants["Greeting"], .string("hello \"world\""))
        XCTAssertEqual(parsed.constants["Node"], .modelValue("NodeA"))
        XCTAssertEqual(
            parsed.constants["Members"],
            .set([
                .modelValue("n1"),
                .modelValue("n2"),
                .string("quoted"),
                .set([.int(1), .int(2)])
            ])
        )
        XCTAssertEqual(parsed.symmetrySets.keys.sorted(), ["Members"])
    }

    func testParseConstantValuePreservesBareExpressionsAndNestedSets() {
        XCTAssertEqual(ModelConfig.parseConstantValue("ProcSet"), .modelValue("ProcSet"))
        XCTAssertEqual(
            ModelConfig.parseConstantValue("{a, {1, 2}, \"hi\"}"),
            .set([
                .modelValue("a"),
                .set([.int(1), .int(2)]),
                .string("hi")
            ])
        )
    }
}
