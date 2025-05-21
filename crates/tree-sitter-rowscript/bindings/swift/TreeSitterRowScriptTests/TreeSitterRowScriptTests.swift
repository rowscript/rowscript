import XCTest
import SwiftTreeSitter
import TreeSitterRowscript

final class TreeSitterRowscriptTests: XCTestCase {
    func testCanLoadGrammar() throws {
        let parser = Parser()
        let language = Language(language: tree_sitter_rowscript())
        XCTAssertNoThrow(try parser.setLanguage(language),
                         "Error loading RowScript grammar")
    }
}
