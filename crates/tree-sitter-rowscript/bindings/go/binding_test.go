package tree_sitter_rowscript_test

import (
	"testing"

	tree_sitter "github.com/tree-sitter/go-tree-sitter"
	tree_sitter_rowscript "github.com/rowscript/rowscript/bindings/go"
)

func TestCanLoadGrammar(t *testing.T) {
	language := tree_sitter.NewLanguage(tree_sitter_rowscript.Language())
	if language == nil {
		t.Errorf("Error loading RowScript grammar")
	}
}
