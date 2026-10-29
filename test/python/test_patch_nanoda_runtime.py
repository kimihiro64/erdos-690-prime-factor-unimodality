"""Require full-source integrity for the pinned NanoDa runtime port."""

import pytest

from scripts.patch_nanoda_runtime import REPLACEMENTS, SOURCE_SHA256, digest, rewrite_source


@pytest.mark.parametrize("relative", sorted(SOURCE_SHA256))
def test_runtime_port_recovers_every_unchanged_checker_byte(relative: str) -> None:
    edits = REPLACEMENTS[relative]
    original = "unchanged kernel arithmetic and axiom checks\n" + "\n".join(
        before for before, _ in edits
    )
    expected = digest(original)
    result, changed = rewrite_source(original, expected, edits)
    assert changed
    recovered = result
    for before, after in reversed(edits):
        recovered = recovered.replace(after, before, 1)
    assert recovered == original
    assert rewrite_source(result, expected, edits) == (result, False)
    with pytest.raises(ValueError, match="source"):
        rewrite_source(original.replace("axiom checks", "missing checks"), expected, edits)
    with pytest.raises(ValueError, match="source"):
        rewrite_source(result.replace("axiom checks", "missing checks"), expected, edits)


def test_runtime_port_rejects_an_omitted_declaration_check() -> None:
    edits = REPLACEMENTS["src/tc.rs"]
    original = "\n".join(before for before, _ in edits)
    expected = digest(original)
    corrupted = original.replace("self.check_declar(declar);", "/* skipped */", 1)
    with pytest.raises(ValueError, match="source"):
        rewrite_source(corrupted, expected, edits)


def test_runtime_port_rejects_ambiguous_anchor() -> None:
    original = "checker\nanchor\nanchor\n"
    with pytest.raises(ValueError, match="anchor is not unique"):
        rewrite_source(original, digest(original), (("anchor", "timed anchor"),))


def test_runtime_port_tracks_only_the_reviewed_runtime_files() -> None:
    assert (
        set(SOURCE_SHA256)
        == set(REPLACEMENTS)
        == {"src/lib.rs", "src/main.rs", "src/parser.rs", "src/tc.rs"}
    )
    assert REPLACEMENTS["src/lib.rs"] == (
        (
            "pub(crate) const STACK_SIZE: usize = 16_777_216;",
            "pub(crate) const STACK_SIZE: usize = 268_435_456;",
        ),
    )
