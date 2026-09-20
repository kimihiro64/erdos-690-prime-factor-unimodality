from itertools import pairwise
from pathlib import Path

from scripts.generate_medium_log_rows import BANDS, band_pairs, primes_through


def test_medium_log_bands_cover_endpoint_with_scaled_products():
    primes = primes_through(361000)
    all_pairs = []
    for lower, upper, lnum, lden, _ in BANDS:
        pairs = band_pairs(primes, lower, upper)
        assert pairs
        assert pairs[0][0] >= lower
        assert pairs[-1][0] <= upper
        assert all((q - p) * lnum**3 <= p * lden**3 for p, q in pairs)
        all_pairs.extend(pairs)

    assert all_pairs[0] == (89753, 89759)
    assert all_pairs[-1] == (360653, 360749)
    assert len(all_pairs) == 22114
    assert all(left[1] == right[0] for left, right in pairwise(all_pairs))


def test_medium_log_generator_has_no_per_witness_output_directory():
    script = Path("scripts/generate_medium_log_rows.py")
    assert script.exists()
    assert "MediumLogBand" in script.read_text()
    assert "MediumLogRows" in script.read_text()
