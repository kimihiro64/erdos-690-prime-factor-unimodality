"""Check the compact Dusart endpoint data and its deterministic renderer."""

from __future__ import annotations

from bisect import bisect_right
from itertools import pairwise

from scripts.generate_dusart_pi_prefix import (
    DESTINATION,
    POWER,
    certificate_rows,
    render,
    row_valid,
)
from scripts.generate_medium_log_rows import primes_through


def test_shared_prime_list_and_jump_at_271() -> None:
    primes = primes_through(1000)
    assert len(primes) == 168
    assert primes == [n for n in range(2, 1001) if all(n % p for p in range(2, n))]
    assert bisect_right(primes, 270) == 57
    assert bisect_right(primes, 271) == 58


def test_exact_endpoint_rows_cover_every_real_boundary() -> None:
    primes = primes_through(1000)
    rows = certificate_rows(primes)
    assert len(rows) == 33
    assert rows[0][0] == 599
    assert rows[-1][1] == 1000
    assert all(row_valid(row, primes) for row in rows)
    assert all(row[0] < row[1] for row in rows)
    assert all(first[1] == second[0] for first, second in pairwise(rows))


def test_checker_rejects_invalid_arithmetic_and_log_power_data() -> None:
    primes = primes_through(1000)
    left, right, lower, upper = certificate_rows(primes)[0]
    assert not row_valid((left, 1000, lower, upper), primes)
    assert not row_valid((left, right, (right**POWER + 1, *lower[1:]), upper), primes)
    assert not row_valid((left, right, lower, (upper[0], upper[1] + 1, *upper[2:])), primes)


def test_generated_source_is_current() -> None:
    source = render()
    assert source == DESTINATION.read_text()
    assert len(source.encode()) < 10000
    assert source.count("theorem dusartPrimesThrough1000_eq") == 1
    assert "interval_cases" not in source
    assert "dusartPrimeCounting_599_1000" in source


def test_representative_row_uses_the_same_renderer() -> None:
    source = render(one_row=True)
    assert "One prime list supplies all 1 rational endpoint rows." in source
    assert "dusartPrimeCounting_599_603" in source
