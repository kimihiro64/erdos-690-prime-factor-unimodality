#!/usr/bin/env python3
"""Generate compact adjacent-prime data for Dusart Proposition 5.4(c)."""

from __future__ import annotations

import argparse
from pathlib import Path

BANDS = (
    (89693, 100000, 58, 5, "log_le_116_over_10_of_89693_le_of_le_100000"),
    (100001, 110000, 59, 5, "log_le_59_over_5_of_100001_le_of_le_110000"),
    (110001, 150000, 12, 1, "log_le_12_of_110001_le_of_le_150000"),
    (150001, 160000, 121, 10, "log_le_121_over_10_of_150001_le_of_le_160000"),
    (160001, 220000, 62, 5, "log_le_62_over_5_of_160001_le_of_le_220000"),
    (220001, 300000, 127, 10, "log_le_127_over_10_of_220001_le_of_le_300000"),
    (300001, 360653, 13, 1, "log_le_13_of_300001_le_of_le_360653"),
)


def primes_through(limit: int) -> list[int]:
    sieve = bytearray(b"\1") * (limit + 1)
    sieve[:2] = b"\0\0"
    for p in range(2, int(limit**0.5) + 1):
        if sieve[p]:
            sieve[p * p : limit + 1 : p] = b"\0" * (((limit - p * p) // p) + 1)
    return [p for p, is_prime in enumerate(sieve) if is_prime]


def band_pairs(primes: list[int], lower: int, upper: int) -> list[tuple[int, int]]:
    first = next(i for i, p in enumerate(primes) if p >= lower)
    result = []
    for index in range(first, len(primes) - 1):
        p, q = primes[index], primes[index + 1]
        if p > upper:
            break
        result.append((p, q))
    return result


def datum_line(p: int, q: int, lower: int, upper: int, lnum: int, lden: int) -> str:
    return f"    ⟨{p}, {q}, by norm_num, by norm_num, by decide, by norm_num, by decide⟩,"


def band_module(
    index: int, band: tuple[int, int, int, int, str], pairs: list[tuple[int, int]]
) -> str:
    lower, upper, lnum, lden, log_bound = band
    datum = f"MediumLogDatum {lower} {upper} {lnum} {lden}"
    row_name = f"mediumLogRow{index:02d}"
    data_name = f"mediumLogData{index:02d}"
    rows_name = f"mediumLogRows{index:02d}"
    chain_name = f"mediumLogDataChain{index:02d}"
    row_chain_name = f"mediumLogRows{index:02d}_chain"
    end = pairs[-1][1] - 1
    previous_import = (
        ""
        if index == 1
        else f"import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.MediumLogBand{index - 1:02d}\n"
    )
    lines = [
        "import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows."
        "EndpointBoundsPart02",
        previous_import.rstrip("\n"),
        "import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.MediumLogRowsBase",
        "",
        "set_option autoImplicit false",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 200000000 in",
        f"/-! # Compact medium log-cubed band {index:02d} -/",
        "",
        "namespace PrimeFactorUnimodality",
        "",
        "noncomputable section",
        "",
        f"def {data_name} : List ({datum}) :=",
        "  [",
    ]
    lines.extend(datum_line(p, q, lower, upper, lnum, lden) for p, q in pairs)
    lines.extend(
        [
            "  ]",
            "",
            f"def {row_name} (datum : {datum}) : FinitePrimeGapLogRow :=",
            "  finitePrimeGapLogRow_of_scaled_explicit datum.q_prime datum.p_lt_q",
            f"    (by have h := datum.p_lower; omega) ({log_bound} datum.p_lower datum.p_upper)",
            "    (by norm_num) datum.scaled_product",
            "",
            f"def {rows_name} : List FinitePrimeGapLogRow :=",
            f"  {data_name}.map {row_name}",
            "",
            f"def {chain_name} : MediumLogDatumChain {pairs[0][0]} {end} {data_name} := by",
            "  decide",
            "",
            f"theorem {row_chain_name} :",
            f"    FinitePrimeGapLogRowsChain {pairs[0][0]} {end} {rows_name} := by",
            f"  exact mediumLogRowsChain_of_data {row_name} (by intro d; rfl) (by",
            f"    intro d; have h := d.p_lt_q; dsimp [{row_name}]; omega) {chain_name}",
            "",
            "end",
            "",
            "end PrimeFactorUnimodality",
            "",
        ]
    )
    return "\n".join(lines)


def aggregate(bands: list[tuple[tuple[int, int, int, int, str], list[tuple[int, int]]]]) -> str:
    imports = (
        "import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.MediumLogBand"
        f"{len(bands):02d}"
    )
    end = bands[-1][1][-1][1] - 1
    lines = [
        imports,
        "",
        "set_option autoImplicit false",
        "",
        "/-! # Generated medium logarithmic rows",
        "",
        "This facade assembles the independent medium log-cubed row bands. -/",
        "",
        "namespace PrimeFactorUnimodality",
        "",
        "noncomputable section",
        "",
    ]
    for index, (_, _pairs) in enumerate(bands, 1):
        lines.append(f"def mediumLogRowsPrefix{index:02d} : List FinitePrimeGapLogRow :=")
        if index == 1:
            lines.append(f"  [mediumLogSeedRow] ++ mediumLogRows{index:02d}")
        else:
            lines.append(f"  mediumLogRowsPrefix{index - 1:02d} ++ mediumLogRows{index:02d}")
        lines.append("")
    for index in range(1, len(bands) + 1):
        chain_start = 89693 if index == 1 else bands[index - 1][1][0][0]
        chain_end = bands[index - 1][1][-1][1] - 1
        lines.append(f"theorem mediumLogRowsPrefix{index:02d}_chain :")
        lines.append(
            f"    FinitePrimeGapLogRowsChain {chain_start} {chain_end} "
            f"mediumLogRowsPrefix{index:02d} := by"
        )
        if index == 1:
            lines.append(
                f"  exact finitePrimeGapLogRowsChain_append mediumLogSeedChain "
                f"mediumLogRows{index:02d}_chain"
            )
        else:
            lines.append(
                "  exact finitePrimeGapLogRowsChain_append "
                f"mediumLogRowsPrefix{index - 1:02d}_chain"
                f" mediumLogRows{index:02d}_chain"
            )
        lines.append("")
    lines.extend(
        [
            "theorem mediumLogRows_89693_360653_chain :",
            f"    FinitePrimeGapLogRowsChain 89693 {end} mediumLogRowsPrefix{len(bands):02d} := by",
            f"  exact mediumLogRowsPrefix{len(bands):02d}_chain",
            "",
        ]
    )
    lines.extend(
        [
            "theorem mediumLogRows_89693_360653_cover :",
            "    FinitePrimeGapLogRowsCoverUpTo "
            f"mediumLogRowsPrefix{len(bands):02d} (360653 : Real) := by",
            "  exact finitePrimeGapLogRowsCoverUpTo_of_chain",
            "    mediumLogRows_89693_360653_chain (by norm_num)",
            "",
            "theorem hasLogCubedShortIntervalPrimeBelow_360653 :",
            "    HasLogCubedShortIntervalPrimeBelow (360653 : Real) := by",
            "  exact hasLogCubedShortIntervalPrimeBelow_of_finite_gap_log_rows",
            "    mediumLogRows_89693_360653_cover",
            "",
            "end",
            "",
            "end PrimeFactorUnimodality",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    primes = primes_through(361000)
    generated = []
    for index, band in enumerate(BANDS, 1):
        pairs = band_pairs(primes, band[0], band[1])
        assert pairs and pairs[0][0] >= band[0] and pairs[-1][0] <= band[1]
        assert all((q - p) * band[2] ** 3 <= p * band[3] ** 3 for p, q in pairs)
        generated.append((band, pairs))
        (output / f"MediumLogBand{index:02d}.lean").write_text(band_module(index, band, pairs))
    (output / "MediumLogRows.lean").write_text(aggregate(generated))
    print("generated", sum(len(pairs) for _, pairs in generated), "adjacent-prime rows")


if __name__ == "__main__":
    main()
