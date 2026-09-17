import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Definitions.SelectionRow
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.Row89
import PrimeFactorUnimodality.Helpers.FirstDifference.PrimeSequence

set_option autoImplicit false

/-! Generated exact weak-descent checks for the finite beginning of `d₃`. -/

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- The generated exact arithmetic checks all initial degree-two ratios.
theorem k3PrimeFactorDensity_finite_descent
    (i : Nat) (hLower : 2 ≤ i) (hUpper : i < 23) :
    primeFactorDensity 3 (i + 1) ≤ primeFactorDensity 3 i := by
  interval_cases i
  case «2» =>
    apply (primeDensityStep_le_iff_ratio_le_gap 1 2 (by omega)).2
    have hp : primeAt 2 = 5 := by
      rw [← show Nat.primeCounting' 5 = 2 by decide]
      exact primeAt_primeCounting' 5 (by decide)
    have hq : primeAt (2 + 1) = 7 := by
      norm_num
      rw [← show Nat.primeCounting' 7 = 3 by decide]
      exact primeAt_primeCounting' 7 (by decide)
    rw [hp, show primeGap 2 = 2 by
      norm_num [primeGap, hq, hp]]
    rw [densityRatio_perm primesBelow5_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix5
        primePrefix5_gt_one 2,
      ← selectionRowBounded_getD 7 primePrefix5 (2 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix5 2 (by omega),
      numericalRow89_5]
    norm_num
  case «3» =>
    apply (primeDensityStep_le_iff_ratio_le_gap 1 3 (by omega)).2
    have hp : primeAt 3 = 7 := by
      rw [← show Nat.primeCounting' 7 = 3 by decide]
      exact primeAt_primeCounting' 7 (by decide)
    have hq : primeAt (3 + 1) = 11 := by
      norm_num
      rw [← show Nat.primeCounting' 11 = 4 by decide]
      exact primeAt_primeCounting' 11 (by decide)
    rw [hp, show primeGap 3 = 4 by
      norm_num [primeGap, hq, hp]]
    rw [densityRatio_perm primesBelow7_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix7
        primePrefix7_gt_one 2,
      ← selectionRowBounded_getD 7 primePrefix7 (2 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix7 2 (by omega),
      numericalRow89_7]
    norm_num
  case «4» =>
    apply (primeDensityStep_le_iff_ratio_le_gap 1 4 (by omega)).2
    have hp : primeAt 4 = 11 := by
      rw [← show Nat.primeCounting' 11 = 4 by decide]
      exact primeAt_primeCounting' 11 (by decide)
    have hq : primeAt (4 + 1) = 13 := by
      norm_num
      rw [← show Nat.primeCounting' 13 = 5 by decide]
      exact primeAt_primeCounting' 13 (by decide)
    rw [hp, show primeGap 4 = 2 by
      norm_num [primeGap, hq, hp]]
    rw [densityRatio_perm primesBelow11_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix11
        primePrefix11_gt_one 2,
      ← selectionRowBounded_getD 7 primePrefix11 (2 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix11 2 (by omega),
      numericalRow89_11]
    norm_num
  case «5» =>
    apply (primeDensityStep_le_iff_ratio_le_gap 1 5 (by omega)).2
    have hp : primeAt 5 = 13 := by
      rw [← show Nat.primeCounting' 13 = 5 by decide]
      exact primeAt_primeCounting' 13 (by decide)
    have hq : primeAt (5 + 1) = 17 := by
      norm_num
      rw [← show Nat.primeCounting' 17 = 6 by decide]
      exact primeAt_primeCounting' 17 (by decide)
    rw [hp, show primeGap 5 = 4 by
      norm_num [primeGap, hq, hp]]
    rw [densityRatio_perm primesBelow13_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix13
        primePrefix13_gt_one 2,
      ← selectionRowBounded_getD 7 primePrefix13 (2 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix13 2 (by omega),
      numericalRow89_13]
    norm_num
  case «6» =>
    apply (primeDensityStep_le_iff_ratio_le_gap 1 6 (by omega)).2
    have hp : primeAt 6 = 17 := by
      rw [← show Nat.primeCounting' 17 = 6 by decide]
      exact primeAt_primeCounting' 17 (by decide)
    have hq : primeAt (6 + 1) = 19 := by
      norm_num
      rw [← show Nat.primeCounting' 19 = 7 by decide]
      exact primeAt_primeCounting' 19 (by decide)
    rw [hp, show primeGap 6 = 2 by
      norm_num [primeGap, hq, hp]]
    rw [densityRatio_perm primesBelow17_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix17
        primePrefix17_gt_one 2,
      ← selectionRowBounded_getD 7 primePrefix17 (2 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix17 2 (by omega),
      numericalRow89_17]
    norm_num
  case «7» =>
    apply (primeDensityStep_le_iff_ratio_le_gap 1 7 (by omega)).2
    have hp : primeAt 7 = 19 := by
      rw [← show Nat.primeCounting' 19 = 7 by decide]
      exact primeAt_primeCounting' 19 (by decide)
    have hq : primeAt (7 + 1) = 23 := by
      norm_num
      rw [← show Nat.primeCounting' 23 = 8 by decide]
      exact primeAt_primeCounting' 23 (by decide)
    rw [hp, show primeGap 7 = 4 by
      norm_num [primeGap, hq, hp]]
    rw [densityRatio_perm primesBelow19_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix19
        primePrefix19_gt_one 2,
      ← selectionRowBounded_getD 7 primePrefix19 (2 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix19 2 (by omega),
      numericalRow89_19]
    norm_num
  case «8» =>
    apply (primeDensityStep_le_iff_ratio_le_gap 1 8 (by omega)).2
    have hp : primeAt 8 = 23 := by
      rw [← show Nat.primeCounting' 23 = 8 by decide]
      exact primeAt_primeCounting' 23 (by decide)
    have hq : primeAt (8 + 1) = 29 := by
      norm_num
      rw [← show Nat.primeCounting' 29 = 9 by decide]
      exact primeAt_primeCounting' 29 (by decide)
    rw [hp, show primeGap 8 = 6 by
      norm_num [primeGap, hq, hp]]
    rw [densityRatio_perm primesBelow23_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix23
        primePrefix23_gt_one 2,
      ← selectionRowBounded_getD 7 primePrefix23 (2 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix23 2 (by omega),
      numericalRow89_23]
    norm_num
  case «9» =>
    apply (primeDensityStep_le_iff_ratio_le_gap 1 9 (by omega)).2
    have hp : primeAt 9 = 29 := by
      rw [← show Nat.primeCounting' 29 = 9 by decide]
      exact primeAt_primeCounting' 29 (by decide)
    have hq : primeAt (9 + 1) = 31 := by
      norm_num
      rw [← show Nat.primeCounting' 31 = 10 by decide]
      exact primeAt_primeCounting' 31 (by decide)
    rw [hp, show primeGap 9 = 2 by
      norm_num [primeGap, hq, hp]]
    rw [densityRatio_perm primesBelow29_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix29
        primePrefix29_gt_one 2,
      ← selectionRowBounded_getD 7 primePrefix29 (2 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix29 2 (by omega),
      numericalRow89_29]
    norm_num
  case «10» =>
    apply (primeDensityStep_le_iff_ratio_le_gap 1 10 (by omega)).2
    have hp : primeAt 10 = 31 := by
      rw [← show Nat.primeCounting' 31 = 10 by decide]
      exact primeAt_primeCounting' 31 (by decide)
    have hq : primeAt (10 + 1) = 37 := by
      norm_num
      rw [← show Nat.primeCounting' 37 = 11 by decide]
      exact primeAt_primeCounting' 37 (by decide)
    rw [hp, show primeGap 10 = 6 by
      norm_num [primeGap, hq, hp]]
    rw [densityRatio_perm primesBelow31_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix31
        primePrefix31_gt_one 2,
      ← selectionRowBounded_getD 7 primePrefix31 (2 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix31 2 (by omega),
      numericalRow89_31]
    norm_num
  case «11» =>
    apply (primeDensityStep_le_iff_ratio_le_gap 1 11 (by omega)).2
    have hp : primeAt 11 = 37 := by
      rw [← show Nat.primeCounting' 37 = 11 by decide]
      exact primeAt_primeCounting' 37 (by decide)
    have hq : primeAt (11 + 1) = 41 := by
      norm_num
      rw [← show Nat.primeCounting' 41 = 12 by decide]
      exact primeAt_primeCounting' 41 (by decide)
    rw [hp, show primeGap 11 = 4 by
      norm_num [primeGap, hq, hp]]
    rw [densityRatio_perm primesBelow37_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix37
        primePrefix37_gt_one 2,
      ← selectionRowBounded_getD 7 primePrefix37 (2 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix37 2 (by omega),
      numericalRow89_37]
    norm_num
  case «12» =>
    apply (primeDensityStep_le_iff_ratio_le_gap 1 12 (by omega)).2
    have hp : primeAt 12 = 41 := by
      rw [← show Nat.primeCounting' 41 = 12 by decide]
      exact primeAt_primeCounting' 41 (by decide)
    have hq : primeAt (12 + 1) = 43 := by
      norm_num
      rw [← show Nat.primeCounting' 43 = 13 by decide]
      exact primeAt_primeCounting' 43 (by decide)
    rw [hp, show primeGap 12 = 2 by
      norm_num [primeGap, hq, hp]]
    rw [densityRatio_perm primesBelow41_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix41
        primePrefix41_gt_one 2,
      ← selectionRowBounded_getD 7 primePrefix41 (2 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix41 2 (by omega),
      numericalRow89_41]
    norm_num
  case «13» =>
    apply (primeDensityStep_le_iff_ratio_le_gap 1 13 (by omega)).2
    have hp : primeAt 13 = 43 := by
      rw [← show Nat.primeCounting' 43 = 13 by decide]
      exact primeAt_primeCounting' 43 (by decide)
    have hq : primeAt (13 + 1) = 47 := by
      norm_num
      rw [← show Nat.primeCounting' 47 = 14 by decide]
      exact primeAt_primeCounting' 47 (by decide)
    rw [hp, show primeGap 13 = 4 by
      norm_num [primeGap, hq, hp]]
    rw [densityRatio_perm primesBelow43_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix43
        primePrefix43_gt_one 2,
      ← selectionRowBounded_getD 7 primePrefix43 (2 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix43 2 (by omega),
      numericalRow89_43]
    norm_num
  case «14» =>
    apply (primeDensityStep_le_iff_ratio_le_gap 1 14 (by omega)).2
    have hp : primeAt 14 = 47 := by
      rw [← show Nat.primeCounting' 47 = 14 by decide]
      exact primeAt_primeCounting' 47 (by decide)
    have hq : primeAt (14 + 1) = 53 := by
      norm_num
      rw [← show Nat.primeCounting' 53 = 15 by decide]
      exact primeAt_primeCounting' 53 (by decide)
    rw [hp, show primeGap 14 = 6 by
      norm_num [primeGap, hq, hp]]
    rw [densityRatio_perm primesBelow47_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix47
        primePrefix47_gt_one 2,
      ← selectionRowBounded_getD 7 primePrefix47 (2 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix47 2 (by omega),
      numericalRow89_47]
    norm_num
  case «15» =>
    apply (primeDensityStep_le_iff_ratio_le_gap 1 15 (by omega)).2
    have hp : primeAt 15 = 53 := by
      rw [← show Nat.primeCounting' 53 = 15 by decide]
      exact primeAt_primeCounting' 53 (by decide)
    have hq : primeAt (15 + 1) = 59 := by
      norm_num
      rw [← show Nat.primeCounting' 59 = 16 by decide]
      exact primeAt_primeCounting' 59 (by decide)
    rw [hp, show primeGap 15 = 6 by
      norm_num [primeGap, hq, hp]]
    rw [densityRatio_perm primesBelow53_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix53
        primePrefix53_gt_one 2,
      ← selectionRowBounded_getD 7 primePrefix53 (2 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix53 2 (by omega),
      numericalRow89_53]
    norm_num
  case «16» =>
    apply (primeDensityStep_le_iff_ratio_le_gap 1 16 (by omega)).2
    have hp : primeAt 16 = 59 := by
      rw [← show Nat.primeCounting' 59 = 16 by decide]
      exact primeAt_primeCounting' 59 (by decide)
    have hq : primeAt (16 + 1) = 61 := by
      norm_num
      rw [← show Nat.primeCounting' 61 = 17 by decide]
      exact primeAt_primeCounting' 61 (by decide)
    rw [hp, show primeGap 16 = 2 by
      norm_num [primeGap, hq, hp]]
    rw [densityRatio_perm primesBelow59_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix59
        primePrefix59_gt_one 2,
      ← selectionRowBounded_getD 7 primePrefix59 (2 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix59 2 (by omega),
      numericalRow89_59]
    norm_num
  case «17» =>
    apply (primeDensityStep_le_iff_ratio_le_gap 1 17 (by omega)).2
    have hp : primeAt 17 = 61 := by
      rw [← show Nat.primeCounting' 61 = 17 by decide]
      exact primeAt_primeCounting' 61 (by decide)
    have hq : primeAt (17 + 1) = 67 := by
      norm_num
      rw [← show Nat.primeCounting' 67 = 18 by decide]
      exact primeAt_primeCounting' 67 (by decide)
    rw [hp, show primeGap 17 = 6 by
      norm_num [primeGap, hq, hp]]
    rw [densityRatio_perm primesBelow61_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix61
        primePrefix61_gt_one 2,
      ← selectionRowBounded_getD 7 primePrefix61 (2 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix61 2 (by omega),
      numericalRow89_61]
    norm_num
  case «18» =>
    apply (primeDensityStep_le_iff_ratio_le_gap 1 18 (by omega)).2
    have hp : primeAt 18 = 67 := by
      rw [← show Nat.primeCounting' 67 = 18 by decide]
      exact primeAt_primeCounting' 67 (by decide)
    have hq : primeAt (18 + 1) = 71 := by
      norm_num
      rw [← show Nat.primeCounting' 71 = 19 by decide]
      exact primeAt_primeCounting' 71 (by decide)
    rw [hp, show primeGap 18 = 4 by
      norm_num [primeGap, hq, hp]]
    rw [densityRatio_perm primesBelow67_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix67
        primePrefix67_gt_one 2,
      ← selectionRowBounded_getD 7 primePrefix67 (2 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix67 2 (by omega),
      numericalRow89_67]
    norm_num
  case «19» =>
    apply (primeDensityStep_le_iff_ratio_le_gap 1 19 (by omega)).2
    have hp : primeAt 19 = 71 := by
      rw [← show Nat.primeCounting' 71 = 19 by decide]
      exact primeAt_primeCounting' 71 (by decide)
    have hq : primeAt (19 + 1) = 73 := by
      norm_num
      rw [← show Nat.primeCounting' 73 = 20 by decide]
      exact primeAt_primeCounting' 73 (by decide)
    rw [hp, show primeGap 19 = 2 by
      norm_num [primeGap, hq, hp]]
    rw [densityRatio_perm primesBelow71_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix71
        primePrefix71_gt_one 2,
      ← selectionRowBounded_getD 7 primePrefix71 (2 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix71 2 (by omega),
      numericalRow89_71]
    norm_num
  case «20» =>
    apply (primeDensityStep_le_iff_ratio_le_gap 1 20 (by omega)).2
    have hp : primeAt 20 = 73 := by
      rw [← show Nat.primeCounting' 73 = 20 by decide]
      exact primeAt_primeCounting' 73 (by decide)
    have hq : primeAt (20 + 1) = 79 := by
      norm_num
      rw [← show Nat.primeCounting' 79 = 21 by decide]
      exact primeAt_primeCounting' 79 (by decide)
    rw [hp, show primeGap 20 = 6 by
      norm_num [primeGap, hq, hp]]
    rw [densityRatio_perm primesBelow73_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix73
        primePrefix73_gt_one 2,
      ← selectionRowBounded_getD 7 primePrefix73 (2 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix73 2 (by omega),
      numericalRow89_73]
    norm_num
  case «21» =>
    apply (primeDensityStep_le_iff_ratio_le_gap 1 21 (by omega)).2
    have hp : primeAt 21 = 79 := by
      rw [← show Nat.primeCounting' 79 = 21 by decide]
      exact primeAt_primeCounting' 79 (by decide)
    have hq : primeAt (21 + 1) = 83 := by
      norm_num
      rw [← show Nat.primeCounting' 83 = 22 by decide]
      exact primeAt_primeCounting' 83 (by decide)
    rw [hp, show primeGap 21 = 4 by
      norm_num [primeGap, hq, hp]]
    rw [densityRatio_perm primesBelow79_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix79
        primePrefix79_gt_one 2,
      ← selectionRowBounded_getD 7 primePrefix79 (2 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix79 2 (by omega),
      numericalRow89_79]
    norm_num
  case «22» =>
    apply (primeDensityStep_le_iff_ratio_le_gap 1 22 (by omega)).2
    have hp : primeAt 22 = 83 := by
      rw [← show Nat.primeCounting' 83 = 22 by decide]
      exact primeAt_primeCounting' 83 (by decide)
    have hq : primeAt (22 + 1) = 89 := by
      norm_num
      rw [← show Nat.primeCounting' 89 = 23 by decide]
      exact primeAt_primeCounting' 89 (by decide)
    rw [hp, show primeGap 22 = 6 by
      norm_num [primeGap, hq, hp]]
    rw [densityRatio_perm primesBelow83_perm,
      densityRatio_eq_selectionNumerator_ratio primePrefix83
        primePrefix83_gt_one 2,
      ← selectionRowBounded_getD 7 primePrefix83 (2 - 1) (by omega),
      ← selectionRowBounded_getD 7 primePrefix83 2 (by omega),
      numericalRow89_83]
    norm_num

end PrimeFactorUnimodality
