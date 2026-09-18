import PrimeFactorUnimodality.Helpers.Analytic.ReciprocalPrimeBounds
import VendorPrimeNumberTheoremAnd.Mertens

set_option autoImplicit false

/-! # Proved Mertens provider

This module connects the complete Mertens development ported from the sibling
`PrimeNumberTheoremAnd` repository to this project's small analytic interface.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The explicit error numerator obtained from the sibling Mertens proof after
inserting its proved upper bound for the auxiliary convergent series `E₁`. -/
def mertensErrorConstant : Real :=
  Real.log 4 + 6 + (5 * Real.log 2 + 3) / 4

theorem mertensErrorConstant_nonneg : 0 ≤ mertensErrorConstant := by
  unfold mertensErrorConstant
  positivity

theorem mertensErrorConstant_lt_901_div_100 :
    mertensErrorConstant < (901 : Real) / 100 := by
  rw [mertensErrorConstant, Real.log_four_eq]
  nlinarith [Real.log_two_lt_d9]

private theorem log_101_lt_577_div_125 :
    Real.log 101 < (577 : Real) / 125 := by
  have powerLt : (101 : Real) ^ 10 < 2 ^ 65 * 3 := by norm_num
  have logged := Real.log_lt_log (by positivity) powerLt
  rw [Real.log_pow, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow] at logged
  norm_num at logged ⊢
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9]

/-- A tighter elementary lower bound for Euler's constant, obtained from the
100th monotone harmonic approximation. -/
theorem eulerMascheroniConstant_gt_57_div_100 :
    (57 : Real) / 100 < Real.eulerMascheroniConstant := by
  have harmonicBound : (57 : Real) / 100 + 577 / 125 <
      (harmonic 100 : Real) := by
    norm_num [harmonic]
  have sequenceBound : (57 : Real) / 100 < Real.eulerMascheroniSeq 100 := by
    rw [Real.eulerMascheroniSeq]
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
    linarith [log_101_lt_577_div_125]
  exact sequenceBound.trans (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 100)

private def logTailMajorant (x : Real) : Real :=
  (∑ i ∈ Finset.range 8, x ^ (i + 1) / (i + 1)) - x +
    |x| ^ 9 / (1 - |x|)

private theorem mertensSummand_ge_neg_majorant {p : Nat} (hp : p.Prime) :
    -logTailMajorant (1 / (p : Real)) ≤ Mertens.M_eq_summand p := by
  let x : Real := 1 / p
  have pTwo : (2 : Real) ≤ p := by exact_mod_cast hp.two_le
  have xPos : 0 < x := by positivity
  have xLt : x < 1 := by
    dsimp only [x]
    exact (div_lt_one (by positivity)).2 (by linarith)
  have expansion := Real.abs_log_sub_add_sum_range_le
    (x := x) (show |x| < 1 by rw [abs_of_pos xPos]; exact xLt) 8
  have lower := (abs_le.mp expansion).1
  unfold Mertens.M_eq_summand
  rw [if_pos hp]
  dsimp only [logTailMajorant, x] at lower ⊢
  rw [abs_of_pos (by positivity : (0 : Real) < 1 / (p : Real))] at lower ⊢
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at lower
  linarith

private def primesBelow500 : Finset Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
    67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137,
    139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211,
    223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283,
    293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379,
    383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461,
    463, 467, 479, 487, 491, 499].toFinset

set_option maxRecDepth 100000 in
private theorem primesBelow500_eq_filter :
    primesBelow500 = (Finset.range 500).filter Nat.Prime := by
  decide

private def mertensMajorantBelow500 : Real :=
  ∑ p ∈ primesBelow500, logTailMajorant (1 / (p : Real))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Exact rational normalization of the finite 95-prime majorant is intentionally unbounded.
private theorem mertensMajorantBelow500_lt :
    mertensMajorantBelow500 < (399 : Real) / 1250 := by
  norm_num [mertensMajorantBelow500, primesBelow500, logTailMajorant]

set_option maxRecDepth 100000 in
/-- A positive rational lower bound for the Meissel--Mertens constant.  The
proof uses an eight-term logarithm expansion below 500 and the proved `4/N`
tail estimate from the vendored Mertens development. -/
theorem mertensConstant_gt_six_twenty_fifths :
    (6 : Real) / 25 < Mertens.M := by
  have finiteLower : -mertensMajorantBelow500 ≤
      ∑ n ∈ Finset.range 500, Mertens.M_eq_summand n := by
    rw [mertensMajorantBelow500, primesBelow500_eq_filter,
      ← Finset.sum_neg_distrib]
    calc
      ∑ n ∈ (Finset.range 500).filter Nat.Prime,
          -logTailMajorant (1 / (n : Real)) ≤
          ∑ n ∈ (Finset.range 500).filter Nat.Prime,
            Mertens.M_eq_summand n := by
        apply Finset.sum_le_sum
        intro n hn
        exact mertensSummand_ge_neg_majorant (Finset.mem_filter.mp hn).2
      _ = ∑ n ∈ Finset.range 500, Mertens.M_eq_summand n := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro n hnRange hnNotMem
        have notPrime : ¬n.Prime := by
          intro prime
          exact hnNotMem (Finset.mem_filter.mpr ⟨hnRange, prime⟩)
        unfold Mertens.M_eq_summand
        rw [if_neg notPrime]
  have tail := Mertens.sum_M_eq_summand_le (N := 500) (by norm_num)
  have tailUpper := (abs_le.mp tail).2
  have gammaLower := eulerMascheroniConstant_gt_57_div_100
  rw [Mertens.γ.eq_eulerMascheroni] at tailUpper
  have sumLower : (-((399 : Real) / 1250)) <
      ∑ n ∈ Finset.range 500, Mertens.M_eq_summand n :=
    (neg_lt_neg mertensMajorantBelow500_lt).trans_le finiteLower
  norm_num at tailUpper
  nlinarith

/-- A sharp enough one-sided bound for the Meissel--Mertens constant.  It
needs no decimal evaluation: the sibling proof identifies `γ - M` as a sum
of nonnegative prime-power terms, and Mathlib proves `γ < 2/3`. -/
theorem mertensConstant_lt_two_thirds : Mertens.M < (2 : Real) / 3 := by
  have sumNonneg : 0 ≤ ∑' n : Nat, Mertens.M_eq_f n := by
    apply tsum_nonneg
    intro n
    unfold Mertens.M_eq_f
    split_ifs with hn
    · rfl
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have sumEq := Mertens.M_eq_f.HasSum.tsum_eq
  rw [sumEq, Mertens.γ.eq_eulerMascheroni] at sumNonneg
  linarith [Real.eulerMascheroniConstant_lt_two_thirds]

/-- A kernel-checked `O(1 / log x)` estimate for reciprocal primes, specialized
to natural cutoffs and the exact convention used by this project. -/
theorem hasMertensReciprocalPrimeEstimate :
    HasReciprocalPrimeEstimate Mertens.M mertensErrorConstant := by
  intro n hn
  have hnReal : (2 : Real) ≤ n := by exact_mod_cast hn
  have logNonneg : 0 ≤ Real.log (n : Real) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have raw := Mertens.E₂p.abs_le hnReal
  have numeratorBound :
      Real.log 4 + 6 + Mertens.E₁ ≤ mertensErrorConstant := by
    unfold mertensErrorConstant
    linarith [Mertens.E₁.le]
  have errorBound :
      (Real.log 4 + 6 + Mertens.E₁) / Real.log n ≤
        mertensErrorConstant / Real.log n := by
    exact div_le_div_of_nonneg_right numeratorBound logNonneg
  rw [reciprocalPrimeSumBelow_succ_eq]
  have floorEq : ⌊(n : Real)⌋₊ = n := by simp
  unfold Mertens.E₂p at raw
  rw [floorEq] at raw
  exact raw.trans errorBound

end

end PrimeFactorUnimodality
