import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiDivisorConjugation
import PrimeFactorUnimodality.Mathlib.Topology.Algebra.InfiniteSum.Paired

/-! # Exact same-height pairing of multiplicity-counted xi zero sums

The proved divisor equivalence and Mathlib's summable reindexing identify
the full series with half its reflected-pair series. Reflection-stable
subsets are allowed; in particular this applies to the closed central
strip without losing critical-line zeros or their multiplicities.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex
open scoped ComplexConjugate

/-- Every summable xi divisor series equals half the series of its same-height pairs. -/
theorem tsum_xi_divisor_eq_half_pair {G : ℂ → ℝ}
    (hG : Summable (fun p : RiemannXiDivisorZeroIndex => G (riemannXiDivisorZeroValue p))) :
    (∑' p : RiemannXiDivisorZeroIndex, G (riemannXiDivisorZeroValue p)) =
      (1 / 2 : ℝ) * ∑' p : RiemannXiDivisorZeroIndex,
        (G (riemannXiDivisorZeroValue p) + G (1 - conj (riemannXiDivisorZeroValue p))) := by
  have hsum := hG.tsum_add (hG.comp_injective riemannXiDivisorSameHeightReflection.injective)
  simp only [Function.comp_apply] at hsum
  rw [riemannXiDivisorSameHeightReflection.tsum_eq (fun p => G (riemannXiDivisorZeroValue p))]
    at hsum
  simp only [riemannXiDivisorZeroValue_sameHeightReflection] at hsum
  rw [hsum]
  ring

/-- Same-height pairing also holds on any reflection-stable divisor subtype. -/
theorem tsum_xi_divisor_subtype_eq_half_pair {G : ℂ → ℝ} (P : ℂ → Prop)
    (hP : ∀ z, P z ↔ P (1 - conj z))
    (hG : Summable (fun p : RiemannXiDivisorZeroIndex => G (riemannXiDivisorZeroValue p))) :
    (∑' p : {p : RiemannXiDivisorZeroIndex // P (riemannXiDivisorZeroValue p)},
      G (riemannXiDivisorZeroValue p.1)) =
      (1 / 2 : ℝ) * ∑' p : {p : RiemannXiDivisorZeroIndex // P (riemannXiDivisorZeroValue p)},
        (G (riemannXiDivisorZeroValue p.1) + G (1 - conj (riemannXiDivisorZeroValue p.1))) := by
  let e := riemannXiDivisorSameHeightReflectionOn P hP
  have hs := hG.subtype (fun p => P (riemannXiDivisorZeroValue p))
  have hsum := hs.tsum_add (hs.comp_injective e.injective)
  simp only [Function.comp_apply] at hsum
  rw [e.tsum_eq (fun p => G (riemannXiDivisorZeroValue p.1))] at hsum
  have hv (p : {p : RiemannXiDivisorZeroIndex // P (riemannXiDivisorZeroValue p)}) :
      riemannXiDivisorZeroValue (e p).1 = 1 - conj (riemannXiDivisorZeroValue p.1) := rfl
  simp only [hv] at hsum
  rw [hsum]
  ring

/-- Nonnegative pairs imply a nonnegative sum on a reflection-stable part of the divisor. -/
theorem tsum_xi_divisor_subtype_nonneg {G : ℂ → ℝ} (P : ℂ → Prop)
    (hP : ∀ z, P z ↔ P (1 - conj z))
    (hG : Summable (fun p : RiemannXiDivisorZeroIndex => G (riemannXiDivisorZeroValue p)))
    (hpair : ∀ z, P z → 0 ≤ G z + G (1 - conj z)) :
    0 ≤ ∑' p : {p : RiemannXiDivisorZeroIndex // P (riemannXiDivisorZeroValue p)},
      G (riemannXiDivisorZeroValue p.1) := by
  rw [tsum_xi_divisor_subtype_eq_half_pair P hP hG]
  exact mul_nonneg (by norm_num) (tsum_nonneg (fun p => hpair _ p.2))

/-- Discarding a reflection-stable set of nonnegative pairs leaves a rigorous lower bound. -/
theorem tsum_xi_divisor_compl_le {G : ℂ → ℝ} (P : ℂ → Prop)
    (hP : ∀ z, P z ↔ P (1 - conj z))
    (hG : Summable (fun p : RiemannXiDivisorZeroIndex => G (riemannXiDivisorZeroValue p)))
    (hpair : ∀ z, P z → 0 ≤ G z + G (1 - conj z)) :
    (∑' p : {p : RiemannXiDivisorZeroIndex // ¬ P (riemannXiDivisorZeroValue p)},
      G (riemannXiDivisorZeroValue p.1)) ≤
      ∑' p : RiemannXiDivisorZeroIndex, G (riemannXiDivisorZeroValue p) := by
  have hs := hG.tsum_subtype_add_tsum_subtype_compl {p | P (riemannXiDivisorZeroValue p)}
  have hn := tsum_xi_divisor_subtype_nonneg P hP hG hpair
  change (∑' p : {p : RiemannXiDivisorZeroIndex // P (riemannXiDivisorZeroValue p)},
      G (riemannXiDivisorZeroValue p.1)) +
    (∑' p : {p : RiemannXiDivisorZeroIndex // ¬ P (riemannXiDivisorZeroValue p)},
      G (riemannXiDivisorZeroValue p.1)) = _ at hs
  linarith

/-- Retain a distinguished off-critical pair inside a reflection-stable divisor subset. -/
theorem xi_divisor_pair_le_tsum_subtype {G : ℂ → ℝ} (P : ℂ → Prop)
    (hP : ∀ z, P z ↔ P (1 - conj z))
    (hG : Summable (fun p : RiemannXiDivisorZeroIndex => G (riemannXiDivisorZeroValue p)))
    (hpair : ∀ z, P z → 0 ≤ G z + G (1 - conj z))
    (p : RiemannXiDivisorZeroIndex) (hp : P (riemannXiDivisorZeroValue p))
    (hne : (riemannXiDivisorZeroValue p).re ≠ 1 / 2) :
    G (riemannXiDivisorZeroValue p) + G (1 - conj (riemannXiDivisorZeroValue p)) ≤
      ∑' q : {q : RiemannXiDivisorZeroIndex // P (riemannXiDivisorZeroValue q)},
        G (riemannXiDivisorZeroValue q.1) := by
  let e := riemannXiDivisorSameHeightReflectionOn P hP
  have hei : Function.Involutive e := by
    intro q
    exact Subtype.ext (riemannXiDivisorSameHeightReflection_involutive q.1)
  let q : {q : RiemannXiDivisorZeroIndex // P (riemannXiDivisorZeroValue q)} := ⟨p, hp⟩
  have hq : q ≠ e q := by
    intro h
    exact hne ((riemannXiDivisorSameHeightReflection_fixed_iff p).mp
      (congrArg Subtype.val h).symm)
  exact (hG.subtype (fun p => P (riemannXiDivisorZeroValue p))).pair_le_tsum_of_involution
    e hei (fun q => hpair _ q.2) q hq

/-- Retaining a distinguished pair while discarding the other nonnegative pairs. -/
theorem xi_divisor_pair_add_tsum_compl_le {G : ℂ → ℝ} (P : ℂ → Prop)
    (hP : ∀ z, P z ↔ P (1 - conj z))
    (hG : Summable (fun p : RiemannXiDivisorZeroIndex => G (riemannXiDivisorZeroValue p)))
    (hpair : ∀ z, P z → 0 ≤ G z + G (1 - conj z))
    (p : RiemannXiDivisorZeroIndex) (hp : P (riemannXiDivisorZeroValue p))
    (hne : (riemannXiDivisorZeroValue p).re ≠ 1 / 2) :
    G (riemannXiDivisorZeroValue p) + G (1 - conj (riemannXiDivisorZeroValue p)) +
      (∑' q : {q : RiemannXiDivisorZeroIndex // ¬ P (riemannXiDivisorZeroValue q)},
        G (riemannXiDivisorZeroValue q.1)) ≤
      ∑' q : RiemannXiDivisorZeroIndex, G (riemannXiDivisorZeroValue q) := by
  have hs := hG.tsum_subtype_add_tsum_subtype_compl {p | P (riemannXiDivisorZeroValue p)}
  have hret := xi_divisor_pair_le_tsum_subtype P hP hG hpair p hp hne
  change (∑' q : {q : RiemannXiDivisorZeroIndex // P (riemannXiDivisorZeroValue q)},
      G (riemannXiDivisorZeroValue q.1)) +
    (∑' q : {q : RiemannXiDivisorZeroIndex // ¬ P (riemannXiDivisorZeroValue q)},
      G (riemannXiDivisorZeroValue q.1)) = _ at hs
  linarith

end

end PrimeFactorUnimodality
