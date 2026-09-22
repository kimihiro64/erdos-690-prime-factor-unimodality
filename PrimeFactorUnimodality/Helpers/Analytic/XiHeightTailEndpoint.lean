import PrimeFactorUnimodality.Helpers.Analytic.XiHeightTailPairing
import PrimeFactorUnimodality.Helpers.Analytic.XiLowReciprocalMass
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ReciprocalSquarePair

/-! # The closed-cutoff correction for a strict Lehman tail

The paper's actual height tail has a closed cutoff. When applying a theorem
about zeros strictly above that cutoff, all boundary multiplicities must
be added back. The exact identity here isolates that finite correction.
It does not assume that the cutoff avoids zeros.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- Every fixed ordinate has finitely many actual divisor labels. -/
theorem finite_xi_divisor_im_eq (A : ℝ) :
    {p : RiemannXiDivisorZeroIndex | (riemannXiDivisorZeroValue p).im = A}.Finite := by
  apply (finite_xi_divisor_abs_im_le |A|).subset
  intro p hp
  change |(riemannXiDivisorZeroValue p).im| ≤ |A|
  rw [show (riemannXiDivisorZeroValue p).im = A from hp]

/-- The total multiplicity on one ordinate, without imposing a real part. -/
def xiOrdinateMultiplicity (A : ℝ) : ℕ :=
  Nat.card {p : RiemannXiDivisorZeroIndex // (riemannXiDivisorZeroValue p).im = A}

/-- The pair kernel is constant on each finite ordinate fiber. -/
theorem tsum_xi_pair_at_ordinate (t A : ℝ) :
    (∑' p : {p : RiemannXiDivisorZeroIndex // (riemannXiDivisorZeroValue p).im = A},
      Real.reciprocalSquarePair t (riemannXiDivisorZeroValue p.1).im) =
      (xiOrdinateMultiplicity A : ℝ) * Real.reciprocalSquarePair t A := by
  let : Fintype {p : RiemannXiDivisorZeroIndex // (riemannXiDivisorZeroValue p).im = A} :=
    (finite_xi_divisor_im_eq A).fintype
  calc
    _ = ∑' _p : {p : RiemannXiDivisorZeroIndex // (riemannXiDivisorZeroValue p).im = A},
        Real.reciprocalSquarePair t A := tsum_congr (fun p => congrArg _ p.2)
    _ = _ := by simp [xiOrdinateMultiplicity, Nat.card_eq_fintype_card]

/-- Closed positive tails are the strict tails plus all cutoff atoms. -/
theorem xiHeightTail_eq_strict_positive_add_boundary {H : ℝ} (hH : 0 < H) (t : ℝ) :
    xiHeightTail t H =
      (∑' p : {p : RiemannXiDivisorZeroIndex // |t| + H < (riemannXiDivisorZeroValue p).im},
        Real.reciprocalSquarePair t (riemannXiDivisorZeroValue p.1).im) +
      (xiOrdinateMultiplicity (|t| + H) : ℝ) * Real.reciprocalSquarePair t (|t| + H) := by
  let S : Set RiemannXiDivisorZeroIndex := {p | |t| + H < (riemannXiDivisorZeroValue p).im}
  let B : Set RiemannXiDivisorZeroIndex := {p | (riemannXiDivisorZeroValue p).im = |t| + H}
  let F (p : RiemannXiDivisorZeroIndex) :=
    Real.reciprocalSquarePair t (riemannXiDivisorZeroValue p).im
  let e : S → {p : RiemannXiDivisorZeroIndex // |t| + H ≤ (riemannXiDivisorZeroValue p).im} :=
    fun p => ⟨p.1, p.2.le⟩
  have he : Function.Injective e := by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun r => r.val) h
  have hclosed : Summable (fun p : {p : RiemannXiDivisorZeroIndex //
      |t| + H ≤ (riemannXiDivisorZeroValue p).im} => F p.1) :=
    summable_xi_positive_height_pair hH t
  have hs : Summable (fun p : S => F p.1) := hclosed.comp_injective (i := e) he
  have hb : Summable (fun p : B => F p.1) := (finite_xi_divisor_im_eq _).summable F
  have hd : Disjoint S B := by
    rw [Set.disjoint_left]
    intro p hp hb
    change |t| + H < (riemannXiDivisorZeroValue p).im at hp
    change (riemannXiDivisorZeroValue p).im = |t| + H at hb
    exact (ne_of_lt hp) hb.symm
  have hu : {p : RiemannXiDivisorZeroIndex | |t| + H ≤ (riemannXiDivisorZeroValue p).im} =
      S ∪ B := by
    ext p
    change |t| + H ≤ (riemannXiDivisorZeroValue p).im ↔
      |t| + H < (riemannXiDivisorZeroValue p).im ∨ (riemannXiDivisorZeroValue p).im = |t| + H
    exact le_iff_lt_or_eq.trans (or_congr_right eq_comm)
  have hsplit := Summable.tsum_union_disjoint (f := F) hd hs hb
  rw [xiHeightTail_eq_positive_pair hH]
  change (∑' p : ({p : RiemannXiDivisorZeroIndex |
      |t| + H ≤ (riemannXiDivisorZeroValue p).im} : Set RiemannXiDivisorZeroIndex), F p.1) = _
  rw [hu, hsplit]
  have hboundary := tsum_xi_pair_at_ordinate t (|t| + H)
  change (∑' p : B, F p.1) = _ at hboundary
  exact congrArg (fun x => (∑' p : S, F p.1) + x) hboundary

/-- A strict-tail bound transfers to the actual tail with the explicit boundary correction. -/
theorem xiHeightTail_le_of_strict_positive {H C : ℝ} (hH : 0 < H) (t : ℝ)
    (hC : (∑' p : {p : RiemannXiDivisorZeroIndex // |t| + H < (riemannXiDivisorZeroValue p).im},
      Real.reciprocalSquarePair t (riemannXiDivisorZeroValue p.1).im) ≤ C) :
    xiHeightTail t H ≤ C +
      (xiOrdinateMultiplicity (|t| + H) : ℝ) * Real.reciprocalSquarePair t (|t| + H) := by
  rw [xiHeightTail_eq_strict_positive_add_boundary hH]
  exact add_le_add hC le_rfl

end

end PrimeFactorUnimodality
