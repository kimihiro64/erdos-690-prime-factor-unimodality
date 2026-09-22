import PrimeFactorUnimodality.Helpers.Analytic.XiHeightTail
import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiDivisorConjugation

/-! # Positive-ordinate decomposition of the actual xi height tail

Conjugation identifies the negative and positive ordinate tails with every
finite multiplicity label retained. Splitting the disjoint closed tails
gives the two rational kernels in Mossinghoff--Trudgian (4.1). No zero at
the cutoff is discarded and no RH hypothesis is used.
Source: https://arxiv.org/pdf/1410.3926
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real Set

/-- Conjugation gives an exact equivalence between the two closed ordinate tails. -/
def xiPositiveNegativeHeightEquiv (A : ℝ) :
    {p : RiemannXiDivisorZeroIndex // A ≤ (riemannXiDivisorZeroValue p).im} ≃
      {p : RiemannXiDivisorZeroIndex // A ≤ -(riemannXiDivisorZeroValue p).im} :=
  riemannXiDivisorConjugation.subtypeEquiv (fun p => by
    simp only [riemannXiDivisorZeroValue_conjugation, conj_im, neg_neg])

/-- Both positive-ordinate kernels converge absolutely, with the actual closed cutoff. -/
theorem summable_xi_positive_height_pair {H : ℝ} (hH : 0 < H) (t : ℝ) :
    Summable (fun p : {p : RiemannXiDivisorZeroIndex //
      |t| + H ≤ (riemannXiDivisorZeroValue p).im} =>
      1 / ((riemannXiDivisorZeroValue p.1).im - t) ^ 2 +
        1 / ((riemannXiDivisorZeroValue p.1).im + t) ^ 2) := by
  have hs (u : ℝ) (hu : |u| ≤ |t|) : Summable (fun p : {p : RiemannXiDivisorZeroIndex //
      |t| + H ≤ (riemannXiDivisorZeroValue p).im} =>
      1 / (u - (riemannXiDivisorZeroValue p.1).im) ^ 2) := by
    exact summable_xi_height_inv_sq hH u (fun p hp =>
      sq_le_sub_sq_of_abs_cutoff hH.le (by
        have hb := hp.trans (le_abs_self (riemannXiDivisorZeroValue p).im)
        linarith))
  have hminus := hs t le_rfl
  have hplus := hs (-t) (by rw [abs_neg])
  convert hminus.add hplus using 1
  funext p
  congr 2 <;> ring

/-- The full absolute-height tail is the positive-height sum of the two reflected kernels. -/
theorem xiHeightTail_eq_positive_pair {H : ℝ} (hH : 0 < H) (t : ℝ) :
    xiHeightTail t H = ∑' p : {p : RiemannXiDivisorZeroIndex //
      |t| + H ≤ (riemannXiDivisorZeroValue p).im},
      (1 / ((riemannXiDivisorZeroValue p.1).im - t) ^ 2 +
        1 / ((riemannXiDivisorZeroValue p.1).im + t) ^ 2) := by
  let P : Set RiemannXiDivisorZeroIndex := {p | |t| + H ≤ (riemannXiDivisorZeroValue p).im}
  let N : Set RiemannXiDivisorZeroIndex := {p | |t| + H ≤ -(riemannXiDivisorZeroValue p).im}
  let f (p : RiemannXiDivisorZeroIndex) := 1 / (t - (riemannXiDivisorZeroValue p).im) ^ 2
  have hp : Summable (fun p : P => f p.1) :=
    summable_xi_height_inv_sq hH t (fun p h =>
      sq_le_sub_sq_of_abs_cutoff hH.le (h.trans (le_abs_self _)))
  have hn : Summable (fun p : N => f p.1) :=
    summable_xi_height_inv_sq hH t (fun p h =>
      sq_le_sub_sq_of_abs_cutoff hH.le (h.trans (neg_le_abs _)))
  have hd : Disjoint P N := by
    rw [Set.disjoint_left]
    intro p hp hn
    change |t| + H ≤ _ at hp hn
    linarith [abs_nonneg t]
  have hunion : {p : RiemannXiDivisorZeroIndex |
      |t| + H ≤ |(riemannXiDivisorZeroValue p).im|} = P ∪ N := by
    ext p
    change |t| + H ≤ |(riemannXiDivisorZeroValue p).im| ↔
      |t| + H ≤ (riemannXiDivisorZeroValue p).im ∨ |t| + H ≤ -(riemannXiDivisorZeroValue p).im
    exact le_abs
  have hsplit := Summable.tsum_union_disjoint (f := f) hd hp hn
  have hconj := (xiPositiveNegativeHeightEquiv (|t| + H)).tsum_eq
    (fun p : N => f p.1)
  have hvalue (p : P) : f ((xiPositiveNegativeHeightEquiv (|t| + H) p).1) =
      1 / ((riemannXiDivisorZeroValue p.1).im + t) ^ 2 := by
    change 1 / (t - (riemannXiDivisorZeroValue (riemannXiDivisorConjugation p.1)).im) ^ 2 = _
    simp only [riemannXiDivisorZeroValue_conjugation, conj_im, sub_neg_eq_add, add_comm]
  simp_rw [hvalue] at hconj
  have hplus : Summable (fun p : P => 1 / ((riemannXiDivisorZeroValue p.1).im + t) ^ 2) :=
    (hn.comp_injective (xiPositiveNegativeHeightEquiv (|t| + H)).injective).congr hvalue
  unfold xiHeightTail
  change (∑' p : ({p : RiemannXiDivisorZeroIndex |
    |t| + H ≤ |(riemannXiDivisorZeroValue p).im|} : Set RiemannXiDivisorZeroIndex), f p.1) = _
  rw [hunion, hsplit]
  change (∑' p : P, f p.1) + (∑' p : N, f p.1) = _
  change (∑' p : P, 1 / ((riemannXiDivisorZeroValue p.1).im + t) ^ 2) =
    (∑' p : N, f p.1) at hconj
  rw [← hconj, ← hp.tsum_add hplus]
  apply tsum_congr
  intro p
  dsimp [f]
  ring

end

end PrimeFactorUnimodality
