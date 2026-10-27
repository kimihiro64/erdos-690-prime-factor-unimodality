/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Basic.Real.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! # Finite Bernoulli means and elementary symmetric coefficients

The coefficients of a product of factors `1 + a * X` are log-concave.
A deletion identity then proves the strict part of Darroch's mean comparison:
if the sum of the odds probabilities is greater than an integer degree, the
coefficient at that degree exceeds its predecessor.

The final theorem applies this comparison after multiplying every weight by
a positive parameter. It gives a strict bound for an adjacent symmetric-sum
ratio, using finite algebra alone. No distribution or prime estimate is assumed.

## References

J. N. Darroch, On the distribution of the number of successes in independent
trials, Annals of Mathematical Statistics 35 (1964), 1317--1321.
The proof here uses a direct log-concavity and deletion-counting argument.
-/

namespace List

/-- Coefficients of the product of the linear factors, extended by zero to negative degrees. -/
noncomputable def oddsCoeff : List Real -> Int -> Real
  | [], k => if k = 0 then 1 else 0
  | a :: s, k => oddsCoeff s k + a * oddsCoeff s (k - 1)

/-- Nonnegative weights give nonnegative coefficients. -/
theorem oddsCoeff_nonneg (s : List Real) (hs : forall a, Membership.mem s a -> 0 <= a)
    (k : Int) : 0 <= oddsCoeff s k := by
  induction s generalizing k with
  | nil => simp only [oddsCoeff]; split <;> norm_num
  | cons a s ih =>
    have ha := hs a (by simp)
    have ht : forall b, Membership.mem s b -> 0 <= b := fun b hb => hs b (by simp [hb])
    exact add_nonneg (ih ht k) (mul_nonneg ha (ih ht (k - 1)))

/-- Coefficients vanish in negative degrees. -/
theorem oddsCoeff_neg (s : List Real) (k : Int) (hk : k < 0) :
    oddsCoeff s k = 0 := by
  induction s generalizing k with
  | nil => simp [oddsCoeff, ne_of_lt hk]
  | cons a s ih => simp [oddsCoeff, ih k hk, ih (k - 1) (by omega)]

/-- The constant coefficient is one. -/
theorem oddsCoeff_zero (s : List Real) : oddsCoeff s 0 = 1 := by
  induction s with
  | nil => simp [oddsCoeff]
  | cons a s ih => simp [oddsCoeff, ih, oddsCoeff_neg s (-1) (by omega)]

/-- Positive weights give a positive coefficient in every supported degree. -/
theorem oddsCoeff_pos (s : List Real) (hs : forall a, Membership.mem s a -> 0 < a)
    (k : Int) (hk : 0 <= k) (hkn : k <= s.length) : 0 < oddsCoeff s k := by
  induction s generalizing k with
  | nil =>
    have hkn' : k <= 0 := by simpa using hkn
    have heq : k = 0 := le_antisymm hkn' hk
    subst k
    simp [oddsCoeff]
  | cons a s ih =>
    by_cases hz : k = 0
    case pos => subst k; rw [oddsCoeff_zero]; norm_num
    have ha := hs a (by simp)
    have ht : forall b, Membership.mem s b -> 0 < b := fun b hb => hs b (by simp [hb])
    have ht0 : forall b, Membership.mem s b -> 0 <= b := fun b hb => (ht b hb).le
    exact add_pos_of_nonneg_of_pos (oddsCoeff_nonneg s ht0 k)
      (mul_pos ha (ih ht (k - 1) (by omega) (by simp at hkn; omega)))

/-- Adjacent coefficient ratios decrease with the degree, including across the support boundary. -/
theorem oddsCoeff_logConcave (s : List Real)
    (hs : forall a, Membership.mem s a -> 0 <= a) (i j : Int) (hij : i <= j) :
    oddsCoeff s (i - 1) * oddsCoeff s (j + 1) <= oddsCoeff s i * oddsCoeff s j := by
  induction s generalizing i j with
  | nil =>
    by_cases hi : i - 1 = 0
    case pos =>
      have hj : Not (j + 1 = 0) := by omega
      have hi' : i = 1 := by omega
      subst i
      simp [oddsCoeff, hj]
    case neg =>
      by_cases hki : i = 0 <;> by_cases hkj : j = 0 <;>
        simp [oddsCoeff, hi, hki, hkj]
  | cons a s ih =>
    have ha := hs a (by simp)
    have ht : forall b, Membership.mem s b -> 0 <= b := fun b hb => hs b (by simp [hb])
    have h0 := ih ht i j hij
    have h2 := ih ht (i - 1) (j - 1) (by omega)
    have hm : oddsCoeff s (i - 2) * oddsCoeff s (j + 1) <=
        oddsCoeff s i * oddsCoeff s (j - 1) := by
      by_cases heq : i = j
      case pos =>
        subst j
        simpa [sub_sub, mul_comm] using ih ht (i - 1) i (by omega)
      case neg =>
        have hm0 := ih ht i (j - 1) (by omega)
        have hm1 := ih ht (i - 1) j (by omega)
        simpa [sub_sub] using hm1.trans (by simpa using hm0)
    have hm' := mul_le_mul_of_nonneg_left hm ha
    have h2' := mul_le_mul_of_nonneg_left h2 (sq_nonneg a)
    simp only [show i - 1 - 1 = i - 2 by omega,
      show j - 1 + 1 = j by omega] at h2'
    simp only [oddsCoeff, show j + 1 - 1 = j by omega,
      show i - 1 - 1 = i - 2 by omega]
    nlinarith only [h0, hm', h2']


/-- Each entry records one distinguished weight and the list left after deleting it. -/
def oddsDeletions : List Real -> List (Prod Real (List Real))
  | [] => []
  | a :: s => (a, s) :: (oddsDeletions s).map (fun x => (x.1, a :: x.2))

/-- The distinguished weights in the deletion list recover the original list. -/
theorem oddsDeletions_map_fst (s : List Real) :
    (oddsDeletions s).map Prod.fst = s := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [oddsDeletions, map_map, Function.comp_def, ih]

/-- Reinsert the distinguished weight in the coefficient recursion. -/
theorem oddsDeletions_reconstruct (s : List Real) (a : Real) (u : List Real)
    (h : Membership.mem (oddsDeletions s) (a, u)) (k : Int) :
    oddsCoeff s k = oddsCoeff u k + a * oddsCoeff u (k - 1) := by
  induction s generalizing a u k with
  | nil => simp [oddsDeletions] at h
  | cons b s ih =>
    simp only [oddsDeletions, mem_cons, mem_map] at h
    cases h with
    | inl h => cases h; rfl
    | inr h =>
      cases h with
      | intro x hx =>
        cases x with
        | mk c v =>
          have heq := hx.2
          cases heq
          simp only [oddsCoeff]
          rw [ih c v hx.1 k, ih c v hx.1 (k - 1)]
          ring

/-- Deletion preserves positivity of all retained weights. -/
theorem oddsDeletions_pos (s : List Real)
    (hs : forall a, Membership.mem s a -> 0 < a) (a : Real) (u : List Real)
    (h : Membership.mem (oddsDeletions s) (a, u)) :
    And (0 < a) (forall b, Membership.mem u b -> 0 < b) := by
  induction s generalizing a u with
  | nil => simp [oddsDeletions] at h
  | cons b s ih =>
    have hb := hs b (by simp)
    have ht : forall c, Membership.mem s c -> 0 < c := fun c hc => hs c (by simp [hc])
    simp only [oddsDeletions, mem_cons, mem_map] at h
    cases h with
    | inl h => cases h; exact And.intro hb ht
    | inr h =>
      cases h with
      | intro x hx =>
        cases x with
        | mk c v =>
          have heq := hx.2
          cases heq
          have hp := ih ht c v hx.1
          refine And.intro hp.1 ?_
          intro d hd
          rcases mem_cons.mp hd with hd | hd
          case inl => subst d; exact hb
          case inr => exact hp.2 d hd

/-- Counting a distinguished selected variable multiplies a coefficient by its degree. -/
theorem oddsDeletions_weighted_sum (s : List Real) (k : Int) :
    ((oddsDeletions s).map (fun x => x.1 * oddsCoeff x.2 (k - 1))).sum =
      (k : Real) * oddsCoeff s k := by
  induction s generalizing k with
  | nil =>
    by_cases hk : k = 0 <;> simp [oddsDeletions, oddsCoeff, hk]
  | cons a s ih =>
    simp only [oddsDeletions, map_cons, sum_cons, map_map, Function.comp_def,
      oddsCoeff]
    have heq : (fun x : Prod Real (List Real) =>
        x.1 * (oddsCoeff x.2 (k - 1) + a * oddsCoeff x.2 (k - 1 - 1))) =
      (fun x => x.1 * oddsCoeff x.2 (k - 1) +
        a * (x.1 * oddsCoeff x.2 (k - 1 - 1))) := by
      funext x
      ring
    rw [heq, sum_map_add, sum_map_mul_left, ih k, ih (k - 1)]
    push_cast
    ring


/-- Adding a positive variable cannot decrease the adjacent coefficient ratio. -/
theorem oddsCoeff_deleted_le_prev (s : List Real)
    (hs : forall b, Membership.mem s b -> 0 < b) (a : Real) (u : List Real)
    (hmem : Membership.mem (oddsDeletions s) (a, u)) (k : Int)
    (hparent : oddsCoeff s k <= oddsCoeff s (k - 1)) :
    oddsCoeff u k <= oddsCoeff u (k - 1) := by
  have hp := oddsDeletions_pos s hs a u hmem
  have hu : forall b, Membership.mem u b -> 0 <= b := fun b hb => (hp.2 b hb).le
  have hy := oddsCoeff_nonneg u hu (k - 1)
  have hlc := oddsCoeff_logConcave u hu (k - 1) (k - 1) le_rfl
  simp only [show k - 1 + 1 = k by omega] at hlc
  rw [oddsDeletions_reconstruct s a u hmem k,
    oddsDeletions_reconstruct s a u hmem (k - 1)] at hparent
  by_contra hnot
  have hyz : oddsCoeff u (k - 1) < oddsCoeff u k := lt_of_not_ge hnot
  have hxy : oddsCoeff u (k - 1 - 1) <= oddsCoeff u (k - 1) := by
    by_contra hnot'
    have hxy' : oddsCoeff u (k - 1) < oddsCoeff u (k - 1 - 1) :=
      lt_of_not_ge hnot'
    have hz : 0 < oddsCoeff u k := hy.trans_lt hyz
    have hpos := mul_pos (sub_pos.mpr hxy') hz
    have hnonneg := mul_nonneg hy (sub_nonneg.mpr hyz.le)
    nlinarith only [hlc, hpos, hnonneg]
  have hscaled := mul_le_mul_of_nonneg_left hxy hp.1.le
  linarith

/-- Mean of the Bernoulli probabilities associated to the odds weights. -/
noncomputable def oddsMean (s : List Real) : Real :=
  (s.map (fun a => a / (1 + a))).sum

/-- The odds mean does not exceed the number of variables. -/
theorem oddsMean_le_length (s : List Real) (hs : forall a, Membership.mem s a -> 0 < a) :
    oddsMean s <= s.length := by
  induction s with
  | nil => simp [oddsMean]
  | cons a s ih =>
    have ha := hs a (by simp)
    have ht : forall b, Membership.mem s b -> 0 < b := fun b hb => hs b (by simp [hb])
    have hfrac : a / (1 + a) < 1 := (div_lt_one (by linarith)).2 (by linarith)
    simp only [oddsMean, map_cons, sum_cons, length_cons, Nat.cast_add,
      Nat.cast_one] at *
    linarith [ih ht]

/-- The strict mean comparison needed for a density descent.
It has no probabilistic, prime-distribution, or asymptotic hypothesis. -/
theorem oddsCoeff_prev_lt_of_lt_mean (s : List Real)
    (hs : forall a, Membership.mem s a -> 0 < a) (k : Int) (hk : 0 <= k)
    (hmean : (k : Real) < oddsMean s) :
    oddsCoeff s (k - 1) < oddsCoeff s k := by
  have hknReal : (k : Real) < (s.length : Real) :=
    hmean.trans_le (oddsMean_le_length s hs)
  have hkn : k <= (s.length : Int) := (by exact_mod_cast hknReal : k < s.length).le
  have hc := oddsCoeff_pos s hs k hk hkn
  by_contra hnot
  have hparent : oddsCoeff s k <= oddsCoeff s (k - 1) := le_of_not_gt hnot
  have hterm : forall x, Membership.mem (oddsDeletions s) x ->
      (x.1 / (1 + x.1)) * oddsCoeff s k <=
        x.1 * oddsCoeff x.2 (k - 1) := by
    intro x hx
    cases x with
    | mk a u =>
      have hp := oddsDeletions_pos s hs a u hx
      have hu := oddsCoeff_deleted_le_prev s hs a u hx k hparent
      have hbound : oddsCoeff s k <= (1 + a) * oddsCoeff u (k - 1) := by
        rw [oddsDeletions_reconstruct s a u hx k]
        nlinarith only [hu]
      have hd : 0 < 1 + a := by linarith [hp.1]
      have heq : oddsCoeff s k / (1 + a) * (1 + a) = oddsCoeff s k := by
        field_simp
      have hdiv : oddsCoeff s k / (1 + a) <= oddsCoeff u (k - 1) :=
        le_of_mul_le_mul_right (by nlinarith only [heq, hbound]) hd
      have hmul := mul_le_mul_of_nonneg_left hdiv hp.1.le
      convert hmul using 1; ring
  have sumMono : forall d : List (Prod Real (List Real)),
      (forall x, Membership.mem d x ->
        (x.1 / (1 + x.1)) * oddsCoeff s k <=
          x.1 * oddsCoeff x.2 (k - 1)) ->
      (d.map (fun x => (x.1 / (1 + x.1)) * oddsCoeff s k)).sum <=
        (d.map (fun x => x.1 * oddsCoeff x.2 (k - 1))).sum := by
    intro d
    induction d with
    | nil => intro hd; simp
    | cons x d ih =>
      intro hd
      simp only [map_cons, sum_cons]
      exact add_le_add (hd x (by simp)) (ih (fun y hy => hd y (by simp [hy])))
  have hsum := sumMono (oddsDeletions s) hterm
  rw [sum_map_mul_right, oddsDeletions_weighted_sum] at hsum
  have hm : ((oddsDeletions s).map (fun x => x.1 / (1 + x.1))).sum = oddsMean s := by
    simpa only [oddsMean, map_map, Function.comp_def] using
      congrArg (fun l : List Real => (l.map (fun a => a / (1 + a))).sum)
        (oddsDeletions_map_fst s)
  rw [hm] at hsum
  exact (not_le_of_gt (mul_lt_mul_of_pos_right hmean hc)) hsum


private theorem oddsEsymm_cons_succ (a : Real) (s : Multiset Real) (n : Nat) :
    (Multiset.cons a s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]

/-- The coefficient recursion agrees with Mathlib's elementary symmetric sum. -/
theorem oddsCoeff_nat_eq_esymm (s : List Real) (n : Nat) :
    oddsCoeff s (n : Int) = (s : Multiset Real).esymm n := by
  induction s generalizing n with
  | nil =>
    cases n with
    | zero => simp [oddsCoeff]
    | succ n =>
      rw [oddsCoeff]
      simp only [Int.natCast_eq_zero, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, ite_false]
      symm
      exact Multiset.esymm_of_card_lt (by simp)
  | cons a s ih =>
    cases n with
    | zero => simp [oddsCoeff_zero]
    | succ n =>
      have hk : ((n + 1 : Nat) : Int) - 1 = (n : Int) := by omega
      rw [oddsCoeff, hk, ih (n + 1), ih n]
      change (s : Multiset Real).esymm (n + 1) +
        a * (s : Multiset Real).esymm n =
        (Multiset.cons a (s : Multiset Real)).esymm (n + 1)
      exact (oddsEsymm_cons_succ a (s : Multiset Real) n).symm

/-- A tilted mean larger than the degree gives a strict upper ratio estimate. -/
theorem esymm_prev_lt_mul_of_lt_oddsMean (s : List Real)
    (hs : forall a, Membership.mem s a -> 0 < a)
    (t : Real) (ht : 0 < t) (r : Nat) (hr : 1 <= r)
    (hmean : (r : Real) < oddsMean (s.map (fun a => t * a))) :
    (s : Multiset Real).esymm (r - 1) < t * (s : Multiset Real).esymm r := by
  have hs' : forall a, Membership.mem (s.map (fun b => t * b)) a -> 0 < a := by
    intro a ha
    simp only [mem_map] at ha
    cases ha with
    | intro b hb =>
      rw [<- hb.2]
      exact mul_pos ht (hs b hb.1)
  have hm : ((r : Int) : Real) < oddsMean (s.map (fun a => t * a)) := by
    simpa using hmean
  have hc := oddsCoeff_prev_lt_of_lt_mean _ hs' (r : Int) (by omega) hm
  have hrInt : (r : Int) - 1 = ((r - 1 : Nat) : Int) := by omega
  rw [hrInt, oddsCoeff_nat_eq_esymm, oddsCoeff_nat_eq_esymm] at hc
  have scale (n : Nat) : ((s.map (fun a => t * a)) : Multiset Real).esymm n =
      t ^ n * (s : Multiset Real).esymm n := by
    simpa only [smul_eq_mul, Multiset.map_coe] using
      (Multiset.pow_smul_esymm t n (s : Multiset Real)).symm
  rw [scale, scale] at hc
  have hr' : r - 1 + 1 = r := by omega
  have hp : t ^ r = t ^ (r - 1) * t := by
    simpa only [hr'] using pow_succ t (r - 1)
  rw [hp] at hc
  have hc' : t ^ (r - 1) * (s : Multiset Real).esymm (r - 1) <
      t ^ (r - 1) * (t * (s : Multiset Real).esymm r) := by
    nlinarith only [hc]
  by_contra hnot
  have hle := mul_le_mul_of_nonneg_left (le_of_not_gt hnot) (pow_pos ht (r - 1)).le
  exact (not_lt_of_ge hle) hc'

end List
