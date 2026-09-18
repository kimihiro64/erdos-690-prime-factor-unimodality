import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.PrimeCounting
import PrimeFactorUnimodality.Definitions.SymmetricDensity
import PrimeFactorUnimodality.Helpers.PrimeSequence.Basic
import PrimeFactorUnimodality.Helpers.PrimeSequence.InitialSegment
import PrimeFactorUnimodality.Helpers.SymmetricBounds.Main

set_option autoImplicit false

/-! # Real-valued reciprocal prime weights -/

namespace PrimeFactorUnimodality

noncomputable section

/-- The real form of the weight `1 / (p - 1)` used by the density-ratio
bounds. -/
def realPrimeWeight (p : Nat) : Real := 1 / ((p - 1 : Nat) : Real)

/-- A real-valued weight sum over an arbitrary list. -/
def realWeightSum (entries : List Nat) : Real :=
  (entries.map realPrimeWeight).sum

theorem ratCast_primeWeight (p : Nat) :
    ((primeWeight p : Rat) : Real) = realPrimeWeight p := by
  simp [primeWeight, realPrimeWeight]

theorem ratCast_weightSum (entries : List Nat) :
    ((weightSum entries : Rat) : Real) = realWeightSum entries := by
  induction entries with
  | nil => simp [weightSum, realWeightSum]
  | cons p entries ih =>
      simp only [weightSum, realWeightSum, List.map_cons, List.sum_cons,
        Rat.cast_add]
      rw [ratCast_primeWeight]
      change realPrimeWeight p + ((weightSum entries : Rat) : Real) =
        realPrimeWeight p + realWeightSum entries
      rw [ih]

theorem weightSum_le_iff_realWeightSum_le (entries : List Nat) (c : Rat) :
    weightSum entries ≤ c ↔ realWeightSum entries ≤ (c : Real) := by
  rw [← ratCast_weightSum]
  exact_mod_cast Iff.rfl

theorem weightSum_lt_iff_realWeightSum_lt (entries : List Nat) (c : Rat) :
    weightSum entries < c ↔ realWeightSum entries < (c : Real) := by
  rw [← ratCast_weightSum]
  exact_mod_cast Iff.rfl

/-- The real sum of reciprocal prime weights below a natural cutoff. -/
def primeWeightSumBelow (x : Nat) : Real :=
  realWeightSum (primesBelow x)

/-- Primes in the half-open natural interval `(a, b]`. -/
def primesIoc (a b : Nat) : Finset Nat :=
  (Nat.primesBelow (b + 1)).filter fun p => a < p

@[simp]
theorem mem_primesIoc {a b p : Nat} :
    p ∈ primesIoc a b ↔ p.Prime ∧ a < p ∧ p ≤ b := by
  simp only [primesIoc, Finset.mem_filter, Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨p_lt, p_prime⟩, a_lt⟩
    exact ⟨p_prime, a_lt, by omega⟩
  · rintro ⟨p_prime, a_lt, p_le⟩
    exact ⟨⟨by omega, p_prime⟩, a_lt⟩

theorem ratCast_weightSum_primesBelow (x : Nat) :
    ((weightSum (primesBelow x) : Rat) : Real) = primeWeightSumBelow x := by
  exact ratCast_weightSum (primesBelow x)

theorem primeWeightSumBelow_eq_finset (x : Nat) :
    primeWeightSumBelow x =
      ∑ p ∈ Nat.primesBelow x, (1 / ((p - 1 : Nat) : Real)) := by
  change (List.map realPrimeWeight ((Nat.primesBelow x).sort (fun a b => a ≤ b))).sum =
    ∑ p ∈ Nat.primesBelow x, realPrimeWeight p
  change
    (Multiset.map realPrimeWeight
      (↑((Nat.primesBelow x).sort (fun a b => a ≤ b)) : Multiset Nat)).sum =
      (Multiset.map realPrimeWeight (Nat.primesBelow x).val).sum
  rw [Finset.sort_eq]

theorem realPrimeWeight_nonneg (p : Nat) : 0 ≤ realPrimeWeight p := by
  exact one_div_nonneg.mpr (by positivity)

theorem realWeightSum_nonneg (entries : List Nat) : 0 ≤ realWeightSum entries := by
  induction entries with
  | nil => simp [realWeightSum]
  | cons p entries ih =>
      simp only [realWeightSum, List.map_cons, List.sum_cons] at ih ⊢
      exact add_nonneg (realPrimeWeight_nonneg p) ih

theorem primeWeightSumBelow_nonneg (x : Nat) : 0 ≤ primeWeightSumBelow x := by
  exact realWeightSum_nonneg (primesBelow x)

/-- A finite set of primes bounded by `bound` contributes at least its
cardinality divided by `bound - 1` to the reciprocal-weight sum. -/
theorem card_div_le_sum_realPrimeWeight (s : Finset Nat) (bound : Nat)
    (prime_mem : ∀ p ∈ s, p.Prime) (le_bound : ∀ p ∈ s, p ≤ bound) :
    (s.card : Real) / ((bound - 1 : Nat) : Real) ≤
      ∑ p ∈ s, realPrimeWeight p := by
  calc
    (s.card : Real) / ((bound - 1 : Nat) : Real) =
        ∑ _p ∈ s, (1 / ((bound - 1 : Nat) : Real)) := by
      simp [div_eq_mul_inv]
    _ ≤ ∑ p ∈ s, realPrimeWeight p := by
      apply Finset.sum_le_sum
      intro p p_mem
      rw [realPrimeWeight]
      have p_gt_one : 1 < p := (prime_mem p p_mem).one_lt
      apply one_div_le_one_div_of_le
      · exact_mod_cast Nat.sub_pos_of_lt p_gt_one
      · exact_mod_cast Nat.sub_le_sub_right (le_bound p p_mem) 1

/-- A finite set of primes all at least `lower` contributes at most its
cardinality divided by `lower - 1`. -/
theorem sum_realPrimeWeight_le_card_div (s : Finset Nat) (lower : Nat)
    (lower_gt_one : 1 < lower) (lower_le : ∀ p ∈ s, lower ≤ p) :
    (∑ p ∈ s, realPrimeWeight p) ≤
      (s.card : Real) / ((lower - 1 : Nat) : Real) := by
  calc
    (∑ p ∈ s, realPrimeWeight p) ≤
        ∑ _p ∈ s, (1 / ((lower - 1 : Nat) : Real)) := by
      apply Finset.sum_le_sum
      intro p p_mem
      rw [realPrimeWeight]
      apply one_div_le_one_div_of_le
      · exact_mod_cast Nat.sub_pos_of_lt lower_gt_one
      · exact_mod_cast Nat.sub_le_sub_right (lower_le p p_mem) 1
    _ = (s.card : Real) / ((lower - 1 : Nat) : Real) := by
      simp [div_eq_mul_inv]

theorem primesIoc_prime {a b p : Nat} (hp : p ∈ primesIoc a b) : p.Prime := by
  exact (mem_primesIoc.mp hp).1

theorem primesIoc_lower {a b p : Nat} (hp : p ∈ primesIoc a b) : a < p :=
  (mem_primesIoc.mp hp).2.1

theorem primesIoc_upper {a b p : Nat} (hp : p ∈ primesIoc a b) : p ≤ b := by
  exact (mem_primesIoc.mp hp).2.2

theorem card_primesIoc (a b : Nat) (hab : a ≤ b) :
    (primesIoc a b).card =
      Nat.primeCounting' (b + 1) - Nat.primeCounting' (a + 1) := by
  have subset : Nat.primesBelow (a + 1) ⊆ Nat.primesBelow (b + 1) := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨hp.1.trans_le (Nat.add_le_add_right hab 1), hp.2⟩
  have shell_eq :
      primesIoc a b = Nat.primesBelow (b + 1) \ Nat.primesBelow (a + 1) := by
    ext p
    simp only [mem_primesIoc, Nat.mem_primesBelow, Finset.mem_sdiff]
    constructor
    · rintro ⟨p_prime, a_lt, p_le⟩
      exact ⟨⟨by omega, p_prime⟩, fun hp => by omega⟩
    · rintro ⟨⟨p_lt, p_prime⟩, hp⟩
      exact ⟨p_prime, by
        by_contra not_lt
        exact hp ⟨by omega, p_prime⟩, by omega⟩
  rw [shell_eq, Finset.card_sdiff_of_subset subset,
    Nat.primesBelow_card_eq_primeCounting',
    Nat.primesBelow_card_eq_primeCounting']

theorem card_primesIoc_div_le_sum (a b : Nat) :
    ((primesIoc a b).card : Real) / ((b - 1 : Nat) : Real) ≤
      ∑ p ∈ primesIoc a b, realPrimeWeight p := by
  exact card_div_le_sum_realPrimeWeight (primesIoc a b) b
    (fun p hp => primesIoc_prime hp) (fun p hp => primesIoc_upper hp)

theorem sum_primesIoc_le_card_div (a b : Nat) (a_pos : 0 < a) :
    (∑ p ∈ primesIoc a b, realPrimeWeight p) ≤
      ((primesIoc a b).card : Real) / (a : Real) := by
  simpa only [show a + 1 - 1 = a by omega] using
    sum_realPrimeWeight_le_card_div (primesIoc a b) (a + 1) (by omega)
      (fun _p hp => Nat.succ_le_iff.mpr (primesIoc_lower hp))

theorem sum_primesIoc_le_primeWeightSumBelow {a b x : Nat} (hb : b < x) :
    (∑ p ∈ primesIoc a b, realPrimeWeight p) ≤ primeWeightSumBelow x := by
  rw [primeWeightSumBelow_eq_finset]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rw [Nat.mem_primesBelow]
    exact ⟨(primesIoc_upper hp).trans_lt hb, primesIoc_prime hp⟩
  · intro p _ _
    exact realPrimeWeight_nonneg p

theorem primeWeightSumBelow_mono : Monotone primeWeightSumBelow := by
  intro x y hxy
  rw [primeWeightSumBelow_eq_finset, primeWeightSumBelow_eq_finset]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simpa only [Nat.mem_primesBelow] using
      ⟨(Nat.mem_primesBelow.mp hp).1.trans_le hxy, (Nat.mem_primesBelow.mp hp).2⟩
  · intro p _ _
    exact one_div_nonneg.mpr (by positivity)

/-- The usual reciprocal-prime sum over primes strictly below `x`. -/
def reciprocalPrimeSumBelow (x : Nat) : Real :=
  ∑ p ∈ Nat.primesBelow x, 1 / (p : Real)

theorem reciprocalPrimeSumBelow_succ_eq (x : Nat) :
    reciprocalPrimeSumBelow (x + 1) =
      ∑ p ∈ Finset.Ioc 0 x with p.Prime, 1 / (p : Real) := by
  rw [reciprocalPrimeSumBelow, ← Nat.primesLE_eq_filter_Ioc_zero]
  rfl

theorem reciprocalPrimeSumBelow_mono : Monotone reciprocalPrimeSumBelow := by
  intro x y hxy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Nat.primesBelow_mono hxy
  · intro p _ _
    positivity

/-- The absolutely convergent correction taking `1/p` to `1/(p-1)`. -/
def primeWeightCorrectionBelow (x : Nat) : Real :=
  ∑ p ∈ Nat.primesBelow x,
    1 / ((p : Real) * ((p - 1 : Nat) : Real))

theorem realPrimeWeight_eq_reciprocal_add_correction {p : Nat} (hp : 1 < p) :
    realPrimeWeight p =
      1 / (p : Real) + 1 / ((p : Real) * ((p - 1 : Nat) : Real)) := by
  rw [realPrimeWeight]
  have hp0 : (p : Real) ≠ 0 := by
    exact_mod_cast (show p ≠ 0 by omega)
  have hp10 : ((p - 1 : Nat) : Real) ≠ 0 := by
    exact_mod_cast (show p - 1 ≠ 0 by omega)
  have cast_pred : ((p - 1 : Nat) : Real) = (p : Real) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    norm_num
  have cast_pred_ne : (p : Real) - 1 ≠ 0 := cast_pred ▸ hp10
  rw [cast_pred]
  field_simp [cast_pred_ne]
  ring

theorem primeWeightSumBelow_eq_reciprocal_add_correction (x : Nat) :
    primeWeightSumBelow x =
      reciprocalPrimeSumBelow x + primeWeightCorrectionBelow x := by
  rw [primeWeightSumBelow_eq_finset, reciprocalPrimeSumBelow,
    primeWeightCorrectionBelow, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  exact realPrimeWeight_eq_reciprocal_add_correction
    (Nat.one_lt_of_mem_primesBelow hp)

theorem primeWeightCorrectionBelow_nonneg (x : Nat) :
    0 ≤ primeWeightCorrectionBelow x := by
  apply Finset.sum_nonneg
  intro p _hp
  positivity

theorem primeWeightCorrectionBelow_mono : Monotone primeWeightCorrectionBelow := by
  intro x y hxy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Nat.primesBelow_mono hxy
  · intro p _ _
    positivity

/-- The elementary telescoping sum used to bound the correction term. -/
theorem sum_Ico_two_reciprocal_mul_pred (x : Nat) (hx : 2 ≤ x) :
    (∑ n ∈ Finset.Ico 2 x,
      1 / ((n : Real) * ((n - 1 : Nat) : Real))) =
        1 - 1 / ((x - 1 : Nat) : Real) := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ih]
      have hx0 : (x : Real) ≠ 0 := by exact_mod_cast (by omega : x ≠ 0)
      have hx10 : ((x - 1 : Nat) : Real) ≠ 0 := by
        exact_mod_cast (show x - 1 ≠ 0 by omega)
      have cast_pred : ((x - 1 : Nat) : Real) = (x : Real) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ x)]
        norm_num
      have cast_succ_pred : ((x + 1 - 1 : Nat) : Real) = (x : Real) := by
        norm_num
      have cast_pred_ne : (x : Real) - 1 ≠ 0 := cast_pred ▸ hx10
      rw [cast_pred, cast_succ_pred]
      field_simp [cast_pred_ne]
      ring

/-- The corresponding telescoping identity on an arbitrary tail interval. -/
theorem sum_Ico_reciprocal_mul_pred (x y : Nat) (hx : 2 ≤ x) (hxy : x ≤ y) :
    (∑ n ∈ Finset.Ico x y,
      1 / ((n : Real) * ((n - 1 : Nat) : Real))) =
        1 / ((x - 1 : Nat) : Real) -
          1 / ((y - 1 : Nat) : Real) := by
  induction y, hxy using Nat.le_induction with
  | base => simp
  | succ y hxy ih =>
      rw [Finset.sum_Ico_succ_top hxy, ih]
      have hy0 : (y : Real) ≠ 0 := by exact_mod_cast (by omega : y ≠ 0)
      have hy10 : ((y - 1 : Nat) : Real) ≠ 0 := by
        exact_mod_cast (show y - 1 ≠ 0 by omega)
      have castPred : ((y - 1 : Nat) : Real) = (y : Real) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ y)]
        norm_num
      have castSuccPred : ((y + 1 - 1 : Nat) : Real) = (y : Real) := by
        norm_num
      have castPredNe : (y : Real) - 1 ≠ 0 := castPred ▸ hy10
      rw [castPred, castSuccPred]
      field_simp [castPredNe]
      ring

theorem primeWeightCorrectionBelow_le_one (x : Nat) :
    primeWeightCorrectionBelow x ≤ 1 := by
  by_cases hx : x < 2
  · have empty : Nat.primesBelow x = ∅ := by
      ext p
      simp only [Nat.mem_primesBelow, Finset.notMem_empty, iff_false]
      rintro ⟨p_lt, p_prime⟩
      have p_two := p_prime.two_le
      omega
    rw [primeWeightCorrectionBelow, empty]
    simp
  · have hx2 : 2 ≤ x := by omega
    calc
      primeWeightCorrectionBelow x ≤
          ∑ n ∈ Finset.Ico 2 x,
            1 / ((n : Real) * ((n - 1 : Nat) : Real)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [Finset.mem_Ico]
          exact ⟨(Nat.prime_of_mem_primesBelow hp).two_le,
            Nat.lt_of_mem_primesBelow hp⟩
        · intro n _ _
          positivity
      _ = 1 - 1 / ((x - 1 : Nat) : Real) :=
        sum_Ico_two_reciprocal_mul_pred x hx2
      _ ≤ 1 := by
        have : 0 ≤ 1 / ((x - 1 : Nat) : Real) := by positivity
        linarith

/-- The correction added when moving a cutoff from `x` to `y` is bounded by
the full telescoping integer tail over the same interval. -/
theorem primeWeightCorrectionBelow_sub_le_tail
    (x y : Nat) (hx : 2 ≤ x) (hxy : x ≤ y) :
    primeWeightCorrectionBelow y - primeWeightCorrectionBelow x ≤
      1 / ((x - 1 : Nat) : Real) -
        1 / ((y - 1 : Nat) : Real) := by
  let summand : Nat → Real := fun n =>
    1 / ((n : Real) * ((n - 1 : Nat) : Real))
  have primeSubset : Nat.primesBelow x ⊆ Nat.primesBelow y :=
    Nat.primesBelow_mono hxy
  have differenceEq :
      primeWeightCorrectionBelow y - primeWeightCorrectionBelow x =
        ∑ p ∈ Nat.primesBelow y \ Nat.primesBelow x, summand p := by
    rw [primeWeightCorrectionBelow, primeWeightCorrectionBelow,
      Finset.sum_sdiff_eq_sub primeSubset]
  rw [differenceEq, ← sum_Ico_reciprocal_mul_pred x y hx hxy]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rw [Finset.mem_sdiff, Nat.mem_primesBelow, Nat.mem_primesBelow] at hp
    rw [Finset.mem_Ico]
    exact ⟨by
      by_contra notLe
      exact hp.2 ⟨by omega, hp.1.2⟩, hp.1.1⟩
  · intro n _ _
    dsimp only [summand]
    positivity

theorem reciprocalPrimeSumBelow_le_primeWeightSumBelow (x : Nat) :
    reciprocalPrimeSumBelow x ≤ primeWeightSumBelow x := by
  rw [primeWeightSumBelow_eq_reciprocal_add_correction]
  exact le_add_of_nonneg_right (primeWeightCorrectionBelow_nonneg x)

theorem primeWeightSumBelow_le_reciprocal_add_one (x : Nat) :
    primeWeightSumBelow x ≤ reciprocalPrimeSumBelow x + 1 := by
  rw [primeWeightSumBelow_eq_reciprocal_add_correction]
  simpa [add_comm] using
    add_le_add_right (primeWeightCorrectionBelow_le_one x)
      (reciprocalPrimeSumBelow x)

/-- Comparing two weight frontiers costs at most one beyond the corresponding
reciprocal-prime difference; no numerical value of the correction constant is
needed. -/
theorem reciprocal_sub_one_le_primeWeight_sub (x y : Nat) :
    reciprocalPrimeSumBelow y - reciprocalPrimeSumBelow x - 1 ≤
      primeWeightSumBelow y - primeWeightSumBelow x := by
  rw [primeWeightSumBelow_eq_reciprocal_add_correction,
    primeWeightSumBelow_eq_reciprocal_add_correction]
  have hx0 := primeWeightCorrectionBelow_nonneg x
  have hy0 := primeWeightCorrectionBelow_nonneg y
  have hx1 := primeWeightCorrectionBelow_le_one x
  linarith

theorem reciprocal_sub_le_primeWeight_sub {x y : Nat} (hxy : x ≤ y) :
    reciprocalPrimeSumBelow y - reciprocalPrimeSumBelow x ≤
      primeWeightSumBelow y - primeWeightSumBelow x := by
  rw [primeWeightSumBelow_eq_reciprocal_add_correction,
    primeWeightSumBelow_eq_reciprocal_add_correction]
  have correction := primeWeightCorrectionBelow_mono hxy
  linarith

/-- Real-valued version of the prefix sum removed by the upper symmetric
ratio estimate. -/
def realLeadingWeightSum (entries : List Nat) (n : Nat) : Real :=
  realWeightSum (entries.take n)

theorem ratCast_leadingWeightSum (entries : List Nat) (n : Nat) :
    ((leadingWeightSum entries n : Rat) : Real) =
      realLeadingWeightSum entries n := by
  rw [leadingWeightSum_eq_weightSum_take, realLeadingWeightSum,
    ratCast_weightSum]

/-- The leading `n` reciprocal weights below any later indexed prime are
exactly the full reciprocal-weight sum below the `n`-th prime. -/
theorem realLeadingWeightSum_primesBelow_primeAt
    (n i : Nat) (hni : n ≤ i) :
    realLeadingWeightSum (primesBelow (primeAt i)) n =
      primeWeightSumBelow (primeAt n) := by
  rw [realLeadingWeightSum, take_primesBelow_primeAt n i hni]
  rfl

/-- Concrete-prime form of `realLeadingWeightSum_primesBelow_primeAt`. -/
theorem realLeadingWeightSum_primesBelow_of_prime
    (p n : Nat) (hp : p.Prime) (hn : n ≤ Nat.primeCounting' p) :
    realLeadingWeightSum (primesBelow p) n =
      primeWeightSumBelow (primeAt n) := by
  rw [realLeadingWeightSum, take_primesBelow_of_prime p n hp hn]
  rfl

/-- The lower symmetric-ratio estimate transported to the reals, ready for
analytic estimates of the reciprocal-prime sum. -/
theorem real_degree_div_weightSum_le_densityRatio
    (entries : List Nat) (hentries : ∀ p ∈ entries, 1 < p)
    (r : Nat) (hr : r ≤ entries.length) (hSum : 0 < weightSum entries) :
    (r : Real) / realWeightSum entries ≤ (densityRatio entries r : Real) := by
  rw [← ratCast_weightSum]
  exact_mod_cast
    degree_div_weightSum_le_densityRatio entries hentries r hr hSum

/-- The upper symmetric-ratio estimate transported to the reals. -/
theorem real_densityRatio_le_degree_div_weightSum_sub_leading
    (entries : List Nat) (hentries : ∀ p ∈ entries, 1 < p)
    (hdescending : entries.Pairwise fun p q => primeWeight q ≤ primeWeight p)
    (r : Nat) (hrPos : 1 ≤ r) (hr : r ≤ entries.length)
    (hComplement : 0 < weightSum entries - leadingWeightSum entries (r - 1)) :
    (densityRatio entries r : Real) ≤
      (r : Real) /
        (realWeightSum entries - realLeadingWeightSum entries (r - 1)) := by
  rw [← ratCast_weightSum, ← ratCast_leadingWeightSum]
  exact_mod_cast densityRatio_le_degree_div_weightSum_sub_leading
    entries hentries hdescending r hrPos hr hComplement

end

end PrimeFactorUnimodality
