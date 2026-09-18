import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.PrimeCounting
import PrimeFactorUnimodality.Helpers.PrimeSequence.Consecutive
import PrimeFactorUnimodality.Helpers.PrimeSequence.Predecessor

set_option autoImplicit false

/-! # Composite blocks from finite congruence covers -/

namespace PrimeFactorUnimodality

/-- The canonical natural representative of `-c` modulo `p`. -/
def negResidue (p c : Nat) : Nat := (p - c % p) % p

theorem negResidue_add_dvd {p c m : Nat} (hp : p ≠ 0)
    (hmc : m ≡ c [MOD p]) : p ∣ negResidue p c + m := by
  rw [← Nat.modEq_zero_iff_dvd]
  rw [Nat.ModEq] at hmc ⊢
  rw [Nat.add_mod, hmc]
  let r := c % p
  have hr : r < p := Nat.mod_lt c (Nat.pos_of_ne_zero hp)
  by_cases hr0 : r = 0
  · simp [negResidue, r, hr0]
  · have hsub : p - r < p := by omega
    rw [negResidue, show c % p = r by rfl, Nat.mod_eq_of_lt hsub]
    simp [Nat.sub_add_cancel (Nat.le_of_lt hr)]

/-- Residues used by the symmetric covering construction around two
consecutive primes `qPrev < q`. -/
def symmetricCoverValue (qPrev _q p : Nat) : Nat :=
  if p < qPrev then qPrev else if p = qPrev then qPrev - 1 else qPrev + 1

/-- Every offset from `1` through `2*qPrev-1` is congruent to one of the
symmetric covering values modulo a prime at most `q`. -/
theorem symmetric_prime_residue_cover {qPrev q : Nat}
    (consecutive : ConsecutivePrimes qPrev q) (qPrev_gt_two : 2 < qPrev) :
    ∀ m, 1 ≤ m → m ≤ 2 * qPrev - 1 →
      ∃ p ∈ Nat.primesLE q, p ≠ 0 ∧
        m ≡ symmetricCoverValue qPrev q p [MOD p] := by
  intro m hmFirst hmLast
  by_cases hleft : m ≤ qPrev - 2
  · have diff_ge_two : 2 ≤ qPrev - m := by omega
    obtain ⟨p, p_prime, p_dvd⟩ := Nat.exists_prime_and_dvd (by omega : qPrev - m ≠ 1)
    have p_le_diff : p ≤ qPrev - m := Nat.le_of_dvd (by omega) p_dvd
    have p_lt_prev : p < qPrev := by omega
    refine ⟨p, (Nat.mem_primesLE.mpr ⟨p_le_diff.trans (Nat.sub_le qPrev m) |>.trans
      (Nat.le_of_lt consecutive.left_lt_right), p_prime⟩), p_prime.ne_zero, ?_⟩
    simpa [symmetricCoverValue, p_lt_prev] using
      (Nat.modEq_iff_dvd' (by omega : m ≤ qPrev)).2 p_dvd
  by_cases hmPrevOne : m = qPrev - 1
  · subst m
    refine ⟨qPrev, Nat.mem_primesLE.mpr ⟨Nat.le_of_lt consecutive.left_lt_right,
      consecutive.left_prime⟩, consecutive.left_prime.ne_zero, ?_⟩
    simpa only [symmetricCoverValue, lt_self_iff_false, ↓reduceIte] using
      (Nat.ModEq.refl (qPrev - 1) : qPrev - 1 ≡ qPrev - 1 [MOD qPrev])
  by_cases hmPrev : m = qPrev
  · subst m
    refine ⟨2, Nat.mem_primesLE.mpr ⟨(qPrev_gt_two.le.trans
      (Nat.le_of_lt consecutive.left_lt_right)), Nat.prime_two⟩, by norm_num, ?_⟩
    simpa only [symmetricCoverValue, qPrev_gt_two, ↓reduceIte] using
      (Nat.ModEq.refl qPrev : qPrev ≡ qPrev [MOD 2])
  by_cases hmNext : m = qPrev + 1
  · subst m
    refine ⟨q, Nat.mem_primesLE.mpr ⟨le_rfl, consecutive.right_prime⟩,
      consecutive.right_prime.ne_zero, ?_⟩
    have q_not_lt : ¬q < qPrev := Nat.not_lt_of_ge consecutive.left_lt_right.le
    have q_ne : q ≠ qPrev := consecutive.left_lt_right.ne'
    simpa only [symmetricCoverValue, q_not_lt, q_ne, ↓reduceIte] using
      (Nat.ModEq.refl (qPrev + 1) : qPrev + 1 ≡ qPrev + 1 [MOD q])
  · have diff_ge_two : 2 ≤ m - qPrev := by omega
    have diff_lt_prev : m - qPrev < qPrev := by omega
    obtain ⟨p, p_prime, p_dvd⟩ := Nat.exists_prime_and_dvd (by omega : m - qPrev ≠ 1)
    have p_le_diff : p ≤ m - qPrev := Nat.le_of_dvd (by omega) p_dvd
    have p_lt_prev : p < qPrev := p_le_diff.trans_lt diff_lt_prev
    refine ⟨p, Nat.mem_primesLE.mpr ⟨(p_lt_prev.trans consecutive.left_lt_right).le,
      p_prime⟩, p_prime.ne_zero, ?_⟩
    simpa [symmetricCoverValue, p_lt_prev] using
      ((Nat.modEq_iff_dvd' (by omega : qPrev ≤ m)).2 p_dvd).symm

/-- A finite family of pairwise-coprime moduli whose prescribed residues cover
an interval can be shifted simultaneously by the Chinese remainder theorem.
This is the reusable exact core of the uniform large-gap construction. -/
theorem exists_shift_of_congruence_cover
    (moduli : Finset Nat) (residue : Nat → Nat)
    (nonzero : ∀ p ∈ moduli, p ≠ 0)
    (pairwise : Set.Pairwise moduli Nat.Coprime)
    (first last : Nat)
    (cover : ∀ m, first ≤ m → m ≤ last →
      ∃ p ∈ moduli, p ∣ residue p + m) :
    ∃ a < ∏ p ∈ moduli, p,
      ∀ m, first ≤ m → m ≤ last → ∃ p ∈ moduli, p ∣ a + m := by
  let crt := Nat.chineseRemainderOfFinset residue id moduli nonzero pairwise
  refine ⟨crt, Nat.chineseRemainderOfFinset_lt_prod residue id nonzero pairwise, ?_⟩
  intro m hmFirst hmLast
  obtain ⟨p, hp, hpDiv⟩ := cover m hmFirst hmLast
  refine ⟨p, hp, ?_⟩
  have hmod : (crt : Nat) ≡ residue p [MOD p] := crt.property p hp
  exact Nat.modEq_zero_iff_dvd.mp
    ((hmod.add_right m).trans hpDiv.modEq_zero_nat)

/-- Adding a common multiple of every covering modulus preserves a CRT
composite block.  The strict size hypothesis makes each supplied divisor
proper, so no primality assumption is smuggled into the construction. -/
theorem not_prime_block_of_shifted_congruence_cover
    (moduli : Finset Nat) (residue : Nat → Nat)
    (nonzero : ∀ p ∈ moduli, p ≠ 0)
    (pairwise : Set.Pairwise moduli Nat.Coprime)
    (first last base : Nat)
    (cover : ∀ m, first ≤ m → m ≤ last →
      ∃ p ∈ moduli, p ∣ residue p + m)
    (baseMultiple : ∀ p ∈ moduli, p ∣ base)
    (nontrivial : ∀ p ∈ moduli, 2 ≤ p)
    (proper : ∀ a, a < ∏ p ∈ moduli, p →
      ∀ m, first ≤ m → m ≤ last →
        ∀ p ∈ moduli, p < a + base + m) :
    ∃ a < ∏ p ∈ moduli, p,
      ∀ m, first ≤ m → m ≤ last → ¬(a + base + m).Prime := by
  obtain ⟨a, ha, hcover⟩ :=
    exists_shift_of_congruence_cover moduli residue nonzero pairwise first last cover
  refine ⟨a, ha, ?_⟩
  intro m hmFirst hmLast
  obtain ⟨p, hp, hpDiv⟩ := hcover m hmFirst hmLast
  have p_dvd : p ∣ a + base + m := by
    obtain ⟨u, hu⟩ := hpDiv
    obtain ⟨v, hv⟩ := baseMultiple p hp
    refine ⟨u + v, ?_⟩
    calc
      a + base + m = (a + m) + base := by omega
      _ = p * u + p * v := by rw [hu, hv]
      _ = p * (u + v) := by rw [Nat.mul_add]
  exact Nat.not_prime_of_dvd_of_lt p_dvd (nontrivial p hp)
    (proper a ha m hmFirst hmLast p hp)

/-- Closed CRT shift for the symmetric prime cover. -/
theorem exists_symmetric_prime_cover_shift {qPrev q : Nat}
    (consecutive : ConsecutivePrimes qPrev q) (qPrev_gt_two : 2 < qPrev) :
    ∃ a < ∏ p ∈ Nat.primesLE q, p,
      ∀ m, 1 ≤ m → m ≤ 2 * qPrev - 1 →
        ∃ p ∈ Nat.primesLE q, p ∣ a + m := by
  let value := symmetricCoverValue qPrev q
  let residue := fun p ↦ negResidue p (value p)
  apply exists_shift_of_congruence_cover (Nat.primesLE q) residue
  · intro p hp
    exact (Nat.prime_of_mem_primesLE hp).ne_zero
  · intro p hp r hr hpr
    exact (Nat.coprime_primes (Nat.prime_of_mem_primesLE hp)
      (Nat.prime_of_mem_primesLE hr)).2 hpr
  · intro m hmFirst hmLast
    obtain ⟨p, hp, hp0, hmod⟩ :=
      symmetric_prime_residue_cover consecutive qPrev_gt_two m hmFirst hmLast
    exact ⟨p, hp, negResidue_add_dvd hp0 hmod⟩

/-- The symmetric CRT shift yields `2*qPrev-1` consecutive composites after
`2P`, where `P` is the product of the primes at most `q`. -/
theorem exists_symmetric_composite_block {qPrev q : Nat}
    (consecutive : ConsecutivePrimes qPrev q) (qPrev_gt_two : 2 < qPrev) :
    let P := ∏ p ∈ Nat.primesLE q, p
    ∃ a < P, ∀ m, 1 ≤ m → m ≤ 2 * qPrev - 1 →
      ¬(a + 2 * P + m).Prime := by
  dsimp only
  obtain ⟨a, ha, cover⟩ :=
    exists_symmetric_prime_cover_shift consecutive qPrev_gt_two
  let P := ∏ p ∈ Nat.primesLE q, p
  have P_pos : 0 < P := by
    apply Finset.prod_pos
    intro p hp
    exact (Nat.prime_of_mem_primesLE hp).pos
  have q_mem : q ∈ Nat.primesLE q :=
    Nat.mem_primesLE.mpr ⟨le_rfl, consecutive.right_prime⟩
  have q_dvd_P : q ∣ P := Finset.dvd_prod_of_mem id q_mem
  have q_le_P : q ≤ P := Nat.le_of_dvd P_pos q_dvd_P
  refine ⟨a, ha, ?_⟩
  intro m hmFirst hmLast
  obtain ⟨p, hp, p_dvd⟩ := cover m hmFirst hmLast
  have p_prime := Nat.prime_of_mem_primesLE hp
  have p_dvd_P : p ∣ P := Finset.dvd_prod_of_mem id hp
  have p_dvd_total : p ∣ a + 2 * P + m := by
    have h := Nat.dvd_add p_dvd (p_dvd_P.mul_left 2)
    simpa only [add_assoc, add_left_comm, add_comm] using h
  have p_le_q := Nat.le_of_mem_primesLE hp
  have p_lt_total : p < a + 2 * P + m := by omega
  exact Nat.not_prime_of_dvd_of_lt p_dvd_total p_prime.two_le p_lt_total

/-- The symmetric composite block is surrounded by a prime gap of length at
least `2*qPrev`; moreover, the predecessor prime lies beyond the primorial
used in the construction.  Endpoint primality certificates are unnecessary. -/
theorem exists_large_primeGap_with_predecessor_of_consecutive {qPrev q : Nat}
    (consecutive : ConsecutivePrimes qPrev q) (qPrev_gt_two : 2 < qPrev) :
    let P := ∏ p ∈ Nat.primesLE q, p
    ∃ a < P,
      2 * qPrev ≤ primeGap (Nat.primeCounting' (a + 2 * P + 1) - 1) ∧
      P < primeAt (Nat.primeCounting' (a + 2 * P + 1) - 1) := by
  dsimp only
  obtain ⟨a, ha, block⟩ :=
    exists_symmetric_composite_block consecutive qPrev_gt_two
  let P := ∏ p ∈ Nat.primesLE q, p
  have P_pos : 0 < P := by
    apply Finset.prod_pos
    intro p hp
    exact (Nat.prime_of_mem_primesLE hp).pos
  have lower_gt_two : 2 < a + 2 * P + 1 := by omega
  have lower_le_upper : a + 2 * P + 1 ≤ a + 2 * P + (2 * qPrev - 1) := by
    omega
  have gap := primeGap_ge_of_not_prime_Icc lower_gt_two lower_le_upper
    (fun n hnLower hnUpper => by
      let m := n - (a + 2 * P)
      have hmLower : 1 ≤ m := by
        dsimp only [m]
        omega
      have hmUpper : m ≤ 2 * qPrev - 1 := by
        dsimp only [m]
        omega
      have hbase : a + 2 * P ≤ n := by omega
      have hb := block m hmLower hmUpper
      change ¬(a + 2 * P + m).Prime at hb
      simpa only [m, Nat.add_sub_of_le hbase] using hb)
  refine ⟨a, ha, ?_, ?_⟩
  · have interval_length :
        (a + 2 * P + (2 * qPrev - 1)) - (a + 2 * P + 1) + 2 =
          2 * qPrev := by omega
    rwa [interval_length] at gap
  · have cutoffNotPrime : ¬(a + 2 * P + 1).Prime := by
      exact block 1 (by omega) (by omega)
    have q_mem : q ∈ Nat.primesLE q :=
      Nat.mem_primesLE.mpr ⟨le_rfl, consecutive.right_prime⟩
    have q_dvd_P : q ∣ P := Finset.dvd_prod_of_mem id q_mem
    have q_le_P : q ≤ P := Nat.le_of_dvd P_pos q_dvd_P
    have P_ge_four : 4 ≤ P := by
      have := consecutive.left_lt_right
      omega
    have predecessorHalf := primeAt_primeCounting_sub_one_gt_half
      (show 4 ≤ a + 2 * P + 1 by omega) cutoffNotPrime
    have P_le_half : P ≤ (a + 2 * P + 1) / 2 := by omega
    exact P_le_half.trans_lt predecessorHalf

/-- Gap-only projection of
`exists_large_primeGap_with_predecessor_of_consecutive`. -/
theorem exists_large_primeGap_of_consecutive {qPrev q : Nat}
    (consecutive : ConsecutivePrimes qPrev q) (qPrev_gt_two : 2 < qPrev) :
    let P := ∏ p ∈ Nat.primesLE q, p
    ∃ a < P,
      2 * qPrev ≤ primeGap (Nat.primeCounting' (a + 2 * P + 1) - 1) := by
  obtain ⟨a, ha, gap, _predecessor⟩ :=
    exists_large_primeGap_with_predecessor_of_consecutive consecutive qPrev_gt_two
  exact ⟨a, ha, gap⟩

end PrimeFactorUnimodality
