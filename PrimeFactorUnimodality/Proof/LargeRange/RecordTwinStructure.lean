import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import PrimeFactorUnimodality.LeanConfig
import PrimeFactorUnimodality.Mathlib.NumberTheory.BLSPrimality
import PrimeFactorUnimodality.Mathlib.NumberTheory.Pocklington

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option exponentiation.threshold 5000

/-!
# Algebraic structure of the record twin-prime input

This file contains no large modular residue claims. It verifies the exact
shape, factored part, size inequalities, and small-prime side conditions for
the 71,298-digit pair used in the large-range argument.  Expensive modular
replay lives in generated provider modules, so rebuilding this structural
layer never repeats a certificate computation.
-/

namespace PrimeFactorUnimodality

/-- The base whose `4096`th power supplies the factored part of both
certificates. -/
def recordBase : ℕ := 504983334

/-- The common factored part `F`. -/
def recordFactor : ℕ := recordBase ^ 4096

/-- A shared exponent from which every main and proper certificate power is
obtained using an exponent of at most `recordBase`. -/
def recordSeedExponent : ℕ := recordBase ^ 4095 * (recordFactor - 1)

/-- The lower endpoint, written in certificate-friendly form. -/
def recordLower : ℕ := recordFactor * (recordFactor - 1) - 1

/-- The upper endpoint, two greater than `recordLower`. -/
def recordUpper : ℕ := recordFactor * (recordFactor - 1) + 1

/-- The Pocklington witness used by the generated upper-endpoint certificate. -/
def recordUpperWitnessBase : ℕ := 11

theorem recordFactor_gt_one : 1 < recordFactor := by
  unfold recordFactor recordBase
  exact one_lt_pow₀ (by norm_num) (by norm_num)

theorem recordLower_add_one :
    recordLower + 1 = recordFactor * (recordFactor - 1) := by
  have hx := recordFactor_gt_one
  have hpos : 0 < recordFactor * (recordFactor - 1) :=
    Nat.mul_pos (by omega) (by omega)
  exact Nat.sub_add_cancel (by omega)

theorem recordSeedExponent_mul_base :
    recordSeedExponent * recordBase = recordLower + 1 := by
  calc
    recordSeedExponent * recordBase =
        (recordBase ^ 4095 * recordBase) * (recordFactor - 1) := by
      simp only [recordSeedExponent]
      ac_rfl
    _ = recordBase ^ 4096 * (recordFactor - 1) := by rw [← pow_succ]
    _ = recordFactor * (recordFactor - 1) := by rfl
    _ = recordLower + 1 := recordLower_add_one.symm

theorem recordLower_quotient_eq_seed_mul (q : ℕ) (hq : q ∣ recordBase) :
    (recordLower + 1) / q = recordSeedExponent * (recordBase / q) := by
  rw [← recordSeedExponent_mul_base, Nat.mul_div_assoc recordSeedExponent hq]

theorem recordUpper_sub_one :
    recordUpper - 1 = recordFactor * (recordFactor - 1) := by
  simp [recordUpper]

theorem recordSeedExponent_mul_base_upper :
    recordSeedExponent * recordBase = recordUpper - 1 := by
  rw [recordUpper_sub_one, ← recordLower_add_one, recordSeedExponent_mul_base]

theorem recordUpper_quotient_eq_seed_mul (q : ℕ) (hq : q ∣ recordBase) :
    (recordUpper - 1) / q = recordSeedExponent * (recordBase / q) := by
  rw [← recordSeedExponent_mul_base_upper,
    Nat.mul_div_assoc recordSeedExponent hq]

theorem recordLower_lt_factor_sq : recordLower < recordFactor ^ 2 := by
  have hx := recordFactor_gt_one
  calc
    recordLower < recordFactor * (recordFactor - 1) := by
      simp only [recordLower]
      have hpos : 0 < recordFactor * (recordFactor - 1) :=
        Nat.mul_pos (by omega) (by omega)
      omega
    _ < recordFactor * recordFactor :=
      (Nat.mul_lt_mul_left (by omega : 0 < recordFactor)).2 (by omega)
    _ = recordFactor ^ 2 := by rw [pow_two]

theorem recordUpper_lt_factor_sq : recordUpper < recordFactor ^ 2 := by
  have hx := recordFactor_gt_one
  have hid : recordFactor * (recordFactor - 1) + recordFactor =
      recordFactor ^ 2 := by
    calc
      recordFactor * (recordFactor - 1) + recordFactor =
          recordFactor * (recordFactor - 1) + recordFactor * 1 := by rw [mul_one]
      _ = recordFactor * ((recordFactor - 1) + 1) := (Nat.mul_add ..).symm
      _ = recordFactor * recordFactor := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ recordFactor)]
      _ = recordFactor ^ 2 := by rw [pow_two]
  simp only [recordUpper]
  omega

theorem recordLower_gt_one : 1 < recordLower := by
  have hfactor : 4 < recordFactor := by
    unfold recordFactor recordBase
    have hpow : (504983334 : ℕ) ≤ 504983334 ^ 4096 := Nat.le_pow (by decide)
    exact lt_of_lt_of_le (by decide) hpow
  simp only [recordLower]
  have hleft : 5 ≤ recordFactor := by omega
  have hright : 4 ≤ recordFactor - 1 := by omega
  have hpos : 20 ≤ recordFactor * (recordFactor - 1) := by
    exact Nat.mul_le_mul hleft hright
  omega

theorem recordUpper_gt_one : 1 < recordUpper := by
  have hx := recordFactor_gt_one
  simp only [recordUpper]
  have hpos : 0 < recordFactor * (recordFactor - 1) :=
    Nat.mul_pos (by omega) (by omega)
  omega

/-- The certificate-friendly lower endpoint is exactly the published numeral
shape. -/
theorem recordLower_eq_published :
    recordLower = 504983334 ^ 8192 - 504983334 ^ 4096 - 1 := by
  rw [recordLower, recordFactor, recordBase, Nat.mul_sub_left_distrib, mul_one,
    ← pow_two, ← pow_mul]

theorem recordUpper_eq_lower_add_two : recordUpper = recordLower + 2 := by
  have hx := recordFactor_gt_one
  have hpos : 0 < recordFactor * (recordFactor - 1) :=
    Nat.mul_pos (by omega) (by omega)
  simp only [recordUpper, recordLower]
  omega

theorem recordLower_isUnit_fortyTwo : IsUnit (42 : ZMod recordLower) := by
  change IsUnit ((42 : ℕ) : ZMod recordLower)
  rw [ZMod.isUnit_iff_coprime 42 recordLower]
  rw [Nat.coprime_comm, ← ZMod.coprime_mod_iff_coprime]
  have hmod : recordLower % 42 = 29 := by
    set_option exponentiation.threshold 5000 in
      norm_num [recordLower, recordFactor, recordBase, Nat.mul_mod]
  rw [hmod]
  norm_num

theorem recordFactor_sub_one_not_dvd_lower :
    ¬ recordFactor - 1 ∣ recordLower := by
  intro h
  have hone : recordFactor - 1 ∣ 1 := by
    apply (Nat.dvd_add_iff_right h).mpr
    rw [recordLower_add_one]
    exact dvd_mul_left _ _
  have heq : recordFactor - 1 = 1 := Nat.eq_one_of_dvd_one hone
  have hlarge : 3 < recordFactor := by
    unfold recordFactor recordBase
    have hpow : (504983334 : ℕ) ≤ 504983334 ^ 4096 := Nat.le_pow (by decide)
    exact lt_of_lt_of_le (by decide) hpow
  omega

theorem recordFactor_sub_one_not_dvd_upper :
    ¬ recordFactor - 1 ∣ recordUpper := by
  intro h
  have hproduct : recordFactor - 1 ∣ recordFactor * (recordFactor - 1) :=
    dvd_mul_left _ _
  have hone : recordFactor - 1 ∣ 1 :=
    (Nat.dvd_add_iff_left hproduct).mpr (by simpa [recordUpper, add_comm] using h)
  have heq : recordFactor - 1 = 1 := Nat.eq_one_of_dvd_one hone
  have hlarge : 3 < recordFactor := by
    unfold recordFactor recordBase
    have hpow : (504983334 : ℕ) ≤ 504983334 ^ 4096 := Nat.le_pow (by decide)
    exact lt_of_lt_of_le (by decide) hpow
  omega

theorem prime_4950817 : Nat.Prime 4950817 := by norm_num

/-- The four possible prime divisors of the common factored part. -/
theorem prime_dvd_recordFactor (q : ℕ) (hq : q.Prime) (hdvd : q ∣ recordFactor) :
    q = 2 ∨ q = 3 ∨ q = 17 ∨ q = 4950817 := by
  have hbase : q ∣ recordBase := hq.dvd_of_dvd_pow (by simpa [recordFactor] using hdvd)
  have hfactor : recordBase = 2 * 3 * 17 * 4950817 := by
    norm_num [recordBase]
  rw [hfactor] at hbase
  have hp3 : Nat.Prime 3 := by norm_num
  have hp17 : Nat.Prime 17 := by norm_num
  rcases hq.dvd_mul.mp hbase with hbase | hbase
  · rcases hq.dvd_mul.mp hbase with hbase | hbase
    · rcases hq.dvd_mul.mp hbase with hbase | hbase
      · exact Or.inl (((Nat.dvd_prime Nat.prime_two).mp hbase).resolve_left hq.ne_one)
      · exact Or.inr (Or.inl (((Nat.dvd_prime hp3).mp hbase).resolve_left hq.ne_one))
    · exact Or.inr (Or.inr (Or.inl (((Nat.dvd_prime hp17).mp hbase).resolve_left hq.ne_one)))
  · exact Or.inr (Or.inr (Or.inr
      (((Nat.dvd_prime prime_4950817).mp hbase).resolve_left hq.ne_one)))

end PrimeFactorUnimodality
