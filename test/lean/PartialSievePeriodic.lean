import PrimeFactorUnimodality.Mathlib.NumberTheory.PartialSievePeriodic

/-! # Exact periodic table leaves, including empty and modulus-one boundaries -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

example (m n : ℕ) : Nat.coprimeCount m n =
    Nat.count (fun a => Nat.Coprime (a + 1) m) n := Nat.coprimeCount_eq_count m n
example (m : ℕ) : Nat.coprimeCount m m = Nat.totient m := Nat.coprimeCount_self m
example (m n : ℕ) : Nat.coprimeCount m n =
    Nat.coprimeCount m (n % m) + (n / m) * Nat.totient m :=
  Nat.coprimeCount_eq_mod_add_div_mul m n

private def wheelPrimes (i : ℕ) : ℕ := if i = 0 then 2 else 3

example : Nat.sievePhi wheelPrimes 2 10000000000 = 3333333333 :=
  Nat.sievePhi_eq_of_periodic (m := 6) (r := 1) (t := 2)
    (by decide) (by decide) (by decide) (by decide +kernel)
    (by decide) (by decide +kernel)

example : Nat.coprimeCount 0 0 =
    Nat.coprimeCount 0 (0 % 0) + (0 / 0) * Nat.totient 0 := by
  decide +kernel

example : Nat.coprimeCount 0 7 =
    Nat.coprimeCount 0 (7 % 0) + (7 / 0) * Nat.totient 0 := by
  decide +kernel

example : Nat.coprimeCount 1 0 =
    Nat.coprimeCount 1 (0 % 1) + (0 / 1) * Nat.totient 1 := by
  decide +kernel

example : Nat.coprimeCount 1 20 =
    Nat.coprimeCount 1 (20 % 1) + (20 / 1) * Nat.totient 1 := by
  decide +kernel

example : Nat.coprimeCount 6 5 =
    Nat.coprimeCount 6 (5 % 6) + (5 / 6) * Nat.totient 6 := by
  decide +kernel

example : Nat.coprimeCount 6 6 =
    Nat.coprimeCount 6 (6 % 6) + (6 / 6) * Nat.totient 6 := by
  decide +kernel

example : Nat.coprimeCount 6 7 =
    Nat.coprimeCount 6 (7 % 6) + (7 / 6) * Nat.totient 6 := by
  decide +kernel

example : Nat.coprimeCount 30 73 =
    Nat.coprimeCount 30 (73 % 30) + (73 / 30) * Nat.totient 30 := by
  decide +kernel

end PrimeFactorUnimodality.Tests
