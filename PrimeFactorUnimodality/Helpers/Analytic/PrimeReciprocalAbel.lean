import Mathlib.NumberTheory.AbelSummation
import PrimeFactorUnimodality.Helpers.Analytic.PrimeWeightSum

set_option autoImplicit false

/-! # Finite Abel summation for reciprocal primes

The natural endpoints use primes at most the endpoint. The counting function
inside the integral is evaluated at the natural floor of its real argument.
-/

namespace PrimeFactorUnimodality

open Finset MeasureTheory

noncomputable section

theorem primeCounting_eq_sum_indicator (n : Nat) :
    (Nat.primeCounting n : Real) =
      ∑ k ∈ Icc 0 n, if k.Prime then (1 : Real) else 0 := by
  rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_zero]
  simp

theorem reciprocalPrimeSumBelow_sub_eq_Ioc {x y : Nat} (hxy : x ≤ y) :
    reciprocalPrimeSumBelow (y + 1) - reciprocalPrimeSumBelow (x + 1) =
      ∑ k ∈ Ioc x y, (1 / (k : Real)) * (if k.Prime then 1 else 0) := by
  have sumAt (n : Nat) : reciprocalPrimeSumBelow (n + 1) =
      ∑ k ∈ Icc 0 n, (1 / (k : Real)) * (if k.Prime then 1 else 0) := by
    simp only [reciprocalPrimeSumBelow, Nat.primesBelow, Finset.sum_filter,
      mul_ite, mul_one, mul_zero, Nat.range_succ_eq_Icc_zero]
  have hsub : Icc 0 x ⊆ Icc 0 y := by
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  have hdiff : Icc 0 y \ Icc 0 x = Ioc x y := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [sumAt, sumAt, ← Finset.sum_sdiff_eq_sub hsub, hdiff]

theorem primeCounting_div_square_integrable {a b : Real} (ha : 0 < a) :
    IntegrableOn (fun t => (Nat.primeCounting ⌊t⌋₊ : Real) / t ^ 2)
      (Set.Icc a b) := by
  have hc : ContinuousOn (fun t : Real => 1 / t ^ 2) (Set.Icc a b) :=
    continuousOn_const.div (continuousOn_id.pow 2) (by
      intro t ht
      exact pow_ne_zero _ (ne_of_gt (ha.trans_le ht.1)))
  have h := integrableOn_mul_sum_Icc
    (fun k : Nat => if k.Prime then (1 : Real) else 0) (m := 0) ha.le
    (hc.integrableOn_Icc : IntegrableOn (fun t : Real => 1 / t ^ 2) (Set.Icc a b))
  simpa only [← primeCounting_eq_sum_indicator, one_div, div_eq_mul_inv,
    mul_comm, mul_one] using h

theorem reciprocalPrimeSumBelow_sub_eq_integral {x y : Nat}
    (hx : 0 < x) (hxy : x ≤ y) :
    reciprocalPrimeSumBelow (y + 1) - reciprocalPrimeSumBelow (x + 1) =
      (Nat.primeCounting y : Real) / y - (Nat.primeCounting x : Real) / x +
        ∫ t in Set.Ioc (x : Real) y, (Nat.primeCounting ⌊t⌋₊ : Real) / t ^ 2 := by
  have xpos : (0 : Real) < x := by exact_mod_cast hx
  have hd (t : Real) (ht : t ∈ Set.Icc (x : Real) y) :
      HasDerivAt (fun u : Real => 1 / u) (-(1 / t ^ 2)) t := by
    simpa only [one_div] using hasDerivAt_inv (ne_of_gt (xpos.trans_le ht.1))
  have derivEq (t : Real) (ht : t ∈ Set.Icc (x : Real) y) :
      deriv (fun u : Real => 1 / u) t = -(1 / t ^ 2) := (hd t ht).deriv
  have hc : ContinuousOn (fun t : Real => -(1 / t ^ 2)) (Set.Icc (x : Real) y) :=
    (continuousOn_const.div (continuousOn_id.pow 2) (by
      intro t ht
      exact pow_ne_zero _ (ne_of_gt (xpos.trans_le ht.1)))).neg
  have hi : IntegrableOn (deriv (fun u : Real => 1 / u)) (Set.Icc (x : Real) y) :=
    hc.integrableOn_Icc.congr_fun (fun t ht => (derivEq t ht).symm) measurableSet_Icc
  have abel := sum_mul_eq_sub_sub_integral_mul'
    (fun k : Nat => if k.Prime then (1 : Real) else 0) hxy
    (fun t ht => (hd t ht).differentiableAt) hi
  rw [← reciprocalPrimeSumBelow_sub_eq_Ioc hxy] at abel
  simp only [← primeCounting_eq_sum_indicator] at abel
  have intEq : (∫ t in Set.Ioc (x : Real) y,
      deriv (fun u : Real => 1 / u) t * (Nat.primeCounting ⌊t⌋₊ : Real)) =
      -(∫ t in Set.Ioc (x : Real) y, (Nat.primeCounting ⌊t⌋₊ : Real) / t ^ 2) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [derivEq t ⟨ht.1.le, ht.2⟩]
    ring
  rw [intEq] at abel
  convert abel using 1
  ring

end

end PrimeFactorUnimodality
