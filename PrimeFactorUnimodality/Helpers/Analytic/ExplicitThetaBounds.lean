import Mathlib.NumberTheory.Chebyshev
import PrimeFactorUnimodality.Helpers.Analytic.PrimorialLogBounds

set_option autoImplicit false

/-! # Interfaces for explicit Chebyshev-theta estimates -/

namespace PrimeFactorUnimodality

noncomputable section

/-- The two Dusart theta estimates used by Wang--Crapis.  Their analytic
provider is intentionally separated from all downstream primorial algebra. -/
def HasDusartThetaBounds : Prop :=
  (∀ x : Real, 0 < x →
    Chebyshev.theta x < x * (1 + 1 / 36260)) ∧
  (∀ x : Real, 2 < x →
    x * (1 - (12323 / 10000 : Real) / Real.log x) <
      Chebyshev.theta x)

/-! Published theta estimates are often supplied as a symmetric error bound.
This interface records exactly the two error scales needed below and the
adapter separates that analytic presentation from the asymmetric inequalities
used by the primorial arguments. -/
def HasDusartSymmetricThetaBounds : Prop :=
  (∀ x : Real, 0 < x →
    |Chebyshev.theta x - x| < x / 36260) ∧
  (∀ x : Real, 2 < x →
    |Chebyshev.theta x - x| <
      (12323 / 10000 : Real) * x / Real.log x)

theorem hasDusartThetaBounds_of_symmetric
    (bounds : HasDusartSymmetricThetaBounds) :
    HasDusartThetaBounds := by
  constructor
  · intro x hx
    have h := bounds.1 x hx
    rw [abs_lt] at h
    nlinarith
  · intro x hx
    have log_pos : 0 < Real.log x :=
      Real.log_pos (by linarith)
    have h := bounds.2 x hx
    rw [abs_lt] at h
    have hleft := h.1
    ring_nf at hleft ⊢
    linarith

theorem log_primorial_lt_of_dusart
    (bounds : HasDusartThetaBounds) (q : Nat) (q_pos : 0 < q) :
    Real.log (primorial q) <
      (q : Real) * (1 + 1 / 36260) := by
  rw [log_primorial_eq_theta]
  exact bounds.1 q (by exact_mod_cast q_pos)

theorem dusart_lower_lt_log_primorial
    (bounds : HasDusartThetaBounds) (q : Nat) (q_gt_two : 2 < q) :
    (q : Real) * (1 - (12323 / 10000 : Real) / Real.log q) <
      Real.log (primorial q) := by
  rw [log_primorial_eq_theta]
  exact bounds.2 q (by exact_mod_cast q_gt_two)

theorem log_eight_mul_primorial_lt_of_dusart
    (bounds : HasDusartThetaBounds) (q : Nat) (q_pos : 0 < q) :
    Real.log (8 * primorial q) <
      Real.log 8 + (q : Real) * (1 + 1 / 36260) := by
  calc
    Real.log (8 * primorial q) =
        Real.log 8 + Real.log (primorial q) :=
      log_mul_primorial 8 q (by omega)
    _ < Real.log 8 + (q : Real) * (1 + 1 / 36260) :=
      add_lt_add_right (log_primorial_lt_of_dusart bounds q q_pos) _

end

end PrimeFactorUnimodality
