import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiZeroContribution

/-! # Reflection of the xi divisor, including multiplicities

The xi functional equation preserves analytic order under `z ↦ 1-z`.
Consequently reflection is an involutive equivalence of the actual divisor
index, not just a map of its underlying zero set. This permits reindexing
absolutely convergent zero sums without an assumed enumeration.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

/-- The functional equation preserves the analytic multiplicity of every point. -/
theorem analyticOrderNatAt_riemannXi_one_sub (z : ℂ) :
    analyticOrderNatAt riemannXi (1 - z) = analyticOrderNatAt riemannXi z := by
  have h := analyticOrderAt_comp_of_deriv_ne_zero
    (f := riemannXi) (g := fun w : ℂ => 1 - w) (z₀ := z)
    (by fun_prop) (by simp)
  have heq : riemannXi ∘ (fun w : ℂ => 1 - w) = riemannXi :=
    funext riemannXi_one_sub
  rw [heq] at h
  exact congrArg ENat.toNat h.symm

private theorem xi_divisor_one_sub (z : ℂ) :
    MeromorphicOn.divisor riemannXi Set.univ (1 - z) =
      MeromorphicOn.divisor riemannXi Set.univ z := by
  simp only [Hadamard.divisor_univ_eq_analyticOrderNatAt_int differentiable_riemannXi,
    analyticOrderNatAt_riemannXi_one_sub]

private def xi_divisor_reflect (p : RiemannXiDivisorZeroIndex) :
    RiemannXiDivisorZeroIndex :=
  ⟨⟨1 - p.1.1, ⟨p.1.2.val, by
    rw [xi_divisor_one_sub]
    exact p.1.2.isLt⟩⟩, by
    intro heq
    have hz := riemannXiDivisorZeroValue_eq_zero p
    have hp : riemannXiDivisorZeroValue p = 1 := sub_eq_zero.mp heq |>.symm
    rw [hp] at hz
    have h1 := riemannXi_one_sub 0
    norm_num [riemannXi_zero, hz] at h1⟩

private theorem xi_divisor_reflect_involutive : Function.Involutive xi_divisor_reflect := by
  intro p
  apply Subtype.ext
  apply Sigma.ext
  · simp [xi_divisor_reflect]
  · apply (Fin.heq_ext_iff (by simp [xi_divisor_reflect])).2
    rfl

/-- Reflection across one half, carrying each multiplicity index unchanged. -/
def riemannXiDivisorReflection : RiemannXiDivisorZeroIndex ≃ RiemannXiDivisorZeroIndex :=
  xi_divisor_reflect_involutive.toPerm xi_divisor_reflect

/-- The value of the reflected divisor index is the reflected complex zero. -/
@[simp] theorem riemannXiDivisorZeroValue_reflection (p : RiemannXiDivisorZeroIndex) :
    riemannXiDivisorZeroValue (riemannXiDivisorReflection p) =
      1 - riemannXiDivisorZeroValue p := rfl

end

end PrimeFactorUnimodality
