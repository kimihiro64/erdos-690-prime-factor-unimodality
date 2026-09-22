import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiDivisorReflection
import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiStechkin
import PrimeFactorUnimodality.Mathlib.Analysis.Analytic.Order.Conjugation

/-! # Conjugation and same-height reflection of the actual xi divisor

The general conjugation-order lemma and the proved xi symmetry transport
each finite multiplicity label unchanged. Composing with `ρ -> 1-ρ` gives
the actual same-height reflection `ρ -> 1-conj(ρ)` used by the smoothed
paired-zero inequality. Both are equivalences, not just maps of zero sets.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex
open scoped ComplexConjugate

/-- Complex conjugation preserves every analytic multiplicity of xi. -/
theorem analyticOrderNatAt_riemannXi_conj (z : ℂ) :
    analyticOrderNatAt riemannXi (conj z) = analyticOrderNatAt riemannXi z := by
  have h := analyticOrderNatAt_conj_conj (differentiable_riemannXi.analyticAt (conj z))
  have heq : (fun w => conj (riemannXi (conj w))) = riemannXi := by
    funext w
    rw [riemannXi_conj, conj_conj]
  rw [heq] at h
  exact h.symm

private theorem xi_divisor_conj (z : ℂ) :
    MeromorphicOn.divisor riemannXi Set.univ (conj z) =
      MeromorphicOn.divisor riemannXi Set.univ z := by
  simp only [Hadamard.divisor_univ_eq_analyticOrderNatAt_int differentiable_riemannXi,
    analyticOrderNatAt_riemannXi_conj]

private def xi_divisor_conjugate (p : RiemannXiDivisorZeroIndex) :
    RiemannXiDivisorZeroIndex :=
  ⟨⟨conj p.1.1, ⟨p.1.2.val, by rw [xi_divisor_conj]; exact p.1.2.isLt⟩⟩,
    by simpa only [map_ne_zero] using p.2⟩

private theorem xi_divisor_conjugate_involutive : Function.Involutive xi_divisor_conjugate := by
  intro p
  apply Subtype.ext
  apply Sigma.ext
  · simp [xi_divisor_conjugate]
  · apply (Fin.heq_ext_iff (by simp [xi_divisor_conjugate])).2
    rfl

/-- Conjugation of the divisor carries the multiplicity label unchanged. -/
def riemannXiDivisorConjugation : RiemannXiDivisorZeroIndex ≃ RiemannXiDivisorZeroIndex :=
  xi_divisor_conjugate_involutive.toPerm xi_divisor_conjugate

/-- The complex zero attached to the conjugate divisor label. -/
@[simp] theorem riemannXiDivisorZeroValue_conjugation (p : RiemannXiDivisorZeroIndex) :
    riemannXiDivisorZeroValue (riemannXiDivisorConjugation p) =
      conj (riemannXiDivisorZeroValue p) := rfl

/-- The natural multiplicity label is unchanged, not merely bounded by the new multiplicity. -/
@[simp] theorem riemannXiDivisorConjugation_label (p : RiemannXiDivisorZeroIndex) :
    (riemannXiDivisorConjugation p).1.2.val = p.1.2.val := rfl

/-- Reflection across the critical line, retaining the imaginary part and multiplicity. -/
def riemannXiDivisorSameHeightReflection :
    RiemannXiDivisorZeroIndex ≃ RiemannXiDivisorZeroIndex :=
  riemannXiDivisorConjugation.trans riemannXiDivisorReflection

/-- The reflected zero is `1-conj(ρ)`, as required by the same-height pair. -/
@[simp] theorem riemannXiDivisorZeroValue_sameHeightReflection (p : RiemannXiDivisorZeroIndex) :
    riemannXiDivisorZeroValue (riemannXiDivisorSameHeightReflection p) =
      1 - conj (riemannXiDivisorZeroValue p) := rfl

/-- Same-height reflection preserves each finite multiplicity label. -/
@[simp] theorem riemannXiDivisorSameHeightReflection_label (p : RiemannXiDivisorZeroIndex) :
    (riemannXiDivisorSameHeightReflection p).1.2.val = p.1.2.val := rfl

/-- Same-height reflection is an involution on labels, including zeros on the critical line. -/
theorem riemannXiDivisorSameHeightReflection_involutive :
    Function.Involutive riemannXiDivisorSameHeightReflection := by
  intro p
  have hval : (riemannXiDivisorSameHeightReflection
      (riemannXiDivisorSameHeightReflection p)).1.1 = p.1.1 := by
    change 1 - conj (1 - conj p.1.1) = p.1.1
    simp
  apply Subtype.ext
  apply Sigma.ext
  · exact hval
  · apply (Fin.heq_ext_iff (congrArg
      (fun z => (MeromorphicOn.divisor riemannXi Set.univ z).toNat) hval)).2
    rfl

/-- A divisor label is fixed exactly when its zero lies on the critical line. -/
theorem riemannXiDivisorSameHeightReflection_fixed_iff (p : RiemannXiDivisorZeroIndex) :
    riemannXiDivisorSameHeightReflection p = p ↔ (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  constructor
  · intro hp
    have h := congrArg (fun q => (riemannXiDivisorZeroValue q).re) hp
    simp only [riemannXiDivisorZeroValue_sameHeightReflection, sub_re, one_re, conj_re] at h
    linarith
  · intro hp
    have hval : (riemannXiDivisorSameHeightReflection p).1.1 = p.1.1 := by
      change 1 - conj (riemannXiDivisorZeroValue p) = riemannXiDivisorZeroValue p
      apply Complex.ext <;> norm_num [hp]
    apply Subtype.ext
    apply Sigma.ext
    · exact hval
    · apply (Fin.heq_ext_iff (congrArg
        (fun z => (MeromorphicOn.divisor riemannXi Set.univ z).toNat) hval)).2
      rfl

/-- A reflection-stable zero predicate gives an equivalence on its actual divisor subtype. -/
def riemannXiDivisorSameHeightReflectionOn (P : ℂ → Prop)
    (hP : ∀ z, P z ↔ P (1 - conj z)) :
    {p : RiemannXiDivisorZeroIndex // P (riemannXiDivisorZeroValue p)} ≃
      {p : RiemannXiDivisorZeroIndex // P (riemannXiDivisorZeroValue p)} :=
  riemannXiDivisorSameHeightReflection.subtypeEquiv (fun p => by
    simpa only [riemannXiDivisorZeroValue_sameHeightReflection] using
      hP (riemannXiDivisorZeroValue p))

end

end PrimeFactorUnimodality
