import PrimeFactorUnimodality.Helpers.Analytic.XiZetaCountingBridge
import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiRealNonvanishing
import PrimeNumberTheoremAnd.RectangleArgumentPrinciple

/-! # The rectangle argument principle counts the actual xi zeros

The symmetric rectangle has vertical sides at `1-sigma` and `sigma`,
with `sigma >= 1`, and heights zero and `T >= 0`. Xi is nonzero on the
real axis and the two vertical sides. When the top avoids zeros, its
divisor support is exactly PNT's strict positive-height zeta zero set,
and each divisor value is the existing zeta-order weight.

Apply the proved rectangle residue theorem from the Apache-2.0 PNT
revision `f6147e7572ab3abe5428101bc0b13627bcb005df`; its divisor support
and fiber machinery are by Matteo Cipollina. This identifies the actual
normalized logarithmic-derivative integral with `N(T)`, with no assumed
argument-count identity, RH premise, or numerical counting estimate.
-/

namespace PrimeFactorUnimodality
noncomputable section
open Complex Filter Set
open scoped Topology

/-- Xi's divisor on any containing domain is its full analytic multiplicity. -/
theorem xi_divisor_eq_analyticOrderNatAt {U : Set ℂ} {z : ℂ} (hz : z ∈ U) :
    MeromorphicOn.divisor riemannXi U z = (analyticOrderNatAt riemannXi z : ℤ) := by
  have hU : MeromorphicOn riemannXi U := fun w _ =>
    (differentiable_riemannXi.analyticAt w).meromorphicAt
  have hall : MeromorphicOn riemannXi univ := fun w _ =>
    (differentiable_riemannXi.analyticAt w).meromorphicAt
  rw [← Hadamard.divisor_univ_eq_analyticOrderNatAt_int differentiable_riemannXi,
    hU.divisor_apply hz, hall.divisor_apply (mem_univ z)]

/-- The xi divisor is supported exactly at the actual zeros in its domain. -/
theorem mem_xi_divisor_support_iff {U : Set ℂ} {z : ℂ} :
    z ∈ (MeromorphicOn.divisor riemannXi U).support ↔ z ∈ U ∧ riemannXi z = 0 := by
  constructor
  · intro hz
    have hzU := (MeromorphicOn.divisor riemannXi U).supportWithinDomain hz
    refine ⟨hzU, apply_eq_zero_of_analyticOrderNatAt_ne_zero ?_⟩
    have hd : MeromorphicOn.divisor riemannXi U z ≠ 0 := hz
    rwa [xi_divisor_eq_analyticOrderNatAt hzU, Int.natCast_ne_zero] at hd
  · rintro ⟨hzU, hz⟩
    change MeromorphicOn.divisor riemannXi U z ≠ 0
    rw [xi_divisor_eq_analyticOrderNatAt hzU, Int.natCast_ne_zero]
    intro hn
    have htop := Hadamard.analyticOrderAt_ne_top_of_exists_ne_zero
      differentiable_riemannXi riemannXi_nontrivial z
    have he : analyticOrderAt riemannXi z = 0 := by
      rw [← Nat.cast_analyticOrderNatAt htop, hn, Nat.cast_zero]
    exact ((differentiable_riemannXi.analyticAt z).analyticOrderAt_eq_zero.mp he) hz

/-- Coordinates in the symmetric counting rectangle, including its boundary. -/
theorem mem_xi_counting_rectangle_iff {σ T : ℝ} (hσ : 1 ≤ σ) (hT : 0 ≤ T) (z : ℂ) :
    z ∈ Rectangle ((1 - σ : ℝ) : ℂ) ((σ : ℂ) + T * I) ↔
      (1 - σ ≤ z.re ∧ z.re ≤ σ) ∧ (0 ≤ z.im ∧ z.im ≤ T) := by
  have hs : 1 - σ ≤ σ := by linarith
  simp [Rectangle, uIcc_of_le, hs, hT, mem_reProdIm]

/-- The complete real axis is free of xi zeros. -/
theorem riemannXi_ne_zero_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : riemannXi z ≠ 0 := by
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
  rw [he]
  exact riemannXi_ofReal_ne_zero _

/-- Avoiding the top ordinate makes the complete counting contour free of zeros. -/
theorem xi_divisor_disjoint_rectangle_border {σ T : ℝ} (hσ : 1 ≤ σ)
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    Disjoint (RectangleBorder ((1 - σ : ℝ) : ℂ) ((σ : ℂ) + T * I))
      (MeromorphicOn.divisor riemannXi
        (Rectangle ((1 - σ : ℝ) : ℂ) ((σ : ℂ) + T * I))).support := by
  rw [Set.disjoint_left]
  intro z hb hd
  have hz := (mem_xi_divisor_support_iff.mp hd).2
  have hs := riemannXi_zero_mem_open_critical_strip hz
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff,
    ofReal_re, ofReal_im, add_re, add_im, mul_re, mul_im, I_re, I_im,
    mul_zero, sub_zero, mul_one, add_zero, zero_add] at hb
  rcases hb with ((hb | hb) | hb) | hb
  · exact riemannXi_ne_zero_of_im_eq_zero hb.2 hz
  · linarith [hb.1]
  · exact htop z hb.2 hz
  · linarith [hb.1]

/-- The rectangle support is exactly the strict positive-height zeta zero set. -/
theorem mem_xi_rectangle_divisor_support_iff {σ T : ℝ} (hσ : 1 ≤ σ) (hT : 0 ≤ T)
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) (z : ℂ) :
    z ∈ (MeromorphicOn.divisor riemannXi
      (Rectangle ((1 - σ : ℝ) : ℂ) ((σ : ℂ) + T * I))).support ↔
        z ∈ riemannZeta.zeroes_rect univ (Ioo 0 T) := by
  rw [mem_xi_divisor_support_iff, mem_xi_counting_rectangle_iff hσ hT]
  constructor
  · rintro ⟨⟨hre, him⟩, hz⟩
    have hp : 0 < z.im := lt_of_le_of_ne him.1 (by
      intro he
      exact riemannXi_ne_zero_of_im_eq_zero he.symm hz)
    have hlt : z.im < T := lt_of_le_of_ne him.2 (by intro he; exact htop z he hz)
    have hs1 : z ≠ 1 := by intro he; simp [he] at hp
    exact ⟨mem_univ _, ⟨hp, hlt⟩,
      (riemannXi_eq_zero_iff_riemannZeta_eq_zero
        (riemannXi_zero_mem_open_critical_strip hz).1 hs1).mp hz⟩
  · intro hz
    have hzeta : riemannZeta z = 0 := hz.2.2
    have him : 0 < z.im ∧ z.im < T := hz.2.1
    have hxi := riemannXi_eq_zero_of_zeta_zero_of_im_ne_zero him.1.ne' hzeta
    have hre := riemannXi_zero_mem_open_critical_strip hxi
    exact ⟨⟨⟨by linarith, by linarith⟩, him.1.le, him.2.le⟩, hxi⟩

/-- The normalized contour integral equals the actual multiplicity-weighted zeta count. -/
theorem rectangleIntegral_logDeriv_xi_eq_zeta_N {σ T : ℝ} (hσ : 1 ≤ σ) (hT : 0 ≤ T)
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    RectangleIntegral' (logDeriv riemannXi) ((1 - σ : ℝ) : ℂ) ((σ : ℂ) + T * I) =
      (riemannZeta.N T : ℂ) := by
  classical
  let R := Rectangle ((1 - σ : ℝ) : ℂ) ((σ : ℂ) + T * I)
  let D := MeromorphicOn.divisor riemannXi R
  let S := (divisor_support_rectangle_finite riemannXi
    ((1 - σ : ℝ) : ℂ) ((σ : ℂ) + T * I)).toFinset
  have hf : MeromorphicOn riemannXi R := fun z _ =>
    (differentiable_riemannXi.analyticAt z).meromorphicAt
  have hn (z : ℂ) (_ : z ∈ R) : meromorphicOrderAt riemannXi z ≠ ⊤ := by
    rw [(differentiable_riemannXi.analyticAt z).meromorphicOrderAt_eq, ne_eq, ENat.map_eq_top_iff]
    exact Hadamard.analyticOrderAt_ne_top_of_exists_ne_zero
      differentiable_riemannXi riemannXi_nontrivial z
  have hrect := rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt
    (f := riemannXi) (z := ((1 - σ : ℝ) : ℂ)) (w := (σ : ℂ) + T * I)
    (by simp; linarith) (by simpa using hT) hf hf.logDeriv hn
    (xi_divisor_disjoint_rectangle_border hσ htop)
  have hS (z : ℂ) : z ∈ S ↔ z ∈ riemannZeta.zeroes_rect univ (Ioo 0 T) := by
    simp only [S, Set.Finite.mem_toFinset]
    exact mem_xi_rectangle_divisor_support_iff hσ hT htop z
  let : Fintype (riemannZeta.zeroes_rect univ (Ioo 0 T)) :=
    (finite_zeta_positive_height_via_xi T).fintype
  have hsum : (∑ z ∈ S, (D z : ℝ)) = riemannZeta.N T := by
    calc
      _ = ∑ z ∈ S, (riemannZeta.order z : ℝ) := by
        apply Finset.sum_congr rfl
        intro z hz
        have hz' := (hS z).mp hz
        have hxi := riemannXi_eq_zero_of_zeta_zero_of_im_ne_zero hz'.2.1.1.ne' hz'.2.2
        have hzR : z ∈ R := (mem_xi_divisor_support_iff.mp
          ((divisor_support_rectangle_finite riemannXi
            ((1 - σ : ℝ) : ℂ) ((σ : ℂ) + T * I)).mem_toFinset.mp hz)).1
        have hs1 : z ≠ 1 := by intro he; simpa [he] using hz'.2.1.1
        have hd := xi_divisor_eq_zeta_order (riemannXi_zero_mem_open_critical_strip hxi).1 hs1
        rw [Hadamard.divisor_univ_eq_analyticOrderNatAt_int differentiable_riemannXi] at hd
        change ((MeromorphicOn.divisor riemannXi R z : ℤ) : ℝ) = _
        rw [xi_divisor_eq_analyticOrderNatAt hzR, hd]
      _ = ∑' z : riemannZeta.zeroes_rect univ (Ioo 0 T), (riemannZeta.order z : ℝ) := by
        rw [tsum_fintype]
        exact Finset.sum_subtype S hS (fun z => (riemannZeta.order z : ℝ))
      _ = riemannZeta.N T := by simp only [riemannZeta.N, riemannZeta.zeroes_sum, one_mul]
  rw [← hsum]
  push_cast
  simpa only [ofReal_sub, ofReal_one] using hrect

end
end PrimeFactorUnimodality
