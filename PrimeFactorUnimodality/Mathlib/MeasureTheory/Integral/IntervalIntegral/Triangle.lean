/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith

/-! # Interchanging integrals on a finite triangle

Fubini on a bounded rectangle, with a measurable triangular indicator,
interchanges two finite integrals with variable upper endpoints.
-/

open MeasureTheory Set

namespace intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem integral_cut_eq (f : ℝ → E) {a b c t : ℝ}
    (hac : a ≤ c - t) (hcb : c - t ≤ b) :
    (∫ v in Icc a b, if t + v ≤ c then f v else 0) = ∫ v in a..c - t, f v := by
  have heq : (fun v => if t + v ≤ c then f v else 0) = (Iic (c - t)).indicator f := by
    funext v
    simp only [indicator, mem_Iic]
    congr 1
    exact propext (by constructor <;> intro h <;> linarith)
  have hset : Icc a b ∩ Iic (c - t) = Icc a (c - t) := by
    ext v
    simp only [mem_inter_iff, mem_Icc, mem_Iic]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, h.2.trans hcb⟩, h.2⟩
  rw [heq, setIntegral_indicator measurableSet_Iic, hset,
    integral_Icc_eq_integral_Ioc, ← integral_of_le hac]

/-- Interchange of a continuous integrand over `0 <= u`, `a <= v`, `u+v <= b`. -/
theorem integral_integral_triangle_swap {F : ℝ × ℝ → E} (hF : Continuous F)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ u in (0 : ℝ)..b - a, ∫ v in a..b - u, F (u, v)) =
      ∫ v in a..b, ∫ u in (0 : ℝ)..b - v, F (u, v) := by
  let G : ℝ → ℝ → E := fun u v => if u + v ≤ b then F (u, v) else 0
  have hD : MeasurableSet {p : ℝ × ℝ | p.1 + p.2 ≤ b} :=
    measurableSet_le (measurable_fst.add measurable_snd) measurable_const
  have hi : Integrable (Function.uncurry G)
      ((volume.restrict (Icc 0 (b - a))).prod (volume.restrict (Icc a b))) := by
    rw [Measure.prod_restrict]
    change IntegrableOn ({p : ℝ × ℝ | p.1 + p.2 ≤ b}.indicator F)
      (Icc 0 (b - a) ×ˢ Icc a b) (volume.prod volume)
    exact (hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).indicator hD
  have hswap := integral_integral_swap hi
  have hleft : (∫ u in Icc 0 (b - a), ∫ v in Icc a b, G u v) =
      ∫ u in (0 : ℝ)..b - a, ∫ v in a..b - u, F (u, v) := by
    rw [integral_of_le (sub_nonneg.mpr hab), ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    exact integral_cut_eq (fun v => F (u, v)) (by linarith [hu.2]) (by linarith [hu.1])
  have hright : (∫ v in Icc a b, ∫ u in Icc 0 (b - a), G u v) =
      ∫ v in a..b, ∫ u in (0 : ℝ)..b - v, F (u, v) := by
    rw [integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    change (∫ u in Icc 0 (b - a), if u + v ≤ b then F (u, v) else 0) = _
    simp_rw [add_comm _ v]
    exact integral_cut_eq (fun u => F (u, v)) (by linarith [hv.2]) (by linarith [hv.1])
  exact hleft.symm.trans (hswap.trans hright)

end intervalIntegral
