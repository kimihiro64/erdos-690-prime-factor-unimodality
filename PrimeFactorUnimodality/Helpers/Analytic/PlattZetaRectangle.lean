import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaPoles

set_option autoImplicit false

/-! # The finite rectangle identity for the actual zeta window

The downward rectangle contains exactly the zeta pole, strictly inside its
boundary. The proved meromorphic and simple-pole facts discharge the locked
rectangle residue theorem, retaining its counterclockwise orientation.
-/

open Complex Set
open scoped Topology

namespace PrimeFactorUnimodality

noncomputable section

/-- The lower left corner of the rightward zeta contour in window coordinates. -/
def plattZetaContourCorner (m : ℕ) (T : ℝ) : ℂ :=
  (-T : ℝ) - (plattRightShift m : ℂ) * Complex.I

@[simp] theorem plattZetaContourCorner_re (m : ℕ) (T : ℝ) :
    (plattZetaContourCorner m T).re = -T := by simp [plattZetaContourCorner]

@[simp] theorem plattZetaContourCorner_im (m : ℕ) (T : ℝ) :
    (plattZetaContourCorner m T).im = -plattRightShift m := by simp [plattZetaContourCorner]

/-- The entire closed rectangle stays in the downward half-plane. -/
theorem plattZetaRectangle_im_nonpos (m : ℕ) {T : ℝ} (hT : 0 < T) {z : ℂ}
    (hz : z ∈ Rectangle (plattZetaContourCorner m T) (T : ℂ)) : z.im ≤ 0 := by
  rw [mem_Rect (by simp; linarith)
    (by simpa only [plattZetaContourCorner_im, Complex.ofReal_im] using
      neg_nonpos.mpr (show 0 ≤ plattRightShift m by unfold plattRightShift; positivity))] at hz
  simpa only [Complex.ofReal_im] using hz.2.2.2

/-- The unique zeta pole lies strictly inside this rectangle. -/
theorem plattZetaRectangle_mem_nhds_pole (m : ℕ) (hm : 1 ≤ m) {t₀ T : ℝ}
    (hT : |t₀| < T) : Rectangle (plattZetaContourCorner m T) (T : ℂ) ∈ 𝓝 (plattZetaPole t₀) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hTpos : 0 < T := (abs_nonneg t₀).trans_lt hT
  rw [rectangle_mem_nhds_iff]
  simp only [Complex.mem_reProdIm, plattZetaContourCorner_re, plattZetaContourCorner_im,
    Complex.ofReal_re, Complex.ofReal_im, plattZetaPole_re, plattZetaPole_im]
  rw [uIoo_of_le (by linarith : -T ≤ T),
    uIoo_of_le (by unfold plattRightShift; linarith : -plattRightShift m ≤ 0)]
  unfold plattRightShift
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith [le_abs_self t₀, neg_le_abs t₀]

/-- The analytic pole set is the singleton already identified geometrically. -/
theorem plattZeta_rectangle_poles (m k : ℕ) (hm : 1 ≤ m) {t₀ T : ℝ}
    (hT : |t₀| < T) (h x : ℝ) :
    Rectangle (plattZetaContourCorner m T) (T : ℂ) ∩
      {z | meromorphicOrderAt (plattZetaContourIntegrand k t₀ h x) z < 0} = {plattZetaPole t₀} := by
  ext z
  constructor
  · intro hz
    exact (meromorphicOrderAt_plattZetaContourIntegrand_neg_iff k t₀ h x
      (plattZetaRectangle_im_nonpos m ((abs_nonneg t₀).trans_lt hT) hz.1)).mp hz.2
  · rintro rfl
    exact ⟨mem_of_mem_nhds (plattZetaRectangle_mem_nhds_pole m hm hT),
      (meromorphicOrderAt_plattZetaContourIntegrand_neg_iff k t₀ h x (by simp)).mpr rfl⟩

/-- The normalized rectangle integral is exactly the complete zeta residue. -/
theorem rectangleIntegral_plattZetaContourIntegrand_eq (m k : ℕ) (hm : 1 ≤ m)
    {t₀ T : ℝ} (hT : |t₀| < T) (h x : ℝ) :
    RectangleIntegral' (plattZetaContourIntegrand k t₀ h x)
      (plattZetaContourCorner m T) (T : ℂ) = plattZetaContourResidueValue k t₀ h x := by
  have hTpos : 0 < T := (abs_nonneg t₀).trans_lt hT
  have hb : Disjoint (RectangleBorder (plattZetaContourCorner m T) (T : ℂ))
      {z | meromorphicOrderAt (plattZetaContourIntegrand k t₀ h x) z < 0} := by
    apply Set.disjoint_left.mpr
    intro z hz hp
    have he := (meromorphicOrderAt_plattZetaContourIntegrand_neg_iff k t₀ h x
      (plattZetaRectangle_im_nonpos m hTpos (rectangleBorder_subset_rectangle _ _ hz))).mp hp
    subst z
    exact (not_mem_rectangleBorder_of_rectangle_mem_nhds
      (plattZetaRectangle_mem_nhds_pole m hm hT)) hz
  have hset := plattZeta_rectangle_poles m k hm hT h x
  rw [RectangleIntegral'_eq_sumResiduesIn (by simp; linarith)
    (by simpa only [plattZetaContourCorner_im, Complex.ofReal_im] using
      neg_nonpos.mpr (show 0 ≤ plattRightShift m by unfold plattRightShift; positivity))
    (fun z hz => meromorphicAt_plattZetaContourIntegrand k t₀ h x
      (plattZetaRectangle_im_nonpos m hTpos hz)) hb
    (by rw [hset]; exact Set.finite_singleton _) (hasSimplePolesOn_plattZetaContourIntegrand
      k t₀ h x _ (fun z hz => plattZetaRectangle_im_nonpos m hTpos hz)), hset]
  simpa only [sumResiduesIn, tsum_singleton] using residue_plattZetaContourIntegrand k t₀ h x

end

end PrimeFactorUnimodality
