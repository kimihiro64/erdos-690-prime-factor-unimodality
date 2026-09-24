import PrimeFactorUnimodality.Helpers.Analytic.PlattContourPoles

set_option autoImplicit false

/-! # The exact finite-rectangle residue identity for the leftward Gamma shift

For every horizontal radius larger than `|t0|`, precisely the poles indexed
by `0,...,m` lie inside the rectangle and none lies on its boundary. Applying
the audited simple-pole residue theorem therefore gives an explicit finite
sum, with every geometric and analytic hypothesis supplied here.
-/

open Complex Set
open scoped Topology

namespace PrimeFactorUnimodality

noncomputable section

/-- The upper right corner for the leftward Gamma displacement. -/
def plattLeftContourCorner (m : ℕ) (T : ℝ) : ℂ :=
  (T : ℂ) + (((2 * (m : ℝ) + 3 / 2 : ℝ)) : ℂ) * Complex.I

@[simp] theorem plattLeftContourCorner_re (m : ℕ) (T : ℝ) :
    (plattLeftContourCorner m T).re = T := by simp [plattLeftContourCorner]

@[simp] theorem plattLeftContourCorner_im (m : ℕ) (T : ℝ) :
    (plattLeftContourCorner m T).im = 2 * (m : ℝ) + 3 / 2 := by simp [plattLeftContourCorner]

/-- Every pole crossed by this shift, without repetition. -/
def plattContourPoleFinset (m : ℕ) (t₀ : ℝ) : Finset ℂ := by
  classical
  exact (Finset.range (m + 1)).image (fun n => plattGammaPole n t₀)

/-- The rectangle contains a listed Gamma pole exactly when its index is at most `m`. -/
theorem plattGammaPole_mem_rectangle_iff (m n : ℕ) {t₀ T : ℝ} (hT : |t₀| < T) :
    plattGammaPole n t₀ ∈ Rectangle ((-T : ℝ) : ℂ) (plattLeftContourCorner m T) ↔ n ≤ m := by
  have hTpos : 0 < T := (abs_nonneg t₀).trans_lt hT
  rw [mem_Rect (by simp; linarith)
    (by simpa only [Complex.ofReal_im, plattLeftContourCorner_im] using
      (show (0 : ℝ) ≤ 2 * (m : ℝ) + 3 / 2 by positivity))]
  simp only [Complex.ofReal_re, Complex.ofReal_im, plattLeftContourCorner_re,
    plattLeftContourCorner_im, plattGammaPole_re, plattGammaPole_im]
  constructor
  · intro hn
    have hnm : (n : ℝ) < m + 1 := by linarith [hn.2.2.2]
    exact Nat.lt_succ_iff.mp (by exact_mod_cast hnm)
  · intro hn
    have hnm : (n : ℝ) ≤ m := by exact_mod_cast hn
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      linarith [le_abs_self t₀, neg_le_abs t₀, Nat.cast_nonneg (α := ℝ) n]

/-- All poles lie strictly off the rectangle boundary. -/
theorem plattGammaPole_not_mem_rectangleBorder (m n : ℕ) {t₀ T : ℝ} (hT : |t₀| < T) :
    plattGammaPole n t₀ ∉ RectangleBorder ((-T : ℝ) : ℂ) (plattLeftContourCorner m T) := by
  intro hb
  have hn := (plattGammaPole_mem_rectangle_iff m n hT).mp
    (rectangleBorder_subset_rectangle _ _ hb)
  have hnm : (n : ℝ) ≤ m := by exact_mod_cast hn
  have hTpos : 0 < T := (abs_nonneg t₀).trans_lt hT
  apply (not_mem_rectangleBorder_of_rectangle_mem_nhds ?_) hb
  rw [rectangle_mem_nhds_iff]
  simp only [Complex.mem_reProdIm, Complex.ofReal_re, Complex.ofReal_im,
    plattLeftContourCorner_re, plattLeftContourCorner_im, plattGammaPole_re, plattGammaPole_im]
  rw [uIoo_of_le (by linarith : -T ≤ T), uIoo_of_le (by positivity : 0 ≤ 2 * (m : ℝ) + 3 / 2)]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    linarith [le_abs_self t₀, neg_le_abs t₀, Nat.cast_nonneg (α := ℝ) n]

/-- The analytic pole set equals the image of the explicit bounded index set. -/
theorem plattContour_rectangle_poles (m k : ℕ) {t₀ T : ℝ} (hT : |t₀| < T) (h u : ℝ) :
    Rectangle ((-T : ℝ) : ℂ) (plattLeftContourCorner m T) ∩
      {z | meromorphicOrderAt (plattContourIntegrand k t₀ h u) z < 0} =
        (plattContourPoleFinset m t₀ : Set ℂ) := by
  classical
  ext z
  simp only [mem_inter_iff, mem_ofPred_eq, meromorphicOrderAt_plattContourIntegrand_neg_iff,
    plattContourPoleFinset, Finset.mem_coe, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨hz, n, rfl⟩
    exact ⟨n, Nat.lt_succ_iff.mpr ((plattGammaPole_mem_rectangle_iff m n hT).mp hz), rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨(plattGammaPole_mem_rectangle_iff m n hT).mpr (Nat.lt_succ_iff.mp hn), n, rfl⟩

/-- The finite contour integral is exactly the sum of the `m+1` proved residues. -/
theorem rectangleIntegral_plattContourIntegrand_eq_sum (m k : ℕ) {t₀ T : ℝ}
    (hT : |t₀| < T) (h u : ℝ) :
    RectangleIntegral' (plattContourIntegrand k t₀ h u)
      ((-T : ℝ) : ℂ) (plattLeftContourCorner m T) =
        ∑ n ∈ Finset.range (m + 1), plattContourResidueValue n k t₀ h u := by
  classical
  have hTpos : 0 < T := (abs_nonneg t₀).trans_lt hT
  have hset := plattContour_rectangle_poles m k hT h u
  have hb : Disjoint (RectangleBorder ((-T : ℝ) : ℂ) (plattLeftContourCorner m T))
      {z | meromorphicOrderAt (plattContourIntegrand k t₀ h u) z < 0} := by
    apply Set.disjoint_left.mpr
    intro z hz hp
    obtain ⟨n, rfl⟩ := (meromorphicOrderAt_plattContourIntegrand_neg_iff k t₀ h u z).mp hp
    exact plattGammaPole_not_mem_rectangleBorder m n hT hz
  rw [RectangleIntegral'_eq_sumResiduesIn (by simp; linarith)
    (by simpa only [Complex.ofReal_im, plattLeftContourCorner_im] using
      (show (0 : ℝ) ≤ 2 * (m : ℝ) + 3 / 2 by positivity))
    (fun z _ => meromorphicAt_plattContourIntegrand k t₀ h u z) hb
    (by rw [hset]; exact Finset.finite_toSet _) (hasSimplePolesOn_plattContourIntegrand k t₀ h u _),
    hset, sumResiduesIn, tsum_fintype,
    Finset.sum_finset_coe (fun z => residue (plattContourIntegrand k t₀ h u) z)
      (plattContourPoleFinset m t₀)]
  unfold plattContourPoleFinset
  rw [Finset.sum_image (by
    intro a ha b hb he
    exact plattGammaPole_injective t₀ he)]
  apply Finset.sum_congr rfl
  intro n hn
  exact residue_plattContourIntegrand n k t₀ h u

end

end PrimeFactorUnimodality
