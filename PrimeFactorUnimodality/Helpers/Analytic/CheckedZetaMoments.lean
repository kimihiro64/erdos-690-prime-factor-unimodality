import PrimeFactorUnimodality.Helpers.Analytic.CheckedZetaGrid
import PrimeFactorUnimodality.Helpers.Analytic.MomentBlockPartition

/-! # Checked moment blocks supply the actual shared zeta hypotheses

The ordered partition proves complete index coverage. Each group receives
its independently checked or composed block bounds; coefficient identities
and rational error budgets connect the retained data to the Fourier input.
No whole-moment enclosure is assumed independently of those checked blocks.
-/

namespace PrimeFactorUnimodality

open Complex Finset DirichletMomentBlock

/-- An ordered partition of checked blocks discharges every shared-moment obligation. -/
theorem ZetaGroupedBlock.valid_of_moment_blocks (d : ZetaGroupedBlock)
    (rows : List (DirichletMomentBlock d.degree)) (hcutoff : 0 < d.cutoff)
    (hchain : Chain 1 (d.cutoff + 1) rows) (hlabels : (rows.map group).Nodup)
    (hrows : ∀ r ∈ rows, r.Valid d.base d.radius)
    (hgroups : d.groups = (rows.map group).toFinset) (hbin : d.bin = binAt rows)
    (hcoeff : ∀ r ∈ rows, ∀ j : Fin d.degree,
      d.coefficient r.group j.val = r.coefficients[j.val].toComplex)
    (herror : ∀ r ∈ rows, ∀ j : Fin d.degree,
      (r.errors[j.val] : ℝ) ≤ d.coefficientError r.group j.val) : d.Valid := by
  have hprefix : Icc 1 d.cutoff = Ico 1 (d.cutoff + 1) := by
    ext n
    simp only [mem_Icc, mem_Ico]
    omega
  refine ⟨hcutoff, ?_, ?_, ?_⟩
  · intro n hn
    rw [hprefix] at hn
    obtain ⟨r, hr, _, hb⟩ := hchain.select (mem_Ico.mp hn)
    rw [hgroups, hbin, hb]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨r, hr, rfl⟩)
  · intro n hn
    rw [hprefix] at hn
    obtain ⟨r, hr, hnr, hb⟩ := hchain.select (mem_Ico.mp hn)
    simpa only [dirichletFrequency, hbin, hb] using (hrows r hr).residual n hnr
  · intro b hb j hj
    rw [hgroups] at hb
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
    have hset : ((Icc 1 d.cutoff).filter (fun n => d.bin n = r.group)) =
        Ico r.first r.stop := by
      rw [hprefix, hbin]
      exact hchain.filter_eq hlabels hr
    rw [hset, hcoeff r hr ⟨j, mem_range.mp hj⟩]
    exact ((hrows r hr).moments ⟨j, mem_range.mp hj⟩).trans
      (herror r hr ⟨j, mem_range.mp hj⟩)

/-- Checked finite moments and checked Fourier arithmetic give the complete shared grid validity. -/
theorem RationalGridRows.valid_of_moment_blocks (r : RationalGridRows) (d : ZetaGroupedBlock)
    (rows : List (DirichletMomentBlock d.degree)) (hcutoff : 0 < d.cutoff)
    (hchain : Chain 1 (d.cutoff + 1) rows) (hlabels : (rows.map group).Nodup)
    (hrows : ∀ a ∈ rows, a.Valid d.base d.radius)
    (hgroups : r.groups.toFinset = (rows.map group).toFinset) (hbin : d.bin = binAt rows)
    (hcoeff : ∀ a ∈ rows, ∀ j : Fin d.degree,
      r.coefficient a.group j.val = a.coefficients[j.val])
    (herror : ∀ a ∈ rows, ∀ j : Fin d.degree,
      (a.errors[j.val] : ℝ) ≤ d.coefficientError a.group j.val)
    (order : ℕ) (hgrid : r.check d.degree order = true) : (r.attach d).Valid := by
  apply r.valid_of_check d ?_ order hgrid
  apply ZetaGroupedBlock.valid_of_moment_blocks (r.attach d).shared rows hcutoff
    hchain hlabels hrows hgroups hbin ?_ herror
  intro a ha j
  exact congrArg RationalPoint.toComplex (hcoeff a ha j)

end PrimeFactorUnimodality
