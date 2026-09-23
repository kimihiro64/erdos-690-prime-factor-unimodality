import PrimeFactorUnimodality.Helpers.Analytic.CheckedZetaMoments
import PrimeFactorUnimodality.Helpers.Analytic.RadixTwiddleChecks

/-! # Shared-moment interfaces and small rational regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset LeanCert.Core
open PrimeFactorUnimodality

variable {degree : ℕ}

open DirichletMomentBlock

example (d : ZetaGroupedBlock)
    (rows : List (DirichletMomentBlock d.degree)) (hcutoff : 0 < d.cutoff)
    (hchain : Chain 1 (d.cutoff + 1) rows) (hlabels : (rows.map group).Nodup)
    (hrows : ∀ r ∈ rows, r.Valid d.base d.radius)
    (hgroups : d.groups = (rows.map group).toFinset) (hbin : d.bin = binAt rows)
    (hcoeff : ∀ r ∈ rows, ∀ j : Fin d.degree,
      d.coefficient r.group j.val = r.coefficients[j.val].toComplex)
    (herror : ∀ r ∈ rows, ∀ j : Fin d.degree,
      (r.errors[j.val] : ℝ) ≤ d.coefficientError r.group j.val) : d.Valid := by
  exact PrimeFactorUnimodality.ZetaGroupedBlock.valid_of_moment_blocks d rows hcutoff hchain hlabels hrows hgroups hbin hcoeff herror

example (r : RationalGridRows) (d : ZetaGroupedBlock)
    (rows : List (DirichletMomentBlock d.degree)) (hcutoff : 0 < d.cutoff)
    (hchain : Chain 1 (d.cutoff + 1) rows) (hlabels : (rows.map group).Nodup)
    (hrows : ∀ a ∈ rows, a.Valid d.base d.radius)
    (hgroups : r.groups.toFinset = (rows.map group).toFinset) (hbin : d.bin = binAt rows)
    (hcoeff : ∀ a ∈ rows, ∀ j : Fin d.degree,
      r.coefficient a.group j.val = a.coefficients[j.val])
    (herror : ∀ a ∈ rows, ∀ j : Fin d.degree,
      (a.errors[j.val] : ℝ) ≤ d.coefficientError a.group j.val)
    (order : ℕ) (hgrid : r.check d.degree order = true) : (r.attach d).Valid := by
  exact PrimeFactorUnimodality.RationalGridRows.valid_of_moment_blocks r d rows hcutoff hchain hlabels hrows hgroups hbin hcoeff herror order hgrid

open DirichletMomentBlock

def unitMomentBlock : DirichletMomentBlock 1 :=
  ofChunk ⟨1, 1, 0, #v[0]⟩ #v[⟨1, 0⟩] #v[0]

theorem unitMomentBlock_valid : unitMomentBlock.Valid 0 0 := by
  simpa [unitMomentBlock] using valid_of_check (MomentIntervalChunk.mk 1 1 0 #v[0])
    (SharedTaylorIntervals.prepare_prepared 0) pi_mem_twiddlePi 0 0
    #v[⟨1, 0⟩] #v[0] (by decide +kernel)

def momentBase : ZetaGroupedBlock :=
  ⟨1, 0, 1, 0, 0, {0}, binAt [unitMomentBlock],
    fun _ _ => (RationalPoint.mk 1 0).toComplex, fun _ _ => 0⟩

def momentGrid : RationalGridRows :=
  ⟨[0], fun _ _ => ⟨1, 0⟩, 0,
    ⟨fun n => Vector.replicate (2 ^ (n + 1)) ⟨1, 0⟩, fun _ => 0⟩,
    fun _ => .leaf ⟨1, 0⟩ 0⟩

example : (momentGrid.attach momentBase).Valid := by
  apply momentGrid.valid_of_moment_blocks momentBase [unitMomentBlock]
    (by decide) ?_ (by decide) ?_ (by decide) rfl ?_ ?_ 0 (by decide +kernel)
  · exact (checkChain_eq_true 1 2 [unitMomentBlock]).mp (by decide +kernel)
  · intro a ha
    have he : a = unitMomentBlock := List.mem_singleton.mp ha
    subst a
    exact unitMomentBlock_valid
  · intro a ha j
    have he : a = unitMomentBlock := List.mem_singleton.mp ha
    subst a
    have hj : j.val = 0 := by have := j.isLt; change j.val < 1 at this; omega
    have hj' : j = (⟨0, by decide⟩ : Fin momentBase.degree) := Fin.ext hj
    subst j
    rfl
  · intro a ha j
    have he : a = unitMomentBlock := List.mem_singleton.mp ha
    subst a
    have hj : j.val = 0 := by have := j.isLt; change j.val < 1 at this; omega
    simp [momentBase, unitMomentBlock, ofChunk, hj]

end

end PrimeFactorUnimodality.Tests
