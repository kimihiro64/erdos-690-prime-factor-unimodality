import PrimeFactorUnimodality.Helpers.Analytic.MomentChunkData

/-! # One reusable assembler for enclosed Dirichlet-moment atoms

The atom table is materialized once and reused across every moment column.
This assembler is independent of the chosen real base/radius enclosures;
the same finite-sum and residual-coverage proofs serve every numerical builder.
-/

namespace PrimeFactorUnimodality.MomentIntervalChunk

open Complex LeanCert.Core Finset

/-- Materialize the supplied atom builder once over the entire consecutive chunk. -/
def evaluateAtoms (r : MomentIntervalChunk) (degree : ℕ)
    (atom : ℕ → DirichletAtomInterval) : MomentChunkEvaluation degree :=
  let atoms := (List.range' r.first r.count).map atom
  ⟨atoms.all (fun a => residualWithinHalf a.residual),
    ComplexInterval.sumVectors (atoms.map
      (fun a => ComplexInterval.momentVector a.weight a.residual degree))⟩

/-- Each exact moment is enclosed whenever its atom weights and frequencies are enclosed. -/
theorem evaluateAtoms_mem (r : MomentIntervalChunk) (degree : ℕ)
    (atom : ℕ → DirichletAtomInterval) (weight : ℕ → ℂ) (frequency : ℕ → ℝ)
    (ha : ∀ n ∈ Ico r.first (r.first + r.count),
      weight n ∈ (atom n).weight ∧ frequency n ∈ (atom n).residual) (j : Fin degree) :
    expSumMoment (Ico r.first (r.first + r.count)) weight frequency j.val ∈
      (r.evaluateAtoms degree atom).columns[j.val] := by
  let value (n : ℕ) : ℂ := weight n * (I * (frequency n : ℂ)) ^ j.val / (j.val.factorial : ℂ)
  have hsum := ComplexInterval.sumVectors_sound (List.range' r.first r.count) value
    (fun n => let a := atom n
      ComplexInterval.momentVector a.weight a.residual degree) j (by
      intro n hn
      have ha' := ha n (by simpa using hn)
      exact ComplexInterval.momentVector_sound _ _ degree ha'.1 ha'.2 j)
  have hset : (List.range' r.first r.count).toFinset = Ico r.first (r.first + r.count) := by
    ext n
    simp
  have he : expSumMoment (Ico r.first (r.first + r.count)) weight frequency j.val =
      ((List.range' r.first r.count).map value).sum := by
    rw [expSumMoment, ← hset, List.sum_toFinset _ (List.nodup_range' ..)]
  rw [he]
  simpa only [evaluateAtoms, List.map_map, Function.comp_def] using hsum

/-- The shared residual check covers all chunk members, not just the endpoints. -/
theorem evaluateAtoms_residuals (r : MomentIntervalChunk) (degree : ℕ)
    (atom : ℕ → DirichletAtomInterval) (frequency : ℕ → ℝ)
    (ha : ∀ n ∈ Ico r.first (r.first + r.count), frequency n ∈ (atom n).residual)
    (h : (r.evaluateAtoms degree atom).residuals = true)
    {n : ℕ} (hn : n ∈ Ico r.first (r.first + r.count)) : |frequency n| ≤ (1 / 2 : ℝ) := by
  have hnlist : n ∈ List.range' r.first r.count := by simpa using hn
  have hcheck : residualWithinHalf (atom n).residual = true := by
    exact List.all_eq_true.mp h _ (List.mem_map.mpr ⟨n, hnlist, rfl⟩)
  exact abs_le_half_of_residualWithinHalf hcheck (ha n hn)

end PrimeFactorUnimodality.MomentIntervalChunk
