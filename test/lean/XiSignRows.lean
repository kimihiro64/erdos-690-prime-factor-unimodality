import PrimeFactorUnimodality.Helpers.Analytic.XiSignRows

/-! # Exact statement regressions for critical-line verification -/

namespace PrimeFactorUnimodality.Tests

open Complex Finset Set XiSignRows

example {row : XiSignRow} (h : row.Valid) :
    ∃ p : RiemannXiDivisorZeroIndex, (riemannXiDivisorZeroValue p).re = 1 / 2 ∧
      (riemannXiDivisorZeroValue p).im ∈ Set.Ioo (row.lower : ℝ) row.upper := by
  exact h.exists_index

example {a b : ℚ} (hab : a ≤ b) : Valid Fin.elim0 a b := by
  exact valid_empty hab

example {row : XiSignRow} (h : row.Valid) :
    Valid (fun _ : Fin 1 => row) row.lower row.upper := by
  exact valid_singleton h

example {n : ℕ} (t : Fin (n + 1) → ℚ) (ht : StrictMono t)
    (hsign : ∀ i : Fin n, xiCriticalLineValue (t i.castSucc) *
      xiCriticalLineValue (t i.succ) < 0) :
    Valid (ofEndpoints t) (t 0) (t (Fin.last n)) := by
  exact valid_of_endpoints t ht hsign

example {n m : ℕ} {rows : Fin n → XiSignRow} {next : Fin m → XiSignRow}
    {a b c : ℚ} (h : Valid rows a b) (h' : Valid next b c) :
    Valid (Fin.append rows next) a c := by
  exact h.append h'

example {n : ℕ} {rows : Fin n → XiSignRow} {a b : ℚ}
    (h : Valid rows a b) {t : Fin n → ℝ}
    (ht : ∀ i, t i ∈ Set.Ioo ((rows i).lower : ℝ) (rows i).upper) :
    Function.Injective t := by
  exact h.injective_of_mem ht

example {n : ℕ} {rows : Fin n → XiSignRow} {a b : ℚ}
    (h : Valid rows a b) :
    ∃ f : Fin n → RiemannXiDivisorZeroIndex, Function.Injective f ∧
      ∀ i, (riemannXiDivisorZeroValue (f i)).re = 1 / 2 ∧
        (riemannXiDivisorZeroValue (f i)).im ∈ Set.Ioo ((rows i).lower : ℝ) (rows i).upper := by
  exact h.exists_indices

example : Valid Fin.elim0 0 0 := valid_empty le_rfl

example {n : ℕ} {rows : Fin n → XiSignRow} {a b : ℚ} (h : Valid rows a b) :
    Valid (Fin.append Fin.elim0 rows) a b := (valid_empty le_rfl).append h

example {n : ℕ} {rows : Fin n → XiSignRow} {a b : ℚ} (h : Valid rows a b) :
    Valid (Fin.append rows Fin.elim0) a b := h.append (valid_empty le_rfl)

example {row next : XiSignRow} (h : row.Valid) (h' : next.Valid)
    (hj : row.upper = next.lower) :
    Valid (Fin.append (fun _ : Fin 1 => row) (fun _ : Fin 1 => next)) row.lower next.upper := by
  have hn : Valid (fun _ : Fin 1 => next) row.upper next.upper :=
    hj.symm ▸ valid_singleton h'
  exact (valid_singleton h).append hn

example {row : XiSignRow} (h : row.Valid) :
    ¬ Valid (fun _ : Fin 2 => row) row.lower row.upper := by
  intro hv
  exact (not_le_of_gt h.1) (hv.ordered 0 1 (by decide))

example {n : ℕ} (t : Fin (n + 1) → ℚ) (i : Fin n) :
    (ofEndpoints t i).lower = t i.castSucc ∧ (ofEndpoints t i).upper = t i.succ :=
  ⟨rfl, rfl⟩

end PrimeFactorUnimodality.Tests
