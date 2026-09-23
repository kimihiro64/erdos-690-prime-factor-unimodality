import Mathlib.Data.Fin.Tuple.Basic
import PrimeFactorUnimodality.Helpers.Analytic.XiCriticalLine

/-! # Compact ordered sign-change rows for critical-line verification

Rows store rational ordinate endpoints only. Local validity gives opposite
signs of the actual xi restriction; ordered placement makes the open
intervals disjoint, allowing shared endpoints. Blocks concatenate without
replaying their signs. Exhaustiveness is a separate total-count obligation,
not a consequence of finding many critical-line zeros.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- Rational data for one open ordinate interval. -/
structure XiSignRow where
  lower : ℚ
  upper : ℚ
  deriving DecidableEq

/-- A local witness has positive width and opposite nonzero endpoint signs. -/
def XiSignRow.Valid (row : XiSignRow) : Prop :=
  row.lower < row.upper ∧
    xiCriticalLineValue row.lower * xiCriticalLineValue row.upper < 0

/-- A checked row supplies an actual critical-line divisor label in its open interval. -/
theorem XiSignRow.Valid.exists_index {row : XiSignRow} (h : row.Valid) :
    ∃ p : RiemannXiDivisorZeroIndex, (riemannXiDivisorZeroValue p).re = 1 / 2 ∧
      (riemannXiDivisorZeroValue p).im ∈ Set.Ioo (row.lower : ℝ) row.upper :=
  exists_xi_criticalLine_index_of_sign_change (by exact_mod_cast h.1) h.2

namespace XiSignRows

/-- Valid rows lie in an ordered rational block; completeness is not included in this predicate. -/
structure Valid {n : ℕ} (rows : Fin n → XiSignRow) (a b : ℚ) : Prop where
  bounds : a ≤ b
  signs : ∀ i, (rows i).Valid
  lower : ∀ i, a ≤ (rows i).lower
  upper : ∀ i, (rows i).upper ≤ b
  ordered : ∀ i j, i < j → (rows i).upper ≤ (rows j).lower

/-- Empty blocks are valid and carry no invented zero witnesses. -/
theorem valid_empty {a b : ℚ} (hab : a ≤ b) : Valid Fin.elim0 a b := by
  refine ⟨hab, ?_, ?_, ?_, ?_⟩ <;> intro i <;> exact Fin.elim0 i

/-- A single checked interval is the base case for block composition. -/
theorem valid_singleton {row : XiSignRow} (h : row.Valid) :
    Valid (fun _ : Fin 1 => row) row.lower row.upper := by
  refine ⟨h.1.le, fun _ => h, fun _ => le_rfl, fun _ => le_rfl, ?_⟩
  intro i j hij
  have hh : ¬ i < j := by rw [Subsingleton.elim i j]; exact lt_irrefl _
  exact (hh hij).elim

/-- Consecutive rows share their rational endpoint data instead of copying interval pairs. -/
def ofEndpoints {n : ℕ} (t : Fin (n + 1) → ℚ) (i : Fin n) : XiSignRow :=
  ⟨t i.castSucc, t i.succ⟩

/-- An increasing endpoint sequence and adjacent sign changes give a complete ordered block. -/
theorem valid_of_endpoints {n : ℕ} (t : Fin (n + 1) → ℚ) (ht : StrictMono t)
    (hsign : ∀ i : Fin n, xiCriticalLineValue (t i.castSucc) *
      xiCriticalLineValue (t i.succ) < 0) :
    Valid (ofEndpoints t) (t 0) (t (Fin.last n)) := by
  refine ⟨ht.monotone (Fin.zero_le _), ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨ht (by simp), hsign i⟩
  · intro i
    exact ht.monotone (Fin.zero_le _)
  · intro i
    exact ht.monotone (Fin.le_last _)
  · intro i j hij
    apply ht.monotone
    change i.val + 1 ≤ j.val
    exact Nat.succ_le_of_lt hij

/-- Ordered blocks concatenate by their common rational boundary, reusing both sign proofs. -/
theorem Valid.append {n m : ℕ} {rows : Fin n → XiSignRow} {next : Fin m → XiSignRow}
    {a b c : ℚ} (h : Valid rows a b) (h' : Valid next b c) :
    Valid (Fin.append rows next) a c := by
  refine ⟨h.bounds.trans h'.bounds, ?_, ?_, ?_, ?_⟩
  · exact Fin.addCases (fun i => by simpa using h.signs i) (fun i => by simpa using h'.signs i)
  · exact Fin.addCases (fun i => by simpa using h.lower i)
      (fun i => by simpa using h.bounds.trans (h'.lower i))
  · exact Fin.addCases (fun i => by simpa using (h.upper i).trans h'.bounds)
      (fun i => by simpa using h'.upper i)
  · intro i j
    refine Fin.addCases ?_ ?_ i <;> intro k
    · refine Fin.addCases ?_ ?_ j <;> intro l hkl
      · change k.val < l.val at hkl
        simpa using h.ordered k l hkl
      · simpa using (h.upper k).trans (h'.lower l)
    · refine Fin.addCases ?_ ?_ j <;> intro l hkl
      · change n + k.val < l.val at hkl
        omega
      · change n + k.val < n + l.val at hkl
        simpa using h'.ordered k l (by omega)

/-- Any interior choices in an ordered block are distinct, including across a shared endpoint. -/
theorem Valid.injective_of_mem {n : ℕ} {rows : Fin n → XiSignRow} {a b : ℚ}
    (h : Valid rows a b) {t : Fin n → ℝ}
    (ht : ∀ i, t i ∈ Set.Ioo ((rows i).lower : ℝ) (rows i).upper) :
    Function.Injective t := by
  have hlt (i j : Fin n) (hij : i < j) : t i < t j := by
    have ho : ((rows i).upper : ℝ) ≤ (rows j).lower := by exact_mod_cast h.ordered i j hij
    exact (ht i).2.trans_le ho |>.trans (ht j).1
  exact (show StrictMono t from fun i j hij => hlt i j hij).injective

/-- Choosing one zero in each row gives an injective family of actual divisor labels. -/
theorem Valid.exists_indices {n : ℕ} {rows : Fin n → XiSignRow} {a b : ℚ}
    (h : Valid rows a b) :
    ∃ f : Fin n → RiemannXiDivisorZeroIndex, Function.Injective f ∧
      ∀ i, (riemannXiDivisorZeroValue (f i)).re = 1 / 2 ∧
        (riemannXiDivisorZeroValue (f i)).im ∈ Set.Ioo ((rows i).lower : ℝ) (rows i).upper := by
  choose f hf using fun i => (h.signs i).exists_index
  refine ⟨f, ?_, hf⟩
  have hinj := h.injective_of_mem (fun i => (hf i).2)
  intro i j hij
  exact hinj (congrArg (fun p => (riemannXiDivisorZeroValue p).im) hij)

end XiSignRows

end

end PrimeFactorUnimodality
