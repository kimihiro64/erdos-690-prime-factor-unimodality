import PrimeFactorUnimodality.Helpers.Analytic.XiCompletedRows

/-! # Scalar summaries of checked critical-line blocks

The exported propositions mention only a count, block boundaries and, when
needed, an integrated-count lower bound. Actual ordered sign rows remain
existential witnesses, so composition does not expose their endpoint vectors
in theorem statements. The common boundary prevents overlapping blocks from
double-counting a zero. Blocks below the integration window need only a count;
their area is exactly the count times the window width for any later cutoff.
These propositions alone do not change Lean's artifact import visibility.
The final integral consumer also checks `a ≤ b` and placement below `b`;
the scalar area identities themselves hold for arbitrary rational cutoffs.
-/

namespace PrimeFactorUnimodality.XiSignRows

/-- A checked block has this many ordered, disjoint critical-line sign intervals. -/
def CountSummary (n : ℕ) (left right : ℚ) : Prop :=
  ∃ rows : Fin n → XiSignRow, Valid rows left right

/-- A checked block has a lower bound on its rational completed-area expression at `a,b`. -/
def AreaSummary (n : ℕ) (left right a b area : ℚ) : Prop :=
  ∃ rows : Fin n → XiSignRow, Valid rows left right ∧ area ≤ completedAreaRat rows a b

/-- Retain the count and block boundaries without exposing the row vector. -/
theorem Valid.countSummary {n : ℕ} {rows : Fin n → XiSignRow} {left right : ℚ}
    (h : Valid rows left right) : CountSummary n left right := ⟨rows, h⟩

/-- Retain any proved lower bound on a block's completed area. -/
theorem Valid.areaSummary {n : ℕ} {rows : Fin n → XiSignRow} {left right a b area : ℚ}
    (h : Valid rows left right) (ha : area ≤ completedAreaRat rows a b) :
    AreaSummary n left right a b area := ⟨rows, h, ha⟩

/-- Empty blocks contain no zero witnesses. -/
theorem CountSummary.empty {left right : ℚ} (h : left ≤ right) :
    CountSummary 0 left right := (valid_empty h).countSummary

/-- Padding the enclosing interval does not change its witnesses or count. -/
theorem CountSummary.enlarge {n : ℕ} {left right L R : ℚ}
    (h : CountSummary n left right) (hL : L ≤ left) (hR : right ≤ R) :
    CountSummary n L R := by
  obtain ⟨rows, hr⟩ := h
  exact (hr.enlarge hL hR).countSummary

/-- Two ordered block summaries combine without revealing either row vector. -/
theorem CountSummary.append {n m : ℕ} {left middle right : ℚ}
    (h : CountSummary n left middle) (h' : CountSummary m middle right) :
    CountSummary (n + m) left right := by
  obtain ⟨rows, hr⟩ := h
  obtain ⟨next, hn⟩ := h'
  exact (hr.append hn).countSummary

/-- Once every upper endpoint has passed, no individual endpoint sum is needed. -/
theorem completedAreaRat_of_before {n : ℕ} (rows : Fin n → XiSignRow) (a b : ℚ)
    (h : ∀ i, (rows i).upper ≤ a) : completedAreaRat rows a b = (n : ℚ) * (b - a) := by
  simp [completedAreaRat, max_eq_left (h _), mul_sub]

/-- A count summary works for every later integration window, without replaying its rows. -/
theorem CountSummary.area_before {n : ℕ} {left right a b : ℚ}
    (h : CountSummary n left right) (ha : right ≤ a) :
    AreaSummary n left right a b ((n : ℚ) * (b - a)) := by
  obtain ⟨rows, hr⟩ := h
  exact hr.areaSummary (completedAreaRat_of_before rows a b
    (fun i => (hr.upper i).trans ha)).ge

/-- A rational lower bound may be rounded down, never up. -/
theorem AreaSummary.weaken {n : ℕ} {left right a b area lower : ℚ}
    (h : AreaSummary n left right a b area) (hl : lower ≤ area) :
    AreaSummary n left right a b lower := by
  obtain ⟨rows, hr, ha⟩ := h
  exact hr.areaSummary (hl.trans ha)

/-- Widening placement preserves the integral window and its area bound. -/
theorem AreaSummary.enlarge {n : ℕ} {left right L R a b area : ℚ}
    (h : AreaSummary n left right a b area) (hL : L ≤ left) (hR : right ≤ R) :
    AreaSummary n L R a b area := by
  obtain ⟨rows, hr, ha⟩ := h
  exact (hr.enlarge hL hR).areaSummary ha

/-- The seam enforces disjointness while both counts and certified areas add. -/
theorem AreaSummary.append {n m : ℕ} {left middle right a b area nextArea : ℚ}
    (h : AreaSummary n left middle a b area)
    (h' : AreaSummary m middle right a b nextArea) :
    AreaSummary (n + m) left right a b (area + nextArea) := by
  obtain ⟨rows, hr, ha⟩ := h
  obtain ⟨next, hn, hb⟩ := h'
  apply (hr.append hn).areaSummary
  rw [completedAreaRat_append]
  exact add_le_add ha hb

/-- Changing the upper integration limit adds the same width once for each row. -/
theorem completedAreaRat_shift_upper {n : ℕ} (rows : Fin n → XiSignRow) (a b b' : ℚ) :
    completedAreaRat rows a b' = completedAreaRat rows a b + (n : ℚ) * (b' - b) := by
  simp only [completedAreaRat, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_fin, nsmul_eq_mul]
  ring

/-- A new upper cutoff reuses the same area summary by a scalar correction. -/
theorem AreaSummary.shift_upper {n : ℕ} {left right a b area : ℚ}
    (h : AreaSummary n left right a b area) (b' : ℚ) :
    AreaSummary n left right a b' (area + (n : ℚ) * (b' - b)) := by
  obtain ⟨rows, hr, ha⟩ := h
  apply hr.areaSummary
  rw [completedAreaRat_shift_upper rows a b b']
  exact add_le_add ha le_rfl

end PrimeFactorUnimodality.XiSignRows
