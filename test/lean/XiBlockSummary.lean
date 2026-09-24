import PrimeFactorUnimodality.Helpers.Analytic.XiBlockSummary

/-! # Count and area summaries preserve disjointness, clipping and scalar bounds -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

open XiSignRows

example {n : ℕ} {rows : Fin n → XiSignRow} {left right : ℚ}
    (h : Valid rows left right) : CountSummary n left right := h.countSummary

example {n : ℕ} {rows : Fin n → XiSignRow} {left right a b area : ℚ}
    (h : Valid rows left right) (ha : area ≤ completedAreaRat rows a b) :
    AreaSummary n left right a b area := h.areaSummary ha

example : CountSummary 0 0 100 := CountSummary.empty (by norm_num)

example {n m k : ℕ} {a b c d : ℚ}
    (h : CountSummary n a b) (h' : CountSummary m b c) (h'' : CountSummary k c d) :
    CountSummary ((n + m) + k) a d := (h.append h').append h''

example {n : ℕ} (h : CountSummary n 10 20) : CountSummary n 0 25 :=
  h.enlarge (by norm_num) (by norm_num)

example {n : ℕ} {left right a b : ℚ} (h : CountSummary n left right) (ha : right ≤ a) :
    AreaSummary n left right a b ((n : ℚ) * (b - a)) := h.area_before ha

example {n : ℕ} (h : CountSummary n 0 100) : AreaSummary n 0 100 100 103 (3 * n) := by
  convert h.area_before (b := 103) (le_refl 100) using 1
  ring

example {n : ℕ} (h : CountSummary n 0 100) : AreaSummary n 0 100 102 103 n := by
  convert h.area_before (b := 103) (by norm_num : (100 : ℚ) ≤ 102) using 1
  norm_num

example {n m : ℕ} {left middle right a b area nextArea : ℚ}
    (h : AreaSummary n left middle a b area)
    (h' : AreaSummary m middle right a b nextArea) :
    AreaSummary (n + m) left right a b (area + nextArea) := h.append h'

example {n : ℕ} {left right a b : ℚ} (h : AreaSummary n left right a b 5) :
    AreaSummary n left right a b 4 := h.weaken (by norm_num)

example {n : ℕ} {a b area : ℚ} (h : AreaSummary n 10 20 a b area) :
    AreaSummary n 0 25 a b area := h.enlarge (by norm_num) (by norm_num)

example {n : ℕ} {left right a b area : ℚ}
    (h : AreaSummary n left right a b area) (b' : ℚ) :
    AreaSummary n left right a b' (area + (n : ℚ) * (b' - b)) := h.shift_upper b'

example {n : ℕ} {area : ℚ} (h : AreaSummary n 0 20 10 20 area) :
    AreaSummary n 0 25 10 25 (area + 5 * n) := by
  convert (h.shift_upper 25).enlarge le_rfl (by norm_num : (20 : ℚ) ≤ 25) using 1
  ring

example (a : ℚ) : ¬ CountSummary 1 a a := by
  rintro ⟨rows, h⟩
  have hl := h.lower 0
  have hu := h.upper 0
  have hs := (h.signs 0).1
  linarith

example {n : ℕ} {a area : ℚ} (h : AreaSummary n 0 a a a area) : area ≤ 0 := by
  obtain ⟨rows, hr, ha⟩ := h
  rw [completedAreaRat_of_before rows a a hr.upper] at ha
  simpa using ha

example {n : ℕ} {area : ℚ} (_h : AreaSummary n 0 10 10 11 area) : True := by
  fail_if_success have bad : AreaSummary (n + n) 0 10 10 11 (area + area) := _h.append _h
  trivial

example : completedAreaRat (fun _ : Fin 1 => (⟨32, 34⟩ : XiSignRow)) 33 35 = 1 := by
  norm_num [completedAreaRat]

example : completedAreaRat (fun _ : Fin 1 => (⟨31, 32⟩ : XiSignRow)) 33 35 = 2 := by
  norm_num [completedAreaRat]

end PrimeFactorUnimodality.Tests
