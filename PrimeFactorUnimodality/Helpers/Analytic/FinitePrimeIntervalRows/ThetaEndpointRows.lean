import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Core
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.ThetaRows

set_option autoImplicit false

/-! # Theta endpoint enclosures and interval coverage

Endpoint inequalities are transported by monotonicity of theta and logarithms.
The small endpoint seeds exercise the same assembler as the larger finite
ranges; this module does not import the generated prime interval certificates.
-/

namespace PrimeFactorUnimodality

noncomputable section

structure DusartThetaEndpointRow where
  left : Nat
  right : Nat
  left_large : 2 ≤ left
  left_le_right : left ≤ right
  theta_lower : Real
  theta_upper : Real
  theta_lower_le : theta_lower ≤ Chebyshev.theta left
  theta_right_le : Chebyshev.theta right ≤ theta_upper
  upper_error : theta_upper - left < (left : Real) / 36260
  lower_upper_error : theta_upper - left <
    (12323 / 10000 : Real) * (left : Real) / Real.log right
  lower_lower_error : right - theta_lower <
    (12323 / 10000 : Real) * (left : Real) / Real.log right

/-! Compact rows for the strict finite prefix used in Schoenfeld's theta
estimate.  They intentionally carry only the upper endpoint information;
the published relaxed error budget is assembled separately. -/
structure StrictThetaUpperRow where
  left : Nat
  right : Nat
  left_large : 2 ≤ left
  left_le_right : left ≤ right
  theta_upper : Real
  theta_right_le : Chebyshev.theta right ≤ theta_upper
  upper_error : theta_upper - left < 0

theorem theta_lower_of_unit_interval_endpoint
    {n : Nat} {a x : Real}
    (ha : 0 ≤ a)
    (hbound : a * ((n : Real) + 1) ≤ Chebyshev.theta (n : Real))
    (hleft : (n : Real) ≤ x)
    (hright : x < (n : Real) + 1) :
    a * x ≤ Chebyshev.theta x := by
  have hx_nonneg : 0 ≤ x := (Nat.cast_nonneg n).trans hleft
  have hfloor : ⌊x⌋₊ = n := by
    apply (Nat.floor_eq_iff hx_nonneg).2
    constructor
    · exact_mod_cast hleft
    · simpa using hright
  have htheta : Chebyshev.theta x = Chebyshev.theta (n : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hfloor]
  calc
    a * x ≤ a * ((n : Real) + 1) :=
      mul_le_mul_of_nonneg_left (le_of_lt hright) ha
    _ ≤ Chebyshev.theta (n : Real) := hbound
    _ = Chebyshev.theta x := htheta.symm

theorem theta_upper_of_unit_interval_endpoint
    {n : Nat} {b x : Real}
    (hb : 0 ≤ b)
    (hbound : Chebyshev.theta (n : Real) ≤ b * (n : Real))
    (hleft : (n : Real) ≤ x)
    (hright : x < (n : Real) + 1) :
    Chebyshev.theta x ≤ b * x := by
  have hx_nonneg : 0 ≤ x := (Nat.cast_nonneg n).trans hleft
  have hfloor : ⌊x⌋₊ = n := by
    apply (Nat.floor_eq_iff hx_nonneg).2
    constructor
    · exact_mod_cast hleft
    · simpa using hright
  have htheta : Chebyshev.theta x = Chebyshev.theta (n : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hfloor]
  calc
    Chebyshev.theta x = Chebyshev.theta (n : Real) := htheta
    _ ≤ b * (n : Real) := hbound
    _ ≤ b * x := mul_le_mul_of_nonneg_left hleft hb

def DusartThetaEndpointRow.toStrictUpperRow
    (row : DusartThetaEndpointRow)
    (hstrict : row.theta_upper < row.left) : StrictThetaUpperRow :=
  { left := row.left
    right := row.right
    left_large := row.left_large
    left_le_right := row.left_le_right
    theta_upper := row.theta_upper
    theta_right_le := row.theta_right_le
    upper_error := by
      exact sub_neg.mpr hstrict }

def DusartThetaEndpointRowsStrictUpperCoverUpTo
    (rows : List DusartThetaEndpointRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right ∧
      row.theta_upper < row.left

theorem strictThetaUpperRow_provides
    (row : StrictThetaUpperRow) {x : Real}
    (hleft : (row.left : Real) ≤ x) (hright : x ≤ row.right) :
    Chebyshev.theta x < x := by
  have htheta : Chebyshev.theta x ≤ row.theta_upper :=
    (Chebyshev.theta_mono hright).trans row.theta_right_le
  have hleft_pos : 0 ≤ (row.left : Real) := by positivity
  linarith [row.upper_error]

theorem hasStrictThetaUpperBelow_of_endpoint_rows
    {X : Real} {rows : List DusartThetaEndpointRow}
    (cover : DusartThetaEndpointRowsStrictUpperCoverUpTo rows X) :
    HasStrictThetaUpperBelow X := by
  intro x hx hX
  by_cases hsmall : x < 2
  · rw [Chebyshev.theta_eq_zero_of_lt_two hsmall]
    linarith
  · obtain ⟨row, hrow, hleft, hright, hstrict⟩ :=
      cover x (le_of_not_gt hsmall) hX
    exact strictThetaUpperRow_provides
      (row.toStrictUpperRow hstrict) hleft hright

def strictThetaUpperRow_singleton (n : Nat) (hn : 2 ≤ n)
    (hupper : Chebyshev.theta n < n) : StrictThetaUpperRow :=
  { left := n
    right := n
    left_large := hn
    left_le_right := le_rfl
    theta_upper := Chebyshev.theta n
    theta_right_le := le_rfl
    upper_error := by simpa using hupper }

def StrictThetaUpperRowsCoverUpTo
    (rows : List StrictThetaUpperRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem hasStrictThetaUpperBelow_of_rows
    {X : Real} {rows : List StrictThetaUpperRow}
    (cover : StrictThetaUpperRowsCoverUpTo rows X) :
    HasStrictThetaUpperBelow X := by
  intro x hx hX
  by_cases hsmall : x < 2
  · rw [Chebyshev.theta_eq_zero_of_lt_two hsmall]
    linarith
  · obtain ⟨row, hrow, hleft, hright⟩ := cover x (le_of_not_gt hsmall) hX
    exact strictThetaUpperRow_provides row hleft hright

def StrictThetaUpperIndexedCoverUpTo
    {n : Nat} (rows : Fin n → StrictThetaUpperRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ i : Fin n, ((rows i).left : Real) ≤ x ∧ x ≤ (rows i).right

theorem hasStrictThetaUpperBelow_of_indexed_rows
    {n : Nat} {rows : Fin n → StrictThetaUpperRow} {X : Real}
    (cover : StrictThetaUpperIndexedCoverUpTo rows X) :
    HasStrictThetaUpperBelow X := by
  intro x hx hX
  by_cases hsmall : x < 2
  · rw [Chebyshev.theta_eq_zero_of_lt_two hsmall]
    linarith
  · obtain ⟨i, hleft, hright⟩ := cover x (le_of_not_gt hsmall) hX
    exact strictThetaUpperRow_provides (rows i) hleft hright

theorem hasStrictThetaUpperBelow_of_prefix_and_indexed_rows
    {x₀ X : Real} (hprefix : HasStrictThetaUpperBelow x₀)
    {n : Nat} {rows : Fin n → StrictThetaUpperRow}
    (cover : ∀ x : Real, x₀ ≤ x → x ≤ X →
      ∃ i : Fin n, (rows i).left ≤ x ∧ x ≤ (rows i).right) :
    HasStrictThetaUpperBelow X := by
  intro x hx hX
  by_cases hsmall : x ≤ x₀
  · exact hprefix x hx hsmall
  · obtain ⟨i, hleft, hright⟩ := cover x
      (le_of_not_ge hsmall) hX
    exact strictThetaUpperRow_provides (rows i) hleft hright

theorem strictThetaUpperRowsCoverUpTo_append
    {m X : Real} {left right : List StrictThetaUpperRow}
    (hleft : StrictThetaUpperRowsCoverUpTo left m)
    (hright : StrictThetaUpperRowsCoverUpTo right X) :
    StrictThetaUpperRowsCoverUpTo (left ++ right) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hleft x hx hxm
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hright x hx hX
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩

theorem strictThetaUpperIndexedCoverUpTo_append
    {m X : Real} {n₁ n₂ : Nat}
    {left : Fin n₁ → StrictThetaUpperRow}
    {right : Fin n₂ → StrictThetaUpperRow}
    (hleft : StrictThetaUpperIndexedCoverUpTo left m)
    (hright : StrictThetaUpperIndexedCoverUpTo right X) :
    StrictThetaUpperIndexedCoverUpTo (Fin.append left right) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨i, hleft_lower, hleft_upper⟩ := hleft x hx hxm
    refine ⟨Fin.castAdd n₂ i, ?_⟩
    simpa [Fin.append_left] using And.intro hleft_lower hleft_upper
  · obtain ⟨i, hright_lower, hright_upper⟩ :=
      hright x hx hX
    refine ⟨Fin.natAdd n₁ i, ?_⟩
    simpa [Fin.append_right] using And.intro hright_lower hright_upper

theorem hasDusartSymmetricThetaBoundsBelow_of_strict_rows_and_lower
    {X : Real} {rows : List StrictThetaUpperRow}
    (cover : StrictThetaUpperRowsCoverUpTo rows X)
    (lower : ∀ x : Real, 2 < x → x ≤ X →
      |Chebyshev.theta x - x| <
        (12323 / 10000 : Real) * x / Real.log x) :
    HasDusartSymmetricThetaBoundsBelow X := by
  exact hasDusartSymmetricThetaBoundsBelow_of_strict_theta_prefix
    (hasStrictThetaUpperBelow_of_rows cover) lower

/-! The certificate-facing form of the preceding assembly.  Keeping the
strict-prefix rows indexed avoids converting a compact generated table into a
large list merely to feed the analytic boundary. -/
theorem hasDusartSymmetricThetaBoundsBelow_of_indexed_strict_rows_and_lower
    {X : Real} {n : Nat} {rows : Fin n → StrictThetaUpperRow}
    (cover : StrictThetaUpperIndexedCoverUpTo rows X)
    (lower : ∀ x : Real, 2 < x → x ≤ X →
      |Chebyshev.theta x - x| <
        (12323 / 10000 : Real) * x / Real.log x) :
    HasDusartSymmetricThetaBoundsBelow X := by
  exact hasDusartSymmetricThetaBoundsBelow_of_strict_theta_prefix
    (hasStrictThetaUpperBelow_of_indexed_rows cover) lower

theorem hasDusartSymmetricThetaBoundsBelow_of_prefix_and_indexed_strict_rows_and_lower
    {x₀ X : Real} (h2x₀ : (2 : Real) ≤ x₀)
    (hprefix : HasDusartSymmetricThetaBoundsBelow x₀)
    {n : Nat} {rows : Fin n → StrictThetaUpperRow}
    (cover : ∀ x : Real, x₀ ≤ x → x ≤ X →
      ∃ i : Fin n, (rows i).left ≤ x ∧ x ≤ (rows i).right)
    (lower : ∀ x : Real, 2 < x → x ≤ X →
      |Chebyshev.theta x - x| <
        (12323 / 10000 : Real) * x / Real.log x) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_upper_lower
  · intro x hx hX
    by_cases hsmall : x ≤ x₀
    · have hupper := hprefix.1 x (by linarith) hsmall
      nlinarith
    · obtain ⟨i, hleft, hright⟩ := cover x (le_of_not_ge hsmall) hX
      have hstrict := strictThetaUpperRow_provides (rows i) hleft hright
      have hxpos : 0 < x := by linarith
      have : 0 < x / (36260 : Real) := by positivity
      linarith
  · intro x hx hX
    by_cases hsmall : x ≤ x₀
    · exact hprefix.2 x hx hsmall
    · exact lower x hx hX

theorem theta_two_eq_log_two : Chebyshev.theta (2 : Real) = Real.log 2 := by
  have hprimes : Nat.primesLE 2 = {2} := by decide
  have hsum := Chebyshev.theta_eq_sum_primesLE_log 2
  rw [hprimes] at hsum
  simpa using hsum

/-! A singleton endpoint row is only sound when its three numerical endpoint
inequalities have already been proved.  Keeping those inequalities explicit
prevents a singleton constructor from being mistaken for a proof of a
nontrivial theta estimate. -/
def dusartThetaEndpointRow_two : DusartThetaEndpointRow :=
  { left := 2
    right := 2
    left_large := by norm_num
    left_le_right := by norm_num
    theta_lower := Chebyshev.theta 2
    theta_upper := Chebyshev.theta 2
    theta_lower_le := le_rfl
    theta_right_le := le_rfl
    upper_error := by
      have hlog : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
      rw [theta_two_eq_log_two]
      norm_num
      nlinarith [Real.log_two_lt_d9]
    lower_upper_error := by
      have hlog : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
      rw [theta_two_eq_log_two]
      norm_num
      have hpos : 0 < (12323 / 5000 : Real) / Real.log 2 :=
        div_pos (by norm_num) hlog
      nlinarith [Real.log_two_lt_d9]
    lower_lower_error := by
      have hlog : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
      rw [theta_two_eq_log_two]
      norm_num
      have hlt : Real.log 2 < 1 := by
        nlinarith [Real.log_two_lt_d9]
      have hquot : (2 : Real) < (12323 / 5000 : Real) / Real.log 2 := by
        apply (lt_div_iff₀ hlog).2
        nlinarith
      nlinarith }

/-! The next endpoint is small enough for a direct Chebyshev sum.  Keeping it
as an ordinary endpoint row lets the same cover and assembler consume it as
the larger finite tables. -/
def dusartThetaEndpointRow_three : DusartThetaEndpointRow := by
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 3
  have hp : Nat.primesLE 3 = {2, 3} := by decide
  rw [hp] at htheta
  norm_num [Nat.log, Nat.log.go] at htheta
  have hlog2pos : 0 < Real.log (2 : Real) :=
    Real.log_pos (by norm_num)
  have hlog3pos : 0 < Real.log (3 : Real) :=
    Real.log_pos (by norm_num)
  have htheta_lt : Chebyshev.theta (3 : Real) < 3 := by
    nlinarith [htheta, Real.log_two_lt_d9, Real.log_three_lt_d9]
  have hupper : Chebyshev.theta (3 : Real) - 3 < (3 : Real) / 36260 := by
    nlinarith
  have hlower_upper : Chebyshev.theta (3 : Real) - 3 <
      (12323 / 10000 : Real) * 3 / Real.log 3 := by
    have hrhs : 0 < (12323 / 10000 : Real) * 3 / Real.log 3 := by
      positivity
    linarith
  have htheta_nonneg : 0 ≤ Chebyshev.theta (3 : Real) :=
    Chebyshev.theta_nonneg 3
  have hdiff_nonneg : 0 ≤ (3 : Real) - Chebyshev.theta 3 := by
    linarith
  have hdiff_log : ((3 : Real) - Chebyshev.theta 3) * Real.log 3 <
      (3 : Real) * (11 / 10 : Real) := by
    have hlog3 : Real.log (3 : Real) < (11 : Real) / 10 := by
      linarith [Real.log_three_lt_d9]
    have hfirst := mul_le_mul_of_nonneg_left hlog3.le hdiff_nonneg
    have hsecond := mul_le_mul_of_nonneg_right
      (show (3 : Real) - Chebyshev.theta 3 ≤ 3 by linarith)
      (by norm_num : (0 : Real) ≤ (11 : Real) / 10)
    nlinarith
  have hlower_lower : (3 : Real) - Chebyshev.theta 3 <
      (12323 / 10000 : Real) * 3 / Real.log 3 := by
    apply (lt_div_iff₀ hlog3pos).2
    nlinarith [hdiff_log]
  exact
    { left := 3
      right := 3
      left_large := by norm_num
      left_le_right := by norm_num
      theta_lower := Chebyshev.theta 3
      theta_upper := Chebyshev.theta 3
      theta_lower_le := le_rfl
      theta_right_le := le_rfl
      upper_error := hupper
      lower_upper_error := hlower_upper
      lower_lower_error := hlower_lower }

def DusartThetaEndpointRowsCoverUpTo
    (rows : List DusartThetaEndpointRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

def dusartThetaEndpointRow_singleton (n : Nat) (hn : 2 ≤ n)
    (hupper : Chebyshev.theta n - n < (n : Real) / 36260)
    (hlower_upper : Chebyshev.theta n - n <
      (12323 / 10000 : Real) * (n : Real) / Real.log n)
    (hlower_lower : (n : Real) - Chebyshev.theta n <
      (12323 / 10000 : Real) * (n : Real) / Real.log n) :
    DusartThetaEndpointRow :=
  { left := n
    right := n
    left_large := hn
    left_le_right := le_rfl
    theta_lower := Chebyshev.theta n
    theta_upper := Chebyshev.theta n
    theta_lower_le := le_rfl
    theta_right_le := le_rfl
    upper_error := hupper
    lower_upper_error := hlower_upper
    lower_lower_error := hlower_lower }

/-! Endpoint rows are only used after the finite theta hprefix.  Requiring
them to cover from `2` would be false: the endpoint error budgets are the
large-`x` Dusart budgets, not a small-`x` theta estimate. -/
def DusartThetaEndpointRowsCoverFrom
    (rows : List DusartThetaEndpointRow) (x₀ X : Real) : Prop :=
  ∀ x : Real, x₀ ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem dusartThetaEndpointRow_two_cover :
    DusartThetaEndpointRowsCoverUpTo [dusartThetaEndpointRow_two] 2 := by
  intro x hx hX
  have hx2 : x = 2 := by linarith
  subst x
  exact ⟨dusartThetaEndpointRow_two, by simp, le_rfl, le_rfl⟩

theorem dusartThetaEndpointRow_singleton_cover (n : Nat) (hn : 2 ≤ n)
    (hupper : Chebyshev.theta n - n < (n : Real) / 36260)
    (hlower_upper : Chebyshev.theta n - n <
      (12323 / 10000 : Real) * (n : Real) / Real.log n)
    (hlower_lower : (n : Real) - Chebyshev.theta n <
      (12323 / 10000 : Real) * (n : Real) / Real.log n) :
    DusartThetaEndpointRowsCoverFrom
      [dusartThetaEndpointRow_singleton n hn hupper hlower_upper hlower_lower] n n := by
  intro x hx hX
  have hxN : x = n := by exact_mod_cast le_antisymm hX hx
  subst x
  exact ⟨dusartThetaEndpointRow_singleton n hn hupper hlower_upper hlower_lower,
    by simp, le_rfl, le_rfl⟩

def DusartThetaEndpointIndexedCoverUpTo {n : Nat}
    (rows : Fin n → DusartThetaEndpointRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ i : Fin n, (rows i).left ≤ x ∧ x ≤ (rows i).right

def DusartThetaEndpointIndexedCoverFrom {n : Nat}
    (rows : Fin n → DusartThetaEndpointRow) (x₀ X : Real) : Prop :=
  ∀ x : Real, x₀ ≤ x → x ≤ X →
    ∃ i : Fin n, (rows i).left ≤ x ∧ x ≤ (rows i).right

theorem dusartThetaEndpointIndexedCover_of_list
    {X : Real} {rows : List DusartThetaEndpointRow}
    (cover : DusartThetaEndpointRowsCoverUpTo rows X) :
    DusartThetaEndpointIndexedCoverUpTo
      (fun i : Fin rows.length => rows.get i) X := by
  exact indexed_interval_cover_of_list_cover rows
      (fun row => row.left) (fun row => row.right) cover

theorem dusartThetaEndpointIndexedCoverFrom_of_list
    {x₀ X : Real} {rows : List DusartThetaEndpointRow}
    (cover : DusartThetaEndpointRowsCoverFrom rows x₀ X) :
    DusartThetaEndpointIndexedCoverFrom
      (fun i : Fin rows.length => rows.get i) x₀ X := by
  exact indexed_interval_cover_of_list_cover rows
    (fun row => row.left) (fun row => row.right) cover

theorem dusartThetaEndpointIndexedCoverUpTo_append
    {m X : Real} {n₁ n₂ : Nat}
    {left : Fin n₁ → DusartThetaEndpointRow}
    {right : Fin n₂ → DusartThetaEndpointRow}
    (hleft : DusartThetaEndpointIndexedCoverUpTo left m)
    (hright : DusartThetaEndpointIndexedCoverUpTo right X) :
    DusartThetaEndpointIndexedCoverUpTo (Fin.append left right) X := by
  intro x hx hX
  exact indexed_interval_cover_append (Q := fun _ => True) left right
    (fun row => row.left) (fun row => row.right)
    (fun y hy _ hym => hleft y hy hym)
    (fun y hy _ hym hyX => hright y hy hyX)
    x hx trivial hX

theorem dusartThetaEndpointIndexedCoverFrom_append
    {x₀ m X : Real} {n₁ n₂ : Nat}
    {left : Fin n₁ → DusartThetaEndpointRow}
    {right : Fin n₂ → DusartThetaEndpointRow}
    (hleft : DusartThetaEndpointIndexedCoverFrom left x₀ m)
    (hright : DusartThetaEndpointIndexedCoverFrom right m X) :
    DusartThetaEndpointIndexedCoverFrom (Fin.append left right) x₀ X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨i, hleft_lower, hleft_upper⟩ := hleft x hx hxm
    refine ⟨Fin.castAdd n₂ i, ?_⟩
    simpa [Fin.append_left] using And.intro hleft_lower hleft_upper
  · obtain ⟨i, hright_lower, hright_upper⟩ :=
      hright x (le_of_not_ge hxm) hX
    refine ⟨Fin.natAdd n₁ i, ?_⟩
    simpa [Fin.append_right] using And.intro hright_lower hright_upper

def dusartThetaEndpointRow_provides
    (row : DusartThetaEndpointRow) {x : Real}
    (hleft : (row.left : Real) ≤ x) (hright : x ≤ row.right) :
    DusartThetaBoundsRow := by
  have hleft2 : (2 : Real) ≤ row.left := by exact_mod_cast row.left_large
  have hright2 : (2 : Real) ≤ (row.right : Real) := by
    exact le_trans hleft2 (by exact_mod_cast row.left_le_right)
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith [hleft2, hleft])
  have hlogr_pos : 0 < Real.log (row.right : Real) := Real.log_pos (by linarith)
  have htheta_lower : row.theta_lower ≤ Chebyshev.theta x :=
    row.theta_lower_le.trans (Chebyshev.theta_mono hleft)
  have htheta_upper : Chebyshev.theta x ≤ row.theta_upper :=
    (Chebyshev.theta_mono hright).trans row.theta_right_le
  have hlog_mono : Real.log x ≤ Real.log (row.right : Real) :=
    Real.log_le_log (by linarith) hright
  have hratio : (row.left : Real) / Real.log (row.right : Real) ≤
      x / Real.log x := by
    apply (div_le_div_iff₀ hlogr_pos hlogx_pos).2
    calc
      (row.left : Real) * Real.log x ≤
          (row.left : Real) * Real.log (row.right : Real) :=
        mul_le_mul_of_nonneg_left hlog_mono (by positivity)
      _ ≤ x * Real.log (row.right : Real) :=
        mul_le_mul_of_nonneg_right hleft (by positivity)
  refine {
    left := row.left
    right := row.right
    left_large := row.left_large
    left_le_right := row.left_le_right
    upper := ?_
    lower := ?_
  }
  · intro y hyl hyr
    have htheta_y_upper : Chebyshev.theta y ≤ row.theta_upper :=
      (Chebyshev.theta_mono hyr).trans row.theta_right_le
    have hleft_y : (row.left : Real) ≤ y := hyl
    calc
      Chebyshev.theta y - y ≤ row.theta_upper - row.left := by linarith
      _ < (row.left : Real) / 36260 := row.upper_error
      _ ≤ y / 36260 := by
        exact div_le_div_of_nonneg_right hleft_y (by norm_num)
  · intro y hy2 hyl hyr
    have htheta_y_lower : row.theta_lower ≤ Chebyshev.theta y :=
      row.theta_lower_le.trans (Chebyshev.theta_mono hyl)
    have htheta_y_upper : Chebyshev.theta y ≤ row.theta_upper :=
      (Chebyshev.theta_mono hyr).trans row.theta_right_le
    have hylog_pos : 0 < Real.log y := Real.log_pos (by linarith)
    have hratio_y : (row.left : Real) / Real.log (row.right : Real) ≤
        y / Real.log y := by
      apply (div_le_div_iff₀ hlogr_pos hylog_pos).2
      calc
        (row.left : Real) * Real.log y ≤
            (row.left : Real) * Real.log (row.right : Real) :=
          mul_le_mul_of_nonneg_left
            (Real.log_le_log (by linarith) hyr) (by positivity)
        _ ≤ y * Real.log (row.right : Real) :=
          mul_le_mul_of_nonneg_right hyl (by positivity)
    have hupper : Chebyshev.theta y - y <
        (12323 / 10000 : Real) * y / Real.log y := by
      calc
        Chebyshev.theta y - y ≤ row.theta_upper - row.left := by linarith
        _ < (12323 / 10000 : Real) * (row.left : Real) /
            Real.log (row.right : Real) := row.lower_upper_error
        _ ≤ (12323 / 10000 : Real) * y / Real.log y := by
          simpa only [mul_div_assoc] using
            mul_le_mul_of_nonneg_left hratio_y (by norm_num : (0 : Real) ≤ 12323 / 10000)
    have hlower : -((12323 / 10000 : Real) * y / Real.log y) <
        Chebyshev.theta y - y := by
      have hdiff : y - Chebyshev.theta y <
          (12323 / 10000 : Real) * y / Real.log y := by
        calc
          y - Chebyshev.theta y ≤ row.right - row.theta_lower := by linarith
          _ < (12323 / 10000 : Real) * (row.left : Real) /
              Real.log (row.right : Real) := row.lower_lower_error
          _ ≤ (12323 / 10000 : Real) * y / Real.log y := by
            simpa only [mul_div_assoc] using
              mul_le_mul_of_nonneg_left hratio_y (by norm_num : (0 : Real) ≤ 12323 / 10000)
      linarith
    exact (abs_lt).2 ⟨hlower, hupper⟩

theorem hasDusartSymmetricThetaBoundsBelow_of_indexed_endpoint_rows
    {n : Nat} {X : Real}
    {rows : Fin n → DusartThetaEndpointRow}
    (cover : DusartThetaEndpointIndexedCoverUpTo rows X) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_upper_lower
  · intro x hx hX
    by_cases hsmall : x < 2
    · rw [Chebyshev.theta_eq_zero_of_lt_two hsmall]
      nlinarith
    · obtain ⟨i, hleft, hright⟩ := cover x
        (le_of_not_gt hsmall) hX
      exact (dusartThetaEndpointRow_provides (rows i) hleft hright).upper
        x hleft hright
  · intro x hx hX
    obtain ⟨i, hleft, hright⟩ := cover x (by linarith) hX
    exact (dusartThetaEndpointRow_provides (rows i) hleft hright).lower
      x hx hleft hright

theorem dusartThetaEndpointRowsCoverUpTo_append
    {m X : Real} {left right : List DusartThetaEndpointRow}
    (hleft : DusartThetaEndpointRowsCoverUpTo left m)
    (hright : DusartThetaEndpointRowsCoverUpTo right X) :
    DusartThetaEndpointRowsCoverUpTo (left ++ right) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hleft x hx hxm
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hright x hx hX
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩

theorem dusartThetaEndpointRowsCoverFrom_append
    {x₀ m X : Real} {left right : List DusartThetaEndpointRow}
    (hleft : DusartThetaEndpointRowsCoverFrom left x₀ m)
    (hright : DusartThetaEndpointRowsCoverFrom right m X) :
    DusartThetaEndpointRowsCoverFrom (left ++ right) x₀ X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hleft x hx hxm
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ :=
      hright x (le_of_not_ge hxm) hX
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩

theorem hasDusartSymmetricThetaBoundsBelow_of_endpoint_rows
    {X : Real} {rows : List DusartThetaEndpointRow}
    (cover : DusartThetaEndpointRowsCoverUpTo rows X) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_upper_lower
  · intro x hx hX
    by_cases hsmall : x < 2
    · rw [Chebyshev.theta_eq_zero_of_lt_two hsmall]
      nlinarith
    · obtain ⟨row, hrow, hleft, hright⟩ := cover x
        (le_of_not_gt hsmall) hX
      exact (dusartThetaEndpointRow_provides row hleft hright).upper x
        hleft hright
  · intro x hx hX
    obtain ⟨row, hrow, hleft, hright⟩ := cover x (by linarith) hX
    exact (dusartThetaEndpointRow_provides row hleft hright).lower x hx
      hleft hright

theorem hasDusartSymmetricThetaBoundsBelow_of_prefix_and_endpoint_rows
    {x₀ X : Real} (h2x₀ : (2 : Real) ≤ x₀)
    (hprefix : HasDusartSymmetricThetaBoundsBelow x₀)
    {rows : List DusartThetaEndpointRow}
    (cover : DusartThetaEndpointRowsCoverFrom rows x₀ X) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_upper_lower
  · intro x hx hX
    by_cases hsmall : x ≤ x₀
    · exact hprefix.1 x (by linarith) hsmall
    · obtain ⟨row, hrow, hleft, hright⟩ := cover x
        (le_of_not_ge hsmall) hX
      exact (dusartThetaEndpointRow_provides row hleft hright).upper
        x hleft hright
  · intro x hx hX
    by_cases hsmall : x ≤ x₀
    · exact hprefix.2 x hx hsmall
    · obtain ⟨row, hrow, hleft, hright⟩ := cover x
        (le_of_not_ge hsmall) hX
      exact (dusartThetaEndpointRow_provides row hleft hright).lower
        x hx hleft hright

theorem hasDusartSymmetricThetaBoundsBelow_of_indexed_prefix_and_endpoint_rows
    {n : Nat} {x₀ X : Real} (h2x₀ : (2 : Real) ≤ x₀)
    (hprefix : HasDusartSymmetricThetaBoundsBelow x₀)
    {rows : Fin n → DusartThetaEndpointRow}
    (cover : DusartThetaEndpointIndexedCoverFrom rows x₀ X) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_upper_lower
  · intro x hx hX
    by_cases hsmall : x ≤ x₀
    · exact hprefix.1 x (by linarith) hsmall
    · obtain ⟨i, hleft, hright⟩ := cover x
        (le_of_not_ge hsmall) hX
      exact (dusartThetaEndpointRow_provides (rows i) hleft hright).upper
        x hleft hright
  · intro x hx hX
    by_cases hsmall : x ≤ x₀
    · exact hprefix.2 x hx hsmall
    · obtain ⟨i, hleft, hright⟩ := cover x
        (le_of_not_ge hsmall) hX
      exact (dusartThetaEndpointRow_provides (rows i) hleft hright).lower
        x hx hleft hright

/-! Compact chunks for the bounded theta endpoint table.  A chunk carries its
    coverage proof, so later generated bands can be appended without exposing
    one declaration per endpoint to the analytic assembly. -/
structure DusartThetaEndpointChunk where
  n : Nat
  cutoff : Real
  rows : Fin n → DusartThetaEndpointRow
  cover : DusartThetaEndpointIndexedCoverUpTo rows cutoff

def DusartThetaEndpointChunk.of_list
    {rows : List DusartThetaEndpointRow} {cutoff : Real}
    (cover : DusartThetaEndpointRowsCoverUpTo rows cutoff) :
    DusartThetaEndpointChunk :=
  { n := rows.length
    cutoff := cutoff
    rows := fun i => rows.get i
    cover := dusartThetaEndpointIndexedCover_of_list cover }

def DusartThetaEndpointChunk.append
    (left right : DusartThetaEndpointChunk) :
    DusartThetaEndpointChunk :=
  { n := left.n + right.n
    cutoff := right.cutoff
    rows := Fin.append left.rows right.rows
    cover := dusartThetaEndpointIndexedCoverUpTo_append
      left.cover right.cover }

def DusartThetaEndpointChunk.appendMany
    (first : DusartThetaEndpointChunk)
    (rest : List DusartThetaEndpointChunk) :
    DusartThetaEndpointChunk :=
  match rest with
  | [] => first
  | next :: tail =>
      DusartThetaEndpointChunk.appendMany
        (DusartThetaEndpointChunk.append first next) tail

theorem hasDusartSymmetricThetaBoundsBelow_of_endpoint_chunk
    (chunk : DusartThetaEndpointChunk) :
    HasDusartSymmetricThetaBoundsBelow chunk.cutoff := by
  exact hasDusartSymmetricThetaBoundsBelow_of_indexed_endpoint_rows
    chunk.cover

theorem hasDusartSymmetricThetaBoundsBelow_of_endpoint_chunks
    (first : DusartThetaEndpointChunk)
    (rest : List DusartThetaEndpointChunk) :
    HasDusartSymmetricThetaBoundsBelow
      (DusartThetaEndpointChunk.appendMany first rest).cutoff := by
  induction rest generalizing first with
  | nil =>
      exact hasDusartSymmetricThetaBoundsBelow_of_endpoint_chunk first
  | cons next tail ih =>
      exact ih (DusartThetaEndpointChunk.append first next)

def DusartThetaBoundsRowsCoverUpTo
    (rows : List DusartThetaBoundsRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem hasDusartSymmetricThetaBoundsBelow_of_rows
    {X : Real} {rows : List DusartThetaBoundsRow}
    (cover : DusartThetaBoundsRowsCoverUpTo rows X) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_upper_lower
  · intro x hx hX
    by_cases hsmall : x < 2
    · rw [Chebyshev.theta_eq_zero_of_lt_two hsmall]
      nlinarith
    · obtain ⟨row, hrow, hleft, hright⟩ := cover x
        (le_of_not_gt hsmall) hX
      exact row.upper x hleft hright
  · intro x hx hX
    obtain ⟨row, hrow, hleft, hright⟩ := cover x
      (by linarith) hX
    exact row.lower x hx hleft hright

end

end PrimeFactorUnimodality
