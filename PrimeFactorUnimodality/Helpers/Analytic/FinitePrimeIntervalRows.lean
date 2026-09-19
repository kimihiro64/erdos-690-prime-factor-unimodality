import PrimeFactorUnimodality.Helpers.Analytic.ShortIntervalPrime
import PrimeFactorUnimodality.Helpers.Analytic.ThetaFromPsi
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitThetaBounds
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCounting

set_option autoImplicit false

/-! # Shared finite row coverage for short prime intervals

The medium numerical part of the explicit interval theorem is naturally a
finite cover.  This module keeps the cover data separate from its consumer:
one row supplies one verified prime, and the cover theorem propagates that
prime to every real point in the row.  Thus a table of rows can be checked as
one list rather than as a collection of one-file witness replays. -/

namespace PrimeFactorUnimodality

noncomputable section

/-! A finite prime-gap computation can be stated purely over `Nat`; the
real-variable short-interval conclusion is then a separate theorem.  This
keeps the computational kernel from seeing any real logarithm expressions. -/
def FinitePrimeGapBound (a b g : Nat) : Prop :=
  ∀ n : Nat, a ≤ n → n ≤ b →
    ∃ q : Nat, q.Prime ∧ n < q ∧ q ≤ n + g

/-! The bounded-witness form is computationally finite in both coordinates.
The witness type is deliberately bounded by `b + g + 1`; this is enough for
every row and makes the proposition suitable for one indexed kernel check. -/
def FinitePrimeGapIndexedCertificate (a b g : Nat) : Prop :=
  ∀ n : Fin (b + 1), a ≤ n.val →
    ∃ q : Fin (b + g + 1), q.val.Prime ∧ n.val < q.val ∧
      q.val ≤ n.val + g

theorem finitePrimeGapBound_of_indexed_certificate
    {a b g : Nat}
    (certificate : FinitePrimeGapIndexedCertificate a b g) :
    FinitePrimeGapBound a b g := by
  intro n hna hnb
  let i : Fin (b + 1) := ⟨n, by omega⟩
  obtain ⟨q, hq, hnq, hq_bound⟩ := certificate i (by simpa [i] using hna)
  exact ⟨q.val, hq, hnq, hq_bound⟩

/-! Adjacent gap tables can be composed before they are turned into a real
interval statement.  This is the basic block operation for the finite
Dusart computation: the arithmetic kernel may check independently generated
blocks, while the analytic consumer sees one bounded gap theorem. -/
theorem finitePrimeGapBound_append
    {a m b g : Nat}
    (left : FinitePrimeGapBound a m g)
    (right : FinitePrimeGapBound (m + 1) b g) :
    FinitePrimeGapBound a b g := by
  intro n hna hnb
  by_cases hnm : n ≤ m
  · exact left n hna hnm
  · exact right n (by omega) hnb

theorem finitePrimeGapIndexedCertificate_append
    {a m b g : Nat} (hmb : m ≤ b)
    (left : FinitePrimeGapIndexedCertificate a m g)
    (right : FinitePrimeGapIndexedCertificate (m + 1) b g) :
    FinitePrimeGapIndexedCertificate a b g := by
  intro n hna
  by_cases hnm : n.val ≤ m
  · obtain ⟨q, hq, hnq, hq_bound⟩ := left
      ⟨n.val, by omega⟩ (by omega)
    refine ⟨⟨q.val, by omega⟩, hq, hnq, ?_⟩
    exact hq_bound
  · obtain ⟨q, hq, hnq, hq_bound⟩ := right n (by omega)
    refine ⟨⟨q.val, by omega⟩, hq, hnq, ?_⟩
    exact hq_bound

/-! A gap table can use intervals instead of one entry per integer.  A row
records one prime which lies immediately to the right of the whole row and
whose distance from the row's left endpoint is at most `g`. -/
structure FinitePrimeGapRow (g : Nat) where
  left : Nat
  right : Nat
  left_le_right : left ≤ right
  witness : Nat
  witness_prime : witness.Prime
  right_lt_witness : right < witness
  witness_le_left_add_gap : witness ≤ left + g

theorem finitePrimeGapRow_of_consecutive
    {g p q : Nat} (h : ConsecutivePrimes p q)
    (hgap : q ≤ p + g) : FinitePrimeGapRow g := by
  refine {
    left := p
    right := q - 1
    left_le_right := by omega
    witness := q
    witness_prime := h.right_prime
    right_lt_witness := by omega
    witness_le_left_add_gap := hgap }

def logCubedWidth (x : Real) : Real :=
  x / (Real.log x) ^ 3

/-! The sharp logarithmic bound has a varying admissible gap.  This row form
stores that local width directly, so a finite table need not be padded to the
largest gap in the table. -/
structure FinitePrimeGapLogRow where
  left : Nat
  right : Nat
  left_large : 89693 ≤ left
  left_le_right : left ≤ right
  witness : Nat
  witness_prime : witness.Prime
  right_lt_witness : right < witness
  witness_width : (witness : Real) - left ≤ logCubedWidth left

inductive FinitePrimeGapLogRowsChain : Nat → Nat →
    List FinitePrimeGapLogRow → Prop
  | empty {a b : Nat} (h : b < a) :
      FinitePrimeGapLogRowsChain a b []
  | cons {a b : Nat} (row : FinitePrimeGapLogRow)
      (hleft : row.left ≤ a)
      (hordered : row.left ≤ row.right)
      {tail : List FinitePrimeGapLogRow}
      (htail : FinitePrimeGapLogRowsChain (row.right + 1) b tail) :
      FinitePrimeGapLogRowsChain a b (row :: tail)

theorem finitePrimeGapLogRowsCover_of_chain
    {a b : Nat} {rows : List FinitePrimeGapLogRow}
    (chain : FinitePrimeGapLogRowsChain a b rows) :
    ∀ x : Real, (a : Real) ≤ x → x ≤ b →
      ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right := by
  induction chain with
  | empty h =>
      intro x hax hxb
      have hab : (b : Real) < a := by exact_mod_cast h
      linarith
  | @cons a b row hleft hordered tail htail ih =>
      intro x hax hxb
      by_cases hrow : x ≤ row.right
      · refine ⟨row, by simp, ?_, hrow⟩
        have hleft' : (row.left : Real) ≤ a := by
          exact_mod_cast hleft
        exact hleft'.trans hax
      · have hright : (row.right + 1 : Real) ≤ x := by
          have hlt : (row.right : Real) < x := lt_of_not_ge hrow
          linarith
        obtain ⟨next, hnext, hnext_left, hnext_right⟩ :=
          ih x hright hxb
        exact ⟨next, by simp [hnext], hnext_left, hnext_right⟩

def FinitePrimeGapLogRow.of_gap_row
    {g : Nat} (row : FinitePrimeGapRow g)
    (hleft : (89693 : Nat) ≤ row.left)
    {L : Real} (hL : 0 ≤ L)
    (hlog : Real.log row.left ≤ L)
    (hproduct : (g : Real) * L ^ 3 ≤ row.left) :
    FinitePrimeGapLogRow := by
  have hwidth : (g : Real) ≤ logCubedWidth row.left :=
    logCubedWidth_lower_of_log_upper (by exact_mod_cast hleft)
      hL hlog hproduct
  refine {
    left := row.left
    right := row.right
    left_large := hleft
    left_le_right := row.left_le_right
    witness := row.witness
    witness_prime := row.witness_prime
    right_lt_witness := row.right_lt_witness
    witness_width := ?_ }
  have hgap : (row.witness : Real) - row.left ≤ (g : Real) := by
    exact_mod_cast (by omega : row.witness - row.left ≤ g)
  exact hgap.trans hwidth

theorem finitePrimeGapLogRow_of_explicit
    {p q : Nat} {L : Real}
    (hq : q.Prime)
    (hpq : p < q)
    (hleft_large : 89693 ≤ p)
    (hlog : Real.log p ≤ L) (hL : 0 ≤ L)
    (hproduct : (q - p : Real) * L ^ 3 ≤ p) :
    FinitePrimeGapLogRow := by
  have hwidth : (q - p : Real) ≤ logCubedWidth p :=
    logCubedWidth_lower_of_log_upper (by exact_mod_cast hleft_large)
      hL hlog hproduct
  refine {
    left := p
    right := q - 1
    left_large := hleft_large
    left_le_right := by omega
    witness := q
    witness_prime := hq
    right_lt_witness := by omega
    witness_width := ?_ }
  have hgap_real : (q : Real) - p ≤ (q - p : Real) := by
    norm_num [Nat.cast_sub (Nat.le_of_lt hpq)]
  linarith

def FinitePrimeGapRowsCover
    {a b g : Nat} (rows : List (FinitePrimeGapRow g)) : Prop :=
  ∀ n : Nat, a ≤ n → n ≤ b →
    ∃ row ∈ rows, row.left ≤ n ∧ n ≤ row.right

def FinitePrimeGapIndexedRowsCover
    {a b g n : Nat} (rows : Fin n → FinitePrimeGapRow g) : Prop :=
  ∀ x : Nat, a ≤ x → x ≤ b →
    ∃ i : Fin n, (rows i).left ≤ x ∧ x ≤ (rows i).right

theorem finitePrimeGapRowsCover_append
    {a m b g : Nat}
    {left right : List (FinitePrimeGapRow g)}
    (hleft : FinitePrimeGapRowsCover (a := a) (b := m) left)
    (hright : FinitePrimeGapRowsCover (a := m + 1) (b := b) right) :
    FinitePrimeGapRowsCover (a := a) (b := b) (left ++ right) := by
  intro n hna hnb
  by_cases hnm : n ≤ m
  · obtain ⟨row, hrow, hrow_left, hrow_right⟩ := hleft n hna hnm
    exact ⟨row, by simp [hrow], hrow_left, hrow_right⟩
  · obtain ⟨row, hrow, hrow_left, hrow_right⟩ :=
      hright n (by omega) hnb
    exact ⟨row, by simp [hrow], hrow_left, hrow_right⟩

theorem finitePrimeGapBound_of_rows_cover
    {a b g : Nat} {rows : List (FinitePrimeGapRow g)}
    (cover : FinitePrimeGapRowsCover rows) :
    FinitePrimeGapBound a b g := by
  intro n hna hnb
  obtain ⟨row, hrow, hleft, hright⟩ := cover n hna hnb
  refine ⟨row.witness, row.witness_prime, ?_, ?_⟩
  · exact lt_of_le_of_lt hright row.right_lt_witness
  · exact le_trans row.witness_le_left_add_gap (Nat.add_le_add_right hleft g)

theorem finitePrimeGapBound_of_indexed_rows_cover
    {a b g n : Nat} {rows : Fin n → FinitePrimeGapRow g}
    (cover : FinitePrimeGapIndexedRowsCover rows) :
    FinitePrimeGapBound a b g := by
  intro x hxa hxb
  obtain ⟨i, hleft, hright⟩ := cover x hxa hxb
  refine ⟨(rows i).witness, (rows i).witness_prime, ?_, ?_⟩
  · exact lt_of_le_of_lt hright (rows i).right_lt_witness
  · exact le_trans (rows i).witness_le_left_add_gap
      (Nat.add_le_add_right hleft g)

theorem finitePrimeGapIndexedRowsCover_of_list
    {a b g : Nat} {rows : List (FinitePrimeGapRow g)}
    (cover : FinitePrimeGapRowsCover rows) :
    FinitePrimeGapIndexedRowsCover
      (fun i : Fin rows.length => rows.get i) := by
  intro x hxa hxb
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hxa hxb
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hrow
  refine ⟨⟨i, hi⟩, ?_⟩
  simpa [List.get_eq_getElem, hget] using And.intro hleft hright

theorem exists_prime_in_real_interval_of_finite_prime_gap_bound
    {a b g : Nat} {x : Real}
    (gap : FinitePrimeGapBound a b g)
    (hx_nonneg : 0 ≤ x) (hx_lower : (a : Real) ≤ x)
    (hx_upper : x ≤ b)
    (width : (g : Real) ≤ x / (Real.log x) ^ 3) :
    ∃ q : Nat, q.Prime ∧ x < q ∧
      (q : Real) ≤ x + x / (Real.log x) ^ 3 := by
  let n : Nat := ⌊x⌋₊
  have hn_lower : a ≤ n := by
    exact Nat.le_floor hx_lower
  have hn_upper : n ≤ b := by
    exact Nat.floor_le_of_le hx_upper
  obtain ⟨q, hq_prime, hnq, hq_upper⟩ := gap n hn_lower hn_upper
  have hn_floor : (n : Real) ≤ x := by
    exact Nat.floor_le hx_nonneg
  have hx_floor : x < (n : Real) + 1 := by
    simpa only [n] using Nat.lt_floor_add_one x
  have hq_lower : (n : Real) + 1 ≤ q := by
    exact_mod_cast (Nat.succ_le_iff.mpr hnq)
  refine ⟨q, hq_prime, ?_, ?_⟩
  · have hq_real : (n : Real) + 1 ≤ (q : Real) := by
      exact hq_lower
    linarith
  · have hq_upper_real : (q : Real) ≤ (n : Real) + g := by
      exact_mod_cast hq_upper
    linarith

theorem hasLogCubedShortIntervalPrimeBelow_of_finite_prime_gap_bound
    {X : Real} {b g : Nat}
    (hX : (89693 : Real) ≤ X)
    (hXb : X ≤ b)
    (gap : FinitePrimeGapBound 89689 b g)
    (width : ∀ x : Real, 89693 ≤ x → x ≤ X →
      (g : Real) ≤ x / (Real.log x) ^ 3) :
    HasLogCubedShortIntervalPrimeBelow X := by
  intro x hx hxx
  exact exists_prime_in_real_interval_of_finite_prime_gap_bound gap
    (by linarith) (by linarith) (hxx.trans hXb)
    (width x hx hxx)

theorem hasLogCubedShortIntervalPrimeBelow_of_indexed_prime_gap_certificate
    {X : Real} {b g : Nat}
    (hX : (89693 : Real) ≤ X)
    (hXb : X ≤ b)
    (certificate : FinitePrimeGapIndexedCertificate 89689 b g)
    (width : ∀ x : Real, 89693 ≤ x → x ≤ X →
      (g : Real) ≤ x / (Real.log x) ^ 3) :
    HasLogCubedShortIntervalPrimeBelow X :=
  hasLogCubedShortIntervalPrimeBelow_of_finite_prime_gap_bound
    hX hXb (finitePrimeGapBound_of_indexed_certificate certificate) width

theorem hasLogCubedShortIntervalPrimeBelow_of_indexed_gap_rows
    {X : Real} {b g n : Nat}
    (hX : (89693 : Real) ≤ X)
    (hXb : X ≤ b)
    {rows : Fin n → FinitePrimeGapRow g}
    (cover : FinitePrimeGapIndexedRowsCover rows)
    (width : ∀ x : Real, 89693 ≤ x → x ≤ X →
      (g : Real) ≤ x / (Real.log x) ^ 3) :
    HasLogCubedShortIntervalPrimeBelow X :=
  hasLogCubedShortIntervalPrimeBelow_of_finite_prime_gap_bound
    hX hXb (finitePrimeGapBound_of_indexed_rows_cover cover) width

theorem hasLogCubedShortIntervalPrimeBelow_of_two_indexed_prime_gap_certificates
    {m b₁ b₂ g₁ g₂ : Nat} {X : Real}
    (hm : (89693 : Real) ≤ m) (hXm : (m : Real) ≤ X)
    (hmb₁ : (m : Real) ≤ b₁) (hXb₂ : X ≤ b₂)
    (first : FinitePrimeGapIndexedCertificate 89689 b₁ g₁)
    (second : FinitePrimeGapIndexedCertificate 89689 b₂ g₂)
    (firstWidth : ∀ x : Real, 89693 ≤ x → x ≤ m →
      (g₁ : Real) ≤ x / (Real.log x) ^ 3)
    (secondWidth : ∀ x : Real, 89693 ≤ x → x ≤ X →
      (g₂ : Real) ≤ x / (Real.log x) ^ 3) :
    HasLogCubedShortIntervalPrimeBelow X := by
  have firstBound : HasLogCubedShortIntervalPrimeBelow (m : Real) :=
    hasLogCubedShortIntervalPrimeBelow_of_indexed_prime_gap_certificate
      hm hmb₁ first firstWidth
  have secondBound : HasLogCubedShortIntervalPrimeBelow X :=
    hasLogCubedShortIntervalPrimeBelow_of_indexed_prime_gap_certificate
      (by linarith [hm, hXm]) hXb₂ second secondWidth
  intro x hx hX
  by_cases hxm : x ≤ m
  · exact firstBound x hx hxm
  · exact secondBound x hx hX

theorem indexed_interval_cover_of_list_cover
    {α : Type} (rows : List α) (left right : α → Nat)
    {P Q : Real → Prop}
    (cover : ∀ x : Real, P x → Q x →
      ∃ row ∈ rows, (left row : Real) ≤ x ∧ x ≤ right row) :
    ∀ x : Real, P x → Q x →
      ∃ i : Fin rows.length,
        (left (rows.get i) : Real) ≤ x ∧ x ≤ right (rows.get i) := by
  intro x hP hQ
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hP hQ
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hrow
  refine ⟨⟨i, hi⟩, ?_⟩
  simpa [List.get_eq_getElem, hget] using And.intro hleft hright

/-! Indexed tables compose in the same way as list tables.  This is the
compact-block interface used by the finite certificates: a block may be
checked independently, and the kernel only has to check the two coverage
proofs and the numerical junction. -/
theorem indexed_interval_cover_append
    {α : Type} {m X : Real} {n₁ n₂ : Nat}
    (left right : Fin n₁ → α) (leftEndpoint rightEndpoint : α → Nat)
    {P Q : Real → Prop}
    (hleft : ∀ x : Real, P x → Q x → x ≤ m →
      ∃ i : Fin n₁,
        (leftEndpoint (left i) : Real) ≤ x ∧
          x ≤ rightEndpoint (left i))
    (hright : ∀ x : Real, P x → Q x → m < x → x ≤ X →
      ∃ i : Fin n₂,
        (leftEndpoint (right i) : Real) ≤ x ∧
          x ≤ rightEndpoint (right i)) :
    ∀ x : Real, P x → Q x → x ≤ X →
      ∃ i : Fin (n₁ + n₂),
        (leftEndpoint (Fin.append left right i) : Real) ≤ x ∧
          x ≤ rightEndpoint (Fin.append left right i) := by
  intro x hP hQ hX
  by_cases hxm : x ≤ m
  · obtain ⟨i, hleft_lower, hleft_upper⟩ := hleft x hP hQ hxm
    refine ⟨Fin.castAdd n₂ i, ?_⟩
    simpa [Fin.append_left] using And.intro hleft_lower hleft_upper
  · obtain ⟨i, hright_lower, hright_upper⟩ :=
      hright x hP hQ (lt_of_not_ge hxm) hX
    refine ⟨Fin.natAdd n₁ i, ?_⟩
    simpa [Fin.append_right] using And.intro hright_lower hright_upper

def logCubedUpper (x : Real) : Real :=
  x + x / (Real.log x) ^ 3

theorem logCubedUpper_monotoneOn :
    MonotoneOn logCubedUpper (Set.Ici (3275 : Real)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici (3275 : Real))
  · have hlog : ContinuousOn (fun y : Real => Real.log y)
        (Set.Ici (3275 : Real)) := by
      exact continuousOn_id.log (by
        intro x hx
        have hx_pos : (0 : Real) < x := by
          norm_num at hx ⊢
          linarith
        simpa only [id_eq] using hx_pos.ne')
    have hden : ContinuousOn (fun y : Real => (Real.log y) ^ 3)
        (Set.Ici (3275 : Real)) := hlog.pow 3
    exact continuousOn_id.add
      (continuousOn_id.div hden (by
        intro x hx
        exact pow_ne_zero 3
          (Real.log_pos (by norm_num at hx ⊢; linarith)).ne'))
  · have hlog : DifferentiableOn ℝ (fun y : Real => Real.log y)
        (interior (Set.Ici (3275 : Real))) := by
      exact differentiableOn_id.log (by
        intro x hx
        have hx' : (3275 : Real) < x := by
          simpa only [interior_Ici, Set.mem_Ioi] using hx
        simpa only [id_eq] using (show x ≠ 0 by linarith))
    have hden : DifferentiableOn ℝ
        (fun y : Real => (Real.log y) ^ 3)
        (interior (Set.Ici (3275 : Real))) :=
      hlog.pow 3
    exact differentiableOn_id.add
      (differentiableOn_id.div hden (by
        intro x hx
        exact pow_ne_zero 3
          (Real.log_pos (by norm_num at hx ⊢; linarith)).ne'))
  · intro x hx
    simp only [interior_Ici, Set.mem_Ioi] at hx
    have x_pos : 0 < x := by linarith
    have x_ne : x ≠ 0 := ne_of_gt x_pos
    have log_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have log_gt_three : (3 : Real) < Real.log x := by
      apply (Real.lt_log_iff_exp_lt x_pos).2
      have exp_three : Real.exp 3 < (3 : Real) ^ 3 := by
        calc
          Real.exp 3 = Real.exp 1 ^ 3 := by
            rw [show (3 : Real) = (3 : ℕ) * 1 by norm_num,
              Real.exp_nat_mul]
          _ < (3 : Real) ^ 3 := by
            exact pow_lt_pow_left₀ Real.exp_one_lt_three
              (Real.exp_pos 1).le (by norm_num)
      have : (3 : Real) ^ 3 < x := by
        have hx' : (3275 : Real) < x := by
          simpa only [interior_Ici, Set.mem_Ioi] using hx
        norm_num at ⊢
        linarith
      exact exp_three.trans this
    have log_cube_pos : 0 < (Real.log x) ^ 3 := by positivity
    have hden_ne : (Real.log x) ^ 3 ≠ 0 := ne_of_gt log_cube_pos
    have hlog := Real.hasDerivAt_log x_ne
    have hderiv := (hasDerivAt_id x).add
      ((hasDerivAt_id x).div (hlog.pow 3) hden_ne)
    simp only [id_eq] at hderiv
    norm_num at hderiv
    change 0 ≤ deriv (id + id / Real.log ^ 3) x
    rw [hderiv.deriv]
    field_simp [x_ne, log_pos.ne']
    have log_sq_pos : 0 < (Real.log x) ^ 2 := by positivity
    have log_four_pos : 0 < (Real.log x) ^ 4 := by positivity
    nlinarith [mul_pos log_sq_pos (by nlinarith [log_gt_three])]

theorem logCubedWidth_monotoneOn :
    MonotoneOn logCubedWidth (Set.Ici (3275 : Real)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici (3275 : Real))
  · have hlog : ContinuousOn (fun y : Real => Real.log y)
        (Set.Ici (3275 : Real)) := by
      exact continuousOn_id.log (by
        intro x hx
        have hx_pos : (0 : Real) < x := by
          norm_num at hx ⊢
          linarith
        simpa only [id_eq] using hx_pos.ne')
    exact continuousOn_id.div (hlog.pow 3) (by
      intro x hx
      exact pow_ne_zero 3
        (Real.log_pos (by norm_num at hx ⊢; linarith)).ne')
  · have hlog : DifferentiableOn ℝ (fun y : Real => Real.log y)
        (interior (Set.Ici (3275 : Real))) := by
      exact differentiableOn_id.log (by
        intro x hx
        have hx' : (3275 : Real) < x := by
          simpa only [interior_Ici, Set.mem_Ioi] using hx
        simpa only [id_eq] using (show x ≠ 0 by linarith))
    exact differentiableOn_id.div (hlog.pow 3) (by
      intro x hx
      exact pow_ne_zero 3
        (Real.log_pos (by norm_num at hx ⊢; linarith)).ne')
  · intro x hx
    simp only [interior_Ici, Set.mem_Ioi] at hx
    have x_pos : 0 < x := by linarith
    have x_ne : x ≠ 0 := ne_of_gt x_pos
    have log_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have log_gt_three : (3 : Real) < Real.log x := by
      apply (Real.lt_log_iff_exp_lt x_pos).2
      have exp_three : Real.exp 3 < (3 : Real) ^ 3 := by
        calc
          Real.exp 3 = Real.exp 1 ^ 3 := by
            rw [show (3 : Real) = (3 : ℕ) * 1 by norm_num,
              Real.exp_nat_mul]
          _ < (3 : Real) ^ 3 := by
            exact pow_lt_pow_left₀ Real.exp_one_lt_three
              (Real.exp_pos 1).le (by norm_num)
      have hx' : (3 : Real) ^ 3 < x := by
        have h3275 : (3275 : Real) < x := by
          simpa only [interior_Ici, Set.mem_Ioi] using hx
        norm_num at ⊢
        linarith
      exact exp_three.trans hx'
    have log_cube_pos : 0 < (Real.log x) ^ 3 := by positivity
    have hden_ne : (Real.log x) ^ 3 ≠ 0 := ne_of_gt log_cube_pos
    have hlog := Real.hasDerivAt_log x_ne
    have hderiv := (hasDerivAt_id x).div (hlog.pow 3) hden_ne
    simp only [id_eq] at hderiv
    change 0 ≤ deriv (id / Real.log ^ 3) x
    rw [hderiv.deriv]
    field_simp [x_ne, log_pos.ne']
    have log_sq_pos : 0 < (Real.log x) ^ 2 := by positivity
    nlinarith [mul_pos log_sq_pos (by nlinarith [log_gt_three])]

theorem logCubedWidth_lower_of_endpoint
    {g x : Nat}
    (hendpoint : (g : Real) ≤ logCubedWidth 89693)
    (hx : (89693 : Real) ≤ x) :
    (g : Real) ≤ logCubedWidth x := by
  exact hendpoint.trans
    (logCubedWidth_monotoneOn (by norm_num) (by exact hx))

theorem logCubedWidth_lower_of_log_upper
    {a g : Nat} {L : Real}
    (ha : (89693 : Real) ≤ a)
    (hL : 0 ≤ L)
    (hlog : Real.log a ≤ L)
    (hproduct : (g : Real) * L ^ 3 ≤ a) :
    (g : Real) ≤ logCubedWidth a := by
  have ha_pos : 0 < (a : Real) := by linarith
  have hlog_pos : 0 < Real.log a := by
    exact Real.log_pos (by linarith)
  have hlog_nonneg : 0 ≤ Real.log a := hlog_pos.le
  have hpow : (Real.log a) ^ 3 ≤ L ^ 3 :=
    pow_le_pow_left₀ hlog_nonneg hlog 3
  have hmul : (g : Real) * (Real.log a) ^ 3 ≤
      (g : Real) * L ^ 3 :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  have hbound : (g : Real) * (Real.log a) ^ 3 ≤ a :=
    hmul.trans hproduct
  exact (le_div_iff₀ (pow_pos hlog_pos 3)).2 (by
    simpa [logCubedWidth] using hbound)

theorem log_89693_le_1141_over_100 :
    Real.log (89693 : Real) ≤ (1141 : Real) / 100 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  interval_decide

theorem logCubedWidth_89693_ge_60 :
    (60 : Real) ≤ logCubedWidth 89693 := by
  apply logCubedWidth_lower_of_log_upper (a := 89693) (g := 60)
    (by norm_num) (by norm_num) log_89693_le_1141_over_100
  norm_num

theorem log_100000_le_116_over_10 :
    Real.log (100000 : Real) ≤ (116 : Real) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  interval_decide

theorem log_le_116_over_10_of_89693_le
    {a : Nat} (ha : (89693 : Nat) ≤ a) (ha100000 : a ≤ 100000) :
    Real.log a ≤ (116 : Real) / 10 := by
  have hmono : Real.log (a : Real) ≤ Real.log (100000 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha100000
  exact hmono.trans log_100000_le_116_over_10

theorem finitePrimeGapLogRow_of_explicit_100000
    {p q : Nat} (hq : q.Prime) (hpq : p < q)
    (hproduct : (q - p : Real) * ((116 : Real) / 10) ^ 3 ≤ p)
    (hleft_large : 89693 ≤ p) (hp100000 : p ≤ 100000) :
    FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit hq hpq hleft_large
    (log_le_116_over_10_of_89693_le hleft_large hp100000)
    (by norm_num) hproduct

def finitePrimeGapLogRow_89693_89752 : FinitePrimeGapLogRow := by
  apply FinitePrimeGapLogRow.of_gap_row (g := 60)
    (row := {
      left := 89693
      right := 89752
      left_le_right := by norm_num
      witness := 89753
      witness_prime := by norm_num
      right_lt_witness := by norm_num
      witness_le_left_add_gap := by norm_num })
    (by norm_num) (L := (1141 : Real) / 100)
  · norm_num
  · exact log_89693_le_1141_over_100
  · norm_num

def finitePrimeGapLogRow_89753_89758 : FinitePrimeGapLogRow := by
  apply FinitePrimeGapLogRow.of_gap_row (g := 6)
    (row := {
      left := 89753
      right := 89758
      left_le_right := by norm_num
      witness := 89759
      witness_prime := by norm_num
      right_lt_witness := by norm_num
      witness_le_left_add_gap := by norm_num })
    (by norm_num) (L := (116 : Real) / 10)
  · norm_num
  · exact log_le_116_over_10_of_89693_le (by norm_num) (by norm_num)
  · norm_num

def finitePrimeGapLogRow_89759_89766 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def finitePrimeGapLogRow_89767_89778 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def finitePrimeGapLogRow_89779_89782 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def finitePrimeGapLogRow_89783_89796 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def finitePrimeGapLogRow_89797_89808 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def finitePrimeGapLogRow_89809_89818 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def finitePrimeGapLogRow_89819_89820 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def finitePrimeGapLogRow_89821_89832 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def finitePrimeGapLogRow_89833_89838 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def finitePrimeGapLogRow_89839_89848 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def finitePrimeGapLogRow_89849_89866 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def finitePrimeGapLogRow_89867_89890 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def dusartUpper (x : Real) : Real :=
  x * (1 + (1 / 2 : Real) / (Real.log x) ^ 2)

theorem dusartUpper_monotoneOn :
    MonotoneOn dusartUpper (Set.Ici (3275 : Real)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici (3275 : Real))
  · have hlog : ContinuousOn (fun y : Real => Real.log y)
        (Set.Ici (3275 : Real)) := by
      exact continuousOn_id.log (by
        intro x hx
        have hx_pos : (0 : Real) < x := by
          norm_num at hx ⊢
          linarith
        simpa only [id_eq] using hx_pos.ne')
    have hden : ContinuousOn (fun y : Real => (Real.log y) ^ 2)
        (Set.Ici (3275 : Real)) := hlog.pow 2
    exact continuousOn_id.mul
      (continuousOn_const.add
        (continuousOn_const.div hden (by
          intro x hx
          have : 0 < Real.log x := by
            exact Real.log_pos (by norm_num at hx ⊢; linarith)
          positivity)))
  · have hlog : DifferentiableOn ℝ (fun y : Real => Real.log y)
        (interior (Set.Ici (3275 : Real))) := by
      exact differentiableOn_id.log (by
        intro x hx
        have hx' : (3275 : Real) < x := by
          simpa only [interior_Ici, Set.mem_Ioi] using hx
        simpa only [id_eq] using (show x ≠ 0 by linarith))
    have hden : DifferentiableOn ℝ
        (fun y : Real => (Real.log y) ^ 2)
        (interior (Set.Ici (3275 : Real))) := hlog.pow 2
    exact differentiableOn_id.mul
      ((differentiableOn_const (1 : Real)).add
        ((differentiableOn_const (1 / 2 : Real)).div hden (by
          intro x hx
          have : 0 < Real.log x := by
            exact Real.log_pos (by norm_num at hx ⊢; linarith)
          positivity)))
  · intro x hx
    simp only [interior_Ici, Set.mem_Ioi] at hx
    have x_ne : x ≠ 0 := by linarith
    have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hlog_gt_two : (2 : Real) < Real.log x := by
      apply (Real.lt_log_iff_exp_lt (by linarith)).2
      have hexp : Real.exp 2 < (9 : Real) := by
        rw [show (2 : Real) = 1 + 1 by norm_num, Real.exp_add]
        have hone : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
        nlinarith [mul_self_lt_mul_self (Real.exp_pos 1).le hone]
      have : (9 : Real) < x := by linarith
      exact hexp.trans this
    have hderiv := (hasDerivAt_id x).mul
      ((hasDerivAt_const x (1 : Real)).add
        ((hasDerivAt_const x (1 / 2 : Real)).div
          ((Real.hasDerivAt_log x_ne).pow 2)
            (pow_ne_zero 2 hlog_pos.ne')))
    simp only [id_eq] at hderiv
    change 0 ≤ deriv (id * (fun y : Real =>
      1 + (1 / 2 : Real) / Real.log y ^ 2)) x
    have hfun : (id * (fun y : Real =>
        1 + (1 / 2 : Real) / Real.log y ^ 2)) =
        id * ((fun x : Real => 1) + (fun x : Real => 1 / 2) /
          Real.log ^ 2) := by
      funext y
      simp [Pi.mul_apply, Pi.add_apply, id_eq]
    rw [hfun]
    rw [hderiv.deriv]
    simp only [Pi.add_apply, Pi.div_apply, Pi.pow_apply]
    field_simp [x_ne, hlog_pos.ne']
    norm_num at *
    nlinarith [mul_pos (show 0 < Real.log x by linarith)
      (show 0 < (Real.log x) ^ 2 by positivity)]

structure DusartPrimeRow where
  left : Nat
  right : Nat
  prime : Nat
  left_large : 3275 ≤ left
  right_lt_prime : right < prime
  prime_prime : prime.Prime
  prime_upper : (prime : Real) ≤ dusartUpper left

def DusartPrimeRowsCoverBelow (rows : List DusartPrimeRow) : Prop :=
  ∀ x : Real, 3275 ≤ x → x ≤ 89693 →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem dusartPrimeRow_provides
    (row : DusartPrimeRow) {x : Real}
    (left_mem : (row.left : Real) ≤ x)
    (right_mem : x ≤ row.right) :
    ∃ q : Nat, q.Prime ∧ x < q ∧
      (q : Real) ≤ x * (1 + 1 / (2 * (Real.log x) ^ 2)) := by
  refine ⟨row.prime, row.prime_prime, ?_, ?_⟩
  · have right_lt_prime : (row.right : Real) < row.prime := by
      exact_mod_cast row.right_lt_prime
    exact_mod_cast right_mem.trans_lt right_lt_prime
  · have hbound : (row.prime : Real) ≤ dusartUpper x :=
      row.prime_upper.trans (dusartUpper_monotoneOn
        (show (row.left : Real) ∈ Set.Ici (3275 : Real) by
          change (3275 : Real) ≤ row.left
          exact_mod_cast row.left_large)
        (show x ∈ Set.Ici (3275 : Real) by
          have hleft : (3275 : Real) ≤ row.left := by
            exact_mod_cast row.left_large
          norm_num at ⊢
          linarith [hleft, left_mem]) left_mem)
    have hrewrite : dusartUpper x =
        x * (1 + 1 / (2 * (Real.log x) ^ 2)) := by
      dsimp [dusartUpper]
      field_simp
    exact hrewrite ▸ hbound

theorem hasDusartShortIntervalPrimeBelow_of_rows
    {rows : List DusartPrimeRow}
    (cover : DusartPrimeRowsCoverBelow rows) :
    HasDusartShortIntervalPrimeBelow (89693 : Real) := by
  intro x hx hX
  obtain ⟨row, row_mem, left_mem, right_mem⟩ := cover x hx hX
  exact dusartPrimeRow_provides row left_mem right_mem

structure LogCubedPrimeRow where
  left : Nat
  right : Nat
  prime : Nat
  left_large : 89693 ≤ left
  right_lt_prime : right < prime
  prime_prime : prime.Prime
  prime_upper : (prime : Real) ≤ logCubedUpper left

theorem FinitePrimeGapLogRow.toLogCubedPrimeRow
    (row : FinitePrimeGapLogRow) : LogCubedPrimeRow := by
  refine {
    left := row.left
    right := row.right
    prime := row.witness
    left_large := row.left_large
    right_lt_prime := row.right_lt_witness
    prime_prime := row.witness_prime
    prime_upper := ?_ }
  have hupper : (row.witness : Real) ≤
      (row.left : Real) + logCubedWidth row.left := by
    linarith [row.witness_width]
  simpa [logCubedWidth, logCubedUpper] using hupper

def FinitePrimeGapLogRowsCoverUpTo
    (rows : List FinitePrimeGapLogRow) (X : Real) : Prop :=
  ∀ x : Real, 89693 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem finitePrimeGapLogRowsCoverUpTo_of_chain
    {b : Nat} {X : Real} {rows : List FinitePrimeGapLogRow}
    (chain : FinitePrimeGapLogRowsChain 89693 b rows)
    (hX : X ≤ b) :
    FinitePrimeGapLogRowsCoverUpTo rows X := by
  intro x hx hupper
  exact finitePrimeGapLogRowsCover_of_chain chain x hx
    (hupper.trans hX)

def FinitePrimeGapLogRowsCoverFrom
    (rows : List FinitePrimeGapLogRow) (a X : Real) : Prop :=
  ∀ x : Real, a ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

def FinitePrimeGapLogIndexedRowsCoverUpTo
    {n : Nat} (rows : Fin n → FinitePrimeGapLogRow) (X : Real) : Prop :=
  ∀ x : Real, 89693 ≤ x → x ≤ X →
    ∃ i : Fin n, (rows i).left ≤ x ∧ x ≤ (rows i).right

def FinitePrimeGapLogIndexedRowsCoverFrom
    {n : Nat} (rows : Fin n → FinitePrimeGapLogRow)
    (a X : Real) : Prop :=
  ∀ x : Real, a ≤ x → x ≤ X →
    ∃ i : Fin n, (rows i).left ≤ x ∧ x ≤ (rows i).right

theorem finitePrimeGapLogIndexedRowsCoverUpTo_append_from
    {m X : Real} {n₁ n₂ : Nat}
    {left : Fin n₁ → FinitePrimeGapLogRow}
    {right : Fin n₂ → FinitePrimeGapLogRow}
    (hleft : FinitePrimeGapLogIndexedRowsCoverUpTo left m)
    (hright : FinitePrimeGapLogIndexedRowsCoverFrom right m X) :
    FinitePrimeGapLogIndexedRowsCoverUpTo (Fin.append left right) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨i, hleft_lower, hleft_upper⟩ := hleft x hx hxm
    refine ⟨Fin.castAdd n₂ i, ?_⟩
    simpa [Fin.append_left] using And.intro hleft_lower hleft_upper
  · obtain ⟨i, hright_lower, hright_upper⟩ :=
      hright x (le_of_lt (lt_of_not_ge hxm)) hX
    refine ⟨Fin.natAdd n₁ i, ?_⟩
    simpa [Fin.append_right] using And.intro hright_lower hright_upper

theorem finitePrimeGapLogRowsCoverUpTo_append
    {m X : Real} {left right : List FinitePrimeGapLogRow}
    (hleft : FinitePrimeGapLogRowsCoverUpTo left m)
    (hright : FinitePrimeGapLogRowsCoverUpTo right X) :
    FinitePrimeGapLogRowsCoverUpTo (left ++ right) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hleft x hx hxm
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hright x hx hX
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩

theorem finitePrimeGapLogRowsCoverUpTo_append_from
    {m X : Real} {left right : List FinitePrimeGapLogRow}
    (hleft : FinitePrimeGapLogRowsCoverUpTo left m)
    (hright : FinitePrimeGapLogRowsCoverFrom right m X) :
    FinitePrimeGapLogRowsCoverUpTo (left ++ right) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hleft x hx hxm
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ :=
      hright x (le_of_lt (lt_of_not_ge hxm)) hX
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩

theorem FinitePrimeGapRow.toLogCubedPrimeRow
    {g : Nat} (row : FinitePrimeGapRow g)
    (hwidth : (g : Real) ≤ (row.left : Real) /
      (Real.log row.left) ^ 3) :
    LogCubedPrimeRow := by
  refine {
    left := row.left
    right := row.right
    prime := row.witness
    left_large := ?_
    right_lt_prime := row.right_lt_witness
    prime_prime := row.witness_prime
    prime_upper := ?_ }
  · exact le_trans (by norm_num) row.left_le_right
  · have hbound : (row.witness : Real) ≤
        (row.left : Real) + (g : Real) := by
      exact_mod_cast row.witness_le_left_add_gap
    calc
      (row.witness : Real) ≤ (row.left : Real) + (g : Real) := hbound
      _ ≤ (row.left : Real) + (row.left : Real) /
          (Real.log row.left) ^ 3 := add_le_add_left hwidth _
      _ = logCubedUpper row.left := by rfl

def LogCubedPrimeRowsCover (rows : List LogCubedPrimeRow) : Prop :=
  ∀ x : Real, 89693 ≤ x →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

/-! A bounded cover is the form used when the explicit analytic argument is
split at a large cutoff.  Keeping the cutoff in the proposition means the
finite table has no obligation to describe the unbounded range handled by the
theta-error argument. -/
def LogCubedPrimeRowsCoverUpTo (rows : List LogCubedPrimeRow) (X : Real) : Prop :=
  ∀ x : Real, 89693 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

def LogCubedPrimeIndexedCoverUpTo {n : Nat}
    (rows : Fin n → LogCubedPrimeRow) (X : Real) : Prop :=
  ∀ x : Real, 89693 ≤ x → x ≤ X →
    ∃ i : Fin n, (rows i).left ≤ x ∧ x ≤ (rows i).right

theorem logCubedPrimeIndexedCover_of_list
    {X : Real} {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows X) :
    LogCubedPrimeIndexedCoverUpTo
      (fun i : Fin rows.length => rows.get i) X := by
  exact indexed_interval_cover_of_list_cover rows
    (fun row => row.left) (fun row => row.right) cover

theorem logCubedPrimeIndexedCoverUpTo_append
    {m X : Real} {n₁ n₂ : Nat}
    {left : Fin n₁ → LogCubedPrimeRow}
    {right : Fin n₂ → LogCubedPrimeRow}
    (hleft : LogCubedPrimeIndexedCoverUpTo left m)
    (hright : LogCubedPrimeIndexedCoverUpTo right X) :
    LogCubedPrimeIndexedCoverUpTo (Fin.append left right) X := by
  intro x hx hX
  exact indexed_interval_cover_append left right
    (fun row => row.left) (fun row => row.right)
    (fun y hy _ hym => hleft y hy hym)
    (fun y hy _ hym hyX => hright y hy hyX)
    x hx trivial hX

theorem hasLogCubedShortIntervalPrimeBelow_of_indexed_rows
    {n : Nat} {X : Real} {rows : Fin n → LogCubedPrimeRow}
    (cover : LogCubedPrimeIndexedCoverUpTo rows X) :
    HasLogCubedShortIntervalPrimeBelow X := by
  intro x hx hX
  obtain ⟨i, hleft, hright⟩ := cover x hx hX
  exact logCubedPrimeRow_provides
    (fun {a b} ha hab => logCubedUpper_monotoneOn
      (by norm_num at ⊢; linarith)
      (by norm_num at ⊢; linarith) hab)
    (rows i) hleft hright

theorem logCubedPrimeRowsCoverUpTo_append
    {m X : Real} {left right : List LogCubedPrimeRow}
    (hleft : LogCubedPrimeRowsCoverUpTo left m)
    (hright : LogCubedPrimeRowsCoverUpTo right X) :
    LogCubedPrimeRowsCoverUpTo (left ++ right) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hleft x hx hxm
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hright x hx hX
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩

/-! A finite theta-error table has the same shape as the interval table, but
the row carries the analytic inequality which its (small) rational
certificate establishes.  Keeping this as a list-level interface is
important: the proof of the global estimate consumes one cover, while the
certificate generator may choose its own row width and arithmetic encoding.
No theorem about theta is imported here; every row must provide its own
kernel-checked local estimate. -/
structure ThetaLogFourthErrorRow (A : Real) where
  left : Nat
  right : Nat
  left_large : 2 ≤ left
  left_le_right : left ≤ right
  error : ∀ x : Real, (left : Real) ≤ x → x ≤ right →
    |Chebyshev.theta x - x| ≤ A * x / (Real.log x) ^ 4

def ThetaLogFourthErrorRowsCoverUpTo
    {A : Real} (rows : List (ThetaLogFourthErrorRow A)) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

/-! Sharp theta rows need not begin at `2`: the Abel core treats the small
interval separately, while the logarithmic error table starts at `x₀`. -/
def ThetaLogFourthErrorRowsCoverFrom
    {A : Real} (rows : List (ThetaLogFourthErrorRow A))
    (x₀ X : Real) : Prop :=
  ∀ x : Real, x₀ ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem hasThetaLogFourthErrorBelow_of_rows
    {A X : Real} {rows : List (ThetaLogFourthErrorRow A)}
    (cover : ThetaLogFourthErrorRowsCoverUpTo rows X) :
    HasThetaLogFourthErrorBelow A X := by
  intro x hx2 hxX
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hx2 hxX
  exact row.error x hleft hright

theorem hasThetaLogFourthErrorOn_of_rows_from
    {A x₀ X : Real} {rows : List (ThetaLogFourthErrorRow A)}
    (cover : ThetaLogFourthErrorRowsCoverFrom rows x₀ X) :
    HasThetaLogFourthErrorOn A x₀ X := by
  intro x hx hxX
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hxX
  exact row.error x hleft hright

theorem hasThetaLogFourthError_of_rows_from_and_tail
    {A x₀ X : Real} {rows : List (ThetaLogFourthErrorRow A)}
    (cover : ThetaLogFourthErrorRowsCoverFrom rows x₀ X)
    (tail : HasThetaLogFourthErrorAbove A X) :
    HasThetaLogFourthErrorAbove A x₀ := by
  intro x hx
  by_cases hsmall : x ≤ X
  · exact (hasThetaLogFourthErrorOn_of_rows_from cover) x hx hsmall
  · exact tail x (le_of_not_ge hsmall)

theorem hasThetaLogFourthError_of_rows_and_tail
    {A X : Real} {rows : List (ThetaLogFourthErrorRow A)}
    (cover : ThetaLogFourthErrorRowsCoverUpTo rows X)
    (tail : HasThetaLogFourthErrorAbove A X) :
    HasThetaLogFourthError A 2 := by
  exact hasThetaLogFourthError_of_below_and_above
    (hasThetaLogFourthErrorBelow_of_rows cover) tail

theorem hasThetaLogFourthError_of_rows_and_psiLogFourthError
    {A X : Real} {rows : List (ThetaLogFourthErrorRow (A + 148 / 1000))}
    (cover : ThetaLogFourthErrorRowsCoverUpTo rows X)
    (hXcutoff : (4e18 : Real) ≤ X)
    (psiError : HasPsiLogFourthError A X) :
    HasThetaLogFourthError (A + 148 / 1000) 2 := by
  apply hasThetaLogFourthError_of_rows_and_tail cover
  exact hasThetaLogFourthError_of_psiLogFourthError_sharp
    hXcutoff psiError

/-! Endpoint theta certificates are enough for an entire row.  The theta
function is monotone, while the logarithmic error envelope is handled by an
explicit numerator/denominator comparison. -/
structure ThetaLogFourthEndpointRow (A : Real) where
  left : Nat
  right : Nat
  left_large : 2 ≤ left
  left_le_right : left ≤ right
  theta_lower : Real
  theta_upper : Real
  theta_lower_le : theta_lower ≤ Chebyshev.theta left
  theta_right_le : Chebyshev.theta right ≤ theta_upper
  upper_error : theta_upper - left ≤
    A * (left : Real) / (Real.log right) ^ 4
  lower_error : right - theta_lower ≤
    A * (left : Real) / (Real.log right) ^ 4

def ThetaLogFourthEndpointRowsCoverUpTo
    {A : Real} (rows : List (ThetaLogFourthEndpointRow A)) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem thetaLogFourthEndpointRowsCoverUpTo_append
    {A m X : Real}
    {left right : List (ThetaLogFourthEndpointRow A)}
    (hleft : ThetaLogFourthEndpointRowsCoverUpTo left m)
    (hright : ThetaLogFourthEndpointRowsCoverUpTo right X) :
    ThetaLogFourthEndpointRowsCoverUpTo (left ++ right) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hleft x hx hxm
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hright x hx hX
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩

/-! The endpoint form also supports a split table whose first row starts at a
valid analytic cutoff rather than at `2`. -/
def ThetaLogFourthEndpointRowsCoverFrom
    {A : Real} (rows : List (ThetaLogFourthEndpointRow A))
    (x₀ X : Real) : Prop :=
  ∀ x : Real, x₀ ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

def ThetaLogFourthEndpointIndexedCoverFrom {n : Nat} {A : Real}
    (rows : Fin n → ThetaLogFourthEndpointRow A)
    (x₀ X : Real) : Prop :=
  ∀ x : Real, x₀ ≤ x → x ≤ X →
    ∃ i : Fin n, (rows i).left ≤ x ∧ x ≤ (rows i).right

theorem thetaLogFourthEndpointIndexedCover_of_list
    {A x₀ X : Real} {rows : List (ThetaLogFourthEndpointRow A)}
    (cover : ThetaLogFourthEndpointRowsCoverFrom rows x₀ X) :
    ThetaLogFourthEndpointIndexedCoverFrom
      (fun i : Fin rows.length => rows.get i) x₀ X := by
  exact indexed_interval_cover_of_list_cover rows
    (fun row => row.left) (fun row => row.right) cover

theorem thetaLogFourthEndpointIndexedCoverFrom_append
    {A m x₀ X : Real} {n₁ n₂ : Nat}
    {left : Fin n₁ → ThetaLogFourthEndpointRow A}
    {right : Fin n₂ → ThetaLogFourthEndpointRow A}
    (hleft : ThetaLogFourthEndpointIndexedCoverFrom left x₀ m)
    (hright : ThetaLogFourthEndpointIndexedCoverFrom right x₀ X) :
    ThetaLogFourthEndpointIndexedCoverFrom
      (Fin.append left right) x₀ X := by
  intro x hx hX
  exact indexed_interval_cover_append left right
    (fun row => row.left) (fun row => row.right)
    (fun y hy _ hym => hleft y hy hym)
    (fun y hy _ hym hyX => hright y hy hyX)
    x hx trivial hX

theorem hasThetaLogFourthErrorAbove_of_indexed_endpoint_rows_from_and_tail
    {n : Nat} {A x₀ X : Real}
    (hA0 : 0 ≤ A)
    {rows : Fin n → ThetaLogFourthEndpointRow A}
    (cover : ThetaLogFourthEndpointIndexedCoverFrom rows x₀ X)
    (tail : HasThetaLogFourthErrorAbove A X) :
    HasThetaLogFourthErrorAbove A x₀ := by
  intro x hx
  by_cases hsmall : x ≤ X
  · obtain ⟨i, hleft, hright⟩ := cover x hx hsmall
    exact thetaLogFourthEndpointRow_provides hA0 (rows i) hleft hright
  · exact tail x (le_of_not_ge hsmall)

theorem thetaLogFourthEndpointRowsCoverFrom_append
    {A x₀ m X : Real}
    {left right : List (ThetaLogFourthEndpointRow A)}
    (hleft : ThetaLogFourthEndpointRowsCoverFrom left x₀ m)
    (hright : ThetaLogFourthEndpointRowsCoverFrom right m X) :
    ThetaLogFourthEndpointRowsCoverFrom (left ++ right) x₀ X := by
  intro x hx₀ hxX
  by_cases hxm : x ≤ m
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hleft x hx₀ hxm
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ :=
      hright x (le_of_not_ge hxm) hxX
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩

theorem thetaLogFourthEndpointRow_provides
    {A : Real} (hA0 : 0 ≤ A)
    (row : ThetaLogFourthEndpointRow A) {x : Real}
    (hleft : (row.left : Real) ≤ x) (hright : x ≤ row.right) :
    |Chebyshev.theta x - x| ≤ A * x / (Real.log x) ^ 4 := by
  have hleft2 : (2 : Real) ≤ row.left := by exact_mod_cast row.left_large
  have hright2 : (2 : Real) ≤ (row.right : Real) := by
    exact le_trans hleft2 (by exact_mod_cast row.left_le_right)
  have hx2 : (2 : Real) ≤ x := hleft2.trans hleft
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogr_pos : 0 < Real.log (row.right : Real) :=
    Real.log_pos (by linarith)
  have htheta_lower : row.theta_lower ≤ Chebyshev.theta x :=
    row.theta_lower_le.trans (Chebyshev.theta_mono hleft)
  have htheta_upper : Chebyshev.theta x ≤ row.theta_upper :=
    (Chebyshev.theta_mono hright).trans row.theta_right_le
  have hlog_mono : Real.log x ≤ Real.log (row.right : Real) :=
    Real.log_le_log (by linarith) hright
  have hlogsq : (Real.log x) ^ 4 ≤
      (Real.log (row.right : Real)) ^ 4 := by
    exact pow_le_pow_left' hlog_mono 4
  have hratio : (row.left : Real) /
      (Real.log (row.right : Real)) ^ 4 ≤
      x / (Real.log x) ^ 4 := by
    apply (div_le_div_iff₀ (pow_pos hlogr_pos 4)
      (pow_pos hlogx_pos 4)).2
    calc
      (row.left : Real) * (Real.log x) ^ 4 ≤
          (row.left : Real) * (Real.log (row.right : Real)) ^ 4 :=
        mul_le_mul_of_nonneg_left hlogsq (by positivity)
      _ ≤ x * (Real.log (row.right : Real)) ^ 4 :=
        mul_le_mul_of_nonneg_right hleft (by positivity)
  have henvelope : A * (row.left : Real) /
      (Real.log (row.right : Real)) ^ 4 ≤ A * x /
        (Real.log x) ^ 4 :=
    mul_le_mul_of_nonneg_left hratio hA0
  have hupper : Chebyshev.theta x - x ≤
      A * x / (Real.log x) ^ 4 := by
    calc
      Chebyshev.theta x - x ≤ row.theta_upper - row.left := by linarith
      _ ≤ A * (row.left : Real) /
          (Real.log (row.right : Real)) ^ 4 := row.upper_error
      _ ≤ A * x / (Real.log x) ^ 4 := henvelope
  have hlower : -(A * x / (Real.log x) ^ 4) ≤
      Chebyshev.theta x - x := by
    calc
      -(A * x / (Real.log x) ^ 4) ≤
          -(A * (row.left : Real) /
            (Real.log (row.right : Real)) ^ 4) := by linarith
      _ ≤ -(row.right - row.theta_lower) := by linarith [row.lower_error]
      _ ≤ Chebyshev.theta x - x := by linarith
  exact (abs_le).2 ⟨hlower, hupper⟩

theorem hasThetaLogFourthErrorBelow_of_endpoint_rows
    {A X : Real} (hA0 : 0 ≤ A)
    {rows : List (ThetaLogFourthEndpointRow A)}
    (cover : ThetaLogFourthEndpointRowsCoverUpTo rows X) :
    HasThetaLogFourthErrorBelow A X := by
  intro x hx2 hxX
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hx2 hxX
  exact thetaLogFourthEndpointRow_provides hA0 row hleft hright

theorem hasThetaLogFourthErrorOn_of_endpoint_rows_from
    {A x₀ X : Real} (hA0 : 0 ≤ A)
    {rows : List (ThetaLogFourthEndpointRow A)}
    (cover : ThetaLogFourthEndpointRowsCoverFrom rows x₀ X) :
    HasThetaLogFourthErrorOn A x₀ X := by
  intro x hx hxX
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hxX
  exact thetaLogFourthEndpointRow_provides hA0 row hleft hright

theorem hasThetaLogFourthErrorAbove_of_endpoint_rows_from_and_tail
    {A x₀ X : Real} (hA0 : 0 ≤ A)
    {rows : List (ThetaLogFourthEndpointRow A)}
    (cover : ThetaLogFourthEndpointRowsCoverFrom rows x₀ X)
    (tail : HasThetaLogFourthErrorAbove A X) :
    HasThetaLogFourthErrorAbove A x₀ := by
  intro x hx
  by_cases hsmall : x ≤ X
  · exact hasThetaLogFourthErrorOn_of_endpoint_rows_from hA0 cover x hx hsmall
  · exact tail x (le_of_not_ge hsmall)

theorem logCubedPrimeRow_provides
    (upper_mono : ∀ {a b : Real}, 89693 ≤ a → a ≤ b →
      logCubedUpper a ≤ logCubedUpper b)
    (row : LogCubedPrimeRow) {x : Real}
    (left_mem : (row.left : Real) ≤ x)
    (right_mem : x ≤ row.right) :
    ∃ q : Nat, q.Prime ∧ x < q ∧ (q : Real) ≤ logCubedUpper x := by
  refine ⟨row.prime, row.prime_prime, ?_, ?_⟩
  · have right_lt_prime : (row.right : Real) < row.prime := by
      exact_mod_cast row.right_lt_prime
    have x_lt_prime : x < (row.prime : Real) :=
      (right_mem.trans_lt right_lt_prime)
    exact_mod_cast x_lt_prime
  · exact row.prime_upper.trans (upper_mono
      (by exact_mod_cast row.left_large) left_mem)

theorem hasLogCubedShortIntervalPrimeBelow_of_indexed_gap_log_rows
    {n : Nat} {X : Real}
    {rows : Fin n → FinitePrimeGapLogRow}
    (cover : FinitePrimeGapLogIndexedRowsCoverUpTo rows X) :
    HasLogCubedShortIntervalPrimeBelow X := by
  intro x hx hX
  obtain ⟨i, hleft, hright⟩ := cover x hx hX
  exact logCubedPrimeRow_provides
    (fun {a b} ha hab => logCubedUpper_monotoneOn
      (by norm_num at ⊢; linarith)
      (by norm_num at ⊢; linarith) hab)
    (rows i).toLogCubedPrimeRow hleft hright

theorem hasLogCubedShortIntervalPrimeBelow_of_finite_gap_log_rows
    {X : Real} {rows : List FinitePrimeGapLogRow}
    (cover : FinitePrimeGapLogRowsCoverUpTo rows X) :
    HasLogCubedShortIntervalPrimeBelow X := by
  intro x hx hX
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
  exact logCubedPrimeRow_provides
    (fun {a b} ha hab => logCubedUpper_monotoneOn
      (by norm_num at ⊢; linarith)
      (by norm_num at ⊢; linarith) hab)
    row.toLogCubedPrimeRow hleft hright

/-! A log-cubed finite table only covers the range beginning at `89693`.
The lower Dusart interval provider is therefore kept as an explicit prefix
input, while this adapter supplies its remainder without duplicating rows. -/
theorem hasDusartShortIntervalPrimeBelow_of_finite_gap_log_rows
    {X : Real} {rows : List FinitePrimeGapLogRow}
    (hX : (89693 : Real) ≤ X)
    (finitePrefix : HasDusartShortIntervalPrimeBelow (89693 : Real))
    (cover : FinitePrimeGapLogRowsCoverUpTo rows X) :
    HasDusartShortIntervalPrimeBelow X := by
  intro x hx hXx
  by_cases hsmall : x ≤ (89693 : Real)
  · exact finitePrefix x hx hsmall
  · have hlarge : (89693 : Real) ≤ x :=
      le_of_lt (lt_of_not_ge hsmall)
    obtain ⟨q, hq, hxq, hupper⟩ :=
      hasLogCubedShortIntervalPrimeBelow_of_finite_gap_log_rows cover
        x hlarge hXx
    refine ⟨q, hq, hxq, ?_⟩
    exact dusartShortIntervalUpper_of_logCubed hlarge hupper

def finitePrimeGapLogRows_89693_89752 :
    List FinitePrimeGapLogRow :=
  [finitePrimeGapLogRow_89693_89752]

theorem finitePrimeGapLogRows_89693_89752_cover :
    FinitePrimeGapLogRowsCoverUpTo
      finitePrimeGapLogRows_89693_89752 (89752 : Real) := by
  intro x hx hX
  refine ⟨finitePrimeGapLogRow_89693_89752, by simp, ?_, ?_⟩
  · norm_num
  · exact hX

def finitePrimeGapLogRows_89693_89758 :
    List FinitePrimeGapLogRow :=
  [finitePrimeGapLogRow_89693_89752,
    finitePrimeGapLogRow_89753_89758]

theorem finitePrimeGapLogRows_89693_89758_chain :
    FinitePrimeGapLogRowsChain 89693 89758
      finitePrimeGapLogRows_89693_89758 := by
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89693_89752
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89753_89758
  · norm_num
  · norm_num
  exact FinitePrimeGapLogRowsChain.empty (by norm_num)

theorem finitePrimeGapLogRows_89693_89758_cover :
    FinitePrimeGapLogRowsCoverUpTo
      finitePrimeGapLogRows_89693_89758 (89758 : Real) := by
  exact finitePrimeGapLogRowsCoverUpTo_of_chain
    finitePrimeGapLogRows_89693_89758_chain (by norm_num)

def finitePrimeGapLogRows_89693_89890 :
    List FinitePrimeGapLogRow :=
  [finitePrimeGapLogRow_89693_89752,
    finitePrimeGapLogRow_89753_89758,
    finitePrimeGapLogRow_89759_89766,
    finitePrimeGapLogRow_89767_89778,
    finitePrimeGapLogRow_89779_89782,
    finitePrimeGapLogRow_89783_89796,
    finitePrimeGapLogRow_89797_89808,
    finitePrimeGapLogRow_89809_89818,
    finitePrimeGapLogRow_89819_89820,
    finitePrimeGapLogRow_89821_89832,
    finitePrimeGapLogRow_89833_89838,
    finitePrimeGapLogRow_89839_89848,
    finitePrimeGapLogRow_89849_89866,
    finitePrimeGapLogRow_89867_89890]

theorem finitePrimeGapLogRows_89693_89890_chain :
    FinitePrimeGapLogRowsChain 89693 89890
      finitePrimeGapLogRows_89693_89890 := by
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89693_89752
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89753_89758
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89759_89766
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89767_89778
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89779_89782
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89783_89796
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89797_89808
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89809_89818
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89819_89820
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89821_89832
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89833_89838
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89839_89848
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89849_89866
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89867_89890
  · norm_num
  · norm_num
  exact FinitePrimeGapLogRowsChain.empty (by norm_num)

theorem finitePrimeGapLogRows_89693_89890_cover :
    FinitePrimeGapLogRowsCoverUpTo
      finitePrimeGapLogRows_89693_89890 (89890 : Real) := by
  exact finitePrimeGapLogRowsCoverUpTo_of_chain
    finitePrimeGapLogRows_89693_89890_chain (by norm_num)

theorem hasLogCubedShortIntervalPrimeBelow_89693_89752 :
    HasLogCubedShortIntervalPrimeBelow (89752 : Real) :=
  hasLogCubedShortIntervalPrimeBelow_of_finite_gap_log_rows
    finitePrimeGapLogRows_89693_89752_cover

theorem hasLogCubedShortIntervalPrimeBelow_89693_89758 :
    HasLogCubedShortIntervalPrimeBelow (89758 : Real) :=
  hasLogCubedShortIntervalPrimeBelow_of_finite_gap_log_rows
    finitePrimeGapLogRows_89693_89758_cover

theorem hasLogCubedShortIntervalPrimeBelow_89693_89890 :
    HasLogCubedShortIntervalPrimeBelow (89890 : Real) :=
  hasLogCubedShortIntervalPrimeBelow_of_finite_gap_log_rows
    finitePrimeGapLogRows_89693_89890_cover

theorem hasLogCubedShortIntervalPrime_of_rows
    (upper_mono : ∀ {a b : Real}, 89693 ≤ a → a ≤ b →
      logCubedUpper a ≤ logCubedUpper b)
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCover rows) :
    HasLogCubedShortIntervalPrime := by
  intro x x_large
  obtain ⟨row, row_mem, left_mem, right_mem⟩ := cover x x_large
  exact logCubedPrimeRow_provides upper_mono row left_mem right_mem

theorem hasLogCubedShortIntervalPrime_of_rows_closed
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCover rows) :
    HasLogCubedShortIntervalPrime := by
  refine hasLogCubedShortIntervalPrime_of_rows ?_ cover
  intro a b ha hab
  exact logCubedUpper_monotoneOn (by norm_num at ⊢; linarith)
    (by norm_num at ⊢; linarith) hab

theorem hasLogCubedShortIntervalPrimeBelow_of_rows
    {X : Real} {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows X) :
    HasLogCubedShortIntervalPrimeBelow X := by
  intro x hx hX
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
  exact logCubedPrimeRow_provides
    (fun {a b} ha hab => logCubedUpper_monotoneOn
      (by norm_num at ⊢; linarith)
      (by norm_num at ⊢; linarith) hab)
    row hleft hright

structure DusartThetaBoundsRow where
  left : Nat
  right : Nat
  left_large : 2 ≤ left
  left_le_right : left ≤ right
  upper : ∀ x : Real, (left : Real) ≤ x → x ≤ right →
    Chebyshev.theta x - x < x / 36260
  lower : ∀ x : Real, 2 < x → (left : Real) ≤ x → x ≤ right →
    |Chebyshev.theta x - x| <
      (12323 / 10000 : Real) * x / Real.log x

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

def DusartThetaEndpointRowsCoverUpTo
    (rows : List DusartThetaEndpointRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

def DusartThetaEndpointIndexedCoverUpTo {n : Nat}
    (rows : Fin n → DusartThetaEndpointRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ i : Fin n, (rows i).left ≤ x ∧ x ≤ (rows i).right

theorem dusartThetaEndpointIndexedCover_of_list
    {X : Real} {rows : List DusartThetaEndpointRow}
    (cover : DusartThetaEndpointRowsCoverUpTo rows X) :
    DusartThetaEndpointIndexedCoverUpTo
      (fun i : Fin rows.length => rows.get i) X := by
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
  exact indexed_interval_cover_append left right
    (fun row => row.left) (fun row => row.right)
    (fun y hy _ hym => hleft y hy hym)
    (fun y hy _ hym hyX => hright y hy hyX)
    x hx trivial hX

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

theorem dusartThetaEndpointRow_provides
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
          exact mul_le_mul_of_nonneg_left hratio_y (by norm_num)
    have hlower : -(12323 / 10000 : Real) * y / Real.log y <
        Chebyshev.theta y - y := by
      have hdiff : y - Chebyshev.theta y <
          (12323 / 10000 : Real) * y / Real.log y := by
        calc
          y - Chebyshev.theta y ≤ row.right - row.theta_lower := by linarith
          _ < (12323 / 10000 : Real) * (row.left : Real) /
              Real.log (row.right : Real) := row.lower_lower_error
          _ ≤ (12323 / 10000 : Real) * y / Real.log y := by
            exact mul_le_mul_of_nonneg_left hratio_y (by norm_num)
      linarith
    exact (abs_lt).2 ⟨hlower, hupper⟩

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

structure DusartPrimeCountingRow where
  left : Nat
  right : Nat
  left_large : 2 ≤ left
  left_le_right : left ≤ right
  lower : ∀ x : Real, (599 : Real) ≤ x → (left : Real) ≤ x →
    x ≤ right →
    dusartPiLower x ≤ (Nat.primeCounting ⌊x⌋₊ : Real)
  upper : ∀ x : Real, (left : Real) ≤ x → x ≤ right →
    (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x

structure DusartPrimeCountingEndpointRow where
  left : Nat
  right : Nat
  left_large : 599 ≤ left
  left_le_right : left ≤ right
  lower_endpoint : dusartPiLower right ≤ (Nat.primeCounting left : Real)
  upper_endpoint : (Nat.primeCounting right : Real) ≤ dusartPiUpper left

def DusartPrimeCountingEndpointRowsCoverFrom599
    (rows : List DusartPrimeCountingEndpointRow) (X : Real) : Prop :=
  ∀ x : Real, (599 : Real) ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

def DusartPrimeCountingEndpointIndexedCoverFrom599 {n : Nat}
    (rows : Fin n → DusartPrimeCountingEndpointRow) (X : Real) : Prop :=
  ∀ x : Real, (599 : Real) ≤ x → x ≤ X →
    ∃ i : Fin n, (rows i).left ≤ x ∧ x ≤ (rows i).right

theorem dusartPrimeCountingEndpointIndexedCover_of_list
    {X : Real} {rows : List DusartPrimeCountingEndpointRow}
    (cover : DusartPrimeCountingEndpointRowsCoverFrom599 rows X) :
    DusartPrimeCountingEndpointIndexedCoverFrom599
      (fun i : Fin rows.length => rows.get i) X := by
  exact indexed_interval_cover_of_list_cover rows
    (fun row => row.left) (fun row => row.right) cover

theorem dusartPrimeCountingEndpointIndexedCoverFrom599_append
    {m X : Real} {n₁ n₂ : Nat}
    {left : Fin n₁ → DusartPrimeCountingEndpointRow}
    {right : Fin n₂ → DusartPrimeCountingEndpointRow}
    (hleft : DusartPrimeCountingEndpointIndexedCoverFrom599 left m)
    (hright : DusartPrimeCountingEndpointIndexedCoverFrom599 right X) :
    DusartPrimeCountingEndpointIndexedCoverFrom599
      (Fin.append left right) X := by
  intro x hx hX
  exact indexed_interval_cover_append left right
    (fun row => row.left) (fun row => row.right)
    (fun y hy _ hym => hleft y hy hym)
    (fun y hy _ hym hyX => hright y hy hyX)
    x hx trivial hX

theorem hasDusartRealPrimeCountingBoundsBelow_of_indexed_endpoint_rows
    {n : Nat} {X : Real}
    {rows : Fin n → DusartPrimeCountingEndpointRow}
    (cover : DusartPrimeCountingEndpointIndexedCoverFrom599 rows X)
    (smallUpper : ∀ x : Real, 2 ≤ x → x < 599 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x) :
    HasDusartRealPrimeCountingBoundsBelow X := by
  constructor
  · intro x hx hX
    obtain ⟨i, hleft, hright⟩ := cover x hx hX
    exact (dusartPrimeCountingEndpointRow_provides (rows i) hleft hright).1
  · intro x hx hX
    by_cases hsmall : x < 599
    · exact smallUpper x hx hsmall
    · obtain ⟨i, hleft, hright⟩ := cover x
        (le_of_not_gt hsmall) hX
      exact (dusartPrimeCountingEndpointRow_provides (rows i) hleft hright).2

theorem dusartPrimeCountingEndpointRowsCoverFrom599_append
    {m X : Real} {left right : List DusartPrimeCountingEndpointRow}
    (hleft : DusartPrimeCountingEndpointRowsCoverFrom599 left m)
    (hright : DusartPrimeCountingEndpointRowsCoverFrom599 right X) :
    DusartPrimeCountingEndpointRowsCoverFrom599 (left ++ right) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hleft x hx hxm
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hright x hx hX
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩

theorem dusartPrimeCountingEndpointRow_provides
    (row : DusartPrimeCountingEndpointRow) {x : Real}
    (hleft : (row.left : Real) ≤ x) (hright : x ≤ row.right) :
    dusartPiLower x ≤ (Nat.primeCounting ⌊x⌋₊ : Real) ∧
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x := by
  have hleft599 : (599 : Real) ≤ row.left := by exact_mod_cast row.left_large
  have hright599 : (599 : Real) ≤ (row.right : Real) :=
    hleft599.trans (by exact_mod_cast row.left_le_right)
  have hfloor_left : row.left ≤ ⌊x⌋₊ := Nat.le_floor hleft
  have hfloor_right : ⌊x⌋₊ ≤ row.right := Nat.floor_le_of_le hright
  have hpi_left : (Nat.primeCounting row.left : Real) ≤
      (Nat.primeCounting ⌊x⌋₊ : Real) := by
    exact_mod_cast Nat.monotone_primeCounting hfloor_left
  have hpi_right : (Nat.primeCounting ⌊x⌋₊ : Real) ≤
      (Nat.primeCounting row.right : Real) := by
    exact_mod_cast Nat.monotone_primeCounting hfloor_right
  have hlower : dusartPiLower x ≤ dusartPiLower (row.right : Real) :=
    dusartPiLower_monotoneOn (by exact hleft599)
      (by exact hright599) hright
  have hupper : dusartPiUpper (row.left : Real) ≤ dusartPiUpper x :=
    dusartPiUpper_monotoneOn (by norm_num at hleft599 ⊢; linarith)
      (by norm_num at hleft599 hright599 ⊢; linarith) hleft
  constructor
  · exact hlower.trans (row.lower_endpoint.trans hpi_left)
  · exact hpi_right.trans (row.upper_endpoint.trans hupper)

theorem hasDusartRealPrimeCountingBoundsBelow_of_endpoint_rows
    {X : Real} {rows : List DusartPrimeCountingEndpointRow}
    (cover : DusartPrimeCountingEndpointRowsCoverFrom599 rows X)
    (smallUpper : ∀ x : Real, 2 ≤ x → x < 599 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x) :
    HasDusartRealPrimeCountingBoundsBelow X := by
  constructor
  · intro x hx hX
    obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
    exact (dusartPrimeCountingEndpointRow_provides row hleft hright).1
  · intro x hx hX
    by_cases hsmall : x < 599
    · exact smallUpper x hx hsmall
    · obtain ⟨row, hrow, hleft, hright⟩ := cover x
        (le_of_not_gt hsmall) hX
      exact (dusartPrimeCountingEndpointRow_provides row hleft hright).2

def DusartPrimeCountingRowsCoverUpTo
    (rows : List DusartPrimeCountingRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

/-! The lower Dusart estimate starts only at `599`.  This variant keeps that
fact visible, so the finite table need not carry rows whose only purpose is
to establish the lower bound below `599`; the short upper range is supplied
by a separate elementary or computational lemma. -/
def DusartPrimeCountingRowsCoverFrom599
    (rows : List DusartPrimeCountingRow) (X : Real) : Prop :=
  ∀ x : Real, (599 : Real) ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem hasDusartRealPrimeCountingBoundsBelow_of_rows_from599
    {X : Real} {rows : List DusartPrimeCountingRow}
    (cover : DusartPrimeCountingRowsCoverFrom599 rows X)
    (smallUpper : ∀ x : Real, 2 ≤ x → x < 599 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x) :
    HasDusartRealPrimeCountingBoundsBelow X := by
  constructor
  · intro x hx hX
    obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
    exact row.lower x hx hleft hright
  · intro x hx hX
    by_cases hsmall : x < 599
    · exact smallUpper x hx hsmall
    · obtain ⟨row, hrow, hleft, hright⟩ := cover x
        (le_of_not_gt hsmall) hX
      exact row.upper x hleft hright

theorem hasDusartRealPrimeCountingBoundsBelow_of_rows
    {X : Real} {rows : List DusartPrimeCountingRow}
    (cover : DusartPrimeCountingRowsCoverUpTo rows X) :
    HasDusartRealPrimeCountingBoundsBelow X := by
  constructor
  · intro x hx hX
    obtain ⟨row, hrow, hleft, hright⟩ := cover x (by linarith) hX
    exact row.lower x hx hleft hright
  · intro x hx hX
    obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
    exact row.upper x hleft hright

theorem hasLogCubedShortIntervalPrime_of_bounded_rows_and_large_x
    {rows : List LogCubedPrimeRow}
    (X : Real) (hX : (4e18 : Real) ≤ X)
    (cover : LogCubedPrimeRowsCoverUpTo rows X)
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    HasLogCubedShortIntervalPrime := by
  intro x hx
  by_cases hsmall : x ≤ X
  · obtain ⟨row, row_mem, left_mem, right_mem⟩ := cover x hx hsmall
    exact logCubedPrimeRow_provides
      (fun {a b} ha hab => logCubedUpper_monotoneOn (by norm_num at ⊢; linarith)
        (by norm_num at ⊢; linarith) hab)
      row left_mem right_mem
  · exact large_x_logCubedShortIntervalPrime thetaError x
      (hX.trans (le_of_lt (lt_of_not_ge hsmall)))

theorem hasLogCubedShortIntervalPrime_of_rows_at_large_cutoff
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    HasLogCubedShortIntervalPrime :=
  hasLogCubedShortIntervalPrime_of_bounded_rows_and_large_x
    (4e18 : Real) le_rfl cover thetaError

theorem hasDusartShortIntervalPrime_of_rows_and_thetaError
    {dusartRows : List DusartPrimeRow}
    (dusartCover : DusartPrimeRowsCoverBelow dusartRows)
    {logRows : List LogCubedPrimeRow}
    (logCover : LogCubedPrimeRowsCoverUpTo logRows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    HasDusartShortIntervalPrime := by
  exact hasDusartShortIntervalPrime_of_below_and_logCubed
    (hasDusartShortIntervalPrimeBelow_of_rows dusartCover)
    (hasLogCubedShortIntervalPrime_of_rows_at_large_cutoff logCover thetaError)

end

end PrimeFactorUnimodality
