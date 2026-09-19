import PrimeFactorUnimodality.Helpers.Analytic.ShortIntervalPrime
import PrimeFactorUnimodality.Helpers.Analytic.ThetaFromPsi
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitThetaBounds
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCounting
import PrimeFactorUnimodality.Helpers.Analytic.MediumPNT

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

theorem log_le_1141_over_100_of_3275_le
    {a : Nat} (ha : 3275 ≤ a) (ha89693 : a ≤ 89693) :
    Real.log a ≤ (1141 : Real) / 100 := by
  have hmono : Real.log (a : Real) ≤ Real.log (89693 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha89693
  exact hmono.trans log_89693_le_1141_over_100

theorem log_3802_le_33_over_4 :
    Real.log (3802 : Real) ≤ (33 : Real) / 4 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  interval_decide

theorem log_le_33_over_4_of_3275_le
    {a : Nat} (ha : 3275 ≤ a) (ha3802 : a ≤ 3802) :
    Real.log a ≤ (33 : Real) / 4 := by
  have hmono : Real.log (a : Real) ≤ Real.log (3802 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha3802
  exact hmono.trans log_3802_le_33_over_4

theorem log_4670_le_169_over_20 :
    Real.log (4670 : Real) ≤ (169 : Real) / 20 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  interval_decide

theorem log_le_169_over_20_of_3803_le
    {a : Nat} (ha : 3803 ≤ a) (ha4670 : a ≤ 4670) :
    Real.log a ≤ (169 : Real) / 20 := by
  have hmono : Real.log (a : Real) ≤ Real.log (4670 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha4670
  exact hmono.trans log_4670_le_169_over_20

theorem log_4914_le_17_over_2 :
    Real.log (4914 : Real) ≤ (17 : Real) / 2 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  interval_decide

theorem log_le_17_over_2_of_4673_le
    {a : Nat} (ha : 4673 ≤ a) (ha4914 : a ≤ 4914) :
    Real.log a ≤ (17 : Real) / 2 := by
  have hmono : Real.log (a : Real) ≤ Real.log (4914 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha4914
  exact hmono.trans log_4914_le_17_over_2

theorem log_5166_le_171_over_20 :
    Real.log (5166 : Real) ≤ (171 : Real) / 20 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  interval_decide

theorem log_le_171_over_20_of_4919_le
    {a : Nat} (ha : 4919 ≤ a) (ha5166 : a ≤ 5166) :
    Real.log a ≤ (171 : Real) / 20 := by
  have hmono : Real.log (a : Real) ≤ Real.log (5166 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha5166
  exact hmono.trans log_5166_le_171_over_20

theorem log_5431_le_43_over_5 :
    Real.log (5431 : Real) ≤ (43 : Real) / 5 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  interval_decide

theorem log_le_43_over_5_of_5167_le
    {a : Nat} (ha : 5167 ≤ a) (ha5431 : a ≤ 5431) :
    Real.log a ≤ (43 : Real) / 5 := by
  have hmono : Real.log (a : Real) ≤ Real.log (5431 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha5431
  exact hmono.trans log_5431_le_43_over_5

theorem log_5710_le_173_over_20 :
    Real.log (5710 : Real) ≤ (173 : Real) / 20 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  interval_decide

theorem log_le_173_over_20_of_5437_le
    {a : Nat} (ha : 5437 ≤ a) (ha5710 : a ≤ 5710) :
    Real.log a ≤ (173 : Real) / 20 := by
  have hmono : Real.log (a : Real) ≤ Real.log (5710 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha5710
  exact hmono.trans log_5710_le_173_over_20

theorem log_6002_le_87_over_10 :
    Real.log (6002 : Real) ≤ (87 : Real) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  interval_decide

theorem log_le_87_over_10_of_5711_le
    {a : Nat} (ha : 5711 ≤ a) (ha6002 : a ≤ 6002) :
    Real.log a ≤ (87 : Real) / 10 := by
  have hmono : Real.log (a : Real) ≤ Real.log (6002 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha6002
  exact hmono.trans log_6002_le_87_over_10

theorem log_6310_le_35_over_4 :
    Real.log (6310 : Real) ≤ (35 : Real) / 4 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  interval_decide

theorem log_le_35_over_4_of_6007_le
    {a : Nat} (ha : 6007 ≤ a) (ha6310 : a ≤ 6310) :
    Real.log a ≤ (35 : Real) / 4 := by
  have hmono : Real.log (a : Real) ≤ Real.log (6310 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha6310
  exact hmono.trans log_6310_le_35_over_4

theorem log_6634_le_44_over_5 :
    Real.log (6634 : Real) ≤ (44 : Real) / 5 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  interval_decide

theorem log_le_44_over_5_of_6311_le
    {a : Nat} (ha : 6311 ≤ a) (ha6634 : a ≤ 6634) :
    Real.log a ≤ (44 : Real) / 5 := by
  have hmono : Real.log (a : Real) ≤ Real.log (6634 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha6634
  exact hmono.trans log_6634_le_44_over_5

theorem log_6974_le_177_over_20 :
    Real.log (6974 : Real) ≤ (177 : Real) / 20 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  interval_decide

theorem log_le_177_over_20_of_6637_le
    {a : Nat} (ha : 6637 ≤ a) (ha6974 : a ≤ 6974) :
    Real.log a ≤ (177 : Real) / 20 := by
  have hmono : Real.log (a : Real) ≤ Real.log (6974 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha6974
  exact hmono.trans log_6974_le_177_over_20

theorem log_7331_le_89_over_10 :
    Real.log (7331 : Real) ≤ (89 : Real) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  interval_decide

theorem log_le_89_over_10_of_6977_le
    {a : Nat} (ha : 6977 ≤ a) (ha7331 : a ≤ 7331) :
    Real.log a ≤ (89 : Real) / 10 := by
  have hmono : Real.log (a : Real) ≤ Real.log (7331 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha7331
  exact hmono.trans log_7331_le_89_over_10

theorem log_7707_le_179_over_20 :
    Real.log (7707 : Real) ≤ (179 : Real) / 20 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  interval_decide

theorem log_le_179_over_20_of_7333_le
    {a : Nat} (ha : 7333 ≤ a) (ha7707 : a ≤ 7707) :
    Real.log a ≤ (179 : Real) / 20 := by
  have hmono : Real.log (a : Real) ≤ Real.log (7707 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha7707
  exact hmono.trans log_7707_le_179_over_20

theorem log_8103_le_9 :
    Real.log (8103 : Real) ≤ (9 : Real) := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  interval_decide

theorem log_le_9_of_7717_le
    {a : Nat} (ha : 7717 ≤ a) (ha8103 : a ≤ 8103) :
    Real.log a ≤ (9 : Real) := by
  have hmono : Real.log (a : Real) ≤ Real.log (8103 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha8103
  exact hmono.trans log_8103_le_9

theorem log_8518_le_181_over_20 :
    Real.log (8518 : Real) ≤ (181 : Real) / 20 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  interval_decide

theorem log_le_181_over_20_of_8111_le
    {a : Nat} (ha : 8111 ≤ a) (ha8518 : a ≤ 8518) :
    Real.log a ≤ (181 : Real) / 20 := by
  have hmono : Real.log (a : Real) ≤ Real.log (8518 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha8518
  exact hmono.trans log_8518_le_181_over_20

theorem log_8955_le_91_over_10 :
    Real.log (8955 : Real) ≤ (91 : Real) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  interval_decide

theorem log_le_91_over_10_of_8521_le
    {a : Nat} (ha : 8521 ≤ a) (ha8955 : a ≤ 8955) :
    Real.log a ≤ (91 : Real) / 10 := by
  have hmono : Real.log (a : Real) ≤ Real.log (8955 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha8955
  exact hmono.trans log_8955_le_91_over_10

theorem log_9414_le_183_over_20 :
    Real.log (9414 : Real) ≤ (183 : Real) / 20 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  interval_decide

theorem log_le_183_over_20_of_8963_le
    {a : Nat} (ha : 8963 ≤ a) (ha9414 : a ≤ 9414) :
    Real.log a ≤ (183 : Real) / 20 := by
  have hmono : Real.log (a : Real) ≤ Real.log (9414 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha9414
  exact hmono.trans log_9414_le_183_over_20

theorem log_9897_le_46_over_5 :
    Real.log (9897 : Real) ≤ (46 : Real) / 5 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  interval_decide

theorem log_le_46_over_5_of_9419_le
    {a : Nat} (ha : 9419 ≤ a) (ha9897 : a ≤ 9897) :
    Real.log a ≤ (46 : Real) / 5 := by
  have hmono : Real.log (a : Real) ≤ Real.log (9897 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha9897
  exact hmono.trans log_9897_le_46_over_5

theorem log_10404_le_37_over_4 :
    Real.log (10404 : Real) ≤ (37 : Real) / 4 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  interval_decide

theorem log_le_37_over_4_of_9901_le
    {a : Nat} (ha : 9901 ≤ a) (ha10404 : a ≤ 10404) :
    Real.log a ≤ (37 : Real) / 4 := by
  have hmono : Real.log (a : Real) ≤ Real.log (10404 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha10404
  exact hmono.trans log_10404_le_37_over_4

theorem log_10938_le_93_over_10 :
    Real.log (10938 : Real) ≤ (93 : Real) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  interval_decide

theorem log_le_93_over_10_of_10427_le
    {a : Nat} (ha : 10427 ≤ a) (ha10938 : a ≤ 10938) :
    Real.log a ≤ (93 : Real) / 10 := by
  have hmono : Real.log (a : Real) ≤ Real.log (10938 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha10938
  exact hmono.trans log_10938_le_93_over_10

theorem log_11498_le_187_over_20 :
    Real.log (11498 : Real) ≤ (187 : Real) / 20 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  interval_decide

theorem log_le_187_over_20_of_10939_le
    {a : Nat} (ha : 10939 ≤ a) (ha11498 : a ≤ 11498) :
    Real.log a ≤ (187 : Real) / 20 := by
  have hmono : Real.log (a : Real) ≤ Real.log (11498 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha11498
  exact hmono.trans log_11498_le_187_over_20

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

theorem dusartPrimeRow_of_explicit
    {p q : Nat} {L : Real}
    (hq : q.Prime)
    (hpq : p < q)
    (hleft_large : 3275 ≤ p)
    (hlog : Real.log p ≤ L)
    (hL : 0 < L)
    (hproduct : (q - p : Real) * (2 * L ^ 2) ≤ p) :
    DusartPrimeRow := by
  have hp_pos : (0 : Real) < p := by
    exact_mod_cast (show 0 < p by omega)
  have hlog_pos : 0 < Real.log p :=
    Real.log_pos (by norm_num at hleft_large ⊢; linarith)
  have hlog_sq : 2 * (Real.log p) ^ 2 ≤ 2 * L ^ 2 := by
    nlinarith [sq_nonneg (Real.log p), sq_nonneg L]
  have hdenL : 0 < 2 * L ^ 2 := by positivity
  have hdenLog : 0 < 2 * (Real.log p) ^ 2 := by positivity
  have hgapL : (q - p : Real) ≤ p / (2 * L ^ 2) := by
    apply (le_div_iff₀ hdenL).2
    exact hproduct
  have hgap : (q - p : Real) ≤ p / (2 * (Real.log p) ^ 2) :=
    hgapL.trans (div_le_div_of_nonneg_left hp_pos.le hdenLog hlog_sq)
  refine {
    left := p
    right := q - 1
    prime := q
    left_large := hleft_large
    right_lt_prime := by omega
    prime_prime := hq
    prime_upper := ?_ }
  have hqreal : (q : Real) - p ≤
      p / (2 * (Real.log p) ^ 2) := by
    exact hgap
  dsimp [dusartUpper]
  linarith

theorem dusartPrimeRow_of_explicit_3802
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((33 : Real) / 4) ^ 2) ≤ p)
    (hleft_large : 3275 ≤ p)
    (hleft_3802 : p ≤ 3802) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq hleft_large
    (log_le_33_over_4_of_3275_le hleft_large hleft_3802)
    (by norm_num) hproduct

theorem dusartPrimeRow_of_explicit_4670
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((169 : Real) / 20) ^ 2) ≤ p)
    (hleft_large : 3803 ≤ p)
    (hleft_4670 : p ≤ 4670) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_169_over_20_of_3803_le hleft_large hleft_4670)
    (by norm_num) hproduct

theorem dusartPrimeRow_of_explicit_4914
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((17 : Real) / 2) ^ 2) ≤ p)
    (hleft_large : 4673 ≤ p)
    (hleft_4914 : p ≤ 4914) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_17_over_2_of_4673_le hleft_large hleft_4914)
    (by norm_num) hproduct

theorem dusartPrimeRow_of_explicit_5166
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((171 : Real) / 20) ^ 2) ≤ p)
    (hleft_large : 4919 ≤ p)
    (hleft_5166 : p ≤ 5166) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_171_over_20_of_4919_le hleft_large hleft_5166)
    (by norm_num) hproduct

theorem dusartPrimeRow_of_explicit_5431
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((43 : Real) / 5) ^ 2) ≤ p)
    (hleft_large : 5167 ≤ p)
    (hleft_5431 : p ≤ 5431) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_43_over_5_of_5167_le hleft_large hleft_5431)
    (by norm_num) hproduct

theorem dusartPrimeRow_of_explicit_5710
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((173 : Real) / 20) ^ 2) ≤ p)
    (hleft_large : 5437 ≤ p)
    (hleft_5710 : p ≤ 5710) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_173_over_20_of_5437_le hleft_large hleft_5710)
    (by norm_num) hproduct

theorem dusartPrimeRow_of_explicit_6002
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((87 : Real) / 10) ^ 2) ≤ p)
    (hleft_large : 5711 ≤ p)
    (hleft_6002 : p ≤ 6002) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_87_over_10_of_5711_le hleft_large hleft_6002)
    (by norm_num) hproduct

theorem dusartPrimeRow_of_explicit_6310
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((35 : Real) / 4) ^ 2) ≤ p)
    (hleft_large : 6007 ≤ p)
    (hleft_6310 : p ≤ 6310) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_35_over_4_of_6007_le hleft_large hleft_6310)
    (by norm_num) hproduct

theorem dusartPrimeRow_of_explicit_6634
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((44 : Real) / 5) ^ 2) ≤ p)
    (hleft_large : 6311 ≤ p)
    (hleft_6634 : p ≤ 6634) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_44_over_5_of_6311_le hleft_large hleft_6634)
    (by norm_num) hproduct

theorem dusartPrimeRow_of_explicit_6974
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((177 : Real) / 20) ^ 2) ≤ p)
    (hleft_large : 6637 ≤ p)
    (hleft_6974 : p ≤ 6974) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_177_over_20_of_6637_le hleft_large hleft_6974)
    (by norm_num) hproduct

theorem dusartPrimeRow_of_explicit_7331
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((89 : Real) / 10) ^ 2) ≤ p)
    (hleft_large : 6977 ≤ p)
    (hleft_7331 : p ≤ 7331) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_89_over_10_of_6977_le hleft_large hleft_7331)
    (by norm_num) hproduct

theorem dusartPrimeRow_of_explicit_7707
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((179 : Real) / 20) ^ 2) ≤ p)
    (hleft_large : 7333 ≤ p)
    (hleft_7707 : p ≤ 7707) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_179_over_20_of_7333_le hleft_large hleft_7707)
    (by norm_num) hproduct

theorem dusartPrimeRow_of_explicit_8103
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * (9 : Real) ^ 2) ≤ p)
    (hleft_large : 7717 ≤ p)
    (hleft_8103 : p ≤ 8103) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_9_of_7717_le hleft_large hleft_8103)
    (by norm_num) hproduct

theorem dusartPrimeRow_of_explicit_8518
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((181 : Real) / 20) ^ 2) ≤ p)
    (hleft_large : 8111 ≤ p)
    (hleft_8518 : p ≤ 8518) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_181_over_20_of_8111_le hleft_large hleft_8518)
    (by norm_num) hproduct

theorem dusartPrimeRow_of_explicit_8955
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((91 : Real) / 10) ^ 2) ≤ p)
    (hleft_large : 8521 ≤ p)
    (hleft_8955 : p ≤ 8955) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_91_over_10_of_8521_le hleft_large hleft_8955)
    (by norm_num) hproduct

theorem dusartPrimeRow_of_explicit_9414
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((183 : Real) / 20) ^ 2) ≤ p)
    (hleft_large : 8963 ≤ p)
    (hleft_9414 : p ≤ 9414) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_183_over_20_of_8963_le hleft_large hleft_9414)
    (by norm_num) hproduct

theorem dusartPrimeRow_of_explicit_9897
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((46 : Real) / 5) ^ 2) ≤ p)
    (hleft_large : 9419 ≤ p)
    (hleft_9897 : p ≤ 9897) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_46_over_5_of_9419_le hleft_large hleft_9897)
    (by norm_num) hproduct

theorem dusartPrimeRow_of_explicit_10404
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((37 : Real) / 4) ^ 2) ≤ p)
    (hleft_large : 9901 ≤ p)
    (hleft_10404 : p ≤ 10404) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_37_over_4_of_9901_le hleft_large hleft_10404)
    (by norm_num) hproduct

theorem dusartPrimeRow_of_explicit_10938
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((93 : Real) / 10) ^ 2) ≤ p)
    (hleft_large : 10427 ≤ p)
    (hleft_10938 : p ≤ 10938) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_93_over_10_of_10427_le hleft_large hleft_10938)
    (by norm_num) hproduct

theorem dusartPrimeRow_of_explicit_11498
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((187 : Real) / 20) ^ 2) ≤ p)
    (hleft_large : 10939 ≤ p)
    (hleft_11498 : p ≤ 11498) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_187_over_20_of_10939_le hleft_large hleft_11498)
    (by norm_num) hproduct

theorem dusartPrimeRow_of_explicit_89693
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((1141 : Real) / 100) ^ 2) ≤ p)
    (hleft_large : 3275 ≤ p)
    (hleft_89693 : p ≤ 89693) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq hleft_large
    (log_le_1141_over_100_of_3275_le hleft_large hleft_89693)
    (by norm_num) hproduct

inductive DusartPrimeRowsChain : Nat → Nat → List DusartPrimeRow → Prop
  | empty {a b : Nat} (h : b < a) :
      DusartPrimeRowsChain a b []
  | cons {a b : Nat} (row : DusartPrimeRow)
      (hleft : row.left ≤ a)
      (hordered : row.left ≤ row.right)
      {tail : List DusartPrimeRow}
      (htail : DusartPrimeRowsChain (row.right + 1) b tail) :
      DusartPrimeRowsChain a b (row :: tail)

theorem dusartPrimeRowsCover_of_chain
    {a b : Nat} {rows : List DusartPrimeRow}
    (chain : DusartPrimeRowsChain a b rows) :
    ∀ x : Real, (a : Real) ≤ x → x ≤ b →
      ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right := by
  induction chain with
  | empty h =>
      intro x hleft hright
      exfalso
      norm_num at h
      linarith
  | @cons a b row hleft hordered tail htail ih =>
      intro x hxa hxb
      by_cases hrow : x ≤ row.right
      · refine ⟨row, by simp, ?_, hrow⟩
        have hleft_real : (row.left : Real) ≤ a := by
          exact_mod_cast hleft
        exact hleft_real.trans hxa
      · have hnext : (row.right + 1 : Real) ≤ x := by
          have : (row.right : Real) < x := lt_of_not_ge hrow
          linarith
        obtain ⟨next, hmem, hnext_left, hnext_right⟩ :=
          ih x hnext hxb
        exact ⟨next, by simp [hmem], hnext_left, hnext_right⟩

theorem dusartPrimeRowsChain_raise_start
    {a a' b : Nat} {rows : List DusartPrimeRow}
    (haa' : a ≤ a')
    (chain : DusartPrimeRowsChain a b rows) :
    DusartPrimeRowsChain a' b rows := by
  induction chain with
  | empty h =>
      exact DusartPrimeRowsChain.empty (by omega)
  | @cons a b row hleft hordered tail htail ih =>
      exact DusartPrimeRowsChain.cons row (by omega) hordered ih

theorem dusartPrimeRowsChain_append
    {a m b : Nat} {left right : List DusartPrimeRow}
    (hleft : DusartPrimeRowsChain a m left)
    (hright : DusartPrimeRowsChain (m + 1) b right) :
    DusartPrimeRowsChain a b (left ++ right) := by
  induction hleft with
  | empty h =>
      simpa using dusartPrimeRowsChain_raise_start (by omega) hright
  | @cons a m row hrow hordered tail htail ih =>
      simpa using DusartPrimeRowsChain.cons row hrow hordered
        (ih hright)

def dusartPrimeRows_3275_3802 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3275) (q := 3299) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3299) (q := 3301) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3301) (q := 3307) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3307) (q := 3313) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3313) (q := 3319) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3319) (q := 3323) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3323) (q := 3329) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3329) (q := 3331) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3331) (q := 3343) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3343) (q := 3347) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3347) (q := 3359) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3359) (q := 3361) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3361) (q := 3371) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3371) (q := 3373) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3373) (q := 3389) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3389) (q := 3391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3391) (q := 3407) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3407) (q := 3413) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3413) (q := 3433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3433) (q := 3449) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3449) (q := 3457) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3457) (q := 3461) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3461) (q := 3463) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3463) (q := 3467) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3467) (q := 3469) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3469) (q := 3491) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3491) (q := 3499) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3499) (q := 3511) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3511) (q := 3517) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3517) (q := 3527) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3527) (q := 3529) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3529) (q := 3533) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3533) (q := 3539) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3539) (q := 3541) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3541) (q := 3547) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3547) (q := 3557) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3557) (q := 3559) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3559) (q := 3571) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3571) (q := 3581) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3581) (q := 3583) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3583) (q := 3593) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3593) (q := 3607) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3607) (q := 3613) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3613) (q := 3617) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3617) (q := 3623) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3623) (q := 3631) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3631) (q := 3637) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3637) (q := 3643) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3643) (q := 3659) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3659) (q := 3671) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3671) (q := 3673) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3673) (q := 3677) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3677) (q := 3691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3691) (q := 3697) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3697) (q := 3701) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3701) (q := 3709) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3709) (q := 3719) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3719) (q := 3727) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3727) (q := 3733) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3733) (q := 3739) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3739) (q := 3761) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3761) (q := 3767) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3767) (q := 3769) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3769) (q := 3779) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3779) (q := 3793) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3793) (q := 3797) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3797) (q := 3803) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]

theorem dusartPrimeRows_3275_3802_chain :
    DusartPrimeRowsChain 3275 3802 dusartPrimeRows_3275_3802 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3275) (q := 3299) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3299) (q := 3301) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3301) (q := 3307) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3307) (q := 3313) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3313) (q := 3319) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3319) (q := 3323) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3323) (q := 3329) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3329) (q := 3331) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3331) (q := 3343) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3343) (q := 3347) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3347) (q := 3359) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3359) (q := 3361) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3361) (q := 3371) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3371) (q := 3373) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3373) (q := 3389) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3389) (q := 3391) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3391) (q := 3407) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3407) (q := 3413) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3413) (q := 3433) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3433) (q := 3449) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3449) (q := 3457) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3457) (q := 3461) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3461) (q := 3463) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3463) (q := 3467) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3467) (q := 3469) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3469) (q := 3491) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3491) (q := 3499) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3499) (q := 3511) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3511) (q := 3517) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3517) (q := 3527) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3527) (q := 3529) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3529) (q := 3533) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3533) (q := 3539) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3539) (q := 3541) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3541) (q := 3547) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3547) (q := 3557) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3557) (q := 3559) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3559) (q := 3571) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3571) (q := 3581) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3581) (q := 3583) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3583) (q := 3593) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3593) (q := 3607) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3607) (q := 3613) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3613) (q := 3617) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3617) (q := 3623) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3623) (q := 3631) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3631) (q := 3637) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3637) (q := 3643) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3643) (q := 3659) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3659) (q := 3671) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3671) (q := 3673) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3673) (q := 3677) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3677) (q := 3691) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3691) (q := 3697) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3697) (q := 3701) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3701) (q := 3709) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3709) (q := 3719) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3719) (q := 3727) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3727) (q := 3733) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3733) (q := 3739) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3739) (q := 3761) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3761) (q := 3767) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3767) (q := 3769) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3769) (q := 3779) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3779) (q := 3793) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3793) (q := 3797) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_3802 (p := 3797) (q := 3803) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


def dusartPrimeRows_3803_4672 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 3803) (q := 3821) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3821) (q := 3823) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3823) (q := 3833) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3833) (q := 3847) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3847) (q := 3851) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3851) (q := 3853) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3853) (q := 3863) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3863) (q := 3877) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3877) (q := 3881) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3881) (q := 3889) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3889) (q := 3907) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3907) (q := 3911) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3911) (q := 3917) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3917) (q := 3919) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3919) (q := 3923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3923) (q := 3929) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3929) (q := 3931) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3931) (q := 3943) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3943) (q := 3947) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3947) (q := 3967) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3967) (q := 3989) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3989) (q := 4001) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4001) (q := 4003) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4003) (q := 4007) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4007) (q := 4013) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4013) (q := 4019) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4019) (q := 4021) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4021) (q := 4027) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4027) (q := 4049) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4049) (q := 4051) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4051) (q := 4057) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4057) (q := 4073) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4073) (q := 4079) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4079) (q := 4091) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4091) (q := 4093) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4093) (q := 4099) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4099) (q := 4111) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4111) (q := 4127) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4127) (q := 4129) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4129) (q := 4133) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4133) (q := 4139) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4139) (q := 4153) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4153) (q := 4157) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4157) (q := 4159) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4159) (q := 4177) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4177) (q := 4201) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4201) (q := 4211) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4211) (q := 4217) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4217) (q := 4219) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4219) (q := 4229) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4229) (q := 4231) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4231) (q := 4241) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4241) (q := 4243) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4243) (q := 4253) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4253) (q := 4259) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4259) (q := 4261) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4261) (q := 4271) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4271) (q := 4273) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4273) (q := 4283) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4283) (q := 4289) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4289) (q := 4297) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4297) (q := 4327) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4327) (q := 4337) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4337) (q := 4339) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4339) (q := 4349) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4349) (q := 4357) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4357) (q := 4363) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4363) (q := 4373) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4373) (q := 4391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4391) (q := 4397) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4397) (q := 4409) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4409) (q := 4421) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4421) (q := 4423) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4423) (q := 4441) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4441) (q := 4447) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4447) (q := 4451) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4451) (q := 4457) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4457) (q := 4463) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4463) (q := 4481) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4481) (q := 4483) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4483) (q := 4493) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4493) (q := 4507) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4507) (q := 4513) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4513) (q := 4517) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4517) (q := 4519) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4519) (q := 4523) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4523) (q := 4547) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4547) (q := 4549) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4549) (q := 4561) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4561) (q := 4567) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4567) (q := 4583) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4583) (q := 4591) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4591) (q := 4597) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4597) (q := 4603) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4603) (q := 4621) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4621) (q := 4637) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4637) (q := 4639) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4639) (q := 4643) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4643) (q := 4649) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4649) (q := 4651) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4651) (q := 4657) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4657) (q := 4663) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4663) (q := 4673) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

theorem dusartPrimeRows_3803_4672_chain :
    DusartPrimeRowsChain 3803 4672 dusartPrimeRows_3803_4672 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 3803) (q := 3821) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 3821) (q := 3823) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 3823) (q := 3833) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 3833) (q := 3847) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 3847) (q := 3851) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 3851) (q := 3853) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 3853) (q := 3863) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 3863) (q := 3877) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 3877) (q := 3881) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 3881) (q := 3889) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 3889) (q := 3907) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 3907) (q := 3911) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 3911) (q := 3917) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 3917) (q := 3919) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 3919) (q := 3923) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 3923) (q := 3929) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 3929) (q := 3931) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 3931) (q := 3943) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 3943) (q := 3947) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 3947) (q := 3967) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 3967) (q := 3989) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 3989) (q := 4001) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4001) (q := 4003) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4003) (q := 4007) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4007) (q := 4013) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4013) (q := 4019) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4019) (q := 4021) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4021) (q := 4027) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4027) (q := 4049) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4049) (q := 4051) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4051) (q := 4057) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4057) (q := 4073) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4073) (q := 4079) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4079) (q := 4091) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4091) (q := 4093) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4093) (q := 4099) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4099) (q := 4111) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4111) (q := 4127) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4127) (q := 4129) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4129) (q := 4133) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4133) (q := 4139) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4139) (q := 4153) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4153) (q := 4157) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4157) (q := 4159) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4159) (q := 4177) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4177) (q := 4201) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4201) (q := 4211) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4211) (q := 4217) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4217) (q := 4219) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4219) (q := 4229) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4229) (q := 4231) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4231) (q := 4241) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4241) (q := 4243) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4243) (q := 4253) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4253) (q := 4259) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4259) (q := 4261) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4261) (q := 4271) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4271) (q := 4273) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4273) (q := 4283) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4283) (q := 4289) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4289) (q := 4297) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4297) (q := 4327) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4327) (q := 4337) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4337) (q := 4339) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4339) (q := 4349) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4349) (q := 4357) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4357) (q := 4363) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4363) (q := 4373) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4373) (q := 4391) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4391) (q := 4397) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4397) (q := 4409) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4409) (q := 4421) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4421) (q := 4423) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4423) (q := 4441) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4441) (q := 4447) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4447) (q := 4451) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4451) (q := 4457) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4457) (q := 4463) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4463) (q := 4481) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4481) (q := 4483) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4483) (q := 4493) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4493) (q := 4507) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4507) (q := 4513) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4513) (q := 4517) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4517) (q := 4519) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4519) (q := 4523) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4523) (q := 4547) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4547) (q := 4549) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4549) (q := 4561) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4561) (q := 4567) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4567) (q := 4583) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4583) (q := 4591) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4591) (q := 4597) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4597) (q := 4603) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4603) (q := 4621) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4621) (q := 4637) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4637) (q := 4639) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4639) (q := 4643) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4643) (q := 4649) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4649) (q := 4651) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4651) (q := 4657) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4657) (q := 4663) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4670 (p := 4663) (q := 4673) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)

def dusartPrimeRows_3275_4672 : List DusartPrimeRow :=
  dusartPrimeRows_3275_3802 ++ dusartPrimeRows_3803_4672

theorem dusartPrimeRows_3275_4672_chain :
    DusartPrimeRowsChain 3275 4672 dusartPrimeRows_3275_4672 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_3802_chain
    dusartPrimeRows_3803_4672_chain

def dusartPrimeRows_4673_4918 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4914 (p := 4673) (q := 4679) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4679) (q := 4691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4691) (q := 4703) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4703) (q := 4721) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4721) (q := 4723) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4723) (q := 4729) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4729) (q := 4733) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4733) (q := 4751) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4751) (q := 4759) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4759) (q := 4783) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4783) (q := 4787) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4787) (q := 4789) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4789) (q := 4793) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4793) (q := 4799) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4799) (q := 4801) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4801) (q := 4813) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4813) (q := 4817) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4817) (q := 4831) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4831) (q := 4861) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4861) (q := 4871) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4871) (q := 4877) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4877) (q := 4889) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4889) (q := 4903) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4903) (q := 4909) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4909) (q := 4919) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

theorem dusartPrimeRows_4673_4918_chain :
    DusartPrimeRowsChain 4673 4918 dusartPrimeRows_4673_4918 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4673) (q := 4679) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4679) (q := 4691) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4691) (q := 4703) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4703) (q := 4721) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4721) (q := 4723) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4723) (q := 4729) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4729) (q := 4733) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4733) (q := 4751) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4751) (q := 4759) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4759) (q := 4783) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4783) (q := 4787) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4787) (q := 4789) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4789) (q := 4793) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4793) (q := 4799) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4799) (q := 4801) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4801) (q := 4813) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4813) (q := 4817) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4817) (q := 4831) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4831) (q := 4861) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4861) (q := 4871) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4871) (q := 4877) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4877) (q := 4889) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4889) (q := 4903) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4903) (q := 4909) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_4914 (p := 4909) (q := 4919) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


def dusartPrimeRows_3275_4918 : List DusartPrimeRow :=
  dusartPrimeRows_3275_4672 ++ dusartPrimeRows_4673_4918

theorem dusartPrimeRows_3275_4918_chain :
    DusartPrimeRowsChain 3275 4918 dusartPrimeRows_3275_4918 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_4672_chain dusartPrimeRows_4673_4918_chain

def dusartPrimeRows_4919_5166 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5166 (p := 4919) (q := 4931) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4931) (q := 4933) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4933) (q := 4937) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4937) (q := 4943) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4943) (q := 4951) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4951) (q := 4957) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4957) (q := 4967) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4967) (q := 4969) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4969) (q := 4973) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4973) (q := 4987) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4987) (q := 4993) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4993) (q := 4999) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4999) (q := 5003) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5003) (q := 5009) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5009) (q := 5011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5011) (q := 5021) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5021) (q := 5023) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5023) (q := 5039) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5039) (q := 5051) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5051) (q := 5059) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5059) (q := 5077) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5077) (q := 5081) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5081) (q := 5087) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5087) (q := 5099) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5099) (q := 5101) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5101) (q := 5107) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5107) (q := 5113) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5113) (q := 5119) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5119) (q := 5147) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5147) (q := 5153) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5153) (q := 5167) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

theorem dusartPrimeRows_4919_5166_chain :
    DusartPrimeRowsChain 4919 5166 dusartPrimeRows_4919_5166 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 4919) (q := 4931) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 4931) (q := 4933) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 4933) (q := 4937) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 4937) (q := 4943) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 4943) (q := 4951) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 4951) (q := 4957) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 4957) (q := 4967) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 4967) (q := 4969) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 4969) (q := 4973) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 4973) (q := 4987) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 4987) (q := 4993) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 4993) (q := 4999) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 4999) (q := 5003) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 5003) (q := 5009) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 5009) (q := 5011) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 5011) (q := 5021) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 5021) (q := 5023) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 5023) (q := 5039) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 5039) (q := 5051) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 5051) (q := 5059) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 5059) (q := 5077) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 5077) (q := 5081) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 5081) (q := 5087) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 5087) (q := 5099) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 5099) (q := 5101) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 5101) (q := 5107) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 5107) (q := 5113) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 5113) (q := 5119) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 5119) (q := 5147) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 5147) (q := 5153) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5166 (p := 5153) (q := 5167) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


def dusartPrimeRows_3275_5166 : List DusartPrimeRow :=
  dusartPrimeRows_3275_4918 ++ dusartPrimeRows_4919_5166

theorem dusartPrimeRows_3275_5166_chain :
    DusartPrimeRowsChain 3275 5166 dusartPrimeRows_3275_5166 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_4918_chain dusartPrimeRows_4919_5166_chain

def dusartPrimeRows_5167_5436 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5431 (p := 5167) (q := 5171) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5171) (q := 5179) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5179) (q := 5189) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5189) (q := 5197) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5197) (q := 5209) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5209) (q := 5227) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5227) (q := 5231) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5231) (q := 5233) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5233) (q := 5237) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5237) (q := 5261) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5261) (q := 5273) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5273) (q := 5279) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5279) (q := 5281) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5281) (q := 5297) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5297) (q := 5303) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5303) (q := 5309) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5309) (q := 5323) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5323) (q := 5333) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5333) (q := 5347) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5347) (q := 5351) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5351) (q := 5381) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5381) (q := 5387) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5387) (q := 5393) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5393) (q := 5399) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5399) (q := 5407) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5407) (q := 5413) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5413) (q := 5417) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5417) (q := 5419) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5419) (q := 5431) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5431) (q := 5437) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

theorem dusartPrimeRows_5167_5436_chain :
    DusartPrimeRowsChain 5167 5436 dusartPrimeRows_5167_5436 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5167) (q := 5171) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5171) (q := 5179) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5179) (q := 5189) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5189) (q := 5197) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5197) (q := 5209) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5209) (q := 5227) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5227) (q := 5231) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5231) (q := 5233) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5233) (q := 5237) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5237) (q := 5261) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5261) (q := 5273) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5273) (q := 5279) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5279) (q := 5281) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5281) (q := 5297) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5297) (q := 5303) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5303) (q := 5309) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5309) (q := 5323) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5323) (q := 5333) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5333) (q := 5347) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5347) (q := 5351) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5351) (q := 5381) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5381) (q := 5387) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5387) (q := 5393) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5393) (q := 5399) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5399) (q := 5407) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5407) (q := 5413) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5413) (q := 5417) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5417) (q := 5419) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5419) (q := 5431) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5431 (p := 5431) (q := 5437) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


def dusartPrimeRows_3275_5436 : List DusartPrimeRow :=
  dusartPrimeRows_3275_5166 ++ dusartPrimeRows_5167_5436

theorem dusartPrimeRows_3275_5436_chain :
    DusartPrimeRowsChain 3275 5436 dusartPrimeRows_3275_5436 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_5166_chain dusartPrimeRows_5167_5436_chain

def dusartPrimeRows_5437_5710 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5437) (q := 5441) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5441) (q := 5443) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5443) (q := 5449) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5449) (q := 5471) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5471) (q := 5477) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5477) (q := 5479) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5479) (q := 5483) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5483) (q := 5501) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5501) (q := 5503) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5503) (q := 5507) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5507) (q := 5519) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5519) (q := 5521) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5521) (q := 5527) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5527) (q := 5531) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5531) (q := 5557) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5557) (q := 5563) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5563) (q := 5569) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5569) (q := 5573) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5573) (q := 5581) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5581) (q := 5591) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5591) (q := 5623) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5623) (q := 5639) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5639) (q := 5641) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5641) (q := 5647) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5647) (q := 5651) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5651) (q := 5653) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5653) (q := 5657) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5657) (q := 5659) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5659) (q := 5669) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5669) (q := 5683) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5683) (q := 5689) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5689) (q := 5693) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5693) (q := 5701) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5701) (q := 5711) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

theorem dusartPrimeRows_5437_5710_chain :
    DusartPrimeRowsChain 5437 5710 dusartPrimeRows_5437_5710 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5437) (q := 5441) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5441) (q := 5443) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5443) (q := 5449) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5449) (q := 5471) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5471) (q := 5477) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5477) (q := 5479) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5479) (q := 5483) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5483) (q := 5501) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5501) (q := 5503) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5503) (q := 5507) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5507) (q := 5519) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5519) (q := 5521) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5521) (q := 5527) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5527) (q := 5531) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5531) (q := 5557) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5557) (q := 5563) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5563) (q := 5569) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5569) (q := 5573) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5573) (q := 5581) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5581) (q := 5591) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5591) (q := 5623) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5623) (q := 5639) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5639) (q := 5641) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5641) (q := 5647) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5647) (q := 5651) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5651) (q := 5653) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5653) (q := 5657) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5657) (q := 5659) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5659) (q := 5669) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5669) (q := 5683) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5683) (q := 5689) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5689) (q := 5693) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5693) (q := 5701) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_5710 (p := 5701) (q := 5711) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


def dusartPrimeRows_3275_5710 : List DusartPrimeRow :=
  dusartPrimeRows_3275_5436 ++ dusartPrimeRows_5437_5710

theorem dusartPrimeRows_3275_5710_chain :
    DusartPrimeRowsChain 3275 5710 dusartPrimeRows_3275_5710 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_5436_chain dusartPrimeRows_5437_5710_chain

def dusartPrimeRows_5711_6006 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6002 (p := 5711) (q := 5717) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5717) (q := 5737) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5737) (q := 5741) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5741) (q := 5743) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5743) (q := 5749) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5749) (q := 5779) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5779) (q := 5783) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5783) (q := 5791) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5791) (q := 5801) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5801) (q := 5807) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5807) (q := 5813) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5813) (q := 5821) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5821) (q := 5827) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5827) (q := 5839) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5839) (q := 5843) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5843) (q := 5849) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5849) (q := 5851) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5851) (q := 5857) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5857) (q := 5861) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5861) (q := 5867) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5867) (q := 5869) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5869) (q := 5879) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5879) (q := 5881) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5881) (q := 5897) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5897) (q := 5903) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5903) (q := 5923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5923) (q := 5927) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5927) (q := 5939) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5939) (q := 5953) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5953) (q := 5981) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5981) (q := 5987) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5987) (q := 6007) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

theorem dusartPrimeRows_5711_6006_chain :
    DusartPrimeRowsChain 5711 6006 dusartPrimeRows_5711_6006 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5711) (q := 5717) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5717) (q := 5737) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5737) (q := 5741) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5741) (q := 5743) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5743) (q := 5749) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5749) (q := 5779) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5779) (q := 5783) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5783) (q := 5791) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5791) (q := 5801) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5801) (q := 5807) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5807) (q := 5813) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5813) (q := 5821) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5821) (q := 5827) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5827) (q := 5839) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5839) (q := 5843) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5843) (q := 5849) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5849) (q := 5851) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5851) (q := 5857) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5857) (q := 5861) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5861) (q := 5867) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5867) (q := 5869) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5869) (q := 5879) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5879) (q := 5881) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5881) (q := 5897) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5897) (q := 5903) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5903) (q := 5923) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5923) (q := 5927) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5927) (q := 5939) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5939) (q := 5953) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5953) (q := 5981) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5981) (q := 5987) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5987) (q := 6007) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


def dusartPrimeRows_3275_6006 : List DusartPrimeRow :=
  dusartPrimeRows_3275_5710 ++ dusartPrimeRows_5711_6006

theorem dusartPrimeRows_3275_6006_chain :
    DusartPrimeRowsChain 3275 6006 dusartPrimeRows_3275_6006 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_5710_chain dusartPrimeRows_5711_6006_chain

def dusartPrimeRows_6007_6310 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6310 (p := 6007) (q := 6011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6011) (q := 6029) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6029) (q := 6037) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6037) (q := 6043) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6043) (q := 6047) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6047) (q := 6053) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6053) (q := 6067) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6067) (q := 6073) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6073) (q := 6079) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6079) (q := 6089) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6089) (q := 6091) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6091) (q := 6101) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6101) (q := 6113) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6113) (q := 6121) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6121) (q := 6131) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6131) (q := 6133) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6133) (q := 6143) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6143) (q := 6151) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6151) (q := 6163) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6163) (q := 6173) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6173) (q := 6197) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6197) (q := 6199) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6199) (q := 6203) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6203) (q := 6211) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6211) (q := 6217) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6217) (q := 6221) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6221) (q := 6229) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6229) (q := 6247) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6247) (q := 6257) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6257) (q := 6263) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6263) (q := 6269) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6269) (q := 6271) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6271) (q := 6277) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6277) (q := 6287) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6287) (q := 6299) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6299) (q := 6301) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6301) (q := 6311) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

theorem dusartPrimeRows_6007_6310_chain :
    DusartPrimeRowsChain 6007 6310 dusartPrimeRows_6007_6310 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6007) (q := 6011) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6011) (q := 6029) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6029) (q := 6037) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6037) (q := 6043) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6043) (q := 6047) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6047) (q := 6053) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6053) (q := 6067) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6067) (q := 6073) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6073) (q := 6079) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6079) (q := 6089) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6089) (q := 6091) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6091) (q := 6101) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6101) (q := 6113) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6113) (q := 6121) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6121) (q := 6131) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6131) (q := 6133) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6133) (q := 6143) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6143) (q := 6151) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6151) (q := 6163) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6163) (q := 6173) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6173) (q := 6197) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6197) (q := 6199) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6199) (q := 6203) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6203) (q := 6211) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6211) (q := 6217) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6217) (q := 6221) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6221) (q := 6229) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6229) (q := 6247) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6247) (q := 6257) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6257) (q := 6263) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6263) (q := 6269) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6269) (q := 6271) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6271) (q := 6277) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6277) (q := 6287) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6287) (q := 6299) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6299) (q := 6301) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6301) (q := 6311) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


def dusartPrimeRows_3275_6310 : List DusartPrimeRow :=
  dusartPrimeRows_3275_6006 ++ dusartPrimeRows_6007_6310

theorem dusartPrimeRows_3275_6310_chain :
    DusartPrimeRowsChain 3275 6310 dusartPrimeRows_3275_6310 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_6006_chain dusartPrimeRows_6007_6310_chain

def dusartPrimeRows_6311_6636 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6634 (p := 6311) (q := 6317) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6317) (q := 6323) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6323) (q := 6329) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6329) (q := 6337) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6337) (q := 6343) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6343) (q := 6353) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6353) (q := 6359) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6359) (q := 6361) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6361) (q := 6367) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6367) (q := 6373) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6373) (q := 6379) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6379) (q := 6389) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6389) (q := 6397) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6397) (q := 6421) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6421) (q := 6427) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6427) (q := 6449) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6449) (q := 6451) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6451) (q := 6469) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6469) (q := 6473) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6473) (q := 6481) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6481) (q := 6491) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6491) (q := 6521) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6521) (q := 6529) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6529) (q := 6547) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6547) (q := 6551) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6551) (q := 6553) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6553) (q := 6563) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6563) (q := 6569) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6569) (q := 6571) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6571) (q := 6577) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6577) (q := 6581) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6581) (q := 6599) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6599) (q := 6607) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6607) (q := 6619) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6619) (q := 6637) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

theorem dusartPrimeRows_6311_6636_chain :
    DusartPrimeRowsChain 6311 6636 dusartPrimeRows_6311_6636 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6311) (q := 6317) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6317) (q := 6323) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6323) (q := 6329) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6329) (q := 6337) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6337) (q := 6343) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6343) (q := 6353) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6353) (q := 6359) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6359) (q := 6361) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6361) (q := 6367) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6367) (q := 6373) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6373) (q := 6379) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6379) (q := 6389) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6389) (q := 6397) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6397) (q := 6421) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6421) (q := 6427) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6427) (q := 6449) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6449) (q := 6451) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6451) (q := 6469) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6469) (q := 6473) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6473) (q := 6481) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6481) (q := 6491) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6491) (q := 6521) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6521) (q := 6529) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6529) (q := 6547) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6547) (q := 6551) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6551) (q := 6553) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6553) (q := 6563) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6563) (q := 6569) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6569) (q := 6571) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6571) (q := 6577) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6577) (q := 6581) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6581) (q := 6599) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6599) (q := 6607) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6607) (q := 6619) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6619) (q := 6637) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


def dusartPrimeRows_3275_6636 : List DusartPrimeRow :=
  dusartPrimeRows_3275_6310 ++ dusartPrimeRows_6311_6636

theorem dusartPrimeRows_3275_6636_chain :
    DusartPrimeRowsChain 3275 6636 dusartPrimeRows_3275_6636 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_6310_chain dusartPrimeRows_6311_6636_chain

def dusartPrimeRows_6637_6976 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6637) (q := 6653) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6653) (q := 6659) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6659) (q := 6661) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6661) (q := 6673) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6673) (q := 6679) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6679) (q := 6689) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6689) (q := 6691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6691) (q := 6701) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6701) (q := 6703) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6703) (q := 6709) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6709) (q := 6719) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6719) (q := 6733) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6733) (q := 6737) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6737) (q := 6761) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6761) (q := 6763) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6763) (q := 6779) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6779) (q := 6781) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6781) (q := 6791) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6791) (q := 6793) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6793) (q := 6803) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6803) (q := 6823) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6823) (q := 6827) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6827) (q := 6829) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6829) (q := 6833) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6833) (q := 6841) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6841) (q := 6857) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6857) (q := 6863) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6863) (q := 6869) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6869) (q := 6871) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6871) (q := 6883) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6883) (q := 6899) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6899) (q := 6907) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6907) (q := 6911) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6911) (q := 6917) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6917) (q := 6947) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6947) (q := 6949) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6949) (q := 6959) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6959) (q := 6961) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6961) (q := 6967) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6967) (q := 6971) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6971) (q := 6977) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

theorem dusartPrimeRows_6637_6976_chain :
    DusartPrimeRowsChain 6637 6976 dusartPrimeRows_6637_6976 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6637) (q := 6653) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6653) (q := 6659) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6659) (q := 6661) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6661) (q := 6673) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6673) (q := 6679) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6679) (q := 6689) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6689) (q := 6691) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6691) (q := 6701) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6701) (q := 6703) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6703) (q := 6709) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6709) (q := 6719) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6719) (q := 6733) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6733) (q := 6737) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6737) (q := 6761) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6761) (q := 6763) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6763) (q := 6779) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6779) (q := 6781) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6781) (q := 6791) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6791) (q := 6793) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6793) (q := 6803) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6803) (q := 6823) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6823) (q := 6827) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6827) (q := 6829) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6829) (q := 6833) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6833) (q := 6841) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6841) (q := 6857) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6857) (q := 6863) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6863) (q := 6869) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6869) (q := 6871) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6871) (q := 6883) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6883) (q := 6899) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6899) (q := 6907) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6907) (q := 6911) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6911) (q := 6917) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6917) (q := 6947) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6947) (q := 6949) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6949) (q := 6959) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6959) (q := 6961) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6961) (q := 6967) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6967) (q := 6971) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6971) (q := 6977) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


def dusartPrimeRows_3275_6976 : List DusartPrimeRow :=
  dusartPrimeRows_3275_6636 ++ dusartPrimeRows_6637_6976

theorem dusartPrimeRows_3275_6976_chain :
    DusartPrimeRowsChain 3275 6976 dusartPrimeRows_3275_6976 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_6636_chain dusartPrimeRows_6637_6976_chain

def dusartPrimeRows_6977_7332 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 6977) (q := 6983) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6983) (q := 6991) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6991) (q := 6997) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6997) (q := 7001) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7001) (q := 7013) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7013) (q := 7019) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7019) (q := 7027) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7027) (q := 7039) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7039) (q := 7043) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7043) (q := 7057) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7057) (q := 7069) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7069) (q := 7079) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7079) (q := 7103) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7103) (q := 7109) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7109) (q := 7121) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7121) (q := 7127) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7127) (q := 7129) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7129) (q := 7151) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7151) (q := 7159) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7159) (q := 7177) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7177) (q := 7187) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7187) (q := 7193) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7193) (q := 7207) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7207) (q := 7211) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7211) (q := 7213) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7213) (q := 7219) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7219) (q := 7229) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7229) (q := 7237) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7237) (q := 7243) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7243) (q := 7247) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7247) (q := 7253) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7253) (q := 7283) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7283) (q := 7297) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7297) (q := 7307) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7307) (q := 7309) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7309) (q := 7321) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7321) (q := 7331) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7331) (q := 7333) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

theorem dusartPrimeRows_6977_7332_chain :
    DusartPrimeRowsChain 6977 7332 dusartPrimeRows_6977_7332 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 6977) (q := 6983) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 6983) (q := 6991) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 6991) (q := 6997) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 6997) (q := 7001) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7001) (q := 7013) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7013) (q := 7019) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7019) (q := 7027) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7027) (q := 7039) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7039) (q := 7043) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7043) (q := 7057) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7057) (q := 7069) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7069) (q := 7079) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7079) (q := 7103) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7103) (q := 7109) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7109) (q := 7121) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7121) (q := 7127) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7127) (q := 7129) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7129) (q := 7151) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7151) (q := 7159) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7159) (q := 7177) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7177) (q := 7187) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7187) (q := 7193) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7193) (q := 7207) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7207) (q := 7211) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7211) (q := 7213) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7213) (q := 7219) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7219) (q := 7229) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7229) (q := 7237) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7237) (q := 7243) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7243) (q := 7247) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7247) (q := 7253) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7253) (q := 7283) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7283) (q := 7297) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7297) (q := 7307) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7307) (q := 7309) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7309) (q := 7321) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7321) (q := 7331) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7331) (q := 7333) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


def dusartPrimeRows_3275_7332 : List DusartPrimeRow :=
  dusartPrimeRows_3275_6976 ++ dusartPrimeRows_6977_7332

theorem dusartPrimeRows_3275_7332_chain :
    DusartPrimeRowsChain 3275 7332 dusartPrimeRows_3275_7332 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_6976_chain dusartPrimeRows_6977_7332_chain

def dusartPrimeRows_7333_7716 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7333) (q := 7349) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7349) (q := 7351) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7351) (q := 7369) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7369) (q := 7393) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7393) (q := 7411) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7411) (q := 7417) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7417) (q := 7433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7433) (q := 7451) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7451) (q := 7457) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7457) (q := 7459) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7459) (q := 7477) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7477) (q := 7481) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7481) (q := 7487) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7487) (q := 7489) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7489) (q := 7499) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7499) (q := 7507) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7507) (q := 7517) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7517) (q := 7523) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7523) (q := 7529) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7529) (q := 7537) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7537) (q := 7541) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7541) (q := 7547) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7547) (q := 7549) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7549) (q := 7559) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7559) (q := 7561) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7561) (q := 7573) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7573) (q := 7577) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7577) (q := 7583) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7583) (q := 7589) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7589) (q := 7591) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7591) (q := 7603) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7603) (q := 7607) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7607) (q := 7621) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7621) (q := 7639) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7639) (q := 7643) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7643) (q := 7649) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7649) (q := 7669) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7669) (q := 7673) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7673) (q := 7681) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7681) (q := 7687) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7687) (q := 7691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7691) (q := 7699) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7699) (q := 7703) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7703) (q := 7717) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

theorem dusartPrimeRows_7333_7716_chain :
    DusartPrimeRowsChain 7333 7716 dusartPrimeRows_7333_7716 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7333) (q := 7349) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7349) (q := 7351) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7351) (q := 7369) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7369) (q := 7393) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7393) (q := 7411) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7411) (q := 7417) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7417) (q := 7433) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7433) (q := 7451) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7451) (q := 7457) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7457) (q := 7459) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7459) (q := 7477) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7477) (q := 7481) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7481) (q := 7487) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7487) (q := 7489) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7489) (q := 7499) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7499) (q := 7507) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7507) (q := 7517) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7517) (q := 7523) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7523) (q := 7529) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7529) (q := 7537) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7537) (q := 7541) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7541) (q := 7547) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7547) (q := 7549) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7549) (q := 7559) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7559) (q := 7561) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7561) (q := 7573) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7573) (q := 7577) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7577) (q := 7583) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7583) (q := 7589) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7589) (q := 7591) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7591) (q := 7603) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7603) (q := 7607) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7607) (q := 7621) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7621) (q := 7639) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7639) (q := 7643) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7643) (q := 7649) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7649) (q := 7669) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7669) (q := 7673) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7673) (q := 7681) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7681) (q := 7687) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7687) (q := 7691) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7691) (q := 7699) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7699) (q := 7703) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7703) (q := 7717) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


def dusartPrimeRows_3275_7716 : List DusartPrimeRow :=
  dusartPrimeRows_3275_7332 ++ dusartPrimeRows_7333_7716

theorem dusartPrimeRows_3275_7716_chain :
    DusartPrimeRowsChain 3275 7716 dusartPrimeRows_3275_7716 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_7332_chain dusartPrimeRows_7333_7716_chain

def dusartPrimeRows_7717_8110 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 7717) (q := 7723) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7723) (q := 7727) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7727) (q := 7741) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7741) (q := 7753) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7753) (q := 7757) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7757) (q := 7759) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7759) (q := 7789) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7789) (q := 7793) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7793) (q := 7817) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7817) (q := 7823) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7823) (q := 7829) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7829) (q := 7841) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7841) (q := 7853) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7853) (q := 7867) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7867) (q := 7873) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7873) (q := 7877) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7877) (q := 7879) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7879) (q := 7883) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7883) (q := 7901) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7901) (q := 7907) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7907) (q := 7919) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7919) (q := 7927) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7927) (q := 7933) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7933) (q := 7937) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7937) (q := 7949) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7949) (q := 7951) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7951) (q := 7963) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7963) (q := 7993) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7993) (q := 8009) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8009) (q := 8011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8011) (q := 8017) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8017) (q := 8039) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8039) (q := 8053) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8053) (q := 8059) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8059) (q := 8069) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8069) (q := 8081) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8081) (q := 8087) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8087) (q := 8089) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8089) (q := 8093) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8093) (q := 8101) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8101) (q := 8111) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

theorem dusartPrimeRows_7717_8110_chain :
    DusartPrimeRowsChain 7717 8110 dusartPrimeRows_7717_8110 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7717) (q := 7723) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7723) (q := 7727) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7727) (q := 7741) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7741) (q := 7753) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7753) (q := 7757) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7757) (q := 7759) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7759) (q := 7789) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7789) (q := 7793) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7793) (q := 7817) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7817) (q := 7823) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7823) (q := 7829) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7829) (q := 7841) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7841) (q := 7853) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7853) (q := 7867) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7867) (q := 7873) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7873) (q := 7877) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7877) (q := 7879) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7879) (q := 7883) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7883) (q := 7901) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7901) (q := 7907) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7907) (q := 7919) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7919) (q := 7927) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7927) (q := 7933) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7933) (q := 7937) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7937) (q := 7949) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7949) (q := 7951) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7951) (q := 7963) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7963) (q := 7993) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7993) (q := 8009) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8009) (q := 8011) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8011) (q := 8017) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8017) (q := 8039) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8039) (q := 8053) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8053) (q := 8059) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8059) (q := 8069) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8069) (q := 8081) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8081) (q := 8087) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8087) (q := 8089) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8089) (q := 8093) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8093) (q := 8101) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8101) (q := 8111) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


def dusartPrimeRows_3275_8110 : List DusartPrimeRow :=
  dusartPrimeRows_3275_7716 ++ dusartPrimeRows_7717_8110

theorem dusartPrimeRows_3275_8110_chain :
    DusartPrimeRowsChain 3275 8110 dusartPrimeRows_3275_8110 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_7716_chain dusartPrimeRows_7717_8110_chain

def dusartPrimeRows_8111_8520 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8111) (q := 8117) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8117) (q := 8123) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8123) (q := 8147) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8147) (q := 8161) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8161) (q := 8167) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8167) (q := 8171) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8171) (q := 8179) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8179) (q := 8191) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8191) (q := 8209) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8209) (q := 8219) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8219) (q := 8221) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8221) (q := 8231) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8231) (q := 8233) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8233) (q := 8237) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8237) (q := 8243) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8243) (q := 8263) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8263) (q := 8269) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8269) (q := 8273) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8273) (q := 8287) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8287) (q := 8291) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8291) (q := 8293) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8293) (q := 8297) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8297) (q := 8311) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8311) (q := 8317) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8317) (q := 8329) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8329) (q := 8353) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8353) (q := 8363) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8363) (q := 8369) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8369) (q := 8377) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8377) (q := 8387) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8387) (q := 8389) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8389) (q := 8419) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8419) (q := 8423) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8423) (q := 8429) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8429) (q := 8431) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8431) (q := 8443) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8443) (q := 8447) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8447) (q := 8461) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8461) (q := 8467) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8467) (q := 8501) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8501) (q := 8513) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8513) (q := 8521) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

theorem dusartPrimeRows_8111_8520_chain :
    DusartPrimeRowsChain 8111 8520 dusartPrimeRows_8111_8520 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8111) (q := 8117) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8117) (q := 8123) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8123) (q := 8147) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8147) (q := 8161) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8161) (q := 8167) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8167) (q := 8171) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8171) (q := 8179) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8179) (q := 8191) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8191) (q := 8209) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8209) (q := 8219) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8219) (q := 8221) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8221) (q := 8231) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8231) (q := 8233) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8233) (q := 8237) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8237) (q := 8243) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8243) (q := 8263) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8263) (q := 8269) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8269) (q := 8273) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8273) (q := 8287) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8287) (q := 8291) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8291) (q := 8293) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8293) (q := 8297) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8297) (q := 8311) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8311) (q := 8317) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8317) (q := 8329) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8329) (q := 8353) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8353) (q := 8363) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8363) (q := 8369) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8369) (q := 8377) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8377) (q := 8387) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8387) (q := 8389) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8389) (q := 8419) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8419) (q := 8423) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8423) (q := 8429) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8429) (q := 8431) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8431) (q := 8443) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8443) (q := 8447) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8447) (q := 8461) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8461) (q := 8467) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8467) (q := 8501) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8501) (q := 8513) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8513) (q := 8521) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


def dusartPrimeRows_3275_8520 : List DusartPrimeRow :=
  dusartPrimeRows_3275_8110 ++ dusartPrimeRows_8111_8520

theorem dusartPrimeRows_3275_8520_chain :
    DusartPrimeRowsChain 3275 8520 dusartPrimeRows_3275_8520 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_8110_chain dusartPrimeRows_8111_8520_chain

def dusartPrimeRows_8521_8962 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8521) (q := 8527) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8527) (q := 8537) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8537) (q := 8539) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8539) (q := 8543) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8543) (q := 8563) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8563) (q := 8573) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8573) (q := 8581) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8581) (q := 8597) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8597) (q := 8599) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8599) (q := 8609) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8609) (q := 8623) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8623) (q := 8627) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8627) (q := 8629) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8629) (q := 8641) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8641) (q := 8647) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8647) (q := 8663) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8663) (q := 8669) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8669) (q := 8677) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8677) (q := 8681) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8681) (q := 8689) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8689) (q := 8693) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8693) (q := 8699) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8699) (q := 8707) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8707) (q := 8713) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8713) (q := 8719) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8719) (q := 8731) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8731) (q := 8737) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8737) (q := 8741) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8741) (q := 8747) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8747) (q := 8753) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8753) (q := 8761) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8761) (q := 8779) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8779) (q := 8783) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8783) (q := 8803) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8803) (q := 8807) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8807) (q := 8819) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8819) (q := 8821) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8821) (q := 8831) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8831) (q := 8837) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8837) (q := 8839) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8839) (q := 8849) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8849) (q := 8861) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8861) (q := 8863) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8863) (q := 8867) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8867) (q := 8887) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8887) (q := 8893) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8893) (q := 8923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8923) (q := 8929) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8929) (q := 8933) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8933) (q := 8941) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8941) (q := 8951) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8951) (q := 8963) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

theorem dusartPrimeRows_8521_8962_chain :
    DusartPrimeRowsChain 8521 8962 dusartPrimeRows_8521_8962 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8521) (q := 8527) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8527) (q := 8537) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8537) (q := 8539) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8539) (q := 8543) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8543) (q := 8563) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8563) (q := 8573) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8573) (q := 8581) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8581) (q := 8597) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8597) (q := 8599) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8599) (q := 8609) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8609) (q := 8623) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8623) (q := 8627) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8627) (q := 8629) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8629) (q := 8641) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8641) (q := 8647) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8647) (q := 8663) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8663) (q := 8669) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8669) (q := 8677) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8677) (q := 8681) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8681) (q := 8689) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8689) (q := 8693) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8693) (q := 8699) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8699) (q := 8707) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8707) (q := 8713) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8713) (q := 8719) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8719) (q := 8731) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8731) (q := 8737) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8737) (q := 8741) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8741) (q := 8747) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8747) (q := 8753) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8753) (q := 8761) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8761) (q := 8779) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8779) (q := 8783) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8783) (q := 8803) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8803) (q := 8807) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8807) (q := 8819) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8819) (q := 8821) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8821) (q := 8831) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8831) (q := 8837) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8837) (q := 8839) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8839) (q := 8849) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8849) (q := 8861) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8861) (q := 8863) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8863) (q := 8867) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8867) (q := 8887) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8887) (q := 8893) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8893) (q := 8923) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8923) (q := 8929) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8929) (q := 8933) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8933) (q := 8941) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8941) (q := 8951) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8951) (q := 8963) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


def dusartPrimeRows_3275_8962 : List DusartPrimeRow :=
  dusartPrimeRows_3275_8520 ++ dusartPrimeRows_8521_8962

theorem dusartPrimeRows_3275_8962_chain :
    DusartPrimeRowsChain 3275 8962 dusartPrimeRows_3275_8962 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_8520_chain dusartPrimeRows_8521_8962_chain

def dusartPrimeRows_8963_9418 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 8963) (q := 8969) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 8969) (q := 8971) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 8971) (q := 8999) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 8999) (q := 9001) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9001) (q := 9007) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9007) (q := 9011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9011) (q := 9013) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9013) (q := 9029) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9029) (q := 9041) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9041) (q := 9043) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9043) (q := 9049) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9049) (q := 9059) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9059) (q := 9067) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9067) (q := 9091) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9091) (q := 9103) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9103) (q := 9109) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9109) (q := 9127) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9127) (q := 9133) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9133) (q := 9137) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9137) (q := 9151) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9151) (q := 9157) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9157) (q := 9161) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9161) (q := 9173) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9173) (q := 9181) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9181) (q := 9187) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9187) (q := 9199) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9199) (q := 9203) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9203) (q := 9209) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9209) (q := 9221) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9221) (q := 9227) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9227) (q := 9239) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9239) (q := 9241) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9241) (q := 9257) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9257) (q := 9277) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9277) (q := 9281) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9281) (q := 9283) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9283) (q := 9293) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9293) (q := 9311) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9311) (q := 9319) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9319) (q := 9323) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9323) (q := 9337) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9337) (q := 9341) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9341) (q := 9343) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9343) (q := 9349) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9349) (q := 9371) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9371) (q := 9377) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9377) (q := 9391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9391) (q := 9397) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9397) (q := 9403) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9403) (q := 9413) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9413) (q := 9419) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

theorem dusartPrimeRows_8963_9418_chain :
    DusartPrimeRowsChain 8963 9418 dusartPrimeRows_8963_9418 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 8963) (q := 8969) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 8969) (q := 8971) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 8971) (q := 8999) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 8999) (q := 9001) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9001) (q := 9007) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9007) (q := 9011) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9011) (q := 9013) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9013) (q := 9029) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9029) (q := 9041) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9041) (q := 9043) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9043) (q := 9049) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9049) (q := 9059) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9059) (q := 9067) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9067) (q := 9091) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9091) (q := 9103) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9103) (q := 9109) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9109) (q := 9127) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9127) (q := 9133) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9133) (q := 9137) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9137) (q := 9151) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9151) (q := 9157) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9157) (q := 9161) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9161) (q := 9173) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9173) (q := 9181) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9181) (q := 9187) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9187) (q := 9199) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9199) (q := 9203) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9203) (q := 9209) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9209) (q := 9221) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9221) (q := 9227) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9227) (q := 9239) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9239) (q := 9241) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9241) (q := 9257) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9257) (q := 9277) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9277) (q := 9281) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9281) (q := 9283) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9283) (q := 9293) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9293) (q := 9311) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9311) (q := 9319) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9319) (q := 9323) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9323) (q := 9337) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9337) (q := 9341) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9341) (q := 9343) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9343) (q := 9349) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9349) (q := 9371) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9371) (q := 9377) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9377) (q := 9391) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9391) (q := 9397) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9397) (q := 9403) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9403) (q := 9413) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9413) (q := 9419) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


def dusartPrimeRows_3275_9418 : List DusartPrimeRow :=
  dusartPrimeRows_3275_8962 ++ dusartPrimeRows_8963_9418

theorem dusartPrimeRows_3275_9418_chain :
    DusartPrimeRowsChain 3275 9418 dusartPrimeRows_3275_9418 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_8962_chain dusartPrimeRows_8963_9418_chain

def dusartPrimeRows_9419_9900 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9419) (q := 9421) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9421) (q := 9431) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9431) (q := 9433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9433) (q := 9437) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9437) (q := 9439) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9439) (q := 9461) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9461) (q := 9463) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9463) (q := 9467) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9467) (q := 9473) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9473) (q := 9479) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9479) (q := 9491) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9491) (q := 9497) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9497) (q := 9511) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9511) (q := 9521) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9521) (q := 9533) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9533) (q := 9539) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9539) (q := 9547) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9547) (q := 9551) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9551) (q := 9587) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9587) (q := 9601) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9601) (q := 9613) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9613) (q := 9619) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9619) (q := 9623) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9623) (q := 9629) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9629) (q := 9631) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9631) (q := 9643) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9643) (q := 9649) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9649) (q := 9661) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9661) (q := 9677) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9677) (q := 9679) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9679) (q := 9689) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9689) (q := 9697) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9697) (q := 9719) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9719) (q := 9721) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9721) (q := 9733) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9733) (q := 9739) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9739) (q := 9743) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9743) (q := 9749) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9749) (q := 9767) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9767) (q := 9769) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9769) (q := 9781) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9781) (q := 9787) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9787) (q := 9791) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9791) (q := 9803) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9803) (q := 9811) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9811) (q := 9817) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9817) (q := 9829) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9829) (q := 9833) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9833) (q := 9839) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9839) (q := 9851) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9851) (q := 9857) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9857) (q := 9859) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9859) (q := 9871) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9871) (q := 9883) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9883) (q := 9887) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9887) (q := 9901) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

theorem dusartPrimeRows_9419_9900_chain :
    DusartPrimeRowsChain 9419 9900 dusartPrimeRows_9419_9900 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9419) (q := 9421) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9421) (q := 9431) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9431) (q := 9433) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9433) (q := 9437) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9437) (q := 9439) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9439) (q := 9461) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9461) (q := 9463) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9463) (q := 9467) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9467) (q := 9473) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9473) (q := 9479) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9479) (q := 9491) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9491) (q := 9497) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9497) (q := 9511) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9511) (q := 9521) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9521) (q := 9533) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9533) (q := 9539) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9539) (q := 9547) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9547) (q := 9551) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9551) (q := 9587) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9587) (q := 9601) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9601) (q := 9613) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9613) (q := 9619) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9619) (q := 9623) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9623) (q := 9629) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9629) (q := 9631) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9631) (q := 9643) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9643) (q := 9649) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9649) (q := 9661) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9661) (q := 9677) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9677) (q := 9679) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9679) (q := 9689) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9689) (q := 9697) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9697) (q := 9719) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9719) (q := 9721) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9721) (q := 9733) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9733) (q := 9739) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9739) (q := 9743) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9743) (q := 9749) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9749) (q := 9767) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9767) (q := 9769) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9769) (q := 9781) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9781) (q := 9787) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9787) (q := 9791) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9791) (q := 9803) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9803) (q := 9811) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9811) (q := 9817) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9817) (q := 9829) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9829) (q := 9833) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9833) (q := 9839) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9839) (q := 9851) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9851) (q := 9857) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9857) (q := 9859) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9859) (q := 9871) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9871) (q := 9883) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9883) (q := 9887) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9887) (q := 9901) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


def dusartPrimeRows_3275_9900 : List DusartPrimeRow :=
  dusartPrimeRows_3275_9418 ++ dusartPrimeRows_9419_9900

theorem dusartPrimeRows_3275_9900_chain :
    DusartPrimeRowsChain 3275 9900 dusartPrimeRows_3275_9900 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_9418_chain dusartPrimeRows_9419_9900_chain

def dusartPrimeRows_9901_10426 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 9901) (q := 9907) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9907) (q := 9923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9923) (q := 9929) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9929) (q := 9931) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9931) (q := 9941) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9941) (q := 9949) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9949) (q := 9967) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9967) (q := 9973) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9973) (q := 10007) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10007) (q := 10009) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10009) (q := 10037) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10037) (q := 10039) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10039) (q := 10061) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10061) (q := 10067) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10067) (q := 10069) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10069) (q := 10079) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10079) (q := 10091) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10091) (q := 10093) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10093) (q := 10099) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10099) (q := 10103) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10103) (q := 10111) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10111) (q := 10133) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10133) (q := 10139) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10139) (q := 10141) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10141) (q := 10151) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10151) (q := 10159) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10159) (q := 10163) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10163) (q := 10169) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10169) (q := 10177) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10177) (q := 10181) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10181) (q := 10193) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10193) (q := 10211) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10211) (q := 10223) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10223) (q := 10243) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10243) (q := 10247) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10247) (q := 10253) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10253) (q := 10259) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10259) (q := 10267) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10267) (q := 10271) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10271) (q := 10273) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10273) (q := 10289) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10289) (q := 10301) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10301) (q := 10303) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10303) (q := 10313) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10313) (q := 10321) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10321) (q := 10331) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10331) (q := 10333) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10333) (q := 10337) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10337) (q := 10343) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10343) (q := 10357) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10357) (q := 10369) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10369) (q := 10391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10391) (q := 10399) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10399) (q := 10427) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

theorem dusartPrimeRows_9901_10426_chain :
    DusartPrimeRowsChain 9901 10426 dusartPrimeRows_9901_10426 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 9901) (q := 9907) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 9907) (q := 9923) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 9923) (q := 9929) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 9929) (q := 9931) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 9931) (q := 9941) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 9941) (q := 9949) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 9949) (q := 9967) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 9967) (q := 9973) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 9973) (q := 10007) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10007) (q := 10009) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10009) (q := 10037) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10037) (q := 10039) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10039) (q := 10061) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10061) (q := 10067) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10067) (q := 10069) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10069) (q := 10079) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10079) (q := 10091) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10091) (q := 10093) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10093) (q := 10099) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10099) (q := 10103) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10103) (q := 10111) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10111) (q := 10133) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10133) (q := 10139) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10139) (q := 10141) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10141) (q := 10151) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10151) (q := 10159) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10159) (q := 10163) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10163) (q := 10169) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10169) (q := 10177) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10177) (q := 10181) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10181) (q := 10193) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10193) (q := 10211) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10211) (q := 10223) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10223) (q := 10243) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10243) (q := 10247) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10247) (q := 10253) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10253) (q := 10259) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10259) (q := 10267) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10267) (q := 10271) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10271) (q := 10273) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10273) (q := 10289) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10289) (q := 10301) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10301) (q := 10303) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10303) (q := 10313) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10313) (q := 10321) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10321) (q := 10331) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10331) (q := 10333) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10333) (q := 10337) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10337) (q := 10343) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10343) (q := 10357) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10357) (q := 10369) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10369) (q := 10391) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10391) (q := 10399) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10399) (q := 10427) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


def dusartPrimeRows_3275_10426 : List DusartPrimeRow :=
  dusartPrimeRows_3275_9900 ++ dusartPrimeRows_9901_10426

theorem dusartPrimeRows_3275_10426_chain :
    DusartPrimeRowsChain 3275 10426 dusartPrimeRows_3275_10426 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_9900_chain dusartPrimeRows_9901_10426_chain

def dusartPrimeRows_10427_10938 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10427) (q := 10429) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10429) (q := 10433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10433) (q := 10453) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10453) (q := 10457) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10457) (q := 10459) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10459) (q := 10463) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10463) (q := 10477) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10477) (q := 10487) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10487) (q := 10499) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10499) (q := 10501) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10501) (q := 10513) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10513) (q := 10529) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10529) (q := 10531) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10531) (q := 10559) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10559) (q := 10567) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10567) (q := 10589) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10589) (q := 10597) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10597) (q := 10601) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10601) (q := 10607) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10607) (q := 10613) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10613) (q := 10627) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10627) (q := 10631) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10631) (q := 10639) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10639) (q := 10651) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10651) (q := 10657) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10657) (q := 10663) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10663) (q := 10667) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10667) (q := 10687) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10687) (q := 10691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10691) (q := 10709) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10709) (q := 10711) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10711) (q := 10723) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10723) (q := 10729) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10729) (q := 10733) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10733) (q := 10739) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10739) (q := 10753) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10753) (q := 10771) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10771) (q := 10781) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10781) (q := 10789) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10789) (q := 10799) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10799) (q := 10831) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10831) (q := 10837) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10837) (q := 10847) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10847) (q := 10853) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10853) (q := 10859) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10859) (q := 10861) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10861) (q := 10867) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10867) (q := 10883) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10883) (q := 10889) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10889) (q := 10891) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10891) (q := 10903) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10903) (q := 10909) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10909) (q := 10937) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10937) (q := 10939) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

theorem dusartPrimeRows_10427_10938_chain :
    DusartPrimeRowsChain 10427 10938 dusartPrimeRows_10427_10938 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10427) (q := 10429) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10429) (q := 10433) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10433) (q := 10453) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10453) (q := 10457) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10457) (q := 10459) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10459) (q := 10463) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10463) (q := 10477) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10477) (q := 10487) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10487) (q := 10499) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10499) (q := 10501) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10501) (q := 10513) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10513) (q := 10529) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10529) (q := 10531) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10531) (q := 10559) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10559) (q := 10567) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10567) (q := 10589) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10589) (q := 10597) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10597) (q := 10601) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10601) (q := 10607) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10607) (q := 10613) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10613) (q := 10627) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10627) (q := 10631) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10631) (q := 10639) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10639) (q := 10651) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10651) (q := 10657) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10657) (q := 10663) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10663) (q := 10667) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10667) (q := 10687) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10687) (q := 10691) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10691) (q := 10709) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10709) (q := 10711) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10711) (q := 10723) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10723) (q := 10729) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10729) (q := 10733) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10733) (q := 10739) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10739) (q := 10753) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10753) (q := 10771) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10771) (q := 10781) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10781) (q := 10789) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10789) (q := 10799) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10799) (q := 10831) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10831) (q := 10837) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10837) (q := 10847) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10847) (q := 10853) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10853) (q := 10859) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10859) (q := 10861) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10861) (q := 10867) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10867) (q := 10883) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10883) (q := 10889) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10889) (q := 10891) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10891) (q := 10903) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10903) (q := 10909) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10909) (q := 10937) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10937) (q := 10939) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


def dusartPrimeRows_3275_10938 : List DusartPrimeRow :=
  dusartPrimeRows_3275_10426 ++ dusartPrimeRows_10427_10938

theorem dusartPrimeRows_3275_10938_chain :
    DusartPrimeRowsChain 3275 10938 dusartPrimeRows_3275_10938 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_10426_chain dusartPrimeRows_10427_10938_chain

def dusartPrimeRows_10939_11502 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 10939) (q := 10949) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10949) (q := 10957) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10957) (q := 10973) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10973) (q := 10979) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10979) (q := 10987) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10987) (q := 10993) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10993) (q := 11003) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11003) (q := 11027) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11027) (q := 11047) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11047) (q := 11057) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11057) (q := 11059) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11059) (q := 11069) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11069) (q := 11071) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11071) (q := 11083) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11083) (q := 11087) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11087) (q := 11093) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11093) (q := 11113) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11113) (q := 11117) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11117) (q := 11119) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11119) (q := 11131) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11131) (q := 11149) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11149) (q := 11159) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11159) (q := 11161) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11161) (q := 11171) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11171) (q := 11173) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11173) (q := 11177) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11177) (q := 11197) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11197) (q := 11213) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11213) (q := 11239) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11239) (q := 11243) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11243) (q := 11251) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11251) (q := 11257) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11257) (q := 11261) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11261) (q := 11273) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11273) (q := 11279) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11279) (q := 11287) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11287) (q := 11299) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11299) (q := 11311) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11311) (q := 11317) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11317) (q := 11321) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11321) (q := 11329) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11329) (q := 11351) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11351) (q := 11353) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11353) (q := 11369) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11369) (q := 11383) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11383) (q := 11393) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11393) (q := 11399) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11399) (q := 11411) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11411) (q := 11423) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11423) (q := 11437) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11437) (q := 11443) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11443) (q := 11447) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11447) (q := 11467) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11467) (q := 11471) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11471) (q := 11483) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11483) (q := 11489) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11489) (q := 11491) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11491) (q := 11497) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11497) (q := 11503) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

theorem dusartPrimeRows_10939_11502_chain :
    DusartPrimeRowsChain 10939 11502 dusartPrimeRows_10939_11502 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 10939) (q := 10949) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 10949) (q := 10957) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 10957) (q := 10973) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 10973) (q := 10979) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 10979) (q := 10987) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 10987) (q := 10993) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 10993) (q := 11003) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11003) (q := 11027) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11027) (q := 11047) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11047) (q := 11057) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11057) (q := 11059) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11059) (q := 11069) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11069) (q := 11071) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11071) (q := 11083) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11083) (q := 11087) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11087) (q := 11093) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11093) (q := 11113) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11113) (q := 11117) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11117) (q := 11119) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11119) (q := 11131) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11131) (q := 11149) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11149) (q := 11159) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11159) (q := 11161) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11161) (q := 11171) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11171) (q := 11173) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11173) (q := 11177) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11177) (q := 11197) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11197) (q := 11213) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11213) (q := 11239) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11239) (q := 11243) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11243) (q := 11251) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11251) (q := 11257) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11257) (q := 11261) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11261) (q := 11273) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11273) (q := 11279) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11279) (q := 11287) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11287) (q := 11299) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11299) (q := 11311) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11311) (q := 11317) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11317) (q := 11321) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11321) (q := 11329) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11329) (q := 11351) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11351) (q := 11353) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11353) (q := 11369) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11369) (q := 11383) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11383) (q := 11393) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11393) (q := 11399) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11399) (q := 11411) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11411) (q := 11423) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11423) (q := 11437) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11437) (q := 11443) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11443) (q := 11447) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11447) (q := 11467) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11467) (q := 11471) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11471) (q := 11483) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11483) (q := 11489) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11489) (q := 11491) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11491) (q := 11497) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11497) (q := 11503) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


def dusartPrimeRows_3275_11502 : List DusartPrimeRow :=
  dusartPrimeRows_3275_10938 ++ dusartPrimeRows_10939_11502

theorem dusartPrimeRows_3275_11502_chain :
    DusartPrimeRowsChain 3275 11502 dusartPrimeRows_3275_11502 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_10938_chain dusartPrimeRows_10939_11502_chain

def DusartPrimeRowsCoverBelow (rows : List DusartPrimeRow) : Prop :=
  ∀ x : Real, 3275 ≤ x → x ≤ 89693 →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

def DusartPrimeRowsCoverUpTo
    (rows : List DusartPrimeRow) (X : Real) : Prop :=
  ∀ x : Real, 3275 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem dusartPrimeRowsCoverUpTo_of_chain
    {b : Nat} {X : Real} {rows : List DusartPrimeRow}
    (chain : DusartPrimeRowsChain 3275 b rows)
    (hXbound : X ≤ (b : Real)) :
    DusartPrimeRowsCoverUpTo rows X := by
  intro x hx hX
  exact dusartPrimeRowsCover_of_chain chain x hx (hX.trans hXbound)

theorem dusartPrimeRows_3275_3802_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_3802 (3802 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_3802_chain (by norm_num)

theorem dusartPrimeRows_3275_4672_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_4672 (4672 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_4672_chain (by norm_num)

theorem dusartPrimeRows_3275_4918_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_4918 (4918 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_4918_chain (by norm_num)

theorem dusartPrimeRows_3275_5166_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_5166 (5166 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_5166_chain (by norm_num)

theorem dusartPrimeRows_3275_5436_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_5436 (5436 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_5436_chain (by norm_num)

theorem dusartPrimeRows_3275_5710_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_5710 (5710 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_5710_chain (by norm_num)

theorem dusartPrimeRows_3275_6006_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_6006 (6006 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_6006_chain (by norm_num)

theorem dusartPrimeRows_3275_6310_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_6310 (6310 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_6310_chain (by norm_num)

theorem dusartPrimeRows_3275_6636_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_6636 (6636 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_6636_chain (by norm_num)

theorem dusartPrimeRows_3275_6976_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_6976 (6976 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_6976_chain (by norm_num)

theorem dusartPrimeRows_3275_7332_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_7332 (7332 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_7332_chain (by norm_num)

theorem dusartPrimeRows_3275_7716_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_7716 (7716 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_7716_chain (by norm_num)

theorem dusartPrimeRows_3275_8110_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_8110 (8110 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_8110_chain (by norm_num)

theorem dusartPrimeRows_3275_8520_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_8520 (8520 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_8520_chain (by norm_num)

theorem dusartPrimeRows_3275_8962_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_8962 (8962 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_8962_chain (by norm_num)

theorem dusartPrimeRows_3275_9418_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_9418 (9418 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_9418_chain (by norm_num)

theorem dusartPrimeRows_3275_9900_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_9900 (9900 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_9900_chain (by norm_num)

theorem dusartPrimeRows_3275_10426_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_10426 (10426 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_10426_chain (by norm_num)

theorem dusartPrimeRows_3275_10938_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_10938 (10938 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_10938_chain (by norm_num)

theorem dusartPrimeRows_3275_11502_cover :
    DusartPrimeRowsCoverUpTo dusartPrimeRows_3275_11502 (11502 : Real) := by
  exact dusartPrimeRowsCoverUpTo_of_chain
    dusartPrimeRows_3275_11502_chain (by norm_num)

theorem dusartPrimeRowsCoverBelow_of_chain
    {rows : List DusartPrimeRow}
    (chain : DusartPrimeRowsChain 3275 89693 rows) :
    DusartPrimeRowsCoverBelow rows := by
  intro x hleft hright
  exact dusartPrimeRowsCover_of_chain chain x hleft hright

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

theorem hasDusartShortIntervalPrimeBelow_of_indexed_gap_log_rows
    {n : Nat} {X : Real}
    {rows : Fin n → FinitePrimeGapLogRow}
    (hX : (89693 : Real) ≤ X)
    (finitePrefix : HasDusartShortIntervalPrimeBelow (89693 : Real))
    (cover : FinitePrimeGapLogIndexedRowsCoverUpTo rows X) :
    HasDusartShortIntervalPrimeBelow X := by
  intro x hx hXx
  by_cases hsmall : x ≤ (89693 : Real)
  · exact finitePrefix x hx hsmall
  · have hlarge : (89693 : Real) ≤ x :=
      le_of_lt (lt_of_not_ge hsmall)
    obtain ⟨q, hq, hxq, hupper⟩ :=
      hasLogCubedShortIntervalPrimeBelow_of_indexed_gap_log_rows cover
        x hlarge hXx
    refine ⟨q, hq, hxq, ?_⟩
    exact dusartShortIntervalUpper_of_logCubed hlarge hupper

theorem hasDusartShortIntervalPrime_of_indexed_gap_log_rows_and_mediumPNT
    {n : Nat} {X : Real}
    {rows : Fin n → FinitePrimeGapLogRow}
    (hX : (89693 : Real) ≤ X)
    (finitePrefix : HasDusartShortIntervalPrimeBelow (89693 : Real))
    (cover : FinitePrimeGapLogIndexedRowsCoverUpTo rows X) :
    HasDusartShortIntervalPrime := by
  exact hasDusartShortIntervalPrime_of_finite_and_mediumPNT hX finitePrefix
    (hasLogCubedShortIntervalPrimeBelow_of_indexed_gap_log_rows cover)

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

theorem hasDusartShortIntervalPrime_of_finite_gap_log_rows_and_mediumPNT
    {X : Real} {rows : List FinitePrimeGapLogRow}
    (hX : (89693 : Real) ≤ X)
    (finitePrefix : HasDusartShortIntervalPrimeBelow (89693 : Real))
    (cover : FinitePrimeGapLogRowsCoverUpTo rows X) :
    HasDusartShortIntervalPrime := by
  exact hasDusartShortIntervalPrime_of_finite_and_mediumPNT hX finitePrefix
    (hasLogCubedShortIntervalPrimeBelow_of_finite_gap_log_rows cover)

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
