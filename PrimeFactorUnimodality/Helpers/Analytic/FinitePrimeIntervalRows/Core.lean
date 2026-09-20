import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCounting
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitThetaBounds
import PrimeFactorUnimodality.Helpers.Analytic.MediumPNT
import PrimeFactorUnimodality.Helpers.Analytic.ShortIntervalPrime
import PrimeFactorUnimodality.Helpers.Analytic.ThetaFromPsi

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Generic finite prime-interval rows and assemblers

This module contains only reusable row structures, interval covers, and their
analytic conversion lemmas.  Concrete endpoint data remains in the facade and
in later prefix modules.
-/

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

def finitePrimeGapRow_of_consecutive
    {g p q : Nat} (h : ConsecutivePrimes p q)
    (hgap : q ≤ p + g) : FinitePrimeGapRow g := by
  have hpq := h.left_lt_right
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
    ∀ x : Real, (a : Real) ≤ x → x < (b : Real) + 1 →
      ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x < (row.right : Real) + 1 := by
  induction chain with
  | @empty a b h =>
      intro x hax hxb
      have hab : (b : Real) < a := by exact_mod_cast h
      have hba : (b : Real) + 1 ≤ a := by
        exact_mod_cast (Nat.succ_le_of_lt h)
      linarith
  | @cons a b row hleft hordered tail htail ih =>
      intro x hax hxb
      by_cases hrow : x < (row.right : Real) + 1
      · refine ⟨row, by simp, ?_, hrow⟩
        have hleft' : (row.left : Real) ≤ a := by
          exact_mod_cast hleft
        exact hleft'.trans hax
      · have hright : ((row.right + 1 : Nat) : Real) ≤ x := by
          have hstep : (row.right : Real) + 1 ≤ x := le_of_not_gt hrow
          simpa using hstep
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
  have hwidth : (g : Real) ≤ logCubedWidth row.left := by
    have ha_pos : 0 < (row.left : Real) := by
      exact_mod_cast (show 0 < row.left by omega)
    have hlog_pos : 0 < Real.log row.left := by
      apply Real.log_pos
      exact_mod_cast (show (1 : Nat) < row.left by omega)
    have hpow : (Real.log row.left) ^ 3 ≤ L ^ 3 :=
      pow_le_pow_left₀ hlog_pos.le hlog 3
    have hbound : (g : Real) * (Real.log row.left) ^ 3 ≤ row.left := by
      exact (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg g)).trans hproduct
    apply (le_div_iff₀ (pow_pos hlog_pos 3)).2
    simpa [logCubedWidth] using hbound
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
    have hleft_witness : row.left ≤ row.witness :=
      row.left_le_right.trans (Nat.le_of_lt row.right_lt_witness)
    calc
      (row.witness : Real) - row.left =
          ((row.witness - row.left : Nat) : Real) := by
            rw [Nat.cast_sub hleft_witness]
      _ ≤ (g : Real) := by
        have hnat : row.witness - row.left ≤ g := by
          have hbound := row.witness_le_left_add_gap
          omega
        exact_mod_cast hnat
  exact hgap.trans hwidth

def finitePrimeGapLogRow_of_explicit
    {p q : Nat} {L : Real}
    (hq : q.Prime)
    (hpq : p < q)
    (hleft_large : 89693 ≤ p)
    (hlog : Real.log p ≤ L) (hL : 0 ≤ L)
    (hproduct : (q - p : Real) * L ^ 3 ≤ p) :
    FinitePrimeGapLogRow := by
  have hwidth : (q - p : Real) ≤ logCubedWidth p := by
    have hp_pos : 0 < (p : Real) := by
      exact_mod_cast (show 0 < p by omega)
    have hlog_pos : 0 < Real.log p := by
      apply Real.log_pos
      exact_mod_cast (show (1 : Nat) < p by omega)
    have hpow : (Real.log p) ^ 3 ≤ L ^ 3 :=
      pow_le_pow_left₀ hlog_pos.le hlog 3
    have hbound : (q - p : Real) * (Real.log p) ^ 3 ≤ p := by
      exact (mul_le_mul_of_nonneg_left hpow
        (sub_nonneg.mpr (by exact_mod_cast (Nat.le_of_lt hpq)))).trans hproduct
    apply (le_div_iff₀ (pow_pos hlog_pos 3)).2
    simpa [logCubedWidth] using hbound
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
    (cover : FinitePrimeGapRowsCover (a := a) (b := b) (g := g) rows) :
    FinitePrimeGapBound a b g := by
  intro n hna hnb
  obtain ⟨row, hrow, hleft, hright⟩ :=
    cover n hna hnb
  refine ⟨row.witness, row.witness_prime, ?_, ?_⟩
  · exact lt_of_le_of_lt hright row.right_lt_witness
  · exact le_trans row.witness_le_left_add_gap (Nat.add_le_add_right hleft g)

theorem finitePrimeGapBound_of_indexed_rows_cover
    {a b g n : Nat} {rows : Fin n → FinitePrimeGapRow g}
    (cover : FinitePrimeGapIndexedRowsCover (a := a) (b := b) (g := g) rows) :
    FinitePrimeGapBound a b g := by
  intro x hxa hxb
  obtain ⟨i, hleft, hright⟩ :=
    cover x hxa hxb
  refine ⟨(rows i).witness, (rows i).witness_prime, ?_, ?_⟩
  · exact lt_of_le_of_lt hright (rows i).right_lt_witness
  · exact le_trans (rows i).witness_le_left_add_gap
      (Nat.add_le_add_right hleft g)

theorem finitePrimeGapIndexedRowsCover_of_list
    {a b g : Nat} {rows : List (FinitePrimeGapRow g)}
    (cover : FinitePrimeGapRowsCover (a := a) (b := b) (g := g) rows) :
    FinitePrimeGapIndexedRowsCover (a := a) (b := b) (g := g)
      (fun i : Fin rows.length => rows.get i) := by
  intro x hxa hxb
  obtain ⟨row, hrow, hleft, hright⟩ :=
    cover x hxa hxb
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
  have hnonneg : (0 : Real) ≤ x := by linarith [hx]
  have hlow : (89689 : Real) ≤ x := by linarith [hx]
  exact exists_prime_in_real_interval_of_finite_prime_gap_bound gap
    hnonneg hlow
    (hxx.trans hXb)
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
    (cover : FinitePrimeGapIndexedRowsCover (a := 89689) (b := b) (g := g) rows)
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
  by_cases hxm : x < m + 1
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
    (left : Fin n₁ → α) (right : Fin n₂ → α)
    (leftEndpoint rightEndpoint : α → Nat)
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



end

end PrimeFactorUnimodality
