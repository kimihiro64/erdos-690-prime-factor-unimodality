import PrimeFactorUnimodality.Helpers.Analytic.ThetaSquaredCheckpoints

/-! # Ordered compact checkpoint chains for a complete theta band

Consecutive steps share their endpoint enclosure. The same generic proof
covers every real point in the band; separately checked chunks compose at
one shared checkpoint. No list lookup is repeated for each interior integer.
-/

set_option autoImplicit false

namespace PrimeFactorUnimodality

namespace ThetaSquaredCheckpoint

/-- Ordered rational step margins, with explicit first and last checkpoints. -/
inductive Chain (c : ℚ) : ThetaSquaredCheckpoint → ThetaSquaredCheckpoint →
    List ThetaSquaredCheckpoint → Prop
  | single (p : ThetaSquaredCheckpoint) (h : Step c p p) : Chain c p p [p]
  | cons (p : ThetaSquaredCheckpoint) {q r : ThetaSquaredCheckpoint}
      {tail : List ThetaSquaredCheckpoint} (h : Step c p q)
      (rest : Chain c q r tail) : Chain c p r (p :: tail)

/-- Chunks append through their common endpoint; only the checkpoint at the seam is repeated. -/
theorem Chain.append {c : ℚ} {p q r : ThetaSquaredCheckpoint}
    {left right : List ThetaSquaredCheckpoint}
    (hl : Chain c p q left) (hr : Chain c q r right) :
    Chain c p r (left ++ right) := by
  induction hl with
  | single p h => exact Chain.cons p h hr
  | cons p h _ ih => exact Chain.cons p h (ih hr)

/-- A chain cannot skip any real point between its endpoints. -/
theorem Chain.covers {c : ℚ} {p q : ThetaSquaredCheckpoint}
    {rows : List ThetaSquaredCheckpoint} (h : Chain c p q rows)
    {x : ℝ} (hpx : (p.point : ℝ) ≤ x) (hxq : x ≤ q.point) :
    ∃ u ∈ rows, ∃ v ∈ rows, Step c u v ∧ (u.point : ℝ) ≤ x ∧ x ≤ v.point := by
  induction h with
  | single p h => exact ⟨p, by simp, p, by simp, h, hpx, hxq⟩
  | @cons p q r tail h rest ih =>
    by_cases hx : x ≤ q.point
    · have hqmem : q ∈ tail := by cases rest <;> simp
      exact ⟨p, by simp, q, List.mem_cons_of_mem _ hqmem, h, hpx, hx⟩
    · obtain ⟨u, hu, v, hv, huv, hux, hxv⟩ := ih (le_of_not_ge hx) hxq
      exact ⟨u, List.mem_cons_of_mem _ hu, v, List.mem_cons_of_mem _ hv, huv, hux, hxv⟩

/-- Valid endpoint enclosures and rational chain margins provide the whole real band. -/
theorem Chain.bound {c : ℚ} (hc : 0 ≤ c) {p q : ThetaSquaredCheckpoint}
    {rows : List ThetaSquaredCheckpoint} (h : Chain c p q rows)
    (hvalid : ∀ r ∈ rows, r.Valid) {x : ℝ}
    (hpx : (p.point : ℝ) ≤ x) (hxq : x ≤ q.point) :
    |Chebyshev.theta x - x| ≤ (c : ℝ) * x / Real.log x ^ 2 := by
  obtain ⟨u, hu, v, hv, huv, hux, hxv⟩ := h.covers hpx hxq
  exact huv.bound hc (hvalid u hu) (hvalid v hv) hux hxv

/-- Local endpoint validity composes independently of the rational margin checks. -/
theorem valid_append {left right : List ThetaSquaredCheckpoint}
    (hl : ∀ p ∈ left, p.Valid) (hr : ∀ p ∈ right, p.Valid) :
    ∀ p ∈ left ++ right, p.Valid := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hl p hp
  · exact hr p hp

end ThetaSquaredCheckpoint

end PrimeFactorUnimodality
