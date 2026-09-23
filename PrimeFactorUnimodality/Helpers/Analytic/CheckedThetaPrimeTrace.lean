import PrimeFactorUnimodality.Helpers.Analytic.SharedTaylorIntervals
import PrimeFactorUnimodality.Helpers.Analytic.ThetaPrimeCheckpoints

/-! # Checked logarithms and linear theta-checkpoint traces

Each new endpoint logarithm is checked once using shared scalar constants.
The adjacent transition checker then transports theta enclosures, retaining
outward rounding at every step. Exact prime counts remain explicit finite
inputs; no conjectural count or theta bound is stored as a proof shortcut.
-/

namespace PrimeFactorUnimodality.ThetaPrimeCheckpoint

open LeanCert.Core

/-- Check positivity and the actual rational endpoint logarithm enclosure. -/
def checkLog (c : SharedTaylorIntervals) (s : ThetaPrimeCheckpoint) : Bool :=
  decide (0 < s.point) && intervalSubset (c.log s.point) s.log

/-- Prepared scalar arithmetic certifies the stored endpoint logarithm. -/
theorem log_mem_of_check {c : SharedTaylorIntervals} (hc : c.Prepared)
    {s : ThetaPrimeCheckpoint} (h : checkLog c s = true) : Real.log s.point ∈ s.log := by
  simp only [checkLog, Bool.and_eq_true, decide_eq_true_eq] at h
  have hq : (0 : ℚ) < s.point := by exact_mod_cast h.1
  have hl := mem_of_intervalSubset h.2 (SharedTaylorIntervals.mem_log hc hq)
  simpa using hl

/-- A trace checks adjacent transitions and each new logarithm once. -/
def checkTrace (c : SharedTaylorIntervals) (start : ThetaPrimeCheckpoint) :
    List ThetaPrimeCheckpoint → Bool
  | [] => true
  | next :: rest => (start.checkStep next && checkLog c next) && checkTrace c next rest

/-- Every retained endpoint is valid when the initial state, prime counts and local checks hold. -/
theorem valid_of_checkTrace {c : SharedTaylorIntervals} (hc : c.Prepared)
    {start : ThetaPrimeCheckpoint} (hs : start.Valid) {points : List ThetaPrimeCheckpoint}
    (hcounts : ∀ s ∈ points, Nat.primeCounting s.point = s.count)
    (h : checkTrace c start points = true) : ∀ s ∈ points, s.Valid := by
  induction points generalizing start with
  | nil => simp
  | cons next rest ih =>
    simp only [checkTrace, Bool.and_eq_true] at h
    have hn := valid_of_checkStep hs (hcounts next (by simp))
      (log_mem_of_check hc h.1.2) h.1.1
    intro s hmem
    rcases List.mem_cons.mp hmem with hmem | hmem
    · simpa only [hmem] using hn
    · exact ih hn (fun t ht => hcounts t (List.mem_cons_of_mem _ ht)) h.2 s hmem

/-- Shared seams compose without repeating any internal transition checks. -/
theorem checkTrace_append (c : SharedTaylorIntervals) (start : ThetaPrimeCheckpoint)
    (left right : List ThetaPrimeCheckpoint) :
    checkTrace c start (left ++ right) =
      (checkTrace c start left && checkTrace c (left.getLast?.getD start) right) := by
  induction left generalizing start with
  | nil => simp [checkTrace]
  | cons next rest ih =>
    cases rest with
    | nil => simp [checkTrace, Bool.and_assoc]
    | cons head tail =>
      rw [List.cons_append, checkTrace, ih next]
      simp [checkTrace, Bool.and_assoc, List.getLast?_eq_some_getLast]

/-- Checked trace data exports all lower-band checkpoint enclosures in one pass. -/
theorem squared_valid_of_checkTrace {c : SharedTaylorIntervals} (hc : c.Prepared)
    {start : ThetaPrimeCheckpoint} (hs : start.Valid) {points : List ThetaPrimeCheckpoint}
    (hcounts : ∀ s ∈ points, Nat.primeCounting s.point = s.count)
    (h : checkTrace c start points = true)
    (hpoint : ∀ s ∈ points, 2 ≤ s.point ∧ 0 < s.log.hi) :
    ∀ p ∈ points.map squared, p.Valid := by
  intro p hp
  obtain ⟨s, hs', rfl⟩ := List.mem_map.mp hp
  exact squared_valid (valid_of_checkTrace hc hs hcounts h s hs')
    (hpoint s hs').1 (hpoint s hs').2

end PrimeFactorUnimodality.ThetaPrimeCheckpoint
