import PrimeFactorUnimodality.Helpers.Analytic.SievedThetaPrimeTrace

/-! # Exact sieve-count interfaces and boundary regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

open PrimeFactorUnimodality.ThetaPrimeCheckpoint
open Finset
open PrimeCert.Sieve

example {N k bits : ℕ} (h : IsSieve N bits)
    {start : ThetaPrimeCheckpoint} (hstart : Nat.primeCounting start.point = start.count)
    {points : List ThetaPrimeCheckpoint} (hc : checkSieveCounts N k bits start points = true) :
    ∀ s ∈ points, Nat.primeCounting s.point = s.count := by
  exact PrimeFactorUnimodality.ThetaPrimeCheckpoint.counts_of_sieve_checks h hstart hc

example {N k bits : ℕ} (h : IsSieve N bits)
    {c : SharedTaylorIntervals} (hc : c.Prepared)
    {start : ThetaPrimeCheckpoint} (hs : start.Valid) {points : List ThetaPrimeCheckpoint}
    (hcounts : checkSieveCounts N k bits start points = true)
    (htrace : checkTrace c start points = true) : ∀ s ∈ points, s.Valid := by
  exact PrimeFactorUnimodality.ThetaPrimeCheckpoint.valid_of_sieve_and_theta_checks h hc hs hcounts htrace

example : three.Valid := by
  exact PrimeFactorUnimodality.ThetaPrimeCheckpoint.three_valid

example
    {N k bits : ℕ} (h : IsSieve N bits) {c : SharedTaylorIntervals} (hc : c.Prepared)
    {start p q : ThetaPrimeCheckpoint} (hs : start.Valid)
    {points : List ThetaPrimeCheckpoint}
    (hcounts : ThetaPrimeCheckpoint.checkSieveCounts N k bits start (p :: points) = true)
    (htrace : ThetaPrimeCheckpoint.checkTrace c start (p :: points) = true)
    (hpositive : ∀ s ∈ p :: points, 2 ≤ s.point ∧ 0 < s.log.hi)
    (hchain : ThetaSquaredCheckpoint.checkFrom (1 / 5) p.squared q.squared
      (points.map ThetaPrimeCheckpoint.squared) = true)
    (hp : p.point ≤ 3594641) (hq : 1441000000000 ≤ q.point) :
    ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 1441000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2 := by
  exact PrimeFactorUnimodality.thetaLogSquared_on_published_band_of_sieve_checks h hc hs hcounts htrace hpositive hchain hp hq

private theorem sieve30 : IsSieve 30 766 :=
  isSieve_of_sieveK_eq (sqrtN := 6) (by decide +kernel) (by decide) (by decide)

private def atEleven : ThetaPrimeCheckpoint :=
  ⟨11, 5, ⟨0, 15, by norm_num⟩, ⟨2, 3, by norm_num⟩⟩
private def atThirty : ThetaPrimeCheckpoint :=
  ⟨30, 10, ⟨0, 40, by norm_num⟩, ⟨3, 4, by norm_num⟩⟩

example : checkSieveCounts 30 3 766 three [atEleven, atThirty] = true := by decide +kernel
example : checkTrace (SharedTaylorIntervals.prepare 4) three [atEleven, atThirty] = true := by
  decide +kernel
example : atThirty.Valid :=
  valid_of_sieve_and_theta_checks sieve30 (SharedTaylorIntervals.prepare_prepared 4)
    three_valid (points := [atEleven, atThirty]) (k := 3)
    (by decide +kernel) (by decide +kernel) atThirty (by simp)
example : checkSieveCounts 30 0 766 three [] = true := rfl

end PrimeFactorUnimodality.Tests
