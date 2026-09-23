import PrimeFactorUnimodality.Helpers.Analytic.DusartCheckedThetaTrace
import PrimeFactorUnimodality.Helpers.Arithmetic.SievePrimeCountIncrements

/-! # Local sieve counts feed the complete checked theta trace

Only each new block's bits are counted. The exact previous count is reused
at every seam. Together with the independent logarithm, theta-transport and
coverage checks, one certified sieve supplies the lower-band interface
without assuming any endpoint prime counts or theta enclosures after the seed.
-/

namespace PrimeFactorUnimodality

open PrimeCert.Sieve

namespace ThetaPrimeCheckpoint

/-- Adjacent count checks use one retained sieve and bounded local bit blocks. -/
def checkSieveCounts (N k bits : ℕ) (start : ThetaPrimeCheckpoint) :
    List ThetaPrimeCheckpoint → Bool
  | [] => true
  | next :: rest => checkSieveCountStep N k bits start.point start.count next.point next.count &&
    checkSieveCounts N k bits next rest

/-- A checked local trace supplies every actual endpoint count from its exact initial count. -/
theorem counts_of_sieve_checks {N k bits : ℕ} (h : IsSieve N bits)
    {start : ThetaPrimeCheckpoint} (hstart : Nat.primeCounting start.point = start.count)
    {points : List ThetaPrimeCheckpoint} (hc : checkSieveCounts N k bits start points = true) :
    ∀ s ∈ points, Nat.primeCounting s.point = s.count := by
  induction points generalizing start with
  | nil => simp
  | cons next rest ih =>
    simp only [checkSieveCounts, Bool.and_eq_true] at hc
    have hn := primeCounting_eq_of_sieve_step h hstart hc.1
    intro s hs
    rcases List.mem_cons.mp hs with hs | hs
    · simpa only [hs] using hn
    · exact ih hn hc.2 s hs

/-- Sieve-backed count rows discharge the count premise of the existing theta transport. -/
theorem valid_of_sieve_and_theta_checks {N k bits : ℕ} (h : IsSieve N bits)
    {c : SharedTaylorIntervals} (hc : c.Prepared)
    {start : ThetaPrimeCheckpoint} (hs : start.Valid) {points : List ThetaPrimeCheckpoint}
    (hcounts : checkSieveCounts N k bits start points = true)
    (htrace : checkTrace c start points = true) : ∀ s ∈ points, s.Valid :=
  valid_of_checkTrace hc hs (counts_of_sieve_checks h hs.2.1 hcounts) htrace

/-- A closed elementary seed at three permits the entire remaining trace to use local increments. -/
def three : ThetaPrimeCheckpoint :=
  ⟨3, 2, ⟨0, 3, by norm_num⟩, ⟨1, 2, by norm_num⟩⟩

/-- The initial count, theta sum and logarithm follow from the two smallest primes. -/
theorem three_valid : three.Valid := by
  have hp : Nat.primesLE 3 = {2, 3} := by decide +kernel
  have hcount : Nat.primeCounting 3 = 2 := by
    rw [← Nat.primesLE_card_eq_primeCounting, hp]
    norm_num
  have ht := Chebyshev.theta_eq_sum_primesLE_log 3
  rw [hp] at ht
  norm_num at ht
  have hl : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact Real.exp_one_lt_d9.trans (by norm_num)
  refine ⟨by norm_num [three], hcount, ?_, ?_⟩
  · norm_num only [three, LeanCert.Core.IntervalRat.mem_def,
      Rat.cast_zero, Rat.cast_ofNat, Nat.cast_ofNat]
    exact ⟨Chebyshev.theta_nonneg _, by
      linarith [Real.log_two_lt_d9, Real.log_three_lt_d9]⟩
  · norm_num only [three, LeanCert.Core.IntervalRat.mem_def,
      Rat.cast_one, Rat.cast_ofNat, Nat.cast_ofNat]
    exact ⟨hl.le, by linarith [Real.log_three_lt_d9]⟩

end ThetaPrimeCheckpoint

/-- Sieve, scalar, transition and coverage checks suffice for the full published lower theta band. -/
theorem thetaLogSquared_on_published_band_of_sieve_checks
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
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2 :=
  thetaLogSquared_on_published_band_of_checked_prime_trace hc hs
    (ThetaPrimeCheckpoint.counts_of_sieve_checks h hs.2.1 hcounts) htrace hpositive hchain hp hq

end PrimeFactorUnimodality
