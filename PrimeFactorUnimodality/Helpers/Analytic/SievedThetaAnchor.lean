import PrimeFactorUnimodality.Helpers.Analytic.CheckedThetaPrimeTrace
import PrimeFactorUnimodality.Helpers.Analytic.NaturalLogScaling
import PrimeFactorUnimodality.Helpers.Arithmetic.SievePrimeProduct

/-! # Tight theta checkpoints from checked primorials

The identity theta(n) = log(primorial n) replaces accumulated lower-log
transport from a coarse small seed. Exact sieve counts, compact product
rows and a scaled logarithm enclosure construct the same checkpoint validity
interface consumed by the lower-band trace.
-/

namespace PrimeFactorUnimodality.ThetaPrimeCheckpoint

/-- Exact counts, complete primorial rows and two checked logarithms give a valid theta anchor. -/
theorem valid_of_sieve_product_checks {N k bits product : ℕ}
    (hsieve : PrimeCert.Sieve.IsSieve N bits) {c : SharedTaylorIntervals} (hc : c.Prepared)
    {s : ThetaPrimeCheckpoint} (hn : s.point ≤ N) {rows : List SieveProductRow}
    (hcount : checkSievePrimeCount N k bits s.point s.count = true)
    (hproduct : SieveProductRow.checkPrimorial s.point bits rows product = true)
    (row : NatLogScaleRow) (htheta : row.check c product s.theta = true)
    (hlog : checkLog c s = true) : s.Valid := by
  have hpos : 0 < s.point := by
    have h := hlog
    simp only [checkLog, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  have hp := SieveProductRow.primorial_eq_of_check hsieve hn hproduct
  refine ⟨hpos, primeCounting_eq_of_sieve_check hsieve hcount, ?_, log_mem_of_check hc hlog⟩
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast, hp]
  exact row.log_mem_of_check hc htheta

end PrimeFactorUnimodality.ThetaPrimeCheckpoint
