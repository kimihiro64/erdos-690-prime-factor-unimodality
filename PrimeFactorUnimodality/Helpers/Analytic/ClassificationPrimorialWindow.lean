import PrimeFactorUnimodality.Helpers.Analytic.ClassificationWindowScalars
import PrimeFactorUnimodality.Helpers.Analytic.FirstPrimorialCrossing

set_option autoImplicit false

/-! # The quantified primorial window used by both gap witnesses -/

namespace PrimeFactorUnimodality

open Real

theorem exists_classification_primorial_window (r : Real) (hr : 38000 <= r) :
    Exists (fun p : Nat => Exists (fun q : Nat =>
      And (ConsecutivePrimes p q)
        (And (2000 <= p)
          (And (classificationT r < 2 * (p : Real))
            (And (classificationEll r <= log (primorial q))
              (And (log (primorial q) < classificationEll r + log (5 * classificationEll r))
                (And ((2 : Nat)^30 <= primorial q)
                  (log (400 * (primorial q : Real)) < classificationMStar r)))))))) := by
  have he := classificationEll_lower r hr
  cases exists_first_primorial_crossing (classificationEll r) he.le with
  | intro p hp =>
    cases hp with
    | intro q hq =>
      have hpair := hq.1
      have hprev := hq.2.1
      have hcross := hq.2.2.1
      have hqbound := hq.2.2.2
      have hstep := theta_consecutive_step hpair
      have hlogq : log (q : Real) < log (5 * classificationEll r) :=
        log_lt_log (by exact_mod_cast hpair.right_prime.pos) hqbound
      have hU := (classification_window_allowances (classificationEll r) he.le).1
      have hthetaPrev : classificationEll r - log (5 * classificationEll r) <
          Chebyshev.theta p := by linarith
      have hprevLarge : (3660 : Real) < Chebyshev.theta p := by nlinarith
      have hlog4 : log (4 : Real) < 1.4 := by
        rw [show (4 : Real) = 2 ^ (2 : Nat) by norm_num, log_pow]
        norm_num
        linarith [LogTables.log_2_lt]
      have hrough := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg p)
      have hpLarge : 2000 <= p := by
        have hpReal : (2000 : Real) < p := by nlinarith
        exact (by exact_mod_cast hpReal : 2000 < p).le
      have hsharp := Chebyshev.theta_upper_112_from_2000 p (by exact_mod_cast hpLarge)
      have ht : classificationT r < 2 * (p : Real) := by
        unfold classificationT
        nlinarith
      have hPpos : (0 : Real) < primorial q := by exact_mod_cast primorial_pos q
      have hlogP : log (primorial q : Real) = Chebyshev.theta q := by
        rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
      have hLlower : classificationEll r <= log (primorial q : Real) := by
        rw [hlogP]
        exact hcross
      have hLupper : log (primorial q : Real) <
          classificationEll r + log (5 * classificationEll r) := by
        rw [hlogP]
        linarith
      have hPpower : (2 : Nat)^30 <= primorial q := by
        by_contra hnot
        have hp : (primorial q : Real) < (2 : Real)^(30 : Nat) := by
          exact_mod_cast (by omega : primorial q < (2 : Nat)^30)
        have hl := log_lt_log hPpos hp
        rw [log_pow] at hl
        norm_num only [Nat.cast_ofNat] at hl
        nlinarith [LogTables.log_2_lt]
      have hM : log (400 * (primorial q : Real)) < classificationMStar r := by
        rw [log_mul (by norm_num) hPpos.ne']
        have heq : log (2000 * classificationEll r) =
            log (400 : Real) + log (5 * classificationEll r) := by
          rw [show 2000 * classificationEll r = 400 * (5 * classificationEll r) by ring,
            log_mul (by norm_num) (by linarith)]
        unfold classificationMStar
        linarith
      exact Exists.intro p (Exists.intro q
        (And.intro hpair (And.intro hpLarge (And.intro ht
          (And.intro hLlower (And.intro hLupper (And.intro hPpower hM)))))))

end PrimeFactorUnimodality
