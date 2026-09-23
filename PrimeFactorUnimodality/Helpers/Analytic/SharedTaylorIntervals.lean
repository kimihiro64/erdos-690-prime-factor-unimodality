import LeanCert.Core.IntervalRat.Taylor

/-! # Shared Taylor constants for finite interval computations

Prepare the logarithmic constant and scalar coefficient lists once per
precision. Each logarithm, exponential and trigonometric evaluation reuses
that configuration; its soundness is the existing scalar interval theorem.
-/

namespace PrimeFactorUnimodality

open LeanCert.Core LeanCert.Core.IntervalRat

/-- Configuration-dependent lists and the logarithm of two, shared by all atoms. -/
structure SharedTaylorIntervals where
  order : ℕ
  logTwo : IntervalRat
  atanhCoeffs : List ℚ
  expCoeffs : List ℚ
  sinCoeffs : List ℚ
  cosCoeffs : List ℚ

namespace SharedTaylorIntervals

/-- The shared values are the exact rational constructions of the scalar library. -/
structure Prepared (c : SharedTaylorIntervals) : Prop where
  logTwo : c.logTwo = ln2Computable c.order
  atanhCoeffs : c.atanhCoeffs = atanhTaylorCoeffs c.order
  expCoeffs : c.expCoeffs = expTaylorCoeffs c.order
  sinCoeffs : c.sinCoeffs = sinTaylorCoeffs c.order
  cosCoeffs : c.cosCoeffs = cosTaylorCoeffs c.order

/-- Build all configuration-dependent objects once. -/
def prepare (order : ℕ) : SharedTaylorIntervals :=
  ⟨order, ln2Computable order, atanhTaylorCoeffs order, expTaylorCoeffs order,
    sinTaylorCoeffs order, cosTaylorCoeffs order⟩

/-- The preparation function needs no separately certified constants. -/
theorem prepare_prepared (order : ℕ) : (prepare order).Prepared :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Binary-reduced rational logarithm with shared coefficients and log-two enclosure. -/
def log (c : SharedTaylorIntervals) (q : ℚ) : IntervalRat :=
  logPointComputablePrepared q c.order c.logTwo c.atanhCoeffs

/-- Scalar exponential with shared coefficients. -/
def exp (c : SharedTaylorIntervals) (J : IntervalRat) : IntervalRat :=
  expComputableWithCoeffs J c.order c.expCoeffs

/-- Direct sine enclosure on a supplied reduced angle interval. -/
def sin (c : SharedTaylorIntervals) (J : IntervalRat) : IntervalRat :=
  sinComputableWithCoeffs J c.order c.sinCoeffs

/-- Direct cosine enclosure on a supplied reduced angle interval. -/
def cos (c : SharedTaylorIntervals) (J : IntervalRat) : IntervalRat :=
  cosComputableWithCoeffs J c.order c.cosCoeffs

/-- Positive rational inputs have their actual logarithm enclosed. -/
theorem mem_log {c : SharedTaylorIntervals} (hc : c.Prepared) {q : ℚ} (hq : 0 < q) :
    Real.log (q : ℝ) ∈ c.log q := by
  rw [log, hc.logTwo, hc.atanhCoeffs, logPointComputablePrepared_eq]
  exact mem_logPointComputable hq c.order

/-- Prepared exponential evaluation encloses every member of its input interval. -/
theorem mem_exp {c : SharedTaylorIntervals} (hc : c.Prepared) {x : ℝ} {J : IntervalRat}
    (hx : x ∈ J) : Real.exp x ∈ c.exp J := by
  rw [exp, hc.expCoeffs, expComputableWithCoeffs_eq]
  exact mem_expComputable hx c.order

/-- Prepared sine evaluation encloses every member of its input interval. -/
theorem mem_sin {c : SharedTaylorIntervals} (hc : c.Prepared) {x : ℝ} {J : IntervalRat}
    (hx : x ∈ J) : Real.sin x ∈ c.sin J := by
  rw [sin, hc.sinCoeffs, sinComputableWithCoeffs_eq]
  exact mem_sinComputable hx c.order

/-- Prepared cosine evaluation encloses every member of its input interval. -/
theorem mem_cos {c : SharedTaylorIntervals} (hc : c.Prepared) {x : ℝ} {J : IntervalRat}
    (hx : x ∈ J) : Real.cos x ∈ c.cos J := by
  rw [cos, hc.cosCoeffs, cosComputableWithCoeffs_eq]
  exact mem_cosComputable hx c.order

end SharedTaylorIntervals

end PrimeFactorUnimodality
