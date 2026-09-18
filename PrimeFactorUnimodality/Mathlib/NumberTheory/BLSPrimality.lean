/-
Copyright (c) 2026 kimihiro64. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kimihiro64
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import PrimeFactorUnimodality.Mathlib.NumberTheory.PrimalityCongruence

/-!
# A quadratic-algebra certificate for an `N + 1` primality test

This file develops the proof-producing algebraic core needed to replay a
Brillhart--Lehmer--Selfridge-style `N + 1` certificate.  Computed residues are
kept separate from the general criterion.
-/

@[expose] public section

namespace BLSPrimality

/-- The quadratic algebra `(ZMod n)[√7]`. -/
abbrev X7 (n : ℕ) := QuadraticAlgebra (ZMod n) 7 0

instance (n : ℕ) : CharP (X7 n) n where
  cast_eq_zero_iff x := by
    convert ZMod.natCast_eq_zero_iff x n
    exact ⟨congr_arg QuadraticAlgebra.re, fun hx ↦
      QuadraticAlgebra.ext hx (by simp)⟩

/-- The element `1 + √7`. -/
def alpha (n : ℕ) : X7 n := ⟨1, 1⟩

/-- The conjugate element `1 - √7`. -/
def alphaBar (n : ℕ) : X7 n := star (alpha n)

@[simp]
theorem alpha_re (n : ℕ) : (alpha n).re = 1 := rfl

@[simp]
theorem alpha_im (n : ℕ) : (alpha n).im = 1 := rfl

@[simp]
theorem alphaBar_re (n : ℕ) : (alphaBar n).re = 1 := by
  simp [alphaBar]

@[simp]
theorem alphaBar_im (n : ℕ) : (alphaBar n).im = -1 := by
  simp [alphaBar]

/-- Reduction from modulus `n` to a divisor modulus `p`. -/
def mapOfDvd {n p : ℕ} (h : p ∣ n) : X7 n →+* X7 p where
  toFun z := ⟨ZMod.castHom h (ZMod p) z.re, ZMod.castHom h (ZMod p) z.im⟩
  map_zero' := by
    ext <;> exact map_zero (ZMod.castHom h (ZMod p))
  map_one' := by
    apply QuadraticAlgebra.ext
    · exact map_one (ZMod.castHom h (ZMod p))
    · exact map_zero (ZMod.castHom h (ZMod p))
  map_add' x y := by
    apply QuadraticAlgebra.ext
    · exact map_add (ZMod.castHom h (ZMod p)) x.re y.re
    · exact map_add (ZMod.castHom h (ZMod p)) x.im y.im
  map_mul' x y := by
    apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_mul, map_add, map_mul, map_ofNat]
    · simp only [QuadraticAlgebra.im_mul, map_add, map_mul, zero_mul, add_zero]

@[simp]
theorem mapOfDvd_re {n p : ℕ} (h : p ∣ n) (z : X7 n) :
    (mapOfDvd h z).re = ZMod.castHom h (ZMod p) z.re := rfl

@[simp]
theorem mapOfDvd_im {n p : ℕ} (h : p ∣ n) (z : X7 n) :
    (mapOfDvd h z).im = ZMod.castHom h (ZMod p) z.im := rfl

@[simp]
theorem mapOfDvd_alpha {n p : ℕ} (h : p ∣ n) :
    mapOfDvd h (alpha n) = alpha p := by
  apply QuadraticAlgebra.ext <;>
    exact map_one (ZMod.castHom h (ZMod p))

@[simp]
theorem mapOfDvd_alphaBar {n p : ℕ} (h : p ∣ n) :
    mapOfDvd h (alphaBar n) = alphaBar p := by
  apply QuadraticAlgebra.ext
  · simp only [mapOfDvd_re, alphaBar_re]
    exact map_one (ZMod.castHom h (ZMod p))
  · simp only [mapOfDvd_im, alphaBar_im]
    rw [map_neg, map_one]

theorem alpha_mul_alphaBar (n : ℕ) :
    alpha n * alphaBar n = (-6 : X7 n) := by
  have hcast : (-6 : X7 n) = (⟨(-6 : ZMod n), 0⟩ : X7 n) := by
    ext <;> norm_num [QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  rw [hcast]
  ext <;> norm_num [alpha, alphaBar]

theorem alphaBar_mul_alpha (n : ℕ) :
    alphaBar n * alpha n = (-6 : X7 n) := by
  rw [mul_comm, alpha_mul_alphaBar]

/-- `1 + √7` is a unit whenever `6` is a unit in the coefficient ring. -/
theorem alpha_isUnit {n : ℕ} (hSix : IsUnit (6 : ZMod n)) :
    IsUnit (alpha n) := by
  have hNegSix : IsUnit (1 - 7 : ZMod n) := by
    rw [show (1 - 7 : ZMod n) = -6 by norm_num]
    exact hSix.neg
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit]
  simpa only [QuadraticAlgebra.norm_def, alpha_re, alpha_im, mul_one,
    zero_mul, add_zero] using hNegSix

/-- `1 - √7` is a unit whenever `6` is a unit in the coefficient ring. -/
theorem alphaBar_isUnit {n : ℕ} (hSix : IsUnit (6 : ZMod n)) :
    IsUnit (alphaBar n) := by
  have hNegSix : IsUnit (1 - 7 : ZMod n) := by
    rw [show (1 - 7 : ZMod n) = -6 by norm_num]
    exact hSix.neg
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit]
  simpa only [QuadraticAlgebra.norm_def, alphaBar_re, alphaBar_im, mul_one,
    mul_neg, zero_mul, add_zero, neg_mul, neg_neg, neg_zero] using hNegSix

/-- The quotient `(1 + √7) / (1 - √7)` as a unit. -/
noncomputable def ratioUnit (n : ℕ) (hSix : IsUnit (6 : ZMod n)) : (X7 n)ˣ :=
  (alpha_isUnit hSix).unit * (alphaBar_isUnit hSix).unit⁻¹

/-- A power of the quotient is one exactly when the corresponding powers of
`1 + √7` and `1 - √7` agree. -/
theorem ratioUnit_pow_eq_one_iff (n e : ℕ) (hSix : IsUnit (6 : ZMod n)) :
    ratioUnit n hSix ^ e = 1 ↔ alpha n ^ e = alphaBar n ^ e := by
  change
    ((alpha_isUnit hSix).unit * (alphaBar_isUnit hSix).unit⁻¹) ^ e = 1 ↔ _
  rw [mul_pow]
  constructor
  · intro h
    have hu : (alpha_isUnit hSix).unit ^ e =
        (alphaBar_isUnit hSix).unit ^ e := by
      exact mul_inv_eq_one.mp h
    exact congr_arg ((↑·) : (X7 n)ˣ → X7 n) hu
  · intro h
    rw [inv_pow]
    apply mul_inv_eq_one.mpr
    apply Units.ext
    exact h

/-- Powers of the conjugate are conjugates of powers. -/
theorem alphaBar_pow (n e : ℕ) :
    alphaBar n ^ e = star (alpha n ^ e) := by
  simp [alphaBar]

/-- A vanishing imaginary coordinate makes the two conjugate powers equal. -/
theorem alpha_pow_eq_alphaBar_pow_of_im_eq_zero (n e : ℕ)
    (him : (alpha n ^ e).im = 0) :
    alpha n ^ e = alphaBar n ^ e := by
  rw [alphaBar_pow]
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_star, zero_mul, add_zero]
  · simp only [QuadraticAlgebra.im_star, him, neg_zero]

/-- An invertible imaginary coordinate prevents two conjugate powers from
being equal. -/
theorem alpha_pow_ne_alphaBar_pow_of_isUnit_im (p e : ℕ) [Fact p.Prime]
    (hTwo : IsUnit (2 : ZMod p)) (him : IsUnit ((alpha p ^ e).im)) :
    alpha p ^ e ≠ alphaBar p ^ e := by
  intro h
  have hcoord : (alpha p ^ e).im = -(alpha p ^ e).im := by
    have hstar : alpha p ^ e = star (alpha p ^ e) := h.trans (alphaBar_pow p e)
    have hcoord0 := congrArg QuadraticAlgebra.im hstar
    simpa only [QuadraticAlgebra.im_star] using hcoord0
  have hzero : (2 : ZMod p) * (alpha p ^ e).im = 0 := by
    calc
      (2 : ZMod p) * (alpha p ^ e).im =
          (alpha p ^ e).im + (alpha p ^ e).im := two_mul _
      _ = -(alpha p ^ e).im + (alpha p ^ e).im :=
        congrArg (fun z ↦ z + (alpha p ^ e).im) hcoord
      _ = 0 := neg_add_cancel _
  exact him.ne_zero ((mul_eq_zero.mp hzero).resolve_left hTwo.ne_zero)

/-- Odd powers of `√7` in `X7`. -/
theorem omega_pow_odd (n k : ℕ) :
    (QuadraticAlgebra.omega : X7 n) ^ (2 * k + 1) =
      ((7 : ZMod n) ^ k) • (QuadraticAlgebra.omega : X7 n) := by
  rw [pow_succ, pow_mul, QuadraticAlgebra.omega_pow_two_eq_add]
  simp [Algebra.smul_def]

/-- Frobenius sends `1 + √7` to the element whose imaginary coordinate is
the Legendre symbol of `7`. -/
theorem alpha_pow_prime {p : ℕ} [Fact p.Prime] (hpOdd : Odd p) :
    alpha p ^ p = ⟨1, ((legendreSym p 7 : ℤ) : ZMod p)⟩ := by
  obtain ⟨k, rfl⟩ := hpOdd
  let p := 2 * k + 1
  have hSeven : (7 : ZMod p) ^ k = ((legendreSym p 7 : ℤ) : ZMod p) := by
    have hhalf : p / 2 = k := by
      simp [p, Nat.mul_add_div (by decide : 0 < 2)]
    rw [← hhalf]
    exact (legendreSym.eq_pow p 7).symm
  have halpha : alpha p = 1 + (QuadraticAlgebra.omega : X7 p) := by
    ext <;> simp [alpha, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  rw [halpha, add_pow_expChar, omega_pow_odd, hSeven]
  ext <;> simp [p, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

/-- Frobenius formula for the conjugate `1 - √7`. -/
theorem alphaBar_pow_prime {p : ℕ} [Fact p.Prime] (hpOdd : Odd p) :
    alphaBar p ^ p =
      ⟨1, -((legendreSym p 7 : ℤ) : ZMod p)⟩ := by
  rw [alphaBar_pow, alpha_pow_prime hpOdd]
  ext <;> simp

/-- If `7` is a quadratic residue modulo `p`, Frobenius fixes the quotient
`(1 + √7) / (1 - √7)`. -/
theorem ratioUnit_pow_prime_eq_self_of_legendre_eq_one {p : ℕ} [Fact p.Prime]
    (hpOdd : Odd p) (hSix : IsUnit (6 : ZMod p))
    (hs : legendreSym p 7 = 1) :
    ratioUnit p hSix ^ p = ratioUnit p hSix := by
  let a := (alpha_isUnit hSix).unit
  let b := (alphaBar_isUnit hSix).unit
  have ha : a ^ p = a := by
    apply Units.ext
    change alpha p ^ p = alpha p
    rw [alpha_pow_prime hpOdd]
    ext <;> simp [alpha, hs]
  have hb : b ^ p = b := by
    apply Units.ext
    change alphaBar p ^ p = alphaBar p
    rw [alphaBar_pow_prime hpOdd]
    ext <;> simp [alphaBar, hs]
  change (a * b⁻¹) ^ p = a * b⁻¹
  simp only [mul_pow, ha, inv_pow, hb]

/-- If `7` is a quadratic nonresidue modulo `p`, Frobenius inverts the
quotient `(1 + √7) / (1 - √7)`. -/
theorem ratioUnit_pow_prime_eq_inv_of_legendre_eq_neg_one {p : ℕ} [Fact p.Prime]
    (hpOdd : Odd p) (hSix : IsUnit (6 : ZMod p))
    (hs : legendreSym p 7 = -1) :
    ratioUnit p hSix ^ p = (ratioUnit p hSix)⁻¹ := by
  let a := (alpha_isUnit hSix).unit
  let b := (alphaBar_isUnit hSix).unit
  have ha : a ^ p = b := by
    apply Units.ext
    change alpha p ^ p = alphaBar p
    rw [alpha_pow_prime hpOdd]
    ext <;> simp [alphaBar, hs]
  have hb : b ^ p = a := by
    apply Units.ext
    change alphaBar p ^ p = alpha p
    rw [alphaBar_pow_prime hpOdd]
    ext <;> simp [alpha, hs]
  change (a * b⁻¹) ^ p = (a * b⁻¹)⁻¹
  simp only [mul_pow, ha, inv_pow, hb, mul_inv_rev, inv_inv]

/-- A certificate coordinate which is a unit modulo `n` remains a unit after
reduction modulo a divisor `p` of `n`. -/
theorem isUnit_im_alpha_pow_of_dvd {n p e : ℕ} (hpn : p ∣ n)
    (hu : IsUnit ((alpha n ^ e).im)) :
    IsUnit ((alpha p ^ e).im) := by
  have hm := hu.map (ZMod.castHom hpn (ZMod p))
  simpa only [← mapOfDvd_im hpn (alpha n ^ e), map_pow, mapOfDvd_alpha] using hm

/-- Invertibility of `6` implies invertibility of `2`. -/
theorem isUnit_two_of_isUnit_six {n : ℕ} (hSix : IsUnit (6 : ZMod n)) :
    IsUnit (2 : ZMod n) := by
  apply isUnit_of_mul_isUnit_left (x := (2 : ZMod n)) (y := (3 : ZMod n))
  convert hSix using 1
  norm_num

set_option linter.style.haveILetI false in
/-- A proof-producing quadratic `N + 1` primality criterion with discriminant
`7` and base `1 + √7`.

The hypotheses are deliberately certificate-shaped: `n + 1 = F * R`, the
known factor `F` exceeds `√n`, the main quadratic residue vanishes, and the
proper residues are units for every prime divisor of `F`. -/
theorem prime_of_bls_n_plus_one (n F R : ℕ)
    (hn : 1 < n)
    (hfactor : n + 1 = F * R)
    (hFpos : 0 < F)
    (hlarge : n < F ^ 2)
    (hFortyTwo : IsUnit (42 : ZMod n))
    (hmain : (alpha n ^ (n + 1)).im = 0)
    (hproper : ∀ q : ℕ, q.Prime → q ∣ F →
      IsUnit ((alpha n ^ ((n + 1) / q)).im))
    (hexclude : ¬ F - 1 ∣ n) :
    n.Prime := by
  apply Nat.prime_of_large_factor_dvd_sub_or_add hn hlarge _ hexclude
  intro p hp hpn
  letI : Fact p.Prime := ⟨hp⟩
  have hFortyTwoP : IsUnit (42 : ZMod p) := by
    convert hFortyTwo.map (ZMod.castHom hpn (ZMod p)) using 1
    exact (map_natCast (ZMod.castHom hpn (ZMod p)) 42).symm
  have hSixP : IsUnit (6 : ZMod p) := by
    apply isUnit_of_mul_isUnit_left (x := (6 : ZMod p)) (y := (7 : ZMod p))
    convert hFortyTwoP using 1
    norm_num
  have hSevenP : IsUnit (7 : ZMod p) := by
    apply isUnit_of_mul_isUnit_right (x := (6 : ZMod p)) (y := (7 : ZMod p))
    convert hFortyTwoP using 1
    norm_num
  have hTwoP : IsUnit (2 : ZMod p) := isUnit_two_of_isUnit_six hSixP
  have hpne2 : p ≠ 2 := by
    intro h
    have hTwoNe : (2 : ZMod p) ≠ 0 := hTwoP.ne_zero
    subst p
    exact hTwoNe (ZMod.natCast_self 2)
  have hpOdd : Odd p := hp.odd_of_ne_two hpne2
  have hmainEqN : alpha n ^ (n + 1) = alphaBar n ^ (n + 1) :=
    alpha_pow_eq_alphaBar_pow_of_im_eq_zero n (n + 1) hmain
  have hmainEqP : alpha p ^ (n + 1) = alphaBar p ^ (n + 1) := by
    have hm := congrArg (mapOfDvd hpn) hmainEqN
    simpa using hm
  let z := ratioUnit p hSixP
  let gamma := z ^ R
  have hzMain : z ^ (n + 1) = 1 :=
    (ratioUnit_pow_eq_one_iff p (n + 1) hSixP).2 hmainEqP
  have hgammaF : gamma ^ F = 1 := by
    dsimp [gamma]
    rw [← pow_mul, mul_comm R F, ← hfactor]
    exact hzMain
  have hgammaProper : ∀ q : ℕ, q.Prime → q ∣ F →
      gamma ^ (F / q) ≠ 1 := by
    intro q hqPrime hqF hgamma
    have himP : IsUnit ((alpha p ^ ((n + 1) / q)).im) :=
      isUnit_im_alpha_pow_of_dvd hpn (hproper q hqPrime hqF)
    have hAlphaNe : alpha p ^ ((n + 1) / q) ≠
        alphaBar p ^ ((n + 1) / q) :=
      alpha_pow_ne_alphaBar_pow_of_isUnit_im p ((n + 1) / q) hTwoP himP
    have hzNe : z ^ ((n + 1) / q) ≠ 1 := by
      intro hzOne
      exact hAlphaNe ((ratioUnit_pow_eq_one_iff p ((n + 1) / q) hSixP).1 hzOne)
    apply hzNe
    dsimp [gamma] at hgamma
    rw [← pow_mul] at hgamma
    have hexp : R * (F / q) = (n + 1) / q := by
      calc
        R * (F / q) = R * F / q := (Nat.mul_div_assoc R hqF).symm
        _ = (F * R) / q := by rw [mul_comm R F]
        _ = (n + 1) / q := by rw [hfactor]
    rwa [hexp] at hgamma
  have horder : orderOf gamma = F :=
    orderOf_eq_of_pow_and_pow_div_prime hFpos hgammaF hgammaProper
  have hSevenNe : ((7 : ℤ) : ZMod p) ≠ 0 := by
    exact_mod_cast hSevenP.ne_zero
  rcases legendreSym.eq_one_or_neg_one (p := p) (a := 7) hSevenNe with hres | hnres
  · left
    have hzFixed : z ^ p = z :=
      ratioUnit_pow_prime_eq_self_of_legendre_eq_one hpOdd hSixP hres
    have hzPow : z ^ (p - 1) = 1 := by
      apply mul_right_cancel (b := z)
      rw [← pow_succ, Nat.sub_add_cancel hp.pos, hzFixed, one_mul]
    have hgammaPow : gamma ^ (p - 1) = 1 := by
      dsimp [gamma]
      rw [← pow_mul, mul_comm R (p - 1), pow_mul, hzPow, one_pow]
    have hdvd := orderOf_dvd_of_pow_eq_one hgammaPow
    rwa [horder] at hdvd
  · right
    have hzInv : z ^ p = z⁻¹ :=
      ratioUnit_pow_prime_eq_inv_of_legendre_eq_neg_one hpOdd hSixP hnres
    have hzPow : z ^ (p + 1) = 1 := by
      rw [pow_succ, hzInv, inv_mul_cancel]
    have hgammaPow : gamma ^ (p + 1) = 1 := by
      dsimp [gamma]
      rw [← pow_mul, mul_comm R (p + 1), pow_mul, hzPow, one_pow]
    have hdvd := orderOf_dvd_of_pow_eq_one hgammaPow
    rwa [horder] at hdvd

end BLSPrimality
