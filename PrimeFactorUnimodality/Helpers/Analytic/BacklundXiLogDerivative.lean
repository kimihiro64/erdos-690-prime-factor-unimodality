import PrimeFactorUnimodality.Helpers.Analytic.BacklundAuxiliary
import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiLogDerivative

/-! # Separating the Backlund surrogate and gamma contributions

On the nonvanishing right half-plane away from one, the xi logarithmic
derivative is the surrogate logarithmic derivative plus the explicit
digamma and constant pi terms. This connects the actual xi counting
contour to the horizontal surrogate estimate. It applies inside the
critical strip when the contour avoids zeros, not only for real part
greater than one. No bound on the remaining gamma integrals is asserted.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Filter
open scoped Topology

/-- Away from the pole, the entire surrogate absorbs the simple zeta pole term. -/
theorem logDeriv_backlundSurrogate_eq {s : ℂ} (hs1 : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    logDeriv Backlund.zetaSurrogate s = 1 / (s - 1) + logDeriv riemannZeta s := by
  have he : Backlund.zetaSurrogate =ᶠ[𝓝 s] (fun z => (z - 1) * riemannZeta z) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
    change z ≠ 1 at hz
    simp only [Backlund.zetaSurrogate, ite_eq_right hz]
  rw [(logDeriv_congr_nhds he).eq_of_nhds]
  rw [logDeriv_fun_mul (f := fun z : ℂ => z - 1) (g := riemannZeta) s
    (sub_ne_zero.mpr hs1) hζ (differentiableAt_id.sub_const 1) (differentiableAt_riemannZeta hs1)]
  simp [logDeriv_apply]

/-- The xi contour integrand separates into the surrogate and explicit gamma terms. -/
theorem logDeriv_xi_eq_backlundSurrogate {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    logDeriv riemannXi s = logDeriv Backlund.zetaSurrogate s -
      (1 / 2 : ℂ) * Real.log Real.pi + (1 / 2 : ℂ) * digamma (s / 2 + 1) := by
  have h := neg_logDeriv_riemannZeta_eq_xi_of_re_pos hs hs1 hζ
  rw [logDeriv_backlundSurrogate_eq hs1 hζ]
  simp only [logDeriv_apply] at *
  linear_combination h

end

end PrimeFactorUnimodality
