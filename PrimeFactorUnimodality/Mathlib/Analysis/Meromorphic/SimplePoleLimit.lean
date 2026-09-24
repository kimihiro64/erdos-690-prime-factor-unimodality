/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Meromorphic.Order

/-! # Recognizing a simple pole from its nonzero residue limit

For a meromorphic function, a nonzero limit of `(z-p)*f(z)` forces order
exactly `-1`, rather than merely an upper bound on the pole order.
-/

open Filter
open scoped Topology

namespace MeromorphicAt

/-- A finite nonzero residue limit identifies a pole of order exactly one. -/
theorem order_eq_neg_one_of_tendsto {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {f : 𝕜 → 𝕜} {p c : 𝕜}
    (hf : MeromorphicAt f p) (hc : c ≠ 0)
    (ht : Tendsto (fun z => (z - p) * f z) (𝓝[≠] p) (𝓝 c)) :
    meromorphicOrderAt f p = (-1 : ℤ) := by
  have hi : MeromorphicAt (fun z : 𝕜 => z - p) p := by fun_prop
  have ho := (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero (hi.mul hf)).mp ⟨c, hc, ht⟩
  rw [meromorphicOrderAt_mul hi hf, meromorphicOrderAt_id_sub_const] at ho
  have hfin : meromorphicOrderAt f p ≠ ⊤ := by
    intro he
    simp [he] at ho
  lift meromorphicOrderAt f p to ℤ using hfin with n hn
  norm_cast at ho ⊢
  omega

end MeromorphicAt
