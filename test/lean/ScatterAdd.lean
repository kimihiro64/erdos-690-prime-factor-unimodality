import Mathlib.Tactic.FinCases
import PrimeFactorUnimodality.Mathlib.Data.Vector.ScatterAdd

/-! # Radix/grid interfaces, collisions and boundary cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Vector

variable {R : Type*} [AddCommMonoid R] {N : ℕ}

example (a : Vector R N) (rows : List (Fin N × R)) (k : Fin N) :
    (scatterAdd a rows)[k.val] =
      a[k.val] + (rows.map (fun p => if p.1 = k then p.2 else 0)).sum := by
  exact Vector.scatterAdd_get a rows k

example (a : Vector R N) (xs ys : List (Fin N × R)) :
    scatterAdd a (xs ++ ys) = scatterAdd (scatterAdd a xs) ys := by
  exact Vector.scatterAdd_append a xs ys

example : (Vector.replicate 3 (0 : ℤ)).scatterAdd
    [(0, 4), (2, -3), (0, 7)] = #v[11, 0, -3] := by decide

example (a : Vector R N) : a.scatterAdd [] = a := rfl

end

end PrimeFactorUnimodality.Tests
