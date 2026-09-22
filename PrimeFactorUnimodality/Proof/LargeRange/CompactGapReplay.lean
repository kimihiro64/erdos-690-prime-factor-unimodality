module
public import Lean.Elab.Tactic
public import Lean.Meta.ReduceEval
public import PrimeFactorUnimodality.Proof.LargeRange.CompactGapCertificate

set_option autoImplicit false

/-! # Proof-producing replay of bounded Fermat rows

Intermediate residues are candidates computed during elaboration. Every block
of exponent bits is checked by the kernel before its theorem is reused.
-/

public meta section
open Lean Meta Elab Tactic

namespace PrimeFactorUnimodality

private def replayPower (n : Nat) : MetaM (Nat × Expr) := do
  let modulus := toExpr n
  let base := toExpr (3 : Nat)
  let e := n - 1
  let bitCount := e.log2 + 1
  let mut exponent := 0
  let mut residue := 1
  let mut proof := mkAppN (mkConst ``powModState_zero) #[base, modulus, eagerReflBoolTrue]
  for start in [0:bitCount:8192] do
    IO.eprintln s!"Fermat checkpoint {start}/{bitCount} bits"
    let width := min 8192 (bitCount - start)
    let block := (e >>> (bitCount - start - width)) % 2 ^ width
    let oldPrefix := exponent
    let oldResidue := residue
    for bit in (List.range width).reverse do
      let b := block.testBit bit
      exponent := 2 * exponent + if b then 1 else 0
      residue := residue * residue % n
      if b then residue := residue * 3 % n
    let next := mkAppN (mkConst ``powBitCheckpoint)
      #[base, modulus, toExpr oldPrefix, toExpr oldResidue, toExpr exponent,
        toExpr residue, toExpr block, toExpr width, proof, eagerReflBoolTrue]
    let type := mkAppN (mkConst ``PowModState)
      #[base, modulus, toExpr exponent, toExpr residue]
    proof := mkConst (← mkAuxLemma [] type next)
  return (residue, proof)

elab "replay_gap_fermat" : tactic => liftMetaFinishingTactic fun goal => do
  let target ← goal.getType
  unless target.isAppOfArity ``CompactGapComposites 1 do
    throwError "expected CompactGapComposites"
  let values ← reduceEval (α := List Nat) target.appArg!
  let mut proof := mkConst ``CompactGapComposites.nil
  let mut tail : List Nat := []
  for n in values.reverse do
    let (r, power) ← replayPower n
    if r == 1 then
      throwError "base-three Fermat test does not reject this candidate"
    let witness := mkAppN (mkConst ``compactGapFermat_sound)
      #[toExpr n, toExpr r, power, eagerReflBoolTrue]
    let type ← mkAppM ``Not #[← mkAppM ``Nat.Prime #[toExpr n]]
    let witness := mkConst (← mkAuxLemma [] type witness)
    proof := mkAppN (mkConst ``CompactGapComposites.cons) #[toExpr n, toExpr tail, witness, proof]
    tail := n :: tail
  goal.assign proof

end PrimeFactorUnimodality
