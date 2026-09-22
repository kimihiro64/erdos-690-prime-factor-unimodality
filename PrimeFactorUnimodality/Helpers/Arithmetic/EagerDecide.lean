module
public import Lean.Elab.Tactic

set_option autoImplicit false

/-! # Eager kernel evaluation for closed Boolean certificates

The tactic emits an ordinary `of_decide_eq_true` proof. Its reflection argument
asks the kernel for eager evaluation; no external evaluator establishes truth.
-/

public meta section

open Lean Meta Elab Tactic in
elab "eager_decide" : tactic => liftMetaFinishingTactic fun goal => do
  let p ← instantiateMVars (← goal.getType)
  if p.hasFVar || p.hasMVar then
    throwError "eager_decide requires a closed proposition"
  let d ← mkDecide p
  let refl ← mkEqRefl (mkConst ``Bool.true)
  let eager ← mkAppM ``eagerReduce #[refl]
  goal.assign (mkApp3 (mkConst ``of_decide_eq_true) p d.appArg! eager)
