import Lean.Elab.BuiltinEvalCommand
import Lean.LibrarySuggestions.Basic

/-!
# Project Lean configuration

Lean 4.34's optional premise-selection exporter runs under a fixed recursion
limit that cannot be raised by a source-file option.  Some closed certificate
signatures in this project exceed that auxiliary limit even though the kernel
checks them normally.  Project theorems are therefore omitted from the
suggestion index.  This changes neither declaration visibility nor proof
checking; it only prevents indexing them as automated tactic suggestions.
-/

run_cmd
  Lean.modifyEnv fun environment =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry
      environment "PrimeFactorUnimodality"
