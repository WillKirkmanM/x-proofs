/-
Copyright (c) 2026 X contributors. All rights reserved.
-/
import Std

namespace XProof.Pure

inductive Expr where
  | literal (value : Nat)
  | localRead
  | globalRead
  | localWrite (value : Nat)
  | globalWrite (value : Nat)
  | sequence (first second : Expr)
  | call (body : Expr)
deriving DecidableEq, Repr

structure Result where
  value : Nat
  localState : Nat
  world : Nat
deriving DecidableEq, Repr

def check : Expr → Bool
  | .literal _ | .localRead | .localWrite _ => true
  | .globalRead | .globalWrite _ => false
  | .sequence first second => check first && check second
  | .call body => check body

def eval : Expr → Nat → Nat → Result
  | .literal n, localState, world => ⟨n, localState, world⟩
  | .localRead, localState, world => ⟨localState, localState, world⟩
  | .globalRead, localState, world => ⟨world, localState, world⟩
  | .localWrite n, _, world => ⟨n, n, world⟩
  | .globalWrite n, localState, _ => ⟨n, localState, n⟩
  | .sequence first second, localState, world =>
    let result := eval first localState world
    eval second result.localState result.world
  | .call body, localState, world => eval body localState world

end XProof.Pure
