/-
Copyright (c) 2026 X contributors. All rights reserved.
-/
import Std

namespace XProof.Static

inductive Expr where
  | literal (value : Int)
  | staticVar (index : Nat)
  | runtimeVar (index : Nat)
  | add (left right : Expr)
  | letValue (value body : Expr)
deriving DecidableEq, Repr

abbrev Environment := Nat → Int

def extend (env : Environment) (value : Int) : Environment
  | 0 => value
  | i + 1 => env i

def eval (staticEnv runtimeEnv : Environment) : Expr → Int
  | .literal v => v
  | .staticVar i => staticEnv i
  | .runtimeVar i => runtimeEnv i
  | .add a b => eval staticEnv runtimeEnv a + eval staticEnv runtimeEnv b
  | .letValue v body =>
    eval staticEnv (extend runtimeEnv (eval staticEnv runtimeEnv v)) body

end XProof.Static
