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

def specialize (env : Environment) : Expr → Expr
  | .literal v => .literal v
  | .staticVar i => .literal (env i)
  | .runtimeVar i => .runtimeVar i
  | .add a b => .add (specialize env a) (specialize env b)
  | .letValue v body => .letValue (specialize env v) (specialize env body)

def RuntimeOnly : Expr → Prop
  | .literal _ | .runtimeVar _ => True
  | .staticVar _ => False
  | .add a b | .letValue a b => RuntimeOnly a ∧ RuntimeOnly b

theorem specialize_runtimeOnly (env : Environment) (e : Expr) :
    RuntimeOnly (specialize env e) := by
  induction e with
  | literal => trivial
  | staticVar => trivial
  | runtimeVar => trivial
  | add a b ha hb => exact ⟨ha, hb⟩
  | letValue a b ha hb => exact ⟨ha, hb⟩

theorem specialize_preserves_eval (s r : Environment) (e : Expr) :
    eval s r (specialize s e) = eval s r e := by
  induction e generalizing r with
  | literal => rfl
  | staticVar => rfl
  | runtimeVar => rfl
  | add a b ha hb => simp only [specialize, eval, ha, hb]
  | letValue v body hv hb => simp only [specialize, eval, hv, hb]

end XProof.Static
