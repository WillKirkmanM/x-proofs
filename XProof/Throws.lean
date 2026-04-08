/-
Copyright (c) 2026 X contributors. All rights reserved.
-/
import Std

namespace XProof.Throws

inductive Outcome (α ε : Type) where
  | success (value : α)
  | error (error : ε)
deriving DecidableEq, Repr

structure Tagged (α ε : Type) where
  success : Bool
  value : Option α
  error : Option ε
deriving DecidableEq, Repr

def encode {α ε : Type} : Outcome α ε → Tagged α ε
  | .success a => ⟨true, some a, none⟩
  | .error e => ⟨false, none, some e⟩

def decode {α ε : Type} (t : Tagged α ε) : Option (Outcome α ε) :=
  if t.success then t.value.map Outcome.success else t.error.map Outcome.error

theorem decode_encode {α ε : Type} (o : Outcome α ε) :
    decode (encode o) = some o := by
  cases o <;> rfl

theorem encode_injective {α ε : Type} {a b : Outcome α ε}
    (h : encode a = encode b) : a = b := by
  have hd := congrArg decode h
  simpa only [decode_encode, Option.some.injEq] using hd

def propagate {α β ε : Type} (o : Outcome α ε) (next : α → Outcome β ε) :
    Outcome β ε :=
  match o with
  | .success value => next value
  | .error error => .error error

theorem propagate_error {α β ε : Type} (e : ε) (next : α → Outcome β ε) :
    propagate (.error e) next = .error e := rfl

theorem propagate_associative {α β γ ε : Type} (o : Outcome α ε)
    (f : α → Outcome β ε) (g : β → Outcome γ ε) :
    propagate (propagate o f) g = propagate o (fun a => propagate (f a) g) := by
  cases o <;> rfl

end XProof.Throws
