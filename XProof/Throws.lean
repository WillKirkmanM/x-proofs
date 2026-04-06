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

end XProof.Throws
