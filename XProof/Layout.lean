/-
Copyright (c) 2026 X contributors. All rights reserved.
-/
import Std

namespace XProof.Layout

variable {α : Type} {rows fields : Nat}

abbrev AoS (rows fields : Nat) (α : Type) := Fin rows → Fin fields → α

abbrev SoA (rows fields : Nat) (α : Type) := Fin fields → Fin rows → α

def transpose (data : AoS rows fields α) : SoA rows fields α :=
  fun field row => data row field

def gather (data : SoA rows fields α) : AoS rows fields α :=
  fun row field => data field row

theorem gather_transpose (data : AoS rows fields α) : gather (transpose data) = data := rfl

theorem transpose_gather (data : SoA rows fields α) : transpose (gather data) = data := rfl

end XProof.Layout
