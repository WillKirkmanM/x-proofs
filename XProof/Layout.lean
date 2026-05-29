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

def writeAoS (data : AoS rows fields α) (row : Fin rows) (field : Fin fields) (value : α) :
    AoS rows fields α :=
  fun r f => if r = row ∧ f = field then value else data r f

def writeSoA (data : SoA rows fields α) (row : Fin rows) (field : Fin fields) (value : α) :
    SoA rows fields α :=
  fun f r => if r = row ∧ f = field then value else data f r

theorem transpose_write (data : AoS rows fields α) (row : Fin rows) (field : Fin fields)
    (value : α) :
    transpose (writeAoS data row field value) = writeSoA (transpose data) row field value := rfl

theorem read_after_write (data : SoA rows fields α) (row : Fin rows) (field : Fin fields)
    (value : α) : writeSoA data row field value field row = value := by simp [writeSoA]

theorem other_projection_unchanged (data : SoA rows fields α) (row otherRow : Fin rows)
    (field otherField : Fin fields) (value : α)
    (different : otherRow ≠ row ∨ otherField ≠ field) :
    writeSoA data row field value otherField otherRow = data otherField otherRow := by
  rcases different with different | different <;> simp [writeSoA, different]

/-- The caller supplies the complete RHS snapshot before replacement. -/
def replaceAoS (data : AoS rows fields α) (row : Fin rows) (snapshot : Fin fields → α) :
    AoS rows fields α := fun r f => if r = row then snapshot f else data r f

def replaceSoA (data : SoA rows fields α) (row : Fin rows) (snapshot : Fin fields → α) :
    SoA rows fields α := fun f r => if r = row then snapshot f else data f r

theorem transpose_replace (data : AoS rows fields α) (row : Fin rows)
    (snapshot : Fin fields → α) :
    transpose (replaceAoS data row snapshot) = replaceSoA (transpose data) row snapshot := rfl

theorem gather_replacement (data : SoA rows fields α) (row : Fin rows)
    (snapshot : Fin fields → α) : gather (replaceSoA data row snapshot) row = snapshot := by
  funext field
  simp [gather, replaceSoA]

def readAoS (data : AoS rows fields α) (row field : Nat) : Option α :=
  if hr : row < rows then
    if hf : field < fields then some (data ⟨row, hr⟩ ⟨field, hf⟩) else none
  else none

def readSoA (data : SoA rows fields α) (row field : Nat) : Option α :=
  if hr : row < rows then
    if hf : field < fields then some (data ⟨field, hf⟩ ⟨row, hr⟩) else none
  else none

theorem checked_read_layout_equivalent (data : AoS rows fields α) (row field : Nat) :
    readSoA (transpose data) row field = readAoS data row field := rfl

theorem out_of_bounds_read (data : SoA rows fields α) (row field : Nat)
    (outside : rows ≤ row ∨ fields ≤ field) : readSoA data row field = none := by
  rcases outside with outside | outside
  · simp [readSoA, Nat.not_lt.mpr outside]
  · simp [readSoA, Nat.not_lt.mpr outside]

theorem checked_read_some_iff (data : SoA rows fields α) (row field : Nat) :
    (∃ value, readSoA data row field = some value) ↔ row < rows ∧ field < fields := by
  unfold readSoA
  split
  next hr =>
    split
    next hf => simp [hr, hf]
    next hf => simp [hf]
  next hr => simp [hr]

def checkedWrite (data : SoA rows fields α) (row field : Nat) (value : α) :
    Option (SoA rows fields α) :=
  if hr : row < rows then
    if hf : field < fields then some (writeSoA data ⟨row, hr⟩ ⟨field, hf⟩ value) else none
  else none

theorem out_of_bounds_write (data : SoA rows fields α) (row field : Nat) (value : α)
    (outside : rows ≤ row ∨ fields ≤ field) : checkedWrite data row field value = none := by
  rcases outside with outside | outside
  · simp [checkedWrite, Nat.not_lt.mpr outside]
  · simp [checkedWrite, Nat.not_lt.mpr outside]

theorem checked_read_after_write {data result : SoA rows fields α} {row field : Nat} {value : α}
    (success : checkedWrite data row field value = some result) :
    readSoA result row field = some value := by
  unfold checkedWrite at success
  split at success
  next hr =>
    split at success
    next hf =>
      cases Option.some.inj success
      simp [readSoA, hr, hf, writeSoA]
    next => contradiction
  next => contradiction

inductive Policy where
  | aos | soa | auto
deriving DecidableEq

def effectivePolicy : Policy → Policy
  | .auto => .aos
  | policy => policy

theorem auto_uses_aos : effectivePolicy .auto = .aos := rfl

end XProof.Layout
