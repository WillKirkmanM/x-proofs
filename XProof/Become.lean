/-
Copyright (c) 2026 X contributors. All rights reserved.
-/
import Std

namespace XProof.Become

structure ABI where
  parameters : List Nat
  result : Nat
  callingConvention : Nat
  storageAttributes : List Nat
  throws : Bool
deriving DecidableEq, Repr

structure Function where
  symbol : Nat
  abi : ABI
deriving DecidableEq, Repr

structure State where
  current : Function
  continuation : List Function
deriving DecidableEq, Repr

def depth (s : State) : Nat := s.continuation.length + 1

structure Request where
  target : Function
  direct : Bool
  tailPosition : Bool
  callerLocalOrigin : Bool
deriving DecidableEq, Repr

def Allowed (s : State) (r : Request) : Prop :=
  s.current.abi = r.target.abi ∧ r.direct = true ∧
  r.tailPosition = true ∧ r.callerLocalOrigin = false

instance (s : State) (r : Request) : Decidable (Allowed s r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def transfer (s : State) (r : Request) : Option State :=
  if Allowed s r then some { s with current := r.target } else none

theorem transfer_iff (s t : State) (r : Request) :
    transfer s r = some t ↔ Allowed s r ∧ t = { s with current := r.target } := by
  unfold transfer
  split <;> simp_all [eq_comm]

theorem transfer_preserves_continuation (s t : State) (r : Request)
    (h : transfer s r = some t) : t.continuation = s.continuation := by
  obtain ⟨_, rfl⟩ := (transfer_iff s t r).mp h
  rfl

theorem transfer_preserves_depth (s t : State) (r : Request)
    (h : transfer s r = some t) : depth t = depth s := by
  simp only [depth, transfer_preserves_continuation s t r h]

theorem transfer_preserves_abi (s t : State) (r : Request)
    (h : transfer s r = some t) : t.current.abi = s.current.abi := by
  obtain ⟨ha, rfl⟩ := (transfer_iff s t r).mp h
  exact ha.1.symm

inductive Transfers : State → State → Prop where
  | refl (s : State) : Transfers s s
  | step {s t u : State} (r : Request) :
    transfer s r = some t → Transfers t u → Transfers s u

theorem transfers_constant_stack {s t : State} (h : Transfers s t) :
    depth t = depth s := by
  induction h with
  | refl => rfl
  | step r ht _ ih => exact ih.trans (transfer_preserves_depth _ _ r ht)

end XProof.Become
