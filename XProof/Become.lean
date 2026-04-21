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

end XProof.Become
