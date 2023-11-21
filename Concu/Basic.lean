import Aesop
import Std.Logic

structure RawDataStructure where
  σ : Type
  init : σ
  Method : Type → Type

structure RawDataStructure.Operation (ρ : RawDataStructure) where
  α : Type
  method : ρ.Method α
  ret : α

section
open RawDataStructure
structure DataStructure extends RawDataStructure : Type _ where
  guard : Operation self → σ → Prop
  [decGuard (op : Operation self) : DecidablePred $ guard op]
  rule (op : Operation self) (s : σ) : guard op s → σ
attribute [instance] DataStructure.decGuard
end
#check DataStructure

namespace DataStructure

def Trace (ρ : DataStructure) :=
  List ρ.Operation

def validTrace (ρ : DataStructure) (s : ρ.σ) : ρ.Trace → Prop
  | .nil => True
  | (op :: ops) =>
    ∃ (g : ρ.guard op s), ρ.validTrace (ρ.rule op s g) ops

private def exists_prop_decidable' {p} (P : p → Prop)
  [Decidable p] (_ : ∀ h, Decidable (P h)) : Decidable (∃ h, P h) :=
  exists_prop_decidable P
    
instance decValidTrace : Decidable (validTrace ρ s trace) := by
  unfold validTrace
  cases trace
  . simp; exact inferInstance
  . simp
    apply exists_prop_decidable'
    intro g
    apply decValidTrace

def Traces (ρ : DataStructure) : ρ.Trace → Prop :=
  ρ.validTrace ρ.init
end DataStructure
