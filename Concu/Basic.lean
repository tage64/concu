import Mathlib.Data.Finset.Basic
import Std.Logic

structure DataStructure : Type _ where
  σ : Type
  init : σ
  Method : Type → Type
  guard : Method Ret → Ret → σ → Prop
  [decGuard (met : Method Ret) (ret) (s) : Decidable $ guard met ret s]
  rule (met : Method Ret) (ret) (s) : guard met ret s → σ
attribute [instance] DataStructure.decGuard

namespace DataStructure
section
variable (ρ : DataStructure)

abbrev Operation :=
  (Ret : Type) × ρ.Method Ret × Ret

def Trace :=
  List ρ.Operation

def validTrace (s : ρ.σ) : ρ.Trace → Prop
  | .nil => True
  | (⟨_, met, ret⟩ :: ops) =>
    ∃ (g : ρ.guard met ret s), validTrace (ρ.rule met ret s g) ops

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

def Traces : ρ.Trace → Prop :=
  ρ.validTrace ρ.init
end
end DataStructure

namespace Register
section
variable (α : Type) [Inhabited α] [DecidableEq α]

inductive Method : Type → Type
| read : Method α
| write : α → Method Unit

def Register : DataStructure where
  σ := α
  init := default
  Method := Method α
  guard
    | .read, ret, s => ret = s
    | .write _, _, _ => True
  decGuard
    | .read, ret, s => if h : ret = s
      then isTrue h
      else isFalse h
    | .write _, _, _ => isTrue trivial
  rule
    | .write x, _, _, _ => x
    | .read, _, s, _ => s
end
end Register
export Register (Register)

namespace Set
section
variable (α : Type) [DecidableEq α]

inductive Method : Type → Type where
| contains : α → Method Bool
| add : α → Method Bool
| remove : α → Method Bool

def Set : DataStructure where
  σ := Finset α
  init := ∅
  Method := Method α
  guard
    | .contains x, true, s 
    | .add x, false, s
    | .remove x, true, s
      => x ∈ s
    | .contains x, false, s
    | .add x, true, s
    | .remove x, false, s
      => x ∉ s
  decGuard
    | .contains _, true, _ 
    | .add _, false, _
    | .remove _, true, _
    | .contains _, false, _
    | .add _, true, _
    | .remove _, false, _
      => inferInstance
  rule
    | .add x, true, s, hIn => s.cons x hIn
    | .remove x, true, s, _ => s.erase x
    | .contains _, _, s, _
    | .add _, false, s, _
    | .remove _, false, s, _
      => s
end
end Set
export Set (Set)
    

