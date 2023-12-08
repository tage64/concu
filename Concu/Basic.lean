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
