import Concu.Basic
import Mathlib.Data.Finset.Basic

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
    

