import Concu.Basic

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
