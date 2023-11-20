structure DataStructure where
  σ : Type
  init : σ
  Method : Type → Type
  guard {α} : Method α → σ → Prop
  [decGuard {α} (mt : Method α) : DecidablePred $ guard mt]
  cmd {α} (m : Method α) (s : σ) : guard m s → α × σ
#check DataStructure

def DataStructure.Trace (struct : DataStructure) :=
  List ((α : Type) × struct.Method α)

def DataStructure.validTrace {struct : DataStructure} (s : struct.σ) : Trace struct → Prop
  | .nil => True
  | (⟨_, mthd⟩ :: xs) => ∃ g : struct.guard mthd s, validTrace (struct.cmd mthd s g).2 xs
