import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime

inductive prod_num
| p0 : prod_num
| pli : Finset (Nat × prod_num) → prod_num

namespace prod_num

/-- Custom equality for `prod_num` that treats missing indices as zero. -/
def prod_eq : prod_num → prod_num → Prop
| p0, _ => True
| _, p0 => True
| pli factors1, pli factors2 =>
  ∀ prime, factors1.lookup prime = factors2.lookup prime

/-- Define equivalence relation for `prod_eq`. -/
instance : Setoid prod_num :=
  ⟨prod_eq,
   ⟨fun x => by cases x; simp, -- Reflexivity
    fun x y hxy => by cases x; cases y; simp at hxy; exact Eq.symm hxy, -- Symmetry
    fun x y z hxy hyz => by cases x; cases y; cases z; simp at *; exact Eq.trans hxy hyz⟩⟩
