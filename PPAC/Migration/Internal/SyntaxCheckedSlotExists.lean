import PPAC.Migration.Internal.FormulaCodeTypedDataKnown

/-! 从任意实际Checked公式消去谓词，仅保留真实槽位存在量词。 -/
namespace PPAC.Migration.Internal.SyntaxCheckedSlotExists
open Source SourceAlgebra SourceLogic SyntaxSlotSyntax SyntaxCheckedFieldSyntax MinimalPredicates ReplacementPredicates

def existsSlot {m} (g : Fin m) (j : Nat) : Formula m := .ex (slot g.castSucc j (Fin.last m))

theorem existsSlot_rename {m n} (g : Fin m) (j : Nat) (r : Fin m → Fin n) :
    (existsSlot g j).rename r = existsSlot (r g) j := by
  simp only [existsSlot, Formula.rename, slot_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem of_checked {n m} {Γ : Context m} (P : Formula (n+1)) (ρ : Fin n → Fin m) (g : Fin m) (j : Nat)
    (hh : Derives Γ (checked P ρ g j)) : Derives Γ (existsSlot g j) := by
  let B := (slot g.castSucc j (Fin.last m)).conj (pred P (paramsUp ρ) (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  change Derives Γ (.ex B) at hh
  apply Derives.exE hh
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho : Derives Δ (existsSlot g.castSucc j) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, slot_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjL hB
  simpa only [Formula.raise, existsSlot_rename] using ho
end PPAC.Migration.Internal.SyntaxCheckedSlotExists
