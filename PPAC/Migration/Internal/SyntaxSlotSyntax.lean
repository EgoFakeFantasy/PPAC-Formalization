import PPAC.Migration.Internal.SyntaxNodeFields

/-! 指定数码位置的实际字段值，见证索引仍由对象存在量词取得。 -/
namespace PPAC.Migration.Internal.SyntaxSlotSyntax
open Source SourceAlgebra SourceLogic GraphSyntax SyntaxNumeralSyntax

def body {m} (g : Fin m) (j : Nat) (y : Fin m) : Formula (m+1) :=
  (numeral j (Fin.last m)).conj (edge g.castSucc (Fin.last m) y.castSucc)
def slot {m} (g : Fin m) (j : Nat) (y : Fin m) : Formula m := .ex (body g j y)

theorem slot_rename {m n} (g : Fin m) (j : Nat) (y : Fin m) (r : Fin m → Fin n) :
    (slot g j y).rename r = slot (r g) j (r y) := by
  simp only [slot, body, Formula.rename, numeral_rename, edge_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_slot {m} {Γ : Context m} (g : Fin m) (j : Nat) (y i : Fin m)
    (hi : Derives Γ (numeral j i)) (he : Derives Γ (edge g i y)) : Derives Γ (slot g j y) := by
  apply Derives.exI i
  simp only [body, Formula.instantiate, Formula.rename, numeral_rename, edge_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hi he

theorem eliminate_slot {m} {Γ : Context m} (g : Fin m) (j : Nat) (y : Fin m) (q : Formula m)
    (hs : Derives Γ (slot g j y))
    (hc : Derives (Context.add (body g j y) (Context.image Formula.raise Γ)) q.raise) : Derives Γ q :=
  .exE hs hc
end PPAC.Migration.Internal.SyntaxSlotSyntax
