import PPAC.Migration.Internal.SmallModeArgumentsRun
import PPAC.Migration.Internal.SmallModeArgumentFieldPoint

/-! 原Separation／Foundation关闭原Run₂全部内部索引的字段正确性归纳。 -/
namespace PPAC.Migration.Internal.SmallModeArgumentFieldInduction
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalArgumentFieldSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ReplacementPredicates (paramsUp)

def matrix {m} (w mode depth parameter a b : Fin m) : Formula (m+1) :=
  property w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc (Fin.last m)

theorem matrix_pred {m j} (w mode depth parameter a b : Fin m) (ρ : Fin m → Fin j) (x : Fin j) :
    MinimalPredicates.pred (matrix w mode depth parameter a b) ρ x = property (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ a) (ρ b) x := by
  simp only [matrix, MinimalPredicates.pred, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter a b : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (Formula.mem depth w))
    (hp : Derives Γ (Formula.mem parameter w))
    : Derives Γ (BoundedInduction.progressive (matrix w mode depth parameter a b) id w) := by
  simp only [BoundedInduction.progressive, BoundedInduction.below, matrix_pred, paramsUp, id_eq]
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) w.castSucc
  let I := earlier w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc (Fin.last m)
  let Δ := Context.add I (Context.add M (Context.image Formula.raise Γ))
  have hZ1 := ZFContext.add (ZFContext.add (ZFContext.rename hZ Fin.castSucc) M) I
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [omega_rename]) (add (add (Derives.rename Fin.castSucc hw) M) I)
  have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral modeIndex mode.castSucc) := of_eq (by simp only [SyntaxNumeralSyntax.numeral_rename]) (add (add (Derives.rename Fin.castSucc hm) M) I)
  have hd1 : Derives Δ (Formula.mem depth.castSucc w.castSucc) := of_eq (by simp only [Formula.rename]) (add (add (Derives.rename Fin.castSucc hd) M) I)
  have hp1 : Derives Δ (Formula.mem parameter.castSucc w.castSucc) := of_eq (by simp only [Formula.rename]) (add (add (Derives.rename Fin.castSucc hp) M) I)
  exact SmallModeArgumentFieldPoint.property_from_earlier hZ1 modeIndex hSmall w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc (Fin.last m) hw1 hm1 hd1 hp1 (.hyp (Or.inl rfl))

theorem all_properties {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter a b : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (Formula.mem depth w))
    (hp : Derives Γ (Formula.mem parameter w))
    : Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc (Fin.last m)))) := by
  have hh := BoundedInduction.induction_on_set (matrix w mode depth parameter a b) id w
    (ZFContext.separation hZ (matrix w mode depth parameter a b).neg) (ZFContext.arithmetic hZ).base.foundation
    (progressive hZ modeIndex hSmall w mode depth parameter a b hw hm hd hp)
  exact of_eq (by simp only [BoundedInduction.holds, matrix_pred, paramsUp, id_eq]) hh

theorem at_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter a b n : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (Formula.mem depth w))
    (hp : Derives Γ (Formula.mem parameter w))
    (hn : Derives Γ (.mem n w)) : Derives Γ (property w mode depth parameter a b n) := by
  have hh : Derives Γ ((Formula.mem n w).imp (property w mode depth parameter a b n)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.allE n (all_properties hZ modeIndex hSmall w mode depth parameter a b hw hm hd hp))
  exact .impE hh hn

theorem actual_fields {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter a b n k q : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (.mem depth w)) (hp : Derives Γ (.mem parameter w))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n))
    (hr : Derives Γ (OriginalTransformRowSyntax.run 2 w mode depth parameter n q)) : Derives Γ (fields w mode depth parameter k n q) :=
  property_at w mode depth parameter a b n k q
    (at_natural hZ modeIndex hSmall w mode depth parameter a b n hw hm hd hp (.conjL (.conjL (.conjR (.conjR hL))))) hL hr

end PPAC.Migration.Internal.SmallModeArgumentFieldInduction
