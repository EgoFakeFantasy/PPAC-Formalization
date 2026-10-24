import PPAC.Migration.Internal.SmallModeArgumentsRun
import PPAC.Migration.Internal.SmallModeArgumentValuePoint

/-! 原Separation／Foundation在全部内部列表码上关闭成员归纳；不保留Earlier前提。 -/
namespace PPAC.Migration.Internal.SmallModeArgumentValueInduction
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalArgumentValueSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ReplacementPredicates (paramsUp)

def matrix {m} (w mode depth parameter a b c d : Fin m) : Formula (m+1) :=
  property w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc c.castSucc d.castSucc (Fin.last m)

theorem matrix_pred {m j} (w mode depth parameter a b c d : Fin m) (ρ : Fin m → Fin j) (x : Fin j) :
    MinimalPredicates.pred (matrix w mode depth parameter a b c d) ρ x = property (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ a) (ρ b) (ρ c) (ρ d) x := by
  simp only [matrix, MinimalPredicates.pred, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter a b c d : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (Formula.mem depth w))
    (hp : Derives Γ (Formula.mem parameter w))
    (hc : Derives Γ (SyntaxTermSyntax.contexts w c d))
    (hpr : Derives Γ (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d))
    : Derives Γ (BoundedInduction.progressive (matrix w mode depth parameter a b c d) id w) := by
  simp only [BoundedInduction.progressive, BoundedInduction.below, matrix_pred, paramsUp, id_eq]
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) w.castSucc
  let I := earlier w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc c.castSucc d.castSucc (Fin.last m)
  let Δ := Context.add I (Context.add M (Context.image Formula.raise Γ))
  have hZ1 := ZFContext.add (ZFContext.add (ZFContext.rename hZ Fin.castSucc) M) I
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [omega_rename]) (add (add (Derives.rename Fin.castSucc hw) M) I)
  have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral modeIndex mode.castSucc) := of_eq (by simp only [SyntaxNumeralSyntax.numeral_rename]) (add (add (Derives.rename Fin.castSucc hm) M) I)
  have hd1 : Derives Δ (Formula.mem depth.castSucc w.castSucc) := of_eq (by simp only [Formula.rename]) (add (add (Derives.rename Fin.castSucc hd) M) I)
  have hp1 : Derives Δ (Formula.mem parameter.castSucc w.castSucc) := of_eq (by simp only [Formula.rename]) (add (add (Derives.rename Fin.castSucc hp) M) I)
  have hc1 : Derives Δ (SyntaxTermSyntax.contexts w.castSucc c.castSucc d.castSucc) := of_eq (by simp only [SyntaxTermSyntax.contexts_rename]) (add (add (Derives.rename Fin.castSucc hc) M) I)
  have hpr1 : Derives Δ (OriginalNumericTermValueSyntax.promise w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc c.castSucc d.castSucc) := of_eq (by simp only [OriginalNumericTermValueSyntax.promise_rename]) (add (add (Derives.rename Fin.castSucc hpr) M) I)
  exact SmallModeArgumentValuePoint.property_from_earlier hZ1 modeIndex hSmall w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc c.castSucc d.castSucc (Fin.last m) hw1 hm1 hd1 hp1 hc1 hpr1 (.hyp (Or.inl rfl))

theorem all_properties {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter a b c d : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (Formula.mem depth w))
    (hp : Derives Γ (Formula.mem parameter w))
    (hc : Derives Γ (SyntaxTermSyntax.contexts w c d))
    (hpr : Derives Γ (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d))
    : Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc c.castSucc d.castSucc (Fin.last m)))) := by
  have hh := BoundedInduction.induction_on_set (matrix w mode depth parameter a b c d) id w
    (ZFContext.separation hZ (matrix w mode depth parameter a b c d).neg) (ZFContext.arithmetic hZ).base.foundation
    (progressive hZ modeIndex hSmall w mode depth parameter a b c d hw hm hd hp hc hpr)
  exact of_eq (by simp only [BoundedInduction.holds, matrix_pred, paramsUp, id_eq]) hh

theorem at_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter a b c d n : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (Formula.mem depth w))
    (hp : Derives Γ (Formula.mem parameter w))
    (hc : Derives Γ (SyntaxTermSyntax.contexts w c d))
    (hpr : Derives Γ (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d))
    (hn : Derives Γ (.mem n w)) : Derives Γ (property w mode depth parameter a b c d n) := by
  have hh : Derives Γ ((Formula.mem n w).imp (property w mode depth parameter a b c d n)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.allE n (all_properties hZ modeIndex hSmall w mode depth parameter a b c d hw hm hd hp hc hpr))
  exact .impE hh hn

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter a b c d n k : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (Formula.mem depth w))
    (hp : Derives Γ (Formula.mem parameter w))
    (hc : Derives Γ (SyntaxTermSyntax.contexts w c d))
    (hpr : Derives Γ (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n)) : Derives Γ (fiber w mode depth parameter k c d n) :=
  property_at w mode depth parameter a b c d n k
    (at_natural hZ modeIndex hSmall w mode depth parameter a b c d n hw hm hd hp hc hpr (.conjL (.conjL (.conjR (.conjR hL))))) hL

end PPAC.Migration.Internal.SmallModeArgumentValueInduction
