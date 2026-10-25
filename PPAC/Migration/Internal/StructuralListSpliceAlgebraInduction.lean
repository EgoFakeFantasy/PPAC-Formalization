import PPAC.Migration.Internal.StructuralListSpliceAlgebraStep

/-! Full original Separation and Foundation close the all-internal-code splice totality and uniqueness induction. -/
namespace PPAC.Migration.Internal.StructuralListSpliceAlgebraInduction
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSpliceAlgebraSyntax
open ReplacementPredicates (paramsUp)
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (BoundedInduction.progressive StructuralListSpliceAlgebraSyntax.matrix (fun _ : Fin 1 => w) w) := by
  simp only [BoundedInduction.progressive,BoundedInduction.below,StructuralListSpliceAlgebraSyntax.matrix_pred,paramsUp]
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) w.castSucc
  let I := earlier w.castSucc (Fin.last m)
  let Δ := Context.add I (Context.add M (Context.image Formula.raise Γ))
  have hZ1 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.rename hZ Fin.castSucc) M) I
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise,omega_rename] using add (add (Derives.rename Fin.castSucc hw) M) I
  exact StructuralListSpliceAlgebraStep.property_from_earlier hZ1 _ _ hw1 (.hyp (Or.inl rfl))

theorem all_properties {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc (Fin.last m)))) := by
  have h := BoundedInduction.induction_on_set StructuralListSpliceAlgebraSyntax.matrix (fun _ : Fin 1 => w) w
    (ZFContext.separation hZ StructuralListSpliceAlgebraSyntax.matrix.neg) (ZFContext.arithmetic hZ).base.foundation (progressive hZ w hw)
  simpa only [BoundedInduction.holds,StructuralListSpliceAlgebraSyntax.matrix_pred,paramsUp] using h

theorem at_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) : Derives Γ (property w n) := by
  have hh : Derives Γ ((Formula.mem n w).imp (property w n)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE n (all_properties hZ w hw))
  exact .impE hh hn

end PPAC.Migration.Internal.StructuralListSpliceAlgebraInduction
