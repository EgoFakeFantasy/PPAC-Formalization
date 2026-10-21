import PPAC.Migration.Internal.StructuralListCheckTerminationPoint

/-! 每个内部自然码的实际tail执行终止；沿原严格尾码界作对象成员归纳。 -/
namespace PPAC.Migration.Internal.StructuralListCheckTermination
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListCheckSyntax
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (BoundedInduction.progressive StructuralListCheckSyntax.matrix (fun _ : Fin 1 => w) w) := by
  simp only [BoundedInduction.progressive, BoundedInduction.below, StructuralListCheckSyntax.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) w.castSucc
  let I := earlier w.castSucc (Fin.last m)
  let Δ := Context.add I (Context.add M (Context.image Formula.raise Γ))
  have hZ1 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.rename hZ Fin.castSucc) M) I
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using add (add (Derives.rename Fin.castSucc hw) M) I
  exact StructuralListCheckTerminationPoint.from_earlier hZ1 _ _ hw1 (.hyp (Or.inl rfl))

theorem all_terminate {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (eventually w.castSucc (Fin.last m)))) := by
  have h := BoundedInduction.induction_on_set StructuralListCheckSyntax.matrix (fun _ : Fin 1 => w) w
    (ZFContext.separation hZ StructuralListCheckSyntax.matrix.neg) (ZFContext.arithmetic hZ).base.foundation (progressive hZ w hw)
  simpa only [BoundedInduction.holds, StructuralListCheckSyntax.matrix_pred, paramsUp] using h

theorem at_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) : Derives Γ (eventually w n) := by
  have h : Derives Γ ((Formula.mem n w).imp (eventually w n)) := by
    simpa only [Formula.instantiate, Formula.rename, eventually_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE n (all_terminate hZ w hw)
  exact .impE h hn
end PPAC.Migration.Internal.StructuralListCheckTermination
