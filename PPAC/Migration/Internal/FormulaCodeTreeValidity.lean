import PPAC.Migration.Internal.FormulaCodeTreeValidityPoint

/-! 原Foundation与全Separation在内部ω上关闭成员归纳；全部内部类型码得到原树有效性。 -/
namespace PPAC.Migration.Internal.FormulaCodeTreeValidity
open Source SourceAlgebra SourceLogic OmegaSyntax FormulaCodeSyntax FormulaCodeTreeValiditySyntax
open StructuralTreeValiditySyntax (valid valid_rename)
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (BoundedInduction.progressive FormulaCodeTreeValiditySyntax.matrix (fun _ : Fin 1 => w) w) := by
  simp only [BoundedInduction.progressive, BoundedInduction.below, FormulaCodeTreeValiditySyntax.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) w.castSucc
  let I := earlier w.castSucc (Fin.last m)
  let Δ := Context.add I (Context.add M (Context.image Formula.raise Γ))
  have hZ1 : ZFContext.Evidence Δ :=
    ZFContext.add (ZFContext.add (ZFContext.rename hZ Fin.castSucc) M) I
  have hw1 : Derives Δ (omega w.castSucc) := by
    simpa only [omega_rename] using add (add (Derives.rename Fin.castSucc hw) M) I
  exact FormulaCodeTreeValidityPoint.property_from_earlier hZ1 w.castSucc (Fin.last m) hw1 (.hyp (Or.inl rfl))

theorem all_properties {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc (Fin.last m)))) := by
  have hh := BoundedInduction.induction_on_set FormulaCodeTreeValiditySyntax.matrix (fun _ : Fin 1 => w) w
    (ZFContext.separation hZ FormulaCodeTreeValiditySyntax.matrix.neg) (ZFContext.arithmetic hZ).base.foundation (progressive hZ w hw)
  simpa only [BoundedInduction.holds, FormulaCodeTreeValiditySyntax.matrix_pred, paramsUp] using hh

theorem code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (formulaCode w n b f)) : Derives Γ (valid w n) := by
  have hn := Derives.conjL (FormulaCodeProperties.guards w n b f hc)
  have hp : Derives Γ ((Formula.mem n w).imp (property w n)) := by
    simpa only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
      using Derives.allE n (all_properties hZ w hw)
  exact .impE (property_at w n b f (.impE hp hn)) hc

theorem reject_non_tree {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (valid w n).neg) : Derives Γ (formulaCode w n b f).neg := by
  apply Derives.impI
  exact .impE (add hb _) (code (ZFContext.add hZ _) w n b f (add hw _) (.hyp (Or.inl rfl)))

theorem decoded {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (formulaCode w n b f)) :
    Derives Γ (StructuralTreeValiditySyntax.decodedFiber w n) :=
  StructuralTreeDecode.exists_unique hZ w n hw (code hZ w n b f hw hc)

theorem children {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (formulaCode w n b f))
    (hs : Derives Γ (StructuralTreeOperatorSyntax.shape w n t p l g)) :
    Derives Γ (StructuralTreeValiditySyntax.validChildren w g) :=
  StructuralTreeEncodeReadback.children_of_shape hZ w n t p l g hw hs (code hZ w n b f hw hc)
end PPAC.Migration.Internal.FormulaCodeTreeValidity
