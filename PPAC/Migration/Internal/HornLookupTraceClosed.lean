import PPAC.Migration.Internal.HornLookupTailPositive

/-! 原Separation的实际规范集合在完整原规则表下闭合，涵盖其所有内部成员。 -/
namespace PPAC.Migration.Internal.HornLookupTraceClosed
open Source SourceAlgebra SourceLogic OmegaSyntax HornLookupRowSyntax
open HornLookupTraceValueSyntax (value value_rename goodBody goodRow value_at)
open SyntaxRenameQuerySyntax (of_eq)

theorem execution_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R n i y r : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (value w R)) (hr : Derives Γ (row w n i y r))
    (he : Derives Γ (LookupTableExecutionSyntax.executed w n i y)) : Derives Γ (HornStepSyntax.originalStep w r R) := by
  have hh := Derives.impE (.conjL (LookupTableRecursive.recursive_iff hZ w n i y hw)) he
  apply Derives.disjE (.conjR (.conjR hh))
  · exact HornLookupHeadPositive.step (ZFContext.add hZ _) w R n i y r (add hw _) (add hr _) (.hyp (Or.inl rfl))
  · exact HornLookupTailPositive.step (ZFContext.add hZ _) w R n i y r (add hw _) (add hv _) (add hr _) (.hyp (Or.inl rfl))

theorem member_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R r : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (value w R)) (hm : Derives Γ (.mem r R)) :
    Derives Γ (HornStepSyntax.originalStep w r R) := by
  have hg := Derives.conjR (.impE (.conjL (value_at w R r hv)) hm)
  let B := goodBody w r
  let Δ := Context.add B (HornBinderSyntax.raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 B (HornStepSyntax.originalStep w r R) hg
  have hZ3 := HornBinderRules.zf_body 3 hZ B
  have hw3 : Derives Δ (omega (HornBinderSyntax.old 3 w)) := of_eq (omega_rename w (HornBinderSyntax.old 3)) (HornBinderRules.under_body 3 hw B)
  have hv3 : Derives Δ (value (HornBinderSyntax.old 3 w) (HornBinderSyntax.old 3 R)) := of_eq (value_rename w R (HornBinderSyntax.old 3)) (HornBinderRules.under_body 3 hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := execution_step hZ3 _ _ _ _ _ _ hw3 hv3 (.conjL hB) (.conjR hB)
  exact of_eq (HornStepSyntax.originalStep_rename w r R (HornBinderSyntax.old 3)).symm ho

theorem closed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (value w R)) : Derives Γ (HornLookupSoundSyntax.closed w R) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) R.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw M)
  have hv1 : Derives Δ (value w.castSucc R.castSucc) := of_eq (value_rename w R Fin.castSucc) (under hv M)
  exact member_step (ZFContext.under hZ M) w.castSucc R.castSucc (Fin.last m) hw1 hv1 (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.HornLookupTraceClosed
