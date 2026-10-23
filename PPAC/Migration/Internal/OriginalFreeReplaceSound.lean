import PPAC.Migration.Internal.LookupExecutionTransport

/-! 原freeReplace矩阵及存在赋值应用的可靠性，查找前提直接回到既有原轨迹定理。 -/
namespace PPAC.Migration.Internal.OriginalFreeReplaceSound
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornApplicationSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation.ObjectSyntaxTransform (freeReplace varCode)

def fields : Fin 5 → Expr 4 := HornRowFields.five (.literal 3) (.var 0) (.var 1) (varCode true (.var 2)) (.var 3)

theorem actual_head : freeReplace.head = Expr.node (.literal 1) (List.ofFn fields) := rfl

theorem actual_premise : freeReplace.premises = [OriginalLookupExpr.premiseExpr] := rfl

theorem premise_execution {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (hc : Derives Γ (HornLookupSoundSyntax.closed w R))
    (hp : Derives Γ (HornRuleSyntax.premise OriginalLookupExpr.premiseExpr w R env)) :
    Derives Γ (LookupTableExecutionSyntax.executed w (env 1) (env 2) (env 3)) := by
  let B := (graph OriginalLookupExpr.premiseExpr w.castSucc (fun i => (env i).castSucc) (Fin.last m)).conj (.mem (Fin.last m) R.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hp
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (environmentNat 4 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 4 w env Fin.castSucc) (under hn B)
  have hc1 : Derives Δ (HornLookupSoundSyntax.closed w.castSucc R.castSucc) := of_eq (HornLookupSoundSyntax.closed_rename w R Fin.castSucc) (under hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hr := Derives.impE (.conjL (OriginalLookupExpr.premise_iff hZ1 _ _ _ hw1 hn1)) (.conjL hB)
  have ho := HornLookupSoundInduction.sound hZ1 _ _ _ _ _ _ hw1 hc1 hr (.conjR hB)
  exact of_eq (LookupTableExecutionSyntax.executed_rename w (env 1) (env 2) (env 3) Fin.castSucc).symm ho

theorem matrix_execution {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r R idx : Fin m)
    (env : Fin 4 → Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat 4 w env)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3)))
    (hclosed : Derives Γ (HornLookupSoundSyntax.closed w R))
    (hm : Derives Γ (HornRuleSyntax.matrix freeReplace w r R env)) :
    Derives Γ (LookupTableExecutionSyntax.executed w (xs 2) idx (xs 4)) := by
  have hg : Derives Γ (graph (Expr.node (.literal 1) (List.ofFn fields)) w env r) := .conjL hm
  have hf2 := HornRowFields.field_graph hZ 1 fields w r env xs 2 hw hn hg hc
  have hf3 := HornRowFields.field_graph hZ 1 fields w r env xs 3 hw hn hg hc
  have hf4 := HornRowFields.field_graph hZ 1 fields w r env xs 4 hw hn hg hc
  have hi : Derives Γ (graph (.var 2) w env (env 2)) := .conjI (environmentNat_at w env hn 2) (.eqRefl _)
  have hcode := HornVariableValue.graph_code hZ false (.var 2) w (env 2) (xs 3) env hw hn hi hf3
  have hei := SyntaxVariableDecode.index_eq hZ false w (env 2) idx (xs 3) hw hcode hv
  have he := premise_execution hZ w R env hw hn hclosed (.conjL (.conjR (.conjR hm)))
  exact LookupExecutionTransport.fields_subst w (env 1) (xs 2) (env 2) idx (env 3) (xs 4) (eq_symm (.conjR hf2)) hei (eq_symm (.conjR hf4)) he

theorem application_execution {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r R idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3)))
    (hclosed : Derives Γ (HornLookupSoundSyntax.closed w R)) (ha : Derives Γ (application freeReplace w r R)) :
    Derives Γ (LookupTableExecutionSyntax.executed w (xs 2) idx (xs 4)) := by
  let B := body freeReplace w r R
  let Δ := Context.add B (raisedContext 4 Γ)
  apply HornApplicationRules.eliminate_application freeReplace w r R _ ha
  have hZ1 := HornBinderRules.zf_body 4 hZ B
  have hw1 : Derives Δ (omega (old 4 w)) := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw B)
  have hc1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 (old 4 w) (fun i => old 4 (xs i)) (old 4 r)) := of_eq
    (SyntaxNodeSyntax.constructor_rename 5 1 w xs r (old 4)) (HornBinderRules.under_body 4 hc B)
  have hv1 : Derives Δ (SyntaxVariableSyntax.code false (old 4 w) (old 4 idx) (old 4 (xs 3))) := of_eq
    (SyntaxVariableSyntax.code_rename false w idx (xs 3) (old 4)) (HornBinderRules.under_body 4 hv B)
  have hclosed1 : Derives Δ (HornLookupSoundSyntax.closed (old 4 w) (old 4 R)) := of_eq
    (HornLookupSoundSyntax.closed_rename w R (old 4)) (HornBinderRules.under_body 4 hclosed B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := matrix_execution hZ1 _ _ _ _ _ _ hw1 (.conjL hB) hc1 hv1 hclosed1 (.conjR (.conjR hB))
  exact of_eq (LookupTableExecutionSyntax.executed_rename w (xs 2) idx (xs 4) (old 4)).symm ho

end PPAC.Migration.Internal.OriginalFreeReplaceSound
