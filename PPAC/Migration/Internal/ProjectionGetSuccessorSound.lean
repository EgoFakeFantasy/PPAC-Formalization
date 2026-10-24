import PPAC.Migration.Internal.ProjectionGetInductionSyntax
import PPAC.Migration.Internal.ProjectionTraceUnfold

/-! 在实际原根集合V中消去getTail子前提，严格前驱正确性只保留在局部后继步骤。 -/
namespace PPAC.Migration.Internal.ProjectionGetSuccessorSound
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax ProjectionGetInductionSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation

theorem tail_application {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i s y row V : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) (hs : Derives Γ (successor s i))
    (hc : Derives Γ (correct w i)) (hv : Derives Γ (ProjectionTraceSetSyntax.value w V))
    (hr : Derives Γ (ProjectionTraceSyntax.getRow w x s y row))
    (ha : Derives Γ (HornApplicationSyntax.application ObjectProjection.getTail w row V)) :
    Derives Γ (RawCodeGetSyntax.get w x s y) := by
  let B := HornApplicationSyntax.body ObjectProjection.getTail w row V
  let Δ := Context.add B (raisedContext 5 Γ)
  apply HornApplicationRules.eliminate_application ObjectProjection.getTail w row V _ ha
  have hZ5 := HornBinderRules.zf_body 5 hZ B
  have hw5 : Derives Δ (omega (old 5 w)) := of_eq (omega_rename w (old 5)) (HornBinderRules.under_body 5 hw B)
  have hi5 : Derives Δ (.mem (old 5 i) (old 5 w)) := HornBinderRules.under_body 5 hi B
  have hs5 : Derives Δ (successor (old 5 s) (old 5 i)) := of_eq (successor_rename s i (old 5)) (HornBinderRules.under_body 5 hs B)
  have hc5 : Derives Δ (correct (old 5 w) (old 5 i)) := of_eq (correct_rename w i (old 5)) (HornBinderRules.under_body 5 hc B)
  have hv5 : Derives Δ (ProjectionTraceSetSyntax.value (old 5 w) (old 5 V)) :=
    of_eq (ProjectionTraceSetSyntax.value_rename w V (old 5)) (HornBinderRules.under_body 5 hv B)
  have hr5 : Derives Δ (ProjectionTraceSyntax.getRow (old 5 w) (old 5 x) (old 5 s) (old 5 y) (old 5 row)) :=
    of_eq (ProjectionTraceSyntax.getRow_rename w x s y row (old 5)) (HornBinderRules.under_body 5 hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hn : Derives Δ (environmentNat 5 (old 5 w) (slot 5)) := .conjL hB
  have hh : Derives Δ (graph ObjectProjection.getTail.head (old 5 w) (slot 5) (old 5 row)) := .conjL (.conjR (.conjR hB))
  have hp : Derives Δ (HornRuleSyntax.premises ObjectProjection.getTail.premises (old 5 w) (old 5 V) (slot 5)) :=
    .conjR (.conjR (.conjR (.conjR hB)))
  have hchild := ProjectionGetLocal.tail_actual_child hZ5 _ _ _ hw5 hn hv5 hp
  have hg := HornNodeFields.field_3 hZ5 1 ProjectionGetConstructors.tailFields (old 5 w) (old 5 row) (slot 5)
    (SyntaxAtomSyntax.three (old 5 x) (old 5 s) (old 5 y)) 1 hw5 hn
    (of_eq (congrArg (fun e => graph e (old 5 w) (slot 5) (old 5 row)) ProjectionGetConstructors.tail_head) hh) hr5
  have hsucc := Derives.impE (.conjL (ProjectionRawPairExpr.successor_variable_iff (3 : Fin 5) (old 5 w) (old 5 s) (slot 5) hn)) hg
  have heq := StructuralNodeCore.predecessor_unique hZ5 (old 5 w) (old 5 s) (old 5 i) (slot 5 3) hw5 hi5 hs5 hsucc
  have hcorrect := index_subst (old 5 w) (old 5 i) (slot 5 3) heq hc5
  have hraw := Derives.conjR (Derives.impE (.conjL (at_value _ _ (slot 5 2) (slot 5 4) hcorrect)) hchild)
  have ho := ProjectionGetLocal.tail_sound_from_child hZ5 _ _ _ _ _ _ hw5 hn hh hr5 hraw
  exact of_eq (RawCodeGetSyntax.get_rename w x s y (old 5)).symm ho

theorem condition_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i s y row V : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) (hs : Derives Γ (successor s i))
    (hc : Derives Γ (correct w i)) (hv : Derives Γ (ProjectionTraceSetSyntax.value w V))
    (hr : Derives Γ (ProjectionTraceSyntax.getRow w x s y row)) (ht : Derives Γ (ProjectionTraceSyntax.condition w row)) :
    Derives Γ (RawCodeGetSyntax.get w x s y) := by
  have hstep := ProjectionTraceUnfold.condition_step w V row hv ht
  have hsel := ProjectionRuleDispatch.get_step hZ 3 w row V (SyntaxAtomSyntax.three x s y) hw hr hstep
  apply HornStepSyntax.step_elim ProjectionRuleDispatch.getRules w row V _ hsel
  intro rule hm
  apply Derives.impI
  simp only [ProjectionRuleDispatch.getRules, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · exact ProjectionGetZeroIndex.zero_application (ZFContext.add hZ _) w x s y row V (add hw _) (add hr _) (.hyp (Or.inl rfl))
  · exact ProjectionGetZeroIndex.head_application (ZFContext.add hZ _) w x s y row V (add hw _) (add hr _) (.hyp (Or.inl rfl))
  · exact tail_application (ZFContext.add hZ _) w x i s y row V (add hw _) (add hi _) (add hs _) (add hc _) (add hv _) (add hr _) (.hyp (Or.inl rfl))

theorem at_actual_set {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i s y V : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) (hs : Derives Γ (successor s i))
    (hc : Derives Γ (correct w i)) (hv : Derives Γ (ProjectionTraceSetSyntax.value w V))
    (hq : Derives Γ (ProjectionTraceSyntax.get w x s y)) : Derives Γ (RawCodeGetSyntax.get w x s y) := by
  let B := (ProjectionTraceSyntax.getRow w.castSucc x.castSucc s.castSucc y.castSucc (Fin.last m)).conj
    (ProjectionTraceSyntax.condition w.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hq
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hs1 := of_eq (successor_rename s i Fin.castSucc) (under hs B)
  have hc1 := of_eq (correct_rename w i Fin.castSucc) (under hc B)
  have hv1 := of_eq (ProjectionTraceSetSyntax.value_rename w V Fin.castSucc) (under hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := condition_sound (ZFContext.under hZ B) _ _ _ _ _ _ _ hw1 (under hi B) hs1 hc1 hv1 (.conjL hB) (.conjR hB)
  exact of_eq (RawCodeGetSyntax.get_rename w x s y Fin.castSucc).symm ho

theorem checked_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i s y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) (hs : Derives Γ (successor s i))
    (hc : Derives Γ (correct w i)) (hq : Derives Γ (ProjectionTraceSyntax.get w x s y)) : Derives Γ (RawCodeGetSyntax.get w x s y) := by
  let B := ProjectionTraceSetSyntax.value w.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (ProjectionTraceSet.exists_value hZ w)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hs1 := of_eq (successor_rename s i Fin.castSucc) (under hs B)
  have hc1 := of_eq (correct_rename w i Fin.castSucc) (under hc B)
  have hq1 := of_eq (ProjectionTraceSyntax.get_rename w x s y Fin.castSucc) (under hq B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := at_actual_set (ZFContext.under hZ B) _ _ _ _ _ _ hw1 (under hi B) hs1 hc1 hB hq1
  exact of_eq (RawCodeGetSyntax.get_rename w x s y Fin.castSucc).symm ho

end PPAC.Migration.Internal.ProjectionGetSuccessorSound
