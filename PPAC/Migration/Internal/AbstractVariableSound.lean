import PPAC.Migration.Internal.ProjectionRawPairExpr
import PPAC.Migration.Internal.FreeWeakenValueSyntax
import PPAC.Migration.Internal.AbstractVariableValueSyntax

/-! 原mode1四条变量局部矩阵推出独立数值输出；读原五字段图并消去实际后继见证。 -/
namespace PPAC.Migration.Internal.AbstractVariableSound
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornApplicationSyntax HornBinderSyntax AbstractVariableValueSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation.ObjectSyntaxTransform

def boundIdentityFields : Fin 5 → Expr 3 := HornRowFields.five (.literal 1) (.var 0) (.var 1) (varCode false (.var 2)) (varCode false (.var 2))

theorem boundIdentityFields_head : (boundIdentity 1 true).head = Expr.node (.literal 1) (List.ofFn boundIdentityFields) := rfl

def boundAbstractFields : Fin 5 → Expr 3 := HornRowFields.five (.literal 1) (.var 0) (.var 1) (varCode false (.var 2)) (varCode false (.succ (.var 2)))

theorem boundAbstractFields_head : boundAbstract.head = Expr.node (.literal 1) (List.ofFn boundAbstractFields) := rfl

def freeHeadFields : Fin 5 → Expr 2 := HornRowFields.five (.literal 1) (.var 0) (.var 1) (varCode true (.literal 0)) (varCode false (.var 0))

theorem freeHeadFields_head : freeAbstractHead.head = Expr.node (.literal 1) (List.ofFn freeHeadFields) := rfl

def freeTailFields : Fin 5 → Expr 3 := HornRowFields.five (.literal 1) (.var 0) (.var 1) (varCode true (.succ (.var 2))) (varCode true (.var 2))

theorem freeTailFields_head : freeAbstractTail.head = Expr.node (.literal 1) (List.ofFn freeTailFields) := rfl

theorem bound_preserved {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r R idx : Fin m)
    (env : Fin 3 → Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat 3 w env)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3)))
    (hm : Derives Γ (HornRuleSyntax.matrix (boundIdentity 1 true) w r R env)) : Derives Γ (boundValue w (xs 1) idx (xs 3) (xs 4)) := by
  have hg : Derives Γ (graph (Expr.node (.literal 1) (List.ofFn boundIdentityFields)) w env r) := .conjL hm
  have h1 := HornRowFields.field_graph hZ 1 boundIdentityFields w r env xs 1 hw hn hg hc
  have h3 := HornRowFields.field_graph hZ 1 boundIdentityFields w r env xs 3 hw hn hg hc
  have h4 := HornRowFields.field_graph hZ 1 boundIdentityFields w r env xs 4 hw hn hg hc
  have hi := AbstractVariableIndex.index_graph hZ true (.var 2) w idx (xs 3) env hw hn h3 hv
  have hgi := Derives.impE (.conjL (OriginalAbstractPositive.bound_identity_guard_iff hZ w env hw hn)) (.conjL (.conjR hm))
  have hlt := UnorderedPairLogic.mem_container_subst (env 0) (xs 1) idx (eq_symm (.conjR h1)) (mem_subst (eq_symm (.conjR hi)) hgi)
  have he := HornExprUnique.unique hZ (varCode false (.var 2)) w (xs 4) (xs 3) env hw hn h4 h3
  exact .disjL (.conjI hlt he)

theorem free_head {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r R idx : Fin m)
    (env : Fin 2 → Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat 2 w env)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3)))
    (hm : Derives Γ (HornRuleSyntax.matrix freeAbstractHead w r R env)) : Derives Γ (freeValue w (xs 1) idx (xs 4)) := by
  have hg : Derives Γ (graph (Expr.node (.literal 1) (List.ofFn freeHeadFields)) w env r) := .conjL hm
  have h1 := HornRowFields.field_graph hZ 1 freeHeadFields w r env xs 1 hw hn hg hc
  have h3 := HornRowFields.field_graph hZ 1 freeHeadFields w r env xs 3 hw hn hg hc
  have h4 := HornRowFields.field_graph hZ 1 freeHeadFields w r env xs 4 hw hn hg hc
  have hi := AbstractVariableIndex.index_graph hZ false (.literal 0) w idx (xs 3) env hw hn h3 hv
  have hy := HornVariableValue.graph_code hZ true (.var 0) w (xs 1) (xs 4) env hw hn h1 h4
  exact .disjL (.conjI hi hy)

theorem free_tail {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r R idx : Fin m)
    (env : Fin 3 → Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat 3 w env)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3)))
    (hm : Derives Γ (HornRuleSyntax.matrix freeAbstractTail w r R env)) : Derives Γ (freeValue w (xs 1) idx (xs 4)) := by
  have hg : Derives Γ (graph (Expr.node (.literal 1) (List.ofFn freeTailFields)) w env r) := .conjL hm
  have h1 := HornRowFields.field_graph hZ 1 freeTailFields w r env xs 1 hw hn hg hc
  have h3 := HornRowFields.field_graph hZ 1 freeTailFields w r env xs 3 hw hn hg hc
  have h4 := HornRowFields.field_graph hZ 1 freeTailFields w r env xs 4 hw hn hg hc
  have hi := AbstractVariableIndex.index_graph hZ false (.succ (.var 2)) w idx (xs 3) env hw hn h3 hv
  have hs := Derives.impE (.conjL (ProjectionRawPairExpr.successor_variable_iff (2 : Fin 3) w idx env hn)) hi
  have hv2 : Derives Γ (graph (.var 2) w env (env 2)) := .conjI (environmentNat_at w env hn 2) (.eqRefl _)
  have hy := HornVariableValue.graph_code hZ false (.var 2) w (env 2) (xs 4) env hw hn hv2 h4
  exact .disjR (intro_freeTail w idx (xs 4) (env 2) hs hy)

theorem bound_shifted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r R idx : Fin m)
    (env : Fin 3 → Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat 3 w env)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3)))
    (hm : Derives Γ (HornRuleSyntax.matrix boundAbstract w r R env)) : Derives Γ (boundValue w (xs 1) idx (xs 3) (xs 4)) := by
  have hg : Derives Γ (graph (Expr.node (.literal 1) (List.ofFn boundAbstractFields)) w env r) := .conjL hm
  have h1 := HornRowFields.field_graph hZ 1 boundAbstractFields w r env xs 1 hw hn hg hc
  have h3 := HornRowFields.field_graph hZ 1 boundAbstractFields w r env xs 3 hw hn hg hc
  have h4 := HornRowFields.field_graph hZ 1 boundAbstractFields w r env xs 4 hw hn hg hc
  have hi := AbstractVariableIndex.index_graph hZ true (.var 2) w idx (xs 3) env hw hn h3 hv
  let B := successor (Fin.last m) idx.castSucc
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (InsertExistence.exists_insert idx idx (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union)
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 := of_eq (environmentNat_rename 3 w env Fin.castSucc) (under hn B)
  have hi1 := of_eq (graph_rename (.var 2) w idx env Fin.castSucc) (under hi B)
  have h41 := of_eq (graph_rename (varCode false (.succ (.var 2))) w (xs 4) env Fin.castSucc) (under h4 B)
  have hd1 : Derives Δ (.equal (env 0).castSucc (xs 1).castSucc) := under (eq_symm (.conjR h1)) B
  have hgs1 := of_eq (HornRuleSyntax.guards_rename boundAbstract.guards w env Fin.castSucc) (under (.conjL (.conjR hm)) B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hse := FreeWeakenValueSyntax.successor_input_subst _ _ _ (.conjR hi1) hB
  have hguard := Derives.impE (.conjL (OriginalAbstractPositive.bound_abstract_guard_iff hZ1 _ _ _ hw1 hn1 hse)) hgs1
  have hdepth := mem_subst hd1 hguard
  have hsgraph := intro_succ (.var 2) w.castSucc (Fin.last m) idx.castSucc (fun j => (env j).castSucc) hi1 hB
  have hy := HornVariableValue.graph_code hZ1 true (.succ (.var 2)) _ _ _ _ hw1 hn1 hsgraph h41
  have ho : Derives Δ (boundValue w.castSucc (xs 1).castSucc idx.castSucc (xs 3).castSucc (xs 4).castSucc) :=
    .disjR (intro_boundShifted _ _ _ _ _ hB hdepth hy)
  exact of_eq (boundValue_rename w (xs 1) idx (xs 3) (xs 4) Fin.castSucc).symm ho

theorem application_bound_preserved {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r R idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3)))
    (ha : Derives Γ (application (boundIdentity 1 true) w r R)) : Derives Γ (boundValue w (xs 1) idx (xs 3) (xs 4)) := by
  let rule := (boundIdentity 1 true)
  let B := body rule w r R
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornApplicationRules.eliminate_application rule w r R _ ha
  have hZ1 := HornBinderRules.zf_body 3 hZ B
  have hw1 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw B)
  have hc1 := of_eq (SyntaxNodeSyntax.constructor_rename 5 1 w xs r (old 3)) (HornBinderRules.under_body 3 hc B)
  have hv1 := of_eq (SyntaxVariableSyntax.code_rename true w idx (xs 3) (old 3)) (HornBinderRules.under_body 3 hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := bound_preserved hZ1 _ _ _ _ _ _ hw1 (.conjL hB) hc1 hv1 (.conjR (.conjR hB))
  exact of_eq (boundValue_rename w (xs 1) idx (xs 3) (xs 4) (old 3)).symm ho

theorem application_bound_shifted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r R idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3)))
    (ha : Derives Γ (application boundAbstract w r R)) : Derives Γ (boundValue w (xs 1) idx (xs 3) (xs 4)) := by
  let rule := boundAbstract
  let B := body rule w r R
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornApplicationRules.eliminate_application rule w r R _ ha
  have hZ1 := HornBinderRules.zf_body 3 hZ B
  have hw1 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw B)
  have hc1 := of_eq (SyntaxNodeSyntax.constructor_rename 5 1 w xs r (old 3)) (HornBinderRules.under_body 3 hc B)
  have hv1 := of_eq (SyntaxVariableSyntax.code_rename true w idx (xs 3) (old 3)) (HornBinderRules.under_body 3 hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := bound_shifted hZ1 _ _ _ _ _ _ hw1 (.conjL hB) hc1 hv1 (.conjR (.conjR hB))
  exact of_eq (boundValue_rename w (xs 1) idx (xs 3) (xs 4) (old 3)).symm ho

theorem application_free_head {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r R idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3)))
    (ha : Derives Γ (application freeAbstractHead w r R)) : Derives Γ (freeValue w (xs 1) idx (xs 4)) := by
  let rule := freeAbstractHead
  let B := body rule w r R
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornApplicationRules.eliminate_application rule w r R _ ha
  have hZ1 := HornBinderRules.zf_body 2 hZ B
  have hw1 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hc1 := of_eq (SyntaxNodeSyntax.constructor_rename 5 1 w xs r (old 2)) (HornBinderRules.under_body 2 hc B)
  have hv1 := of_eq (SyntaxVariableSyntax.code_rename false w idx (xs 3) (old 2)) (HornBinderRules.under_body 2 hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := free_head hZ1 _ _ _ _ _ _ hw1 (.conjL hB) hc1 hv1 (.conjR (.conjR hB))
  exact of_eq (freeValue_rename w (xs 1) idx (xs 4) (old 2)).symm ho

theorem application_free_tail {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r R idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3)))
    (ha : Derives Γ (application freeAbstractTail w r R)) : Derives Γ (freeValue w (xs 1) idx (xs 4)) := by
  let rule := freeAbstractTail
  let B := body rule w r R
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornApplicationRules.eliminate_application rule w r R _ ha
  have hZ1 := HornBinderRules.zf_body 3 hZ B
  have hw1 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw B)
  have hc1 := of_eq (SyntaxNodeSyntax.constructor_rename 5 1 w xs r (old 3)) (HornBinderRules.under_body 3 hc B)
  have hv1 := of_eq (SyntaxVariableSyntax.code_rename false w idx (xs 3) (old 3)) (HornBinderRules.under_body 3 hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := free_tail hZ1 _ _ _ _ _ _ hw1 (.conjL hB) hc1 hv1 (.conjR (.conjR hB))
  exact of_eq (freeValue_rename w (xs 1) idx (xs 4) (old 3)).symm ho

end PPAC.Migration.Internal.AbstractVariableSound
