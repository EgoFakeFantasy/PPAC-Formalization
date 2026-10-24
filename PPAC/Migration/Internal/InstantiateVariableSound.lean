import PPAC.Migration.Internal.OriginalInstantiatePositive
import PPAC.Migration.Internal.InstantiateVariableValueSyntax

/-! 待编译：实际mode2变量规则矩阵推出独立数值规格，字段均取自原五字段行。 -/
namespace PPAC.Migration.Internal.InstantiateVariableSound
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax InstantiateVariableValueSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation.ObjectSyntaxTransform
open HornApplicationSyntax HornBinderSyntax

def boundIdentityFields : Fin 5 → Expr 3 := HornRowFields.five (.literal 2) (.var 0) (.var 1) (varCode false (.var 2)) (varCode false (.var 2))

def boundPointFields : Fin 5 → Expr 2 := HornRowFields.five (.literal 2) (.var 0) (.var 1) (varCode false (.var 0)) (.var 1)

def boundPredecessorFields : Fin 5 → Expr 3 := HornRowFields.five (.literal 2) (.var 0) (.var 1) (varCode false (.succ (.var 2))) (varCode false (.var 2))

def freeIdentityFields : Fin 5 → Expr 3 := HornRowFields.five (.literal 2) (.var 0) (.var 1) (varCode true (.var 2)) (varCode true (.var 2))

theorem boundIdentityFields_head : (boundIdentity 2 true).head = Expr.node (.literal 1) (List.ofFn boundIdentityFields) := rfl

theorem boundPointFields_head : boundPoint.head = Expr.node (.literal 1) (List.ofFn boundPointFields) := rfl

theorem boundPredecessorFields_head : boundPredecessor.head = Expr.node (.literal 1) (List.ofFn boundPredecessorFields) := rfl

theorem freeIdentityFields_head : freeIdentity.head = Expr.node (.literal 1) (List.ofFn freeIdentityFields) := rfl

theorem bound_preserved {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r R idx : Fin m)
    (env : Fin 3 → Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat 3 w env)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3)))
    (hm : Derives Γ (HornRuleSyntax.matrix (boundIdentity 2 true) w r R env)) : Derives Γ (boundValue w (xs 1) (xs 2) idx (xs 3) (xs 4)) := by
  have hg : Derives Γ (graph (Expr.node (.literal 1) (List.ofFn boundIdentityFields)) w env r) := .conjL hm
  have h1 := HornRowFields.field_graph hZ 1 boundIdentityFields w r env xs 1 hw hn hg hc
  have h3 := HornRowFields.field_graph hZ 1 boundIdentityFields w r env xs 3 hw hn hg hc
  have h4 := HornRowFields.field_graph hZ 1 boundIdentityFields w r env xs 4 hw hn hg hc
  have hi := AbstractVariableIndex.index_graph hZ true (.var 2) w idx (xs 3) env hw hn h3 hv
  have hgi := Derives.impE (.conjL (OriginalInstantiatePositive.bound_identity_guard_iff hZ w env hw hn)) (.conjL (.conjR hm))
  have hlt := UnorderedPairLogic.mem_container_subst (env 0) (xs 1) idx (eq_symm (.conjR h1)) (mem_subst (eq_symm (.conjR hi)) hgi)
  have he := HornExprUnique.unique hZ (varCode false (.var 2)) w (xs 4) (xs 3) env hw hn h4 h3
  exact .disjL (.conjI hlt he)

theorem bound_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r R idx : Fin m)
    (env : Fin 2 → Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat 2 w env)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3)))
    (hm : Derives Γ (HornRuleSyntax.matrix boundPoint w r R env)) : Derives Γ (boundValue w (xs 1) (xs 2) idx (xs 3) (xs 4)) := by
  have hg : Derives Γ (graph (Expr.node (.literal 1) (List.ofFn boundPointFields)) w env r) := .conjL hm
  have h1 := HornRowFields.field_graph hZ 1 boundPointFields w r env xs 1 hw hn hg hc
  have h2 := HornRowFields.field_graph hZ 1 boundPointFields w r env xs 2 hw hn hg hc
  have h3 := HornRowFields.field_graph hZ 1 boundPointFields w r env xs 3 hw hn hg hc
  have h4 := HornRowFields.field_graph hZ 1 boundPointFields w r env xs 4 hw hn hg hc
  have hi := AbstractVariableIndex.index_graph hZ true (.var 0) w idx (xs 3) env hw hn h3 hv
  exact .disjR (.disjL (.conjI (eq_trans (.conjR hi) (eq_symm (.conjR h1)))
    (eq_trans (.conjR h4) (eq_symm (.conjR h2)))))

theorem successor_from_variable_graph {m a} {Γ : Context m} (j : Fin a) (w idx : Fin m) (env : Fin a → Fin m)
    (hg : Derives Γ (graph (.succ (.var j)) w env idx)) : Derives Γ (successor idx (env j)) := by
  let B := (graph (.var j) w.castSucc (fun i => (env i).castSucc) (Fin.last m)).conj (successor idx.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hg
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hs := FreeWeakenValueSyntax.successor_input_subst idx.castSucc (Fin.last m) (env j).castSucc (.conjR (.conjL hB)) (.conjR hB)
  exact of_eq (successor_rename idx (env j) Fin.castSucc).symm hs

theorem bound_predecessor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r R idx : Fin m)
    (env : Fin 3 → Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat 3 w env)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3)))
    (hm : Derives Γ (HornRuleSyntax.matrix boundPredecessor w r R env)) : Derives Γ (boundValue w (xs 1) (xs 2) idx (xs 3) (xs 4)) := by
  have hg : Derives Γ (graph (Expr.node (.literal 1) (List.ofFn boundPredecessorFields)) w env r) := .conjL hm
  have h1 := HornRowFields.field_graph hZ 1 boundPredecessorFields w r env xs 1 hw hn hg hc
  have h3 := HornRowFields.field_graph hZ 1 boundPredecessorFields w r env xs 3 hw hn hg hc
  have h4 := HornRowFields.field_graph hZ 1 boundPredecessorFields w r env xs 4 hw hn hg hc
  have hi := AbstractVariableIndex.index_graph hZ true (.succ (.var 2)) w idx (xs 3) env hw hn h3 hv
  have hs := successor_from_variable_graph (2 : Fin 3) w idx env hi
  have hguard := Derives.impE (.conjL (OriginalInstantiatePositive.bound_predecessor_guard_iff hZ w idx env hw hn hs)) (.conjL (.conjR hm))
  have hd := mem_subst (eq_symm (.conjR h1)) hguard
  have hk : Derives Γ (graph (.var 2) w env (env 2)) := .conjI (environmentNat_at w env hn 2) (.eqRefl _)
  have hy := HornVariableValue.graph_code hZ true (.var 2) w (env 2) (xs 4) env hw hn hk h4
  exact .disjR (.disjR (intro_boundTail w (xs 1) idx (xs 4) (env 2) hs hd hy))

theorem free_identity {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r R idx : Fin m)
    (env : Fin 3 → Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat 3 w env)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (_hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3)))
    (hm : Derives Γ (HornRuleSyntax.matrix freeIdentity w r R env)) : Derives Γ (.equal (xs 4) (xs 3)) := by
  have hg : Derives Γ (graph (Expr.node (.literal 1) (List.ofFn freeIdentityFields)) w env r) := .conjL hm
  have h3 := HornRowFields.field_graph hZ 1 freeIdentityFields w r env xs 3 hw hn hg hc
  have h4 := HornRowFields.field_graph hZ 1 freeIdentityFields w r env xs 4 hw hn hg hc
  exact HornExprUnique.unique hZ (varCode true (.var 2)) w (xs 4) (xs 3) env hw hn h4 h3

theorem application_bound_preserved {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r R idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3)))
    (ha : Derives Γ (application (boundIdentity 2 true) w r R)) : Derives Γ (boundValue w (xs 1) (xs 2) idx (xs 3) (xs 4)) := by
  let rule := (boundIdentity 2 true)
  let B := body rule w r R
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornApplicationRules.eliminate_application rule w r R _ ha
  have hZ1 := HornBinderRules.zf_body 3 hZ B
  have hw1 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw B)
  have hc1 := of_eq (SyntaxNodeSyntax.constructor_rename 5 1 w xs r (old 3)) (HornBinderRules.under_body 3 hc B)
  have hv1 := of_eq (SyntaxVariableSyntax.code_rename true w idx (xs 3) (old 3)) (HornBinderRules.under_body 3 hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := bound_preserved hZ1 _ _ _ _ _ _ hw1 (.conjL hB) hc1 hv1 (.conjR (.conjR hB))
  exact of_eq (boundValue_rename w (xs 1) (xs 2) idx (xs 3) (xs 4) (old 3)).symm ho

theorem application_bound_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r R idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3)))
    (ha : Derives Γ (application boundPoint w r R)) : Derives Γ (boundValue w (xs 1) (xs 2) idx (xs 3) (xs 4)) := by
  let rule := boundPoint
  let B := body rule w r R
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornApplicationRules.eliminate_application rule w r R _ ha
  have hZ1 := HornBinderRules.zf_body 2 hZ B
  have hw1 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hc1 := of_eq (SyntaxNodeSyntax.constructor_rename 5 1 w xs r (old 2)) (HornBinderRules.under_body 2 hc B)
  have hv1 := of_eq (SyntaxVariableSyntax.code_rename true w idx (xs 3) (old 2)) (HornBinderRules.under_body 2 hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := bound_point hZ1 _ _ _ _ _ _ hw1 (.conjL hB) hc1 hv1 (.conjR (.conjR hB))
  exact of_eq (boundValue_rename w (xs 1) (xs 2) idx (xs 3) (xs 4) (old 2)).symm ho

theorem application_bound_predecessor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r R idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3)))
    (ha : Derives Γ (application boundPredecessor w r R)) : Derives Γ (boundValue w (xs 1) (xs 2) idx (xs 3) (xs 4)) := by
  let rule := boundPredecessor
  let B := body rule w r R
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornApplicationRules.eliminate_application rule w r R _ ha
  have hZ1 := HornBinderRules.zf_body 3 hZ B
  have hw1 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw B)
  have hc1 := of_eq (SyntaxNodeSyntax.constructor_rename 5 1 w xs r (old 3)) (HornBinderRules.under_body 3 hc B)
  have hv1 := of_eq (SyntaxVariableSyntax.code_rename true w idx (xs 3) (old 3)) (HornBinderRules.under_body 3 hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := bound_predecessor hZ1 _ _ _ _ _ _ hw1 (.conjL hB) hc1 hv1 (.conjR (.conjR hB))
  exact of_eq (boundValue_rename w (xs 1) (xs 2) idx (xs 3) (xs 4) (old 3)).symm ho

theorem application_free_identity {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r R idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3)))
    (ha : Derives Γ (application freeIdentity w r R)) : Derives Γ (.equal (xs 4) (xs 3)) := by
  let rule := freeIdentity
  let B := body rule w r R
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornApplicationRules.eliminate_application rule w r R _ ha
  have hZ1 := HornBinderRules.zf_body 3 hZ B
  have hw1 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw B)
  have hc1 := of_eq (SyntaxNodeSyntax.constructor_rename 5 1 w xs r (old 3)) (HornBinderRules.under_body 3 hc B)
  have hv1 := of_eq (SyntaxVariableSyntax.code_rename false w idx (xs 3) (old 3)) (HornBinderRules.under_body 3 hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := free_identity hZ1 _ _ _ _ _ _ hw1 (.conjL hB) hc1 hv1 (.conjR (.conjR hB))
  exact ho

end PPAC.Migration.Internal.InstantiateVariableSound
