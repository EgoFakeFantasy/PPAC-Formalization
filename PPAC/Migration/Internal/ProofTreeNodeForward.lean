import PPAC.Migration.Internal.ProofTreeNodeSyntax

/-! 原node0入口展开全部12分支，排除root1后取得六类载荷与各子Node。 -/
namespace PPAC.Migration.Internal.ProofTreeNodeForward
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation
open ProofTreeBranchConstruction (shape)

theorem matrix_forward {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (kind : Fin 6) (root : Bool)
    (w r code : Fin m) (env : Fin ((shape kind).extra+2) → Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (SyntaxNodeSyntax.constructor 1 0 w (fun _ => code) r))
    (hn : Derives Γ (environmentNat ((shape kind).extra+2) w env))
    (hm : Derives Γ (ProofTreeTracedStep.matrix test (ObjectProofTree.branch (shape kind) root) w r env)) :
    Derives Γ (ProofTreeNodeSyntax.payloadCases test w code) := by
  let s := shape kind
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (graph (ObjectProofTree.payload s) w.castSucc (fun i => (env i).castSucc) (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (HornExprExistence.exists_value hZ (ObjectProofTree.payload s) w env hw hn)
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 := of_eq (environmentNat_rename (s.extra+2) w env Fin.castSucc) (under hn B)
  have hr1 := of_eq (SyntaxNodeSyntax.constructor_rename 1 0 w (fun _ => code) r Fin.castSucc) (under hr B)
  have hm1 := of_eq (ProofTreeTracedStep.matrix_rename test (ObjectProofTree.branch s root) w r env Fin.castSucc) (under hm B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho : Derives Δ (ProofTreeNodeSyntax.payloadCases test w.castSucc code.castSucc) := by
    cases root
    · have hc := Derives.impE (.conjL (ProofTreeBranchHead.node_iff hZ1 s w.castSucc r.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hn1 (.conjR hB))) (.conjL hm1)
      have hp := ProofTreeConstructorFacts.field_equal hZ1 1 0 w.castSucc r.castSucc (fun _ => Fin.last m) (fun _ => code.castSucc) 0 hw1 hc hr1
      have hpc := Derives.impE (.conjL (ProofTreeBranchHead.payload_iff hZ1 s w.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hn1)) (.conjR hB)
      have hcode := HornExprConstructor.output_subst (s.extra+2) s.tag w.castSucc (Fin.last m) code.castSucc (fun i => (env i).castSucc) hp hpc
      have hchildren := Derives.impE (.conjL (ProofTreeChildren.children_iff test hZ1 s.children w.castSucc (fun i => (env i).castSucc) hw1 hn1)) (.conjR (.conjR hm1))
      exact ProofTreeNodeSyntax.intro_cases test kind w.castSucc code.castSucc (fun i => (env i).castSucc) (.conjI hn1 (.conjI hcode hchildren))
    · have hc := Derives.impE (.conjL (ProofTreeBranchHead.root_iff hZ1 s w.castSucc r.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hn1 (.conjR hB))) (.conjL hm1)
      exact .botE (SyntaxConstructors.disjoint hZ1 2 1 1 0 (by decide) w.castSucc (SetLanguage.args2 (Fin.last m) (env 1).castSucc) (fun _ => code.castSucc) r.castSucc hw1 hc hr1)
  exact of_eq (ProofTreeNodeSyntax.payloadCases_rename test w code Fin.castSucc).symm ho

theorem application_forward {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (kind : Fin 6) (root : Bool)
    (w r code : Fin m) (hw : Derives Γ (omega w))
    (hr : Derives Γ (SyntaxNodeSyntax.constructor 1 0 w (fun _ => code) r))
    (ha : Derives Γ (ProofTreeTracedStep.application test (ObjectProofTree.branch (shape kind) root) w r)) :
    Derives Γ (ProofTreeNodeSyntax.payloadCases test w code) := by
  let rule := ObjectProofTree.branch (shape kind) root
  let B := ProofTreeTracedStep.body test rule w r
  let Δ := Context.add B (raisedContext rule.arity Γ)
  apply HornBinderRules.eliminate_many rule.arity B _ ha
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hwN := of_eq (omega_rename w (old rule.arity)) (HornBinderRules.under_body rule.arity hw B)
  have hrN := of_eq (SyntaxNodeSyntax.constructor_rename 1 0 w (fun _ => code) r (old rule.arity)) (HornBinderRules.under_body rule.arity hr B)
  have ho := matrix_forward test (HornBinderRules.zf_body rule.arity hZ B) kind root (old rule.arity w) (old rule.arity r)
    (old rule.arity code) (slot rule.arity) hwN hrN (.conjL hB) (.conjR (.conjR hB))
  exact of_eq (ProofTreeNodeSyntax.payloadCases_rename test w code (old rule.arity)).symm ho

theorem node_forward {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w code : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (ProofTreeEntrySyntax.node test w code)) :
    Derives Γ (ProofTreeNodeSyntax.normalized test w code) := by
  let B := (SyntaxNodeSyntax.constructor 1 0 w.castSucc (fun _ => code.castSucc) (Fin.last m)).conj
    (ProofTreeTraceSyntax.condition test w.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hr
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hEq := Derives.impE (.conjL (ProofTreeTraceEquation.recursive_iff test hZ1 w.castSucc (Fin.last m))) (.conjR hB)
  have hl := Derives.impE (.conjL (ProofTreeNodeTag.local_iff test hZ1 w.castSucc (Fin.last m) code.castSucc hw1 (.conjL hB))) (.conjR (.conjR hEq))
  have hc : Derives Δ (ProofTreeNodeSyntax.payloadCases test w.castSucc code.castSucc) := by
    apply ProofTreeRootForward.step_elim test ObjectProofTree.rules w.castSucc (Fin.last m) _ (.conjL (.conjR hEq))
    intro rule hRule
    obtain ⟨kind,root,rfl⟩ := ProofTreeRootForward.rule_cases rule hRule
    apply Derives.impI
    exact application_forward test (ZFContext.add hZ1 _) kind root w.castSucc (Fin.last m) code.castSucc (add hw1 _) (add (.conjL hB) _) (.hyp (Or.inl rfl))
  exact of_eq (ProofTreeNodeSyntax.normalized_rename test w code Fin.castSucc).symm (.conjI hl hc)

end PPAC.Migration.Internal.ProofTreeNodeForward
