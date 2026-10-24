import PPAC.Migration.Internal.ProofTreeRootSyntax

/-! 根行展开原12分支后消去所有赋值和载荷见证，得到零自由变量与精确结论。 -/
namespace PPAC.Migration.Internal.ProofTreeRootForward
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation
open ProofTreeBranchConstruction (shape)

theorem shape_cases (s : ObjectProofTree.Shape) (hs : s ∈ ObjectProofTree.shapes) : ∃ kind : Fin 6, shape kind = s := by
  simp only [ObjectProofTree.shapes, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨4,rfl⟩
  · exact ⟨5,rfl⟩

theorem rule_cases (rule : ObjectHorn.Rule) (hr : rule ∈ ObjectProofTree.rules) :
    ∃ (kind : Fin 6) (root : Bool), rule = ObjectProofTree.branch (shape kind) root := by
  obtain ⟨s,hs,hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨kind,rfl⟩ := shape_cases s hs
  rcases List.mem_cons.mp hr with rfl | hr
  · exact ⟨kind,false,rfl⟩
  · have he := List.mem_singleton.mp hr
    subst rule
    exact ⟨kind,true,rfl⟩

theorem step_elim {m} {Γ : Context m} (test : Formula 1) (rules : List ObjectHorn.Rule) (w row : Fin m) (p : Formula m)
    (he : Derives Γ (ProofTreeTracedStep.step test rules w row))
    (hr : ∀ rule, rule ∈ rules → Derives Γ ((ProofTreeTracedStep.application test rule w row).imp p)) : Derives Γ p := by
  induction rules generalizing Γ with
  | nil => exact .botE he
  | cons rule rules ih =>
    apply Derives.disjE he
    · exact .impE (add (hr rule List.mem_cons_self) _) (.hyp (Or.inl rfl))
    · exact ih (.hyp (Or.inl rfl)) (fun a ha => add (hr a (List.mem_cons_of_mem rule ha)) _)

theorem matrix_forward {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (kind : Fin 6) (root : Bool)
    (w r code conclusion : Fin m) (env : Fin ((shape kind).extra+2) → Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (SyntaxNodeSyntax.constructor 2 1 w (SetLanguage.args2 code conclusion) r))
    (hn : Derives Γ (environmentNat ((shape kind).extra+2) w env))
    (hm : Derives Γ (ProofTreeTracedStep.matrix test (ObjectProofTree.branch (shape kind) root) w r env)) :
    Derives Γ (ProofTreeRootSyntax.normalized test w code conclusion) := by
  let s := shape kind
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (graph (ObjectProofTree.payload s) w.castSucc (fun i => (env i).castSucc) (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (HornExprExistence.exists_value hZ (ObjectProofTree.payload s) w env hw hn)
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 := of_eq (environmentNat_rename (s.extra+2) w env Fin.castSucc) (under hn B)
  have hr1 := of_eq (SyntaxNodeSyntax.constructor_rename 2 1 w (SetLanguage.args2 code conclusion) r Fin.castSucc) (under hr B)
  have hm1 := of_eq (ProofTreeTracedStep.matrix_rename test (ObjectProofTree.branch s root) w r env Fin.castSucc) (under hm B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho : Derives Δ (ProofTreeRootSyntax.normalized test w.castSucc code.castSucc conclusion.castSucc) := by
    cases root
    · have hc := Derives.impE (.conjL (ProofTreeBranchHead.node_iff hZ1 s w.castSucc r.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hn1 (.conjR hB))) (.conjL hm1)
      exact .botE (SyntaxConstructors.disjoint hZ1 1 2 0 1 (by decide) w.castSucc (fun _ => Fin.last m) (SetLanguage.args2 code.castSucc conclusion.castSucc) r.castSucc hw1 hc hr1)
    · have hc := Derives.impE (.conjL (ProofTreeBranchHead.root_iff hZ1 s w.castSucc r.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hn1 (.conjR hB))) (.conjL hm1)
      have hp := ProofTreeConstructorFacts.field_equal hZ1 2 1 w.castSucc r.castSucc (SetLanguage.args2 (Fin.last m) (env 1).castSucc) (SetLanguage.args2 code.castSucc conclusion.castSucc) 0 hw1 hc hr1
      have he := ProofTreeConstructorFacts.field_equal hZ1 2 1 w.castSucc r.castSucc (SetLanguage.args2 (Fin.last m) (env 1).castSucc) (SetLanguage.args2 code.castSucc conclusion.castSucc) 1 hw1 hc hr1
      have hz := Derives.impE (.conjL (ProofTreeZeroGuard.guard_iff hZ1 0 w.castSucc (fun i => (env i).castSucc) hw1 hn1)) (.conjL (.conjL (.conjR hm1)))
      have hpc := Derives.impE (.conjL (ProofTreeBranchHead.payload_iff hZ1 s w.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hn1)) (.conjR hB)
      have hcode := HornExprConstructor.output_subst (s.extra+2) s.tag w.castSucc (Fin.last m) code.castSucc (fun i => (env i).castSucc) hp hpc
      have hnode := Derives.impE (.conjL (ProofTreeBranchHead.premise_iff test hZ1 s w.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hn1 (.conjR hB))) (.conjL (.conjR (.conjR hm1)))
      exact .conjI (ProofTreeEntryFacts.node_subst test w.castSucc (Fin.last m) code.castSucc hp hnode)
        (ProofTreeRootSyntax.intro_closedPayload kind w.castSucc code.castSucc conclusion.castSucc (fun i => (env i).castSucc) (.conjI hn1 (.conjI hcode (.conjI hz he))))
  exact of_eq (ProofTreeRootSyntax.normalized_rename test w code conclusion Fin.castSucc).symm ho

theorem application_forward {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (kind : Fin 6) (root : Bool)
    (w r code conclusion : Fin m) (hw : Derives Γ (omega w))
    (hr : Derives Γ (SyntaxNodeSyntax.constructor 2 1 w (SetLanguage.args2 code conclusion) r))
    (ha : Derives Γ (ProofTreeTracedStep.application test (ObjectProofTree.branch (shape kind) root) w r)) :
    Derives Γ (ProofTreeRootSyntax.normalized test w code conclusion) := by
  let rule := ObjectProofTree.branch (shape kind) root
  let B := ProofTreeTracedStep.body test rule w r
  let Δ := Context.add B (raisedContext rule.arity Γ)
  apply HornBinderRules.eliminate_many rule.arity B _ ha
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hwN := of_eq (omega_rename w (old rule.arity)) (HornBinderRules.under_body rule.arity hw B)
  have hrN := of_eq (SyntaxNodeSyntax.constructor_rename 2 1 w (SetLanguage.args2 code conclusion) r (old rule.arity)) (HornBinderRules.under_body rule.arity hr B)
  have ho := matrix_forward test (HornBinderRules.zf_body rule.arity hZ B) kind root (old rule.arity w) (old rule.arity r)
    (old rule.arity code) (old rule.arity conclusion) (slot rule.arity) hwN hrN (.conjL hB) (.conjR (.conjR hB))
  exact of_eq (ProofTreeRootSyntax.normalized_rename test w code conclusion (old rule.arity)).symm ho

theorem root_forward {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w code conclusion : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (ProofTreeEntrySyntax.root test w code conclusion)) :
    Derives Γ (ProofTreeRootSyntax.normalized test w code conclusion) := by
  let B := (SyntaxNodeSyntax.constructor 2 1 w.castSucc (SetLanguage.args2 code.castSucc conclusion.castSucc) (Fin.last m)).conj
    (ProofTreeTraceSyntax.condition test w.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hr
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hEq := Derives.impE (.conjL (ProofTreeTraceEquation.recursive_iff test hZ1 w.castSucc (Fin.last m))) (.conjR hB)
  have ho : Derives Δ (ProofTreeRootSyntax.normalized test w.castSucc code.castSucc conclusion.castSucc) := by
    apply step_elim test ObjectProofTree.rules w.castSucc (Fin.last m) _ (.conjL (.conjR hEq))
    intro rule hRule
    obtain ⟨kind,root,rfl⟩ := rule_cases rule hRule
    apply Derives.impI
    exact application_forward test (ZFContext.add hZ1 _) kind root w.castSucc (Fin.last m) code.castSucc conclusion.castSucc (add hw1 _) (add (.conjL hB) _) (.hyp (Or.inl rfl))
  exact of_eq (ProofTreeRootSyntax.normalized_rename test w code conclusion Fin.castSucc).symm ho

end PPAC.Migration.Internal.ProofTreeRootForward
