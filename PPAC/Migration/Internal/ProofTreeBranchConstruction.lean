import PPAC.Migration.Internal.ProofTreeTraceEquation

/-! 原六形状、node/root共12分支的对象正向组合；保留实际局部检查与真实递归前提。 -/
namespace PPAC.Migration.Internal.ProofTreeBranchConstruction
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation

def shape (kind : Fin 6) : ObjectProofTree.Shape :=
  match kind.val with
  | 0 => ObjectProofTree.logicalShape
  | 1 => ObjectProofTree.theoryShape
  | 2 => ObjectProofTree.mpShape
  | 3 => ObjectProofTree.forallShape
  | 4 => ObjectProofTree.strengtheningShape
  | _ => ObjectProofTree.substitutionShape

theorem shape_mem (kind : Fin 6) : shape kind ∈ ObjectProofTree.shapes := by
  rcases kind with ⟨k,hk⟩
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · change ObjectProofTree.logicalShape ∈ ObjectProofTree.shapes
    simp [ObjectProofTree.shapes]
  · change ObjectProofTree.theoryShape ∈ ObjectProofTree.shapes
    simp [ObjectProofTree.shapes]
  · change ObjectProofTree.mpShape ∈ ObjectProofTree.shapes
    simp [ObjectProofTree.shapes]
  · change ObjectProofTree.forallShape ∈ ObjectProofTree.shapes
    simp [ObjectProofTree.shapes]
  · change ObjectProofTree.strengtheningShape ∈ ObjectProofTree.shapes
    simp [ObjectProofTree.shapes]
  · change ObjectProofTree.substitutionShape ∈ ObjectProofTree.shapes
    simp [ObjectProofTree.shapes]

theorem head_variables (kind : Fin 6) (root : Bool) :
    ∀ i, i ∈ (ObjectProofTree.branch (shape kind) root).head.variables := by
  rcases kind with ⟨k,hk⟩
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> cases root
  · change ∀ i, i ∈ (ObjectProofTree.branch ObjectProofTree.logicalShape false).head.variables
    decide
  · change ∀ i, i ∈ (ObjectProofTree.branch ObjectProofTree.logicalShape true).head.variables
    decide
  · change ∀ i, i ∈ (ObjectProofTree.branch ObjectProofTree.theoryShape false).head.variables
    decide
  · change ∀ i, i ∈ (ObjectProofTree.branch ObjectProofTree.theoryShape true).head.variables
    decide
  · change ∀ i, i ∈ (ObjectProofTree.branch ObjectProofTree.mpShape false).head.variables
    decide
  · change ∀ i, i ∈ (ObjectProofTree.branch ObjectProofTree.mpShape true).head.variables
    decide
  · change ∀ i, i ∈ (ObjectProofTree.branch ObjectProofTree.forallShape false).head.variables
    decide
  · change ∀ i, i ∈ (ObjectProofTree.branch ObjectProofTree.forallShape true).head.variables
    decide
  · change ∀ i, i ∈ (ObjectProofTree.branch ObjectProofTree.strengtheningShape false).head.variables
    decide
  · change ∀ i, i ∈ (ObjectProofTree.branch ObjectProofTree.strengtheningShape true).head.variables
    decide
  · change ∀ i, i ∈ (ObjectProofTree.branch ObjectProofTree.substitutionShape false).head.variables
    decide
  · change ∀ i, i ∈ (ObjectProofTree.branch ObjectProofTree.substitutionShape true).head.variables
    decide

theorem all_bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 6) (root : Bool)
    (w r : Fin m) (env : Fin ((shape kind).extra+2) → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat ((shape kind).extra+2) w env))
    (hh : Derives Γ (graph (ObjectProofTree.branch (shape kind) root).head w env r)) :
    Derives Γ (HornExprBounds.environmentBound ((shape kind).extra+2) r env) :=
  HornExprBounds.intro_environmentBound r env (fun i => HornExprBounds.variable_bound hZ _ i (head_variables kind root i) w r env hw hn hh)

theorem rule_intro {m} {Γ : Context m} (test : Formula 1) (rules : List ObjectHorn.Rule) (rule : ObjectHorn.Rule)
    (hr : rule ∈ rules) (w r : Fin m) (he : Derives Γ (ProofTreeTracedStep.application test rule w r)) :
    Derives Γ (ProofTreeTracedStep.step test rules w r) := by
  induction rules with
  | nil => simp only [List.not_mem_nil] at hr
  | cons a rules ih =>
    rcases List.mem_cons.mp hr with h | h
    · subst rule
      exact .disjL he
    · exact .disjR (ih h)

theorem intro_branch {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (kind : Fin 6) (root : Bool)
    (w r : Fin m) (env : Fin ((shape kind).extra+2) → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat ((shape kind).extra+2) w env))
    (hm : Derives Γ (ProofTreeTracedStep.matrix test (ObjectProofTree.branch (shape kind) root) w r env))
    (hl : Derives Γ (ProofTreeRowLocalSyntax.localCondition test w r)) :
    Derives Γ (ProofTreeTraceSyntax.condition test w r) := by
  let rule := ObjectProofTree.branch (shape kind) root
  have hb := all_bounds hZ kind root w r env hw hn (.conjL hm)
  have hM : Derives Γ (ProofTreeTracedStep.boundedMatrix test rule w r env) := .conjI hn (.conjI hb hm)
  have ha : Derives Γ (ProofTreeTracedStep.application test rule w r) := by
    apply HornBinderRules.intro_many rule.arity (ProofTreeTracedStep.body test rule w r) env
    exact of_eq (by simp only [ProofTreeTracedStep.body, ProofTreeTracedStep.boundedMatrix_rename, assign_old, assign_slot]) hM
  have hs := rule_intro test ObjectProofTree.rules rule (ObjectProofTree.branch_mem (shape kind) (shape_mem kind) root) w r ha
  have hr := HornExprRange.range hZ rule.head w r env hw hn (.conjL hm)
  exact .impE (.conjR (ProofTreeTraceEquation.recursive_iff test hZ w r)) (.conjI hr (.conjI hs hl))

end PPAC.Migration.Internal.ProofTreeBranchConstruction
