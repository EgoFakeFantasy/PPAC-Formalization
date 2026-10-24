import PPAC.Migration.Internal.ProofTreeEquationUnique

/-! 原Node的实际有限Formula2模板确实满足递归方程；不只提供假设方程后的唯一性。 -/
namespace PPAC.Migration.Internal.ProofTreeEquationCanonical
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax ProofTreeInductionSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ProofTreeBranchConstruction (shape)

theorem args2_zero {α : Type} (x y : α) : SetLanguage.args2 x y 0 = x := rfl

theorem args2_last {α : Type} (x y : α) : SetLanguage.args2 x y (Fin.last 1) = y := by
  change Fin.cases x (SetLanguage.args1 y) (0 : Fin 1).succ = y
  simp only [Fin.cases_succ, SetLanguage.args1, Fin.cases_zero]

def nodeTemplate (test : Formula 1) : Formula 2 := ProofTreeEntrySyntax.node test (0 : Fin 2) (Fin.last 1)
attribute [local irreducible] nodeTemplate

theorem property_node {m} (test : Formula 1) (w code : Fin m) :
    property (nodeTemplate test) w code = ProofTreeEntrySyntax.node test w code := by
  simp only [property, nodeTemplate, ProofTreeEntryFacts.node_rename, args2_zero, args2_last]

theorem children_node {m a} (test : Formula 1) (is : List (Fin a)) (w : Fin m) (env : Fin a → Fin m) :
    children (nodeTemplate test) is w env = ProofTreeChildren.children test is w env := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [children, ProofTreeChildren.children, property_node, ih]

theorem matrix_node {m} (test : Formula 1) (kind : Fin 6) (w code : Fin m) (env : Fin ((shape kind).extra+2) → Fin m) :
    matrix (nodeTemplate test) kind w code env = ProofTreeNodeSyntax.matrix test kind w code env := by
  simp only [ProofTreeInductionSyntax.matrix, ProofTreeNodeSyntax.matrix, children_node]

theorem body_node {m} (test : Formula 1) (kind : Fin 6) (w code : Fin m) :
    body (nodeTemplate test) kind w code = ProofTreeNodeSyntax.body test kind w code := matrix_node test kind _ _ _

theorem branch_node {m} (test : Formula 1) (kind : Fin 6) (w code : Fin m) :
    branch (nodeTemplate test) kind w code = ProofTreeNodeSyntax.branch test kind w code := by
  simp only [branch, ProofTreeNodeSyntax.branch, body_node]

theorem cases_node {m} (test : Formula 1) (w code : Fin m) :
    cases (nodeTemplate test) w code = ProofTreeNodeSyntax.payloadCases test w code := by
  unfold cases ProofTreeNodeSyntax.payloadCases
  apply congrArg LogicalAllPatterns.disjoin
  apply List.map_congr_left
  intro kind _
  exact branch_node test kind w code

theorem normalized_node {m} (test : Formula 1) (w code : Fin m) :
    normalized test (nodeTemplate test) w code = ProofTreeNodeSyntax.normalized test w code := by
  simp only [normalized, ProofTreeNodeSyntax.normalized, cases_node]

theorem equation_proved {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (ProofTreeEquationSyntax.equation test (nodeTemplate test) w) := by
  unfold ProofTreeEquationSyntax.equation
  apply Derives.allI
  have hw1 := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  simpa only [property_node, normalized_node] using
    ProofTreeNodeBackward.node_iff test (ZFContext.rename hZ Fin.castSucc) w.castSucc (Fin.last m) hw1

end PPAC.Migration.Internal.ProofTreeEquationCanonical
