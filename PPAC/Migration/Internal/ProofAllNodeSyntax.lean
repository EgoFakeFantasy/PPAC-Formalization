import PPAC.Migration.Internal.ProofAllQueryBundles

/-! 直接按原六Shape的arity/head/Kind查询表构造完整纯关系局部表；理论测试明确参数化。 -/
namespace PPAC.Migration.Internal.ProofAllNodeSyntax
open Source SourceAlgebra SourceLogic HornExprSyntax HornBinderSyntax
open YesMetaZFC.Automation

def matrix {m} (test : Formula 1) (shape : ObjectProofNode.Shape) (w row : Fin m) (env : Fin shape.arity → Fin m) : Formula m :=
  (environmentNat shape.arity w env).conj ((HornExprBounds.environmentBound shape.arity row env).conj
    ((graph shape.head w env row).conj (ProofAllQuerySyntax.listBundle test shape.queries w env)))

def body {m} (test : Formula 1) (shape : ObjectProofNode.Shape) (w row : Fin m) : Formula (m+shape.arity) :=
  matrix test shape (old shape.arity w) (old shape.arity row) (slot shape.arity)

def node {m} (test : Formula 1) (shape : ObjectProofNode.Shape) (w row : Fin m) : Formula m :=
  existsMany shape.arity (body test shape w row)

def table {m} (test : Formula 1) (w row : Fin m) : Formula m :=
  LogicalAllPatterns.disjoin (ObjectProofNode.shapes.map (fun shape => node test shape w row))

theorem original_arity_order : ObjectProofNode.shapes.map (fun shape => shape.arity) = [3, 3, 5, 4, 4, 6] := rfl

theorem original_query_counts : ObjectProofNode.shapes.map (fun shape => shape.queries.length) = [1, 2, 6, 4, 4, 5] := rfl

def selectedNodes {m} (test : Formula 1) (w row : Fin m) : List (Formula m) := [
  ProofLogicalNodeSyntax.node w row,
  ProofTheoryNodeSyntax.node test w row,
  ProofMPNodeSyntax.node w row,
  ProofForallNodeSyntax.node w row,
  ProofStrengtheningNodeSyntax.node w row,
  ProofSubstitutionNodeSyntax.node w row]

def specificationNodes {m} (test : Formula 1) (w z row : Fin m) : List (Formula m) := [
  ProofLogicalNodeSyntax.normalized w z row,
  ProofTheoryNodeSyntax.normalized test w z row,
  ProofMPNodeSyntax.specification w z row,
  ProofForallNode.normalized w z row,
  ProofStrengtheningNodeSyntax.specification w z row,
  ProofSubstitutionNodeSyntax.specification w z row]

def selected {m} (test : Formula 1) (w row : Fin m) : Formula m := LogicalAllPatterns.disjoin (selectedNodes test w row)

def specification {m} (test : Formula 1) (w z row : Fin m) : Formula m := LogicalAllPatterns.disjoin (specificationNodes test w z row)

end PPAC.Migration.Internal.ProofAllNodeSyntax
