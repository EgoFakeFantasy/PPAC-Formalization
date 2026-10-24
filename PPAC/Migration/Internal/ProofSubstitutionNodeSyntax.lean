import PPAC.Migration.Internal.ProofSubstitutionBounds
import PPAC.Migration.Internal.HornApplicationBounds

/-! 原替换模式的完整纯关系式局部节点：实际原头、全部五查询及原六赋值有界存在块。 -/
namespace PPAC.Migration.Internal.ProofSubstitutionNodeSyntax
open Source SourceAlgebra SourceLogic HornExprSyntax HornBinderSyntax
open YesMetaZFC.Automation

def queryMatrix {m} (w row : Fin m) (env : Fin 6 → Fin m) : Formula m :=
  (graph ObjectProofNode.substitutionShape.head w env row).conj (ProofSubstitutionAllQueries.bundle w env)

def boundedMatrix {m} (w row : Fin m) (env : Fin 6 → Fin m) : Formula m :=
  (environmentNat 6 w env).conj ((HornExprBounds.environmentBound 6 row env).conj (queryMatrix w row env))

def specificationMatrix {m} (w z row : Fin m) (env : Fin 6 → Fin m) : Formula m :=
  (environmentNat 6 w env).conj ((graph ObjectProofNode.substitutionShape.head w env row).conj
    (ProofSubstitutionAllQueries.specification w z env))

def body {m} (w row : Fin m) : Formula (m+6) := boundedMatrix (old 6 w) (old 6 row) (slot 6)
def specificationBody {m} (w z row : Fin m) : Formula (m+6) := specificationMatrix (old 6 w) (old 6 z) (old 6 row) (slot 6)
def node {m} (w row : Fin m) : Formula m := existsMany 6 (body w row)
def specification {m} (w z row : Fin m) : Formula m := existsMany 6 (specificationBody w z row)

theorem queryMatrix_rename {m l} (w row : Fin m) (env : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (queryMatrix w row env).rename ρ = queryMatrix (ρ w) (ρ row) (fun j => ρ (env j)) := by
  simp only [queryMatrix, Formula.rename, graph_rename, ProofSubstitutionAllQueries.bundle_rename]

theorem boundedMatrix_rename {m l} (w row : Fin m) (env : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (boundedMatrix w row env).rename ρ = boundedMatrix (ρ w) (ρ row) (fun j => ρ (env j)) := by
  simp only [boundedMatrix, Formula.rename, environmentNat_rename, HornExprBounds.environmentBound_rename, queryMatrix_rename]

theorem specificationMatrix_rename {m l} (w z row : Fin m) (env : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (specificationMatrix w z row env).rename ρ = specificationMatrix (ρ w) (ρ z) (ρ row) (fun j => ρ (env j)) := by
  simp only [specificationMatrix, Formula.rename, environmentNat_rename, graph_rename, ProofSubstitutionAllQueries.specification_rename]

theorem body_lift {m l} (w row : Fin m) (ρ : Fin m → Fin l) :
    (body w row).rename (lift 6 ρ) = body (ρ w) (ρ row) := by
  simp only [body, boundedMatrix_rename, lift_old, lift_slot]

theorem specificationBody_lift {m l} (w z row : Fin m) (ρ : Fin m → Fin l) :
    (specificationBody w z row).rename (lift 6 ρ) = specificationBody (ρ w) (ρ z) (ρ row) := by
  simp only [specificationBody, specificationMatrix_rename, lift_old, lift_slot]

theorem node_rename {m l} (w row : Fin m) (ρ : Fin m → Fin l) :
    (node w row).rename ρ = node (ρ w) (ρ row) := by simp only [node, existsMany_rename, body_lift]

theorem specification_rename {m l} (w z row : Fin m) (ρ : Fin m → Fin l) :
    (specification w z row).rename ρ = specification (ρ w) (ρ z) (ρ row) := by
  simp only [specification, existsMany_rename, specificationBody_lift]

end PPAC.Migration.Internal.ProofSubstitutionNodeSyntax
