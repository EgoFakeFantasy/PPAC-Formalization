import PPAC.Migration.Internal.ProofForallBounds
import PPAC.Migration.Internal.HornApplicationBounds

/-! 原forall模式的完整纯关系式局部节点：实际原头、全部四查询及原四赋值有界存在块。 -/
namespace PPAC.Migration.Internal.ProofForallNodeSyntax
open Source SourceAlgebra SourceLogic HornExprSyntax HornBinderSyntax
open YesMetaZFC.Automation

def queryMatrix {m} (w row : Fin m) (env : Fin 4 → Fin m) : Formula m :=
  (graph ObjectProofNode.forallShape.head w env row).conj (ProofForallSyntax.bundle w env)

def boundedMatrix {m} (w row : Fin m) (env : Fin 4 → Fin m) : Formula m :=
  (environmentNat 4 w env).conj ((HornExprBounds.environmentBound 4 row env).conj (queryMatrix w row env))

def specificationMatrix {m} (w z row : Fin m) (env : Fin 4 → Fin m) : Formula m :=
  (environmentNat 4 w env).conj ((graph ObjectProofNode.forallShape.head w env row).conj
    (ProofForallSyntax.specification w z env))

def body {m} (w row : Fin m) : Formula (m+4) := boundedMatrix (old 4 w) (old 4 row) (slot 4)
def specificationBody {m} (w z row : Fin m) : Formula (m+4) := specificationMatrix (old 4 w) (old 4 z) (old 4 row) (slot 4)
def node {m} (w row : Fin m) : Formula m := existsMany 4 (body w row)
def specification {m} (w z row : Fin m) : Formula m := existsMany 4 (specificationBody w z row)

theorem queryMatrix_rename {m l} (w row : Fin m) (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (queryMatrix w row env).rename ρ = queryMatrix (ρ w) (ρ row) (fun j => ρ (env j)) := by
  simp only [queryMatrix, Formula.rename, graph_rename, ProofForallSyntax.bundle_rename]

theorem boundedMatrix_rename {m l} (w row : Fin m) (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (boundedMatrix w row env).rename ρ = boundedMatrix (ρ w) (ρ row) (fun j => ρ (env j)) := by
  simp only [boundedMatrix, Formula.rename, environmentNat_rename, HornExprBounds.environmentBound_rename, queryMatrix_rename]

theorem specificationMatrix_rename {m l} (w z row : Fin m) (env : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (specificationMatrix w z row env).rename ρ = specificationMatrix (ρ w) (ρ z) (ρ row) (fun j => ρ (env j)) := by
  simp only [specificationMatrix, Formula.rename, environmentNat_rename, graph_rename, ProofForallSyntax.specification_rename]

theorem body_lift {m l} (w row : Fin m) (ρ : Fin m → Fin l) :
    (body w row).rename (lift 4 ρ) = body (ρ w) (ρ row) := by
  simp only [body, boundedMatrix_rename, lift_old, lift_slot]

theorem specificationBody_lift {m l} (w z row : Fin m) (ρ : Fin m → Fin l) :
    (specificationBody w z row).rename (lift 4 ρ) = specificationBody (ρ w) (ρ z) (ρ row) := by
  simp only [specificationBody, specificationMatrix_rename, lift_old, lift_slot]

theorem node_rename {m l} (w row : Fin m) (ρ : Fin m → Fin l) :
    (node w row).rename ρ = node (ρ w) (ρ row) := by simp only [node, existsMany_rename, body_lift]

theorem specification_rename {m l} (w z row : Fin m) (ρ : Fin m → Fin l) :
    (specification w z row).rename ρ = specification (ρ w) (ρ z) (ρ row) := by
  simp only [specification, existsMany_rename, specificationBody_lift]

end PPAC.Migration.Internal.ProofForallNodeSyntax
