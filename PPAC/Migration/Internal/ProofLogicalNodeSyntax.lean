import PPAC.Migration.Internal.ProofLogicalQueries

/-! 完整原三赋值块；独立数值头规格。理论公理测试保持显式对象公式参数。 -/
namespace PPAC.Migration.Internal.ProofLogicalNodeSyntax
open Source SourceAlgebra SourceLogic HornExprSyntax HornBinderSyntax
open YesMetaZFC.Automation

def boundedMatrix {m} (w row : Fin m) (env : Fin 3 → Fin m) : Formula m :=
  (environmentNat 3 w env).conj ((HornExprBounds.environmentBound 3 row env).conj
    ((graph ObjectProofNode.logicalShape.head w env row).conj (ProofLogicalSyntax.bundle w env)))

def normalizedMatrix {m} (w z row : Fin m) (env : Fin 3 → Fin m) : Formula m :=
  (environmentNat 3 w env).conj ((SyntaxNodeSyntax.constructor 3 0 w env row).conj (ProofLogicalSyntax.specification w z env))

def body {m} (w row : Fin m) : Formula (m+3) := boundedMatrix (old 3 w) (old 3 row) (slot 3)

def normalizedBody {m} (w z row : Fin m) : Formula (m+3) := normalizedMatrix (old 3 w) (old 3 z) (old 3 row) (slot 3)

def node {m} (w row : Fin m) : Formula m := existsMany 3 (body w row)

def normalized {m} (w z row : Fin m) : Formula m := existsMany 3 (normalizedBody w z row)

end PPAC.Migration.Internal.ProofLogicalNodeSyntax
