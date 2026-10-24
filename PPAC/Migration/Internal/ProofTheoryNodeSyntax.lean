import PPAC.Migration.Internal.ProofTheoryQueries

/-! 完整原三赋值块；独立数值头规格。理论公理测试保持显式对象公式参数。 -/
namespace PPAC.Migration.Internal.ProofTheoryNodeSyntax
open Source SourceAlgebra SourceLogic HornExprSyntax HornBinderSyntax
open YesMetaZFC.Automation

def boundedMatrix {m} (test : Formula 1) (w row : Fin m) (env : Fin 3 → Fin m) : Formula m :=
  (environmentNat 3 w env).conj ((HornExprBounds.environmentBound 3 row env).conj
    ((graph ObjectProofNode.theoryShape.head w env row).conj (ProofTheorySyntax.bundle test w env)))

def normalizedMatrix {m} (test : Formula 1) (w z row : Fin m) (env : Fin 3 → Fin m) : Formula m :=
  (environmentNat 3 w env).conj ((SyntaxNodeSyntax.constructor 3 1 w env row).conj (ProofTheorySyntax.specification test w z env))

def body {m} (test : Formula 1) (w row : Fin m) : Formula (m+3) := boundedMatrix test (old 3 w) (old 3 row) (slot 3)

def normalizedBody {m} (test : Formula 1) (w z row : Fin m) : Formula (m+3) := normalizedMatrix test (old 3 w) (old 3 z) (old 3 row) (slot 3)

def node {m} (test : Formula 1) (w row : Fin m) : Formula m := existsMany 3 (body test w row)

def normalized {m} (test : Formula 1) (w z row : Fin m) : Formula m := existsMany 3 (normalizedBody test w z row)

end PPAC.Migration.Internal.ProofTheoryNodeSyntax
