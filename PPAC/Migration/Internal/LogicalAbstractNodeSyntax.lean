import PPAC.Migration.Internal.LogicalRule21Head
import PPAC.Migration.Internal.LogicalRule24Head
import PPAC.Migration.Internal.LogicalAbstractQueryList

/-! 原21／24完整赋值块及独立数值头规格；接受式保留实际查询。 -/
namespace PPAC.Migration.Internal.LogicalAbstractNodeSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open YesMetaZFC.Automation

def head21 := ObjectLogicalAxiom.rule21.head

theorem head21_variables : ∀ i, i ∈ head21.variables := by decide

def queryMatrix21 {m} (w row : Fin m) (env : Fin 5 → Fin m) : Formula m :=
  (graph head21 w env row).conj (LogicalAbstractSyntax.bundle21 w env)

def boundedMatrix21 {m} (w row : Fin m) (env : Fin 5 → Fin m) : Formula m :=
  (environmentNat 5 w env).conj ((HornExprBounds.environmentBound 5 row env).conj (queryMatrix21 w row env))

def normalizedMatrix21 {m} (w z row : Fin m) (env : Fin 5 → Fin m) : Formula m :=
  (environmentNat 5 w env).conj ((LogicalRule21Head.normalized w row env).conj (LogicalAbstractSyntax.specification21 w z env))

def body21 {m} (w row : Fin m) : Formula (m+5) := boundedMatrix21 (old 5 w) (old 5 row) (slot 5)

def normalizedBody21 {m} (w z row : Fin m) : Formula (m+5) := normalizedMatrix21 (old 5 w) (old 5 z) (old 5 row) (slot 5)

def node21 {m} (w row : Fin m) : Formula m := existsMany 5 (body21 w row)

def normalized21 {m} (w z row : Fin m) : Formula m := existsMany 5 (normalizedBody21 w z row)

def head24 := ObjectLogicalAxiom.rule24.head

theorem head24_variables : ∀ i, i ∈ head24.variables := by decide

def queryMatrix24 {m} (w row : Fin m) (env : Fin 4 → Fin m) : Formula m :=
  (graph head24 w env row).conj (LogicalAbstractSyntax.bundle24 w env)

def boundedMatrix24 {m} (w row : Fin m) (env : Fin 4 → Fin m) : Formula m :=
  (environmentNat 4 w env).conj ((HornExprBounds.environmentBound 4 row env).conj (queryMatrix24 w row env))

def normalizedMatrix24 {m} (w z row : Fin m) (env : Fin 4 → Fin m) : Formula m :=
  (environmentNat 4 w env).conj ((LogicalRule24Head.normalized w row env).conj (LogicalAbstractSyntax.specification24 w z env))

def body24 {m} (w row : Fin m) : Formula (m+4) := boundedMatrix24 (old 4 w) (old 4 row) (slot 4)

def normalizedBody24 {m} (w z row : Fin m) : Formula (m+4) := normalizedMatrix24 (old 4 w) (old 4 z) (old 4 row) (slot 4)

def node24 {m} (w row : Fin m) : Formula m := existsMany 4 (body24 w row)

def normalized24 {m} (w z row : Fin m) : Formula m := existsMany 4 (normalizedBody24 w z row)

end PPAC.Migration.Internal.LogicalAbstractNodeSyntax
