import PPAC.Migration.Internal.LogicalAllPatterns
import PPAC.Migration.Internal.LogicalOriginalQueryBundles

/-! 直接按原Shape的arity／head／有序查询表构造完整纯关系节点，无规格调用。 -/
namespace PPAC.Migration.Internal.LogicalOriginalNodeSyntax
open Source SourceAlgebra SourceLogic HornExprSyntax HornBinderSyntax
open YesMetaZFC.Automation

def matrix {m} (shape : ObjectLogicalAxiom.Shape) (w row : Fin m) (env : Fin shape.arity → Fin m) : Formula m :=
  (environmentNat shape.arity w env).conj ((HornExprBounds.environmentBound shape.arity row env).conj
    ((graph shape.head w env row).conj (LogicalStaticQueryList.listBundle shape.queries w env)))

def body {m} (shape : ObjectLogicalAxiom.Shape) (w row : Fin m) : Formula (m+shape.arity) :=
  matrix shape (old shape.arity w) (old shape.arity row) (slot shape.arity)

def node {m} (shape : ObjectLogicalAxiom.Shape) (w row : Fin m) : Formula m :=
  existsMany shape.arity (body shape w row)

def table {m} (w row : Fin m) : Formula m :=
  LogicalAllPatterns.disjoin (ObjectLogicalAxiom.shapes.map (fun shape => node shape w row))

end PPAC.Migration.Internal.LogicalOriginalNodeSyntax
