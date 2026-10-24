import PPAC.Migration.Internal.ProofLogicalNode
import PPAC.Migration.Internal.ProofTheoryNode
import PPAC.Migration.Internal.ProofMPNode
import PPAC.Migration.Internal.ProofForallNode
import PPAC.Migration.Internal.ProofStrengtheningNode
import PPAC.Migration.Internal.ProofSubstitutionNode

/-! 六类原证明节点的五种查询；axiom测试为明确对象一元公式，未默认任何理论。 -/
namespace PPAC.Migration.Internal.ProofAllQuerySyntax
open Source SourceAlgebra SourceLogic
open YesMetaZFC.Automation
open YesMetaZFC.Automation.ObjectHorn (Expr)

def query {m a} (test : Formula 1) : ObjectProofNode.Kind → Expr a → Fin m → (Fin a → Fin m) → Formula m
  | .projection, e, w, env => ProjectionExprQuery.query e w env
  | .syntax, e, w, env => PureSyntaxExprQuery.query e w env
  | .transform, e, w, env => OriginalTransformExprQuery.query e w env
  | .logical, e, w, env => OriginalLogicalExprQuery.query e w env
  | .axiom, e, w, env => OriginalAxiomExprQuery.query test e w env

def listBundle {m a} (test : Formula 1) : List (ObjectProofNode.Kind × Expr a) → Fin m → (Fin a → Fin m) → Formula m
  | .nil, _, _ => HornRuleSyntax.truth
  | .cons (kind, e) rest, w, env => (query test kind e w env).conj (listBundle test rest w env)

end PPAC.Migration.Internal.ProofAllQuerySyntax
