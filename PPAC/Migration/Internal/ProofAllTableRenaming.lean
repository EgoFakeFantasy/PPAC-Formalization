import PPAC.Migration.Internal.ProofAllNodes

/-! 原五Kind查询及完整六类局部表的捕获规避重命名，公理测试参数保持同一对象公式。 -/
namespace PPAC.Migration.Internal.ProofAllTableRenaming
open Source SourceAlgebra SourceLogic HornExprSyntax HornBinderSyntax
open YesMetaZFC.Automation

theorem query_rename {m a l} (test : Formula 1) (kind : ObjectProofNode.Kind) (e : ObjectHorn.Expr a) (w : Fin m) (env : Fin a → Fin m) (ρ : Fin m → Fin l) :
    (ProofAllQuerySyntax.query test kind e w env).rename ρ = ProofAllQuerySyntax.query test kind e (ρ w) (fun i => ρ (env i)) := by
  cases kind
  · exact ProjectionExprQuery.query_rename e w env ρ
  · exact PureSyntaxExprQuery.query_rename e w env ρ
  · exact OriginalTransformExprQuery.query_rename e w env ρ
  · exact OriginalLogicalExprQuery.query_rename e w env ρ
  · exact OriginalAxiomExprQuery.query_rename test e w env ρ

theorem listBundle_rename {m a l} (test : Formula 1) (qs : List (ObjectProofNode.Kind × ObjectHorn.Expr a)) (w : Fin m) (env : Fin a → Fin m) (ρ : Fin m → Fin l) :
    (ProofAllQuerySyntax.listBundle test qs w env).rename ρ = ProofAllQuerySyntax.listBundle test qs (ρ w) (fun i => ρ (env i)) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    rcases q with ⟨kind, e⟩
    change ((ProofAllQuerySyntax.query test kind e w env).rename ρ).conj ((ProofAllQuerySyntax.listBundle test qs w env).rename ρ) =
      (ProofAllQuerySyntax.query test kind e (ρ w) (fun i => ρ (env i))).conj (ProofAllQuerySyntax.listBundle test qs (ρ w) (fun i => ρ (env i)))
    rw [query_rename, ih]

theorem matrix_rename {m l} (test : Formula 1) (shape : ObjectProofNode.Shape) (w row : Fin m) (env : Fin shape.arity → Fin m) (ρ : Fin m → Fin l) :
    (ProofAllNodeSyntax.matrix test shape w row env).rename ρ = ProofAllNodeSyntax.matrix test shape (ρ w) (ρ row) (fun i => ρ (env i)) := by
  simp only [ProofAllNodeSyntax.matrix, Formula.rename, environmentNat_rename, HornExprBounds.environmentBound_rename, graph_rename, listBundle_rename]

theorem body_lift {m l} (test : Formula 1) (shape : ObjectProofNode.Shape) (w row : Fin m) (ρ : Fin m → Fin l) :
    (ProofAllNodeSyntax.body test shape w row).rename (lift shape.arity ρ) = ProofAllNodeSyntax.body test shape (ρ w) (ρ row) := by
  simp only [ProofAllNodeSyntax.body, matrix_rename, lift_old, lift_slot]

theorem node_rename {m l} (test : Formula 1) (shape : ObjectProofNode.Shape) (w row : Fin m) (ρ : Fin m → Fin l) :
    (ProofAllNodeSyntax.node test shape w row).rename ρ = ProofAllNodeSyntax.node test shape (ρ w) (ρ row) := by
  simp only [ProofAllNodeSyntax.node, existsMany_rename, body_lift]

theorem table_rename {m l} (test : Formula 1) (w row : Fin m) (ρ : Fin m → Fin l) :
    (ProofAllNodeSyntax.table test w row).rename ρ = ProofAllNodeSyntax.table test (ρ w) (ρ row) := by
  unfold ProofAllNodeSyntax.table
  rw [LogicalTableRenaming.disjoin_rename, List.map_map]
  congr 1
  apply List.map_congr_left
  intro shape _
  exact node_rename test shape w row ρ

end PPAC.Migration.Internal.ProofAllTableRenaming
