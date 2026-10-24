import PPAC.Migration.Internal.LogicalOriginalNodes

/-! 准确原27模式纯关系表的捕获规避重命名；用于对象EX中的实际查询行码。 -/
namespace PPAC.Migration.Internal.LogicalTableRenaming
open Source SourceAlgebra SourceLogic HornExprSyntax HornBinderSyntax
open YesMetaZFC.Automation

theorem listBundle_rename {m a l} (qs : List (Bool × ObjectHorn.Expr a)) (w : Fin m) (env : Fin a → Fin m) (ρ : Fin m → Fin l) :
    (LogicalStaticQueryList.listBundle qs w env).rename ρ = LogicalStaticQueryList.listBundle qs (ρ w) (fun i => ρ (env i)) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    rcases q with ⟨flag, expr⟩
    cases flag with
    | false =>
      change ((PureSyntaxExprQuery.query expr w env).rename ρ).conj ((LogicalStaticQueryList.listBundle qs w env).rename ρ) =
        (PureSyntaxExprQuery.query expr (ρ w) (fun i => ρ (env i))).conj (LogicalStaticQueryList.listBundle qs (ρ w) (fun i => ρ (env i)))
      rw [PureSyntaxExprQuery.query_rename, ih]
    | true =>
      change ((OriginalTransformExprQuery.query expr w env).rename ρ).conj ((LogicalStaticQueryList.listBundle qs w env).rename ρ) =
        (OriginalTransformExprQuery.query expr (ρ w) (fun i => ρ (env i))).conj (LogicalStaticQueryList.listBundle qs (ρ w) (fun i => ρ (env i)))
      rw [OriginalTransformExprQuery.query_rename, ih]

theorem matrix_rename {m l} (shape : ObjectLogicalAxiom.Shape) (w row : Fin m) (env : Fin shape.arity → Fin m) (ρ : Fin m → Fin l) :
    (LogicalOriginalNodeSyntax.matrix shape w row env).rename ρ = LogicalOriginalNodeSyntax.matrix shape (ρ w) (ρ row) (fun i => ρ (env i)) := by
  simp only [LogicalOriginalNodeSyntax.matrix, Formula.rename, environmentNat_rename, HornExprBounds.environmentBound_rename, graph_rename, listBundle_rename]

theorem body_lift {m l} (shape : ObjectLogicalAxiom.Shape) (w row : Fin m) (ρ : Fin m → Fin l) :
    (LogicalOriginalNodeSyntax.body shape w row).rename (lift shape.arity ρ) = LogicalOriginalNodeSyntax.body shape (ρ w) (ρ row) := by
  simp only [LogicalOriginalNodeSyntax.body, matrix_rename, lift_old, lift_slot]

theorem node_rename {m l} (shape : ObjectLogicalAxiom.Shape) (w row : Fin m) (ρ : Fin m → Fin l) :
    (LogicalOriginalNodeSyntax.node shape w row).rename ρ = LogicalOriginalNodeSyntax.node shape (ρ w) (ρ row) := by
  simp only [LogicalOriginalNodeSyntax.node, existsMany_rename, body_lift]

theorem disjoin_rename {m l} (ps : List (Formula m)) (ρ : Fin m → Fin l) :
    (LogicalAllPatterns.disjoin ps).rename ρ = LogicalAllPatterns.disjoin (ps.map (fun p => p.rename ρ)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => exact congrArg (Formula.disj (p.rename ρ)) ih

theorem table_rename {m l} (w row : Fin m) (ρ : Fin m → Fin l) :
    (LogicalOriginalNodeSyntax.table w row).rename ρ = LogicalOriginalNodeSyntax.table (ρ w) (ρ row) := by
  unfold LogicalOriginalNodeSyntax.table
  rw [disjoin_rename, List.map_map]
  congr 1
  apply List.map_congr_left
  intro shape _
  exact node_rename shape w row ρ

end PPAC.Migration.Internal.LogicalTableRenaming
