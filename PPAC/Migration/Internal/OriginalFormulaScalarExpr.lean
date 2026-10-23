import PPAC.Migration.Internal.OriginalFormulaRowGraph

/-! 实际变量标签的零字段节点对应；关系符号码不以宿主数值替代。 -/
namespace PPAC.Migration.Internal.OriginalFormulaScalarExpr
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

theorem scalar_graph {m a} {Γ : Context m} (i : Fin a) (w y : Fin m) (env : Fin a → Fin m)
    (hn : Derives Γ (environmentNat a w env)) (hy : Derives Γ (SyntaxNodeSyntax.scalar w (env i) y)) :
    Derives Γ (graph (Expr.node (.var i) []) w env y) := by
  have ht : Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl _)
  simpa only [List.ofFn_zero, SyntaxNodeSyntax.scalar] using HornExprForest.node_graph 0 (.var i) Fin.elim0 w (env i) y env Fin.elim0 ht (fun j => Fin.elim0 j) hy

theorem scalar_iff {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (i : Fin a) (w y : Fin m) (env : Fin a → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env)) :
    Derives Γ ((graph (Expr.node (.var i) []) w env y).iff (SyntaxNodeSyntax.scalar w (env i) y)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := graph (Expr.node (.var i) []) w env y
    have he := SyntaxNodes.exists_node (ZFContext.add hZ E) 0 w (env i) Fin.elim0 (add hw E) (add (environmentNat_at w env hn i) E) (.eqRefl w)
    let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNodeSyntax.scalar w.castSucc (env i).castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) he
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hn1 : Derives Δ (environmentNat a w.castSucc (fun j => (env j).castSucc)) := of_eq (environmentNat_rename a w env Fin.castSucc) (under (add hn E) B)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hg1 : Derives Δ (graph (Expr.node (.var i) []) w.castSucc (fun j => (env j).castSucc) y.castSucc) := of_eq (graph_rename _ w y env Fin.castSucc) (under hE B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hEq := HornExprUnique.unique (ZFContext.under (ZFContext.add hZ E) B) (Expr.node (.var i) []) w.castSucc y.castSucc (Fin.last m) (fun j => (env j).castSucc) hw1 hn1 hg1 (scalar_graph i w.castSucc (Fin.last m) (fun j => (env j).castSucc) hn1 (.conjR hB))
    exact of_eq (SyntaxNodeSyntax.scalar_rename w (env i) y Fin.castSucc).symm (SyntaxNodeInjective.scalar_output_subst _ _ _ _ (eq_symm hEq) (.conjR hB))
  · apply Derives.impI
    exact scalar_graph i w y env (add hn _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.OriginalFormulaScalarExpr
