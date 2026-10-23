import PPAC.Migration.Internal.OriginalVariableDispatch

/-! 原变量Expr的代码图从实际内部scalar／变量码取得，不执行宿主变量构造。 -/
namespace PPAC.Migration.Internal.HornVariableExpr
open Source SourceAlgebra SourceLogic HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

def expression {n} (bound : Bool) (e : Expr n) : Expr n :=
  Expr.node (.literal (SyntaxVariableSyntax.tag bound)) [Expr.node e []]

theorem actual_expression {n} (bound : Bool) (e : Expr n) : expression bound e =
    YesMetaZFC.Automation.ObjectSyntaxTransform.varCode (!bound) e := by cases bound <;> rfl

theorem code_graph {m n} {Γ : Context m} (bound : Bool) (e : Expr n) (w idx y : Fin m) (env : Fin n → Fin m)
    (hi : Derives Γ (graph e w env idx)) (hc : Derives Γ (SyntaxVariableSyntax.code bound w idx y)) :
    Derives Γ (graph (expression bound e) w env y) := by
  let B := SyntaxVariableSyntax.codeBody bound w idx y
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply SyntaxVariableSyntax.eliminate_code bound w idx y _ hc
  have hi1 : Derives Δ (graph e w.castSucc (fun i => (env i).castSucc) idx.castSucc) := of_eq (graph_rename e w idx env Fin.castSucc) (under hi B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hs := HornExprForest.node_graph 0 e Fin.elim0 w.castSucc idx.castSucc (Fin.last m) (fun i => (env i).castSucc) Fin.elim0 hi1 (fun i => Fin.elim0 i) (.conjL hB)
  have ho := HornExprForest.constructor_graph 1 (SyntaxVariableSyntax.tag bound) (fun _ => Expr.node e []) w.castSucc y.castSucc
    (fun i => (env i).castSucc) (fun _ => Fin.last m) (fun _ => hs) (.conjR hB)
  exact of_eq (graph_rename (expression bound e) w y env Fin.castSucc).symm ho

end PPAC.Migration.Internal.HornVariableExpr
