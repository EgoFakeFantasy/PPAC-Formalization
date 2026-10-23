import PPAC.Migration.Internal.HornExprStructural

/-! 上游Expr.list的实际内部值由原森林构造取得，字段为任意内部表达式值。 -/
namespace PPAC.Migration.Internal.HornExprForest
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

theorem forest_graph {m n} {Γ : Context m} (k : Nat) (exprs : Fin k → Expr n)
    (w y : Fin m) (env : Fin n → Fin m) (xs : Fin k → Fin m)
    (hs : ∀ i, Derives Γ (graph (exprs i) w env (xs i)))
    (hy : Derives Γ (SyntaxForestSyntax.forest k w xs y)) :
    Derives Γ (graph (Expr.list (List.ofFn exprs)) w env y) := by
  induction k generalizing m with
  | zero => simpa only [List.ofFn_zero, SyntaxForestSyntax.forest] using HornExprStructural.nil_graph w y env hy
  | succ k ih =>
    let T := (Formula.mem (xs 0).castSucc w.castSucc).conj
      ((SyntaxForestSyntax.forest k w.castSucc (fun i => (xs i.succ).castSucc) (Fin.last m)).conj
        (StructuralListSyntax.consCode w.castSucc (xs 0).castSucc (Fin.last m) y.castSucc))
    let Δ := Context.add T (Context.image Formula.raise Γ)
    apply Derives.exE (p := T) hy
    have hs1 (i : Fin (k+1)) : Derives Δ (graph (exprs i) w.castSucc (fun j => (env j).castSucc) (xs i).castSucc) :=
      of_eq (graph_rename (exprs i) w (xs i) env Fin.castSucc) (under (hs i) T)
    have hT : Derives Δ T := .hyp (Or.inl rfl)
    have ht := ih (fun i => exprs i.succ) w.castSucc (Fin.last m) (fun j => (env j).castSucc) (fun i => (xs i.succ).castSucc) (fun i => hs1 i.succ) (.conjL (.conjR hT))
    have ho := HornExprStructural.cons_graph (exprs 0) (Expr.list (List.ofFn (fun i => exprs i.succ))) _ _ _ _ _ (hs1 0) ht (.conjR (.conjR hT))
    exact of_eq (by simp only [Formula.raise, graph_rename, List.ofFn_succ, Expr.list]) ho

theorem node_graph {m n} {Γ : Context m} (k : Nat) (tag : Expr n) (exprs : Fin k → Expr n)
    (w t y : Fin m) (env : Fin n → Fin m) (xs : Fin k → Fin m)
    (ht : Derives Γ (graph tag w env t)) (hs : ∀ i, Derives Γ (graph (exprs i) w env (xs i)))
    (hy : Derives Γ (SyntaxNodeSyntax.node k w t xs y)) :
    Derives Γ (graph (Expr.node tag (List.ofFn exprs)) w env y) := by
  let P := SyntaxNodeSyntax.nodeBody k w t xs y
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) hy
  have ht1 := of_eq (graph_rename tag w t env Fin.castSucc) (under ht P)
  have hs1 (i : Fin k) : Derives Δ (graph (exprs i) w.castSucc (fun j => (env j).castSucc) (xs i).castSucc) :=
    of_eq (graph_rename (exprs i) w (xs i) env Fin.castSucc) (under (hs i) P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have ho := HornExprStructural.raw_graph tag (Expr.list (List.ofFn exprs)) _ _ _ _ _ ht1
    (forest_graph k exprs _ _ _ _ hs1 (.conjL (.conjR hP))) (.conjR (.conjR hP))
  exact of_eq (graph_rename (Expr.node tag (List.ofFn exprs)) w y env Fin.castSucc).symm ho

theorem constructor_graph {m n} {Γ : Context m} (k tag : Nat) (exprs : Fin k → Expr n)
    (w y : Fin m) (env : Fin n → Fin m) (xs : Fin k → Fin m)
    (hs : ∀ i, Derives Γ (graph (exprs i) w env (xs i)))
    (hy : Derives Γ (SyntaxNodeSyntax.constructor k tag w xs y)) :
    Derives Γ (graph (Expr.node (.literal tag) (List.ofFn exprs)) w env y) := by
  let T := SyntaxNodeSyntax.constructorBody k tag w xs y
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) hy
  have hs1 (i : Fin k) : Derives Δ (graph (exprs i) w.castSucc (fun j => (env j).castSucc) (xs i).castSucc) :=
    of_eq (graph_rename (exprs i) w (xs i) env Fin.castSucc) (under (hs i) T)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact of_eq (graph_rename (Expr.node (.literal tag) (List.ofFn exprs)) w y env Fin.castSucc).symm
    (node_graph k (.literal tag) exprs _ _ _ _ _ (.conjL hT) hs1 (.conjR hT))

end PPAC.Migration.Internal.HornExprForest
