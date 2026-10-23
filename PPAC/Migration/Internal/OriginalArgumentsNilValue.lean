import PPAC.Migration.Internal.OriginalArgumentsRuleMatrix

/-! 原空参数表达式在全部内部候选上的精确Nil码对应，不预设候选为Nil。 -/
namespace PPAC.Migration.Internal.OriginalArgumentsNilValue
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

theorem nil_iff {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w y : Fin m) (env : Fin n → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env)) :
    Derives Γ ((graph (Expr.list []) w env y).iff (StructuralListSyntax.nilCode w y)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := graph (Expr.list []) w env y
    have he := SyntaxForests.exists_forest (ZFContext.add hZ E) 0 w Fin.elim0 (add hw E) (.eqRefl w)
    let B := (Formula.mem (Fin.last m) w.castSucc).conj (StructuralListSyntax.nilCode w.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) he
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hn1 : Derives Δ (environmentNat n w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename n w env Fin.castSucc) (under (add hn E) B)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hy1 : Derives Δ (graph (Expr.list []) w.castSucc (fun i => (env i).castSucc) y.castSucc) := of_eq (graph_rename (Expr.list []) w y env Fin.castSucc) (under hE B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have heq := HornExprUnique.unique (ZFContext.under (ZFContext.add hZ E) B) (Expr.list []) w.castSucc y.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hn1 hy1
      (HornExprStructural.nil_graph _ _ _ (.conjR hB))
    exact of_eq (StructuralListSyntax.nilCode_rename w y Fin.castSucc).symm (StructuralListTraceOrder.nil_output_subst _ _ _ (eq_symm heq) (.conjR hB))
  · apply Derives.impI
    exact HornExprStructural.nil_graph w y env (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.OriginalArgumentsNilValue
