import PPAC.Migration.Internal.ProofSubstitutionProjection

/-! 原固定投影表达式的通用0／1读取；运行数码值只由对象图和对象数码公式给出。 -/
namespace PPAC.Migration.Internal.ProofProjectionExpr
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open ProofSubstitutionProjectionSyntax (atOne atOne_rename intro_atOne)
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation

def expr {a} (k : Nat) (input output : Expr a) : Expr a := (ObjectProofNode.projection input k output).2
def fields {a} (k : Nat) (input output : Expr a) : Fin 3 → Expr a := ProjectionTracePremises.three input (.literal k) output

theorem actual_expr {a} (k : Nat) (input output : Expr a) : expr k input output = Expr.node (.literal 2) (List.ofFn (fields k input output)) := rfl

theorem zero_iff {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (input output : Expr a)
    (w z p y : Fin m) (env : Fin a → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env))
    (hz : Derives Γ (empty z)) (hp : Derives Γ (graph input w env p)) (hy : Derives Γ (graph output w env y)) :
    Derives Γ ((ProjectionExprQuery.query (expr 0 input output) w env).iff (RawCodeFieldSyntax.field w p z y)) := by
  rw [actual_expr]
  exact ProjectionExprQueryTyping.field_iff hZ (fields 0 input output) w p z y env hw hn hp hz hy

theorem one_at {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (input output : Expr a)
    (w one p y : Fin m) (env : Fin a → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env))
    (ho : Derives Γ (SyntaxNumeralSyntax.numeral 1 one)) (hp : Derives Γ (graph input w env p)) (hy : Derives Γ (graph output w env y)) :
    Derives Γ ((ProjectionExprQuery.query (expr 1 input output) w env).iff (RawCodeFieldSyntax.field w p one y)) := by
  rw [actual_expr]
  exact ProjectionExprQueryTyping.field_iff hZ (fields 1 input output) w p one y env hw hn hp ho hy

theorem one_iff {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (input output : Expr a)
    (w p y : Fin m) (env : Fin a → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env))
    (hp : Derives Γ (graph input w env p)) (hy : Derives Γ (graph output w env y)) :
    Derives Γ ((ProjectionExprQuery.query (expr 1 input output) w env).iff (atOne w p y)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := ProjectionExprQuery.query (expr 1 input output) w env
    let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral 1 (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (SyntaxNumerals.exists_numeral (ZFContext.add hZ E) 1 w (add hw E))
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename a w env Fin.castSucc) (lift hn)
    have hp1 := of_eq (graph_rename input w p env Fin.castSucc) (lift hp)
    have hy1 := of_eq (graph_rename output w y env Fin.castSucc) (lift hy)
    have hq : Derives Δ (ProjectionExprQuery.query (expr 1 input output) w.castSucc (fun j => (env j).castSucc)) :=
      of_eq (ProjectionExprQuery.query_rename _ w env Fin.castSucc) (under (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl)) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hf := Derives.impE (.conjL (one_at (ZFContext.under (ZFContext.add hZ E) B) input output _ _ _ _ _ hw1 hn1 (.conjR hB) hp1 hy1)) hq
    exact of_eq (atOne_rename w p y Fin.castSucc).symm (intro_atOne _ _ _ _ (.conjR hB) hf)
  · apply Derives.impI
    let E := atOne w p y
    let B := (SyntaxNumeralSyntax.numeral 1 (Fin.last m)).conj (RawCodeFieldSyntax.field w.castSucc p.castSucc (Fin.last m) y.castSucc)
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename a w env Fin.castSucc) (lift hn)
    have hp1 := of_eq (graph_rename input w p env Fin.castSucc) (lift hp)
    have hy1 := of_eq (graph_rename output w y env Fin.castSucc) (lift hy)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hq := Derives.impE (.conjR (one_at (ZFContext.under (ZFContext.add hZ E) B) input output _ _ _ _ _ hw1 hn1 (.conjL hB) hp1 hy1)) (.conjR hB)
    exact of_eq (ProjectionExprQuery.query_rename _ w env Fin.castSucc).symm hq

end PPAC.Migration.Internal.ProofProjectionExpr
