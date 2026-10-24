import PPAC.Migration.Internal.ProjectionField

/-! 实际原Expr投影查询与其计算字段的数值关系；自然域由实际表达式图推出。 -/
namespace PPAC.Migration.Internal.ProjectionExprQueryTyping
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open YesMetaZFC.Automation.ObjectHorn (Expr)

theorem field_iff {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (es : Fin 3 → Expr a)
    (w x i y : Fin m) (env : Fin a → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env))
    (h0 : Derives Γ (graph (es 0) w env x)) (h1 : Derives Γ (graph (es 1) w env i)) (h2 : Derives Γ (graph (es 2) w env y)) :
    Derives Γ ((ProjectionExprQuery.query (Expr.node (.literal 2) (List.ofFn es)) w env).iff (RawCodeFieldSyntax.field w x i y)) := by
  have hs : ∀ j, Derives Γ (graph (es j) w env (SyntaxAtomSyntax.three x i y j)) :=
    Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (fun z => Fin.elim0 z)))
  have hrow := ProjectionExprQuery.constructor_query_iff hZ 3 2 es w env (SyntaxAtomSyntax.three x i y) hw hn hs
  have hfull := ProjectionField.checked_iff hZ w x i y hw
  have hx := HornExprRange.range hZ (es 0) w x env hw hn h0
  have hi := HornExprRange.range hZ (es 1) w i env hw hn h1
  have hremove : Derives Γ (((Formula.mem x w).conj ((Formula.mem i w).conj (RawCodeFieldSyntax.field w x i y))).iff
      (RawCodeFieldSyntax.field w x i y)) := by
    apply Derives.conjI
    · apply Derives.impI
      exact .conjR (.conjR (.hyp (Or.inl rfl)))
    · apply Derives.impI
      exact .conjI (add hx _) (.conjI (add hi _) (.hyp (Or.inl rfl)))
  exact SyntaxTypeLocalTransfer.iff_trans hrow (SyntaxTypeLocalTransfer.iff_trans hfull hremove)

end PPAC.Migration.Internal.ProjectionExprQueryTyping
