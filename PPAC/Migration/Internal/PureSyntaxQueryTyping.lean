import PPAC.Migration.Internal.PureSyntaxExprQuery

/-! 原固定语法查询表达式与纯类型在全部内部实际字段处等价，行码见证已消去。 -/
namespace PPAC.Migration.Internal.PureSyntaxQueryTyping
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax PureSyntaxExprQuery
open YesMetaZFC.Automation.ObjectHorn (Expr)

theorem term_iff {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (es : Fin 3 → Expr a)
    (w b f n : Fin m) (env : Fin a → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env))
    (hs : ∀ i, Derives Γ (graph (es i) w env (SyntaxAtomSyntax.three b f n i))) :
    Derives Γ ((query (Expr.node (.literal 0) (List.ofFn es)) w env).iff (SyntaxTermSyntax.term w b f n)) := by
  have ht : Derives Γ ((rowQuery 3 0 w (SyntaxAtomSyntax.three b f n)).iff (SyntaxTermSyntax.term w b f n)) := by
    simpa only [rowQuery, PureSyntaxTrace.term, PureSyntaxTrace.termRow, SyntaxAtomSyntax.three_map] using PureSyntaxTermCorrectness.checked_iff hZ w b f n hw
  exact SyntaxTypeLocalTransfer.iff_trans (constructor_query_iff hZ 3 0 es w env (SyntaxAtomSyntax.three b f n) hw hn hs) ht

theorem arguments_iff {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (es : Fin 4 → Expr a)
    (w b f k n : Fin m) (env : Fin a → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env))
    (hs : ∀ i, Derives Γ (graph (es i) w env (PureSyntaxTrace.four b f k n i))) :
    Derives Γ ((query (Expr.node (.literal 1) (List.ofFn es)) w env).iff (SyntaxMixedImageCodeSyntax.termList w k b f n)) := by
  have ht : Derives Γ ((rowQuery 4 1 w (PureSyntaxTrace.four b f k n)).iff (SyntaxMixedImageCodeSyntax.termList w k b f n)) := by
    simpa only [rowQuery, PureSyntaxTrace.arguments, PureSyntaxTrace.argumentRow, PureSyntaxTrace.four_map] using PureSyntaxArgumentInduction.checked_iff hZ w b f k n hw
  exact SyntaxTypeLocalTransfer.iff_trans (constructor_query_iff hZ 4 1 es w env (PureSyntaxTrace.four b f k n) hw hn hs) ht

theorem formula_iff {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (es : Fin 3 → Expr a)
    (w b f n : Fin m) (env : Fin a → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env))
    (hs : ∀ i, Derives Γ (graph (es i) w env (SyntaxAtomSyntax.three b f n i))) :
    Derives Γ ((query (Expr.node (.literal 4) (List.ofFn es)) w env).iff (FormulaCodeSyntax.formulaCode w n b f)) := by
  have ht : Derives Γ ((rowQuery 3 4 w (SyntaxAtomSyntax.three b f n)).iff (FormulaCodeSyntax.formulaCode w n b f)) := by
    simpa only [rowQuery, PureSyntaxTrace.formula, PureSyntaxTrace.formulaRow, SyntaxAtomSyntax.three_map] using PureSyntaxFormulaInduction.checked_iff hZ w b f n hw
  exact SyntaxTypeLocalTransfer.iff_trans (constructor_query_iff hZ 3 4 es w env (SyntaxAtomSyntax.three b f n) hw hn hs) ht

end PPAC.Migration.Internal.PureSyntaxQueryTyping
