import PPAC.Migration.Internal.HornVariableExpr

/-! 原变量表达式与实际内部变量码的双向对应和等词传输。 -/
namespace PPAC.Migration.Internal.HornVariableValue
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

theorem code_output_subst {m} {Γ : Context m} (bound : Bool) (w idx y z : Fin m)
    (he : Derives Γ (.equal y z)) (hc : Derives Γ (SyntaxVariableSyntax.code bound w idx y)) :
    Derives Γ (SyntaxVariableSyntax.code bound w idx z) := by
  let P := SyntaxVariableSyntax.code bound w.castSucc idx.castSucc (Fin.last m)
  have h0 : P.instantiate y = SyntaxVariableSyntax.code bound w idx y := by simp only [P, Formula.instantiate, SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate z = SyntaxVariableSyntax.code bound w idx z := by simp only [P, Formula.instantiate, SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hc))

theorem graph_code {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (e : Expr n)
    (w idx y : Fin m) (env : Fin n → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env))
    (hi : Derives Γ (graph e w env idx)) (hy : Derives Γ (graph (HornVariableExpr.expression bound e) w env y)) :
    Derives Γ (SyntaxVariableSyntax.code bound w idx y) := by
  have he := SyntaxVariables.exists_code hZ bound w idx hw (HornExprRange.range hZ e w idx env hw hn hi)
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxVariableSyntax.code bound w.castSucc idx.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (environmentNat n w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename n w env Fin.castSucc) (under hn B)
  have hi1 : Derives Δ (graph e w.castSucc (fun i => (env i).castSucc) idx.castSucc) := of_eq (graph_rename e w idx env Fin.castSucc) (under hi B)
  have hy1 : Derives Δ (graph (HornVariableExpr.expression bound e) w.castSucc (fun i => (env i).castSucc) y.castSucc) := of_eq (graph_rename _ w y env Fin.castSucc) (under hy B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hg := HornVariableExpr.code_graph bound e _ _ _ _ hi1 (.conjR hB)
  have heq := HornExprUnique.unique (ZFContext.under hZ B) (HornVariableExpr.expression bound e) _ _ _ _ hw1 hn1 hg hy1
  have ho := code_output_subst bound _ _ _ _ heq (.conjR hB)
  exact of_eq (SyntaxVariableSyntax.code_rename bound w idx y Fin.castSucc).symm ho

theorem graph_iff_code {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (e : Expr n)
    (w idx y : Fin m) (env : Fin n → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env))
    (hi : Derives Γ (graph e w env idx)) :
    Derives Γ ((graph (HornVariableExpr.expression bound e) w env y).iff (SyntaxVariableSyntax.code bound w idx y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact graph_code (ZFContext.add hZ _) bound e w idx y env (add hw _) (add hn _) (add hi _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact HornVariableExpr.code_graph bound e w idx y env (add hi _) (.hyp (Or.inl rfl))

theorem code_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w idx y : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxVariableSyntax.code bound w idx y)) : Derives Γ (.mem y w) := by
  let B := SyntaxVariableSyntax.codeBody bound w idx y
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply SyntaxVariableSyntax.eliminate_code bound w idx y _ hc
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxNodeInjective.constructor_range (ZFContext.under hZ B) 1 (SyntaxVariableSyntax.tag bound) _ _ _ hw1 (.conjR hB)

end PPAC.Migration.Internal.HornVariableValue
