import PPAC.Migration.Internal.ProofSubstitutionProjectionSyntax

/-! 两项原投影查询的全部内部赋值对应；零／一数码均通过对象公式处理。 -/
namespace PPAC.Migration.Internal.ProofSubstitutionProjection
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax ProofSubstitutionProjectionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem free_query_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((ProjectionExprQuery.query freeProjection w env).iff (RawCodeFieldSyntax.field w (env 4) z (env 2))) := by
  have hv (j : Fin 6) : Derives Γ (graph (.var j) w env (env j)) := .conjI (environmentNat_at w env hn j) (.eqRefl _)
  rw [free_expr]
  exact ProjectionExprQueryTyping.field_iff hZ freeFields w (env 4) z (env 2) env hw hn (hv 4) hz (hv 2)

theorem formula_query_at_one {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w one : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) (ho : Derives Γ (SyntaxNumeralSyntax.numeral 1 one)) :
    Derives Γ ((ProjectionExprQuery.query formulaProjection w env).iff (RawCodeFieldSyntax.field w (env 4) one (env 5))) := by
  have hv (j : Fin 6) : Derives Γ (graph (.var j) w env (env j)) := .conjI (environmentNat_at w env hn j) (.eqRefl _)
  rw [formula_expr]
  exact ProjectionExprQueryTyping.field_iff hZ formulaFields w (env 4) one (env 5) env hw hn (hv 4) ho (hv 5)

theorem formula_query_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) :
    Derives Γ ((ProjectionExprQuery.query formulaProjection w env).iff (atOne w (env 4) (env 5))) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := ProjectionExprQuery.query formulaProjection w env
    let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral 1 (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (SyntaxNumerals.exists_numeral (ZFContext.add hZ E) 1 w (add hw E))
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename 6 w env Fin.castSucc) (lift hn)
    have hq : Derives Δ (ProjectionExprQuery.query formulaProjection w.castSucc (fun j => (env j).castSucc)) :=
      of_eq (ProjectionExprQuery.query_rename formulaProjection w env Fin.castSucc) (under (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl)) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hf := Derives.impE (.conjL (formula_query_at_one (ZFContext.under (ZFContext.add hZ E) B) _ _ _ hw1 hn1 (.conjR hB))) hq
    exact of_eq (atOne_rename w (env 4) (env 5) Fin.castSucc).symm (intro_atOne _ _ _ _ (.conjR hB) hf)
  · apply Derives.impI
    let E := atOne w (env 4) (env 5)
    let B := (SyntaxNumeralSyntax.numeral 1 (Fin.last m)).conj
      (RawCodeFieldSyntax.field w.castSucc (env 4).castSucc (Fin.last m) (env 5).castSucc)
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename 6 w env Fin.castSucc) (lift hn)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hq := Derives.impE (.conjR (formula_query_at_one (ZFContext.under (ZFContext.add hZ E) B) _ _ _ hw1 hn1 (.conjL hB))) (.conjR hB)
    exact of_eq (ProjectionExprQuery.query_rename formulaProjection w env Fin.castSucc).symm hq

theorem projections_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((projections w env).iff (metadata w z env)) :=
  FormulaCodeCongruence.conj_congr (free_query_iff hZ w z env hw hn hz) (formula_query_iff hZ w env hw hn)

end PPAC.Migration.Internal.ProofSubstitutionProjection
