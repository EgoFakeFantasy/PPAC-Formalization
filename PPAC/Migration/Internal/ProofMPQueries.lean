import PPAC.Migration.Internal.ProofMPSyntax

/-! 原MP六查询的对象对应；最后一投影实际构造／消去蕴含码见证。 -/
namespace PPAC.Migration.Internal.ProofMPQueries
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax ProofMPSyntax
open ProofSubstitutionProjectionSyntax (atOne)
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

theorem conclusion_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((PureSyntaxExprQuery.query conclusionQuery w env).iff (FormulaCodeSyntax.formulaCode w (env 1) z (env 0))) := by
  have hv (j : Fin 5) : Derives Γ (graph (.var j) w env (env j)) := .conjI (environmentNat_at w env hn j) (.eqRefl _)
  exact PureProofSubstitutionQueries.original_formula_query_iff hZ (.var 0) (.var 1) w z (env 0) (env 1) env hw hn hz (hv 0) (hv 1)

theorem antecedent_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((PureSyntaxExprQuery.query antecedentQuery w env).iff (FormulaCodeSyntax.formulaCode w (env 4) z (env 0))) := by
  have hv (j : Fin 5) : Derives Γ (graph (.var j) w env (env j)) := .conjI (environmentNat_at w env hn j) (.eqRefl _)
  exact PureProofSubstitutionQueries.original_formula_query_iff hZ (.var 0) (.var 4) w z (env 0) (env 4) env hw hn hz (hv 0) (hv 4)

theorem leftFree_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((ProjectionExprQuery.query leftFreeQuery w env).iff (RawCodeFieldSyntax.field w (env 2) z (env 0))) := by
  have hv (j : Fin 5) : Derives Γ (graph (.var j) w env (env j)) := .conjI (environmentNat_at w env hn j) (.eqRefl _)
  exact ProofProjectionExpr.zero_iff hZ (.var 2) (.var 0) w z (env 2) (env 0) env hw hn hz (hv 2) (hv 0)

theorem leftFormula_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env)) :
    Derives Γ ((ProjectionExprQuery.query leftFormulaQuery w env).iff (atOne w (env 2) (env 4))) := by
  have hv (j : Fin 5) : Derives Γ (graph (.var j) w env (env j)) := .conjI (environmentNat_at w env hn j) (.eqRefl _)
  exact ProofProjectionExpr.one_iff hZ (.var 2) (.var 4) w (env 2) (env 4) env hw hn (hv 2) (hv 4)

theorem rightFree_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((ProjectionExprQuery.query rightFreeQuery w env).iff (RawCodeFieldSyntax.field w (env 3) z (env 0))) := by
  have hv (j : Fin 5) : Derives Γ (graph (.var j) w env (env j)) := .conjI (environmentNat_at w env hn j) (.eqRefl _)
  exact ProofProjectionExpr.zero_iff hZ (.var 3) (.var 0) w z (env 3) (env 0) env hw hn hz (hv 3) (hv 0)

theorem implication_graph_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w q : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env)) :
    Derives Γ ((graph implicationExpr w env q).iff (SyntaxNodeSyntax.constructor 2 7 w (SetLanguage.args2 (env 4) (env 1)) q)) := by
  have hv (j : Fin 5) : Derives Γ (graph (.var j) w env (env j)) := .conjI (environmentNat_at w env hn j) (.eqRefl _)
  have hs : ∀ j, Derives Γ (graph (implicationFields j) w env (SetLanguage.args2 (env 4) (env 1) j)) :=
    Fin.cases (hv 4) (Fin.cases (hv 1) (fun z => Fin.elim0 z))
  rw [actual_implication]
  exact HornExprConstructor.constructor_iff hZ 2 7 implicationFields w q env (SetLanguage.args2 (env 4) (env 1)) hw hn hs

theorem rightImplication_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w q : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env))
    (hq : Derives Γ (SyntaxNodeSyntax.constructor 2 7 w (SetLanguage.args2 (env 4) (env 1)) q)) :
    Derives Γ ((ProjectionExprQuery.query rightImplicationQuery w env).iff (atOne w (env 3) q)) := by
  have hp : Derives Γ (graph (.var 3) w env (env 3)) := .conjI (environmentNat_at w env hn 3) (.eqRefl _)
  have hg := Derives.impE (.conjR (implication_graph_iff hZ w q env hw hn)) hq
  exact ProofProjectionExpr.one_iff hZ (.var 3) implicationExpr w (env 3) q env hw hn hp hg

theorem rightImplication_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env)) :
    Derives Γ ((ProjectionExprQuery.query rightImplicationQuery w env).iff (implicationRead w (env 3) (env 4) (env 1))) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := ProjectionExprQuery.query rightImplicationQuery w env
    have hi := SyntaxForestSyntax.intro_inputs 2 w (SetLanguage.args2 (env 4) (env 1))
      (Fin.cases (environmentNat_at w env hn 4) (Fin.cases (environmentNat_at w env hn 1) (fun z => Fin.elim0 z)))
    have he := SyntaxConstructors.exists_constructor (ZFContext.add hZ E) 2 7 w (SetLanguage.args2 (env 4) (env 1)) (add hw E) (add hi E)
    let B := (Formula.mem (Fin.last m) w.castSucc).conj
      (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SetLanguage.args2 (env 4).castSucc (env 1).castSucc) (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) he
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename 5 w env Fin.castSucc) (lift hn)
    have hq : Derives Δ (ProjectionExprQuery.query rightImplicationQuery w.castSucc (fun j => (env j).castSucc)) :=
      of_eq (ProjectionExprQuery.query_rename _ w env Fin.castSucc) (under (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl)) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hp := Derives.impE (.conjL (rightImplication_at (ZFContext.under (ZFContext.add hZ E) B) _ _ _ hw1 hn1 (.conjR hB))) hq
    have hout := intro_implicationRead _ _ _ _ _ (.conjR hB) hp
    exact of_eq (implicationRead_rename w (env 3) (env 4) (env 1) Fin.castSucc).symm hout
  · apply Derives.impI
    let E := implicationRead w (env 3) (env 4) (env 1)
    let B := (SyntaxNodeSyntax.constructor 2 7 w.castSucc (SetLanguage.args2 (env 4).castSucc (env 1).castSucc) (Fin.last m)).conj
      (atOne w.castSucc (env 3).castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise := under (add h E) B
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename 5 w env Fin.castSucc) (lift hn)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hq := Derives.impE (.conjR (rightImplication_at (ZFContext.under (ZFContext.add hZ E) B) _ _ _ hw1 hn1 (.conjL hB))) (.conjR hB)
    exact of_eq (ProjectionExprQuery.query_rename _ w env Fin.castSucc).symm hq

theorem projections_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((projections w env).iff (metadata w z env)) :=
  FormulaCodeCongruence.conj_congr (leftFree_iff hZ w z env hw hn hz)
    (FormulaCodeCongruence.conj_congr (leftFormula_iff hZ w env hw hn)
      (FormulaCodeCongruence.conj_congr (rightFree_iff hZ w z env hw hn hz) (rightImplication_iff hZ w env hw hn)))

end PPAC.Migration.Internal.ProofMPQueries
