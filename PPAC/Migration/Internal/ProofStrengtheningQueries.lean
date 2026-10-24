import PPAC.Migration.Internal.ProofStrengtheningSyntax

/-! 原strengthening实际语法／投影／mode0完整公式查询的对象对应。 -/
namespace PPAC.Migration.Internal.ProofStrengtheningQueries
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax ProofStrengtheningSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem formula_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((PureSyntaxExprQuery.query formulaQuery w env).iff (FormulaCodeSyntax.formulaCode w (env 1) z (env 0))) := by
  have hv (j : Fin 4) : Derives Γ (graph (.var j) w env (env j)) := .conjI (environmentNat_at w env hn j) (.eqRefl _)
  exact PureProofSubstitutionQueries.original_formula_query_iff hZ (.var 0) (.var 1) w z (env 0) (env 1) env hw hn hz (hv 0) (hv 1)

theorem free_iff_at_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z B : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) (hz : Derives Γ (empty z))
    (hs : Derives Γ (successor B (env 0))) :
    Derives Γ ((ProjectionExprQuery.query freeQuery w env).iff (RawCodeFieldSyntax.field w (env 2) z B)) := by
  have hv (j : Fin 4) : Derives Γ (graph (.var j) w env (env j)) := .conjI (environmentNat_at w env hn j) (.eqRefl _)
  exact ProofProjectionExpr.zero_iff hZ (.var 2) (.succ (.var 0)) w z (env 2) B env hw hn hz (hv 2) (intro_succ (.var 0) w B (env 0) env (hv 0) hs)

theorem predecessorFormula_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) :
    Derives Γ ((ProjectionExprQuery.query predecessorFormulaQuery w env).iff (ProofSubstitutionProjectionSyntax.atOne w (env 2) (env 3))) := by
  have hv (j : Fin 4) : Derives Γ (graph (.var j) w env (env j)) := .conjI (environmentNat_at w env hn j) (.eqRefl _)
  exact ProofProjectionExpr.one_iff hZ (.var 2) (.var 3) w (env 2) (env 3) env hw hn (hv 2) (hv 3)

theorem transform_at_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((OriginalTransformExprQuery.query transformQuery w env).iff (OriginalTransformRowSyntax.run 3 w z z z (env 1) (env 3))) := by
  have hv (j : Fin 4) : Derives Γ (graph (.var j) w env (env j)) := .conjI (environmentNat_at w env hn j) (.eqRefl _)
  have hq := OriginalTransformExprQuery.constructor_query_iff hZ 5 3
    (HornRowFields.five (.literal 0) (.literal 0) (.literal 0) (.var 1) (.var 3)) w env
    (HornRowFields.five z z z (env 1) (env 3)) hw hn
    (fun i => Fin.cases hz (fun j => Fin.cases hz (fun k => Fin.cases hz (fun l => Fin.cases (hv 1) (fun _ => hv 3) l) k) j) i)
  change Derives Γ ((OriginalTransformExprQuery.query transformQuery w env).iff
    (OriginalTransformExprQuery.rowQuery 5 3 w (HornRowFields.five z z z (env 1) (env 3)))) at hq
  simpa only [OriginalTransformExprQuery.rowQuery, OriginalTransformRowSyntax.run, OriginalTransformRowSyntax.row, FreeWeakenResultSyntax.five_map] using hq

theorem guarded_transform_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z B : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) (hz : Derives Γ (empty z))
    (hs : Derives Γ (successor B (env 0))) (hf : Derives Γ (PureSyntaxExprQuery.query formulaQuery w env)) :
    Derives Γ ((OriginalTransformExprQuery.query transformQuery w env).iff (WeakenFreeProgramSyntax.executed w z (env 0) B (env 1) (env 3))) := by
  have ht := Derives.impE (.conjL (formula_iff hZ w z env hw hn hz)) hf
  have hzn := HornExprRange.range hZ (.literal 0) w z env hw hn hz
  have hm : Derives Γ (SyntaxNumeralSyntax.numeral 0 z) := hz
  have hd : Derives Γ (OriginalTermTraceSyntax.metadata w z z) := .conjI hzn hzn
  exact SyntaxTypeLocalTransfer.iff_trans (transform_at_zero hZ w z env hw hn hz)
    (OriginalWeakenFormulaRun.program_iff hZ w z z z z (env 0) B (env 1) (env 3) hw hm hd ht hs)

end PPAC.Migration.Internal.ProofStrengtheningQueries
