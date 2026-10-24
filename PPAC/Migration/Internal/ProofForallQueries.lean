import PPAC.Migration.Internal.ProofForallSyntax

/-! 原forall实际语法／投影／mode1完整公式查询的对象对应。 -/
namespace PPAC.Migration.Internal.ProofForallQueries
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax ProofForallSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem formula_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z B : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) (hz : Derives Γ (empty z))
    (hs : Derives Γ (successor B (env 0))) :
    Derives Γ ((PureSyntaxExprQuery.query formulaQuery w env).iff (FormulaCodeSyntax.formulaCode w (env 3) z B)) := by
  have hv (j : Fin 4) : Derives Γ (graph (.var j) w env (env j)) := .conjI (environmentNat_at w env hn j) (.eqRefl _)
  exact PureProofSubstitutionQueries.original_formula_query_iff hZ (.succ (.var 0)) (.var 3) w z B (env 3) env hw hn hz
    (intro_succ (.var 0) w B (env 0) env (hv 0) hs) (hv 3)

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

theorem transform_at_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z A : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (SyntaxNumeralSyntax.numeral 1 A)) :
    Derives Γ ((OriginalTransformExprQuery.query transformQuery w env).iff (OriginalTransformRowSyntax.run 3 w A z z (env 3) (env 1))) := by
  have hv (j : Fin 4) : Derives Γ (graph (.var j) w env (env j)) := .conjI (environmentNat_at w env hn j) (.eqRefl _)
  have hq := OriginalTransformExprQuery.constructor_query_iff hZ 5 3
    (HornRowFields.five (.literal 1) (.literal 0) (.literal 0) (.var 3) (.var 1)) w env
    (HornRowFields.five A z z (env 3) (env 1)) hw hn
    (fun i => Fin.cases hA (fun j => Fin.cases hz (fun k => Fin.cases hz (fun l => Fin.cases (hv 3) (fun _ => hv 1) l) k) j) i)
  change Derives Γ ((OriginalTransformExprQuery.query transformQuery w env).iff
    (OriginalTransformExprQuery.rowQuery 5 3 w (HornRowFields.five A z z (env 3) (env 1)))) at hq
  simpa only [OriginalTransformExprQuery.rowQuery, OriginalTransformRowSyntax.run, OriginalTransformRowSyntax.row, FreeWeakenResultSyntax.five_map] using hq

theorem guarded_transform_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z A B : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A z)) (hs : Derives Γ (successor B (env 0)))
    (hf : Derives Γ (PureSyntaxExprQuery.query formulaQuery w env)) :
    Derives Γ ((OriginalTransformExprQuery.query transformQuery w env).iff (SyntaxTopFormulaSyntax.abstracted w z (env 0) A B (env 3) (env 1))) := by
  have ht := Derives.impE (.conjL (formula_iff hZ w z B env hw hn hz hs)) hf
  have hzn := HornExprRange.range hZ (.literal 0) w z env hw hn hz
  have hm := SyntaxNumeralSyntax.intro_succ 0 A z hz hA
  have hd : Derives Γ (OriginalTermTraceSyntax.metadata w z z) := .conjI hzn hzn
  have hi : Derives Γ (SyntaxTopEnvironmentSyntax.abstractInput w z (env 0) A B) :=
    .conjI (.conjI hzn (environmentNat_at w env hn 0)) (.conjI hA hs)
  exact SyntaxTypeLocalTransfer.iff_trans (transform_at_zero hZ w z A env hw hn hz hm)
    (AbstractTopFormulaOperation.run_iff hZ w A z z z (env 0) A B (env 3) (env 1) hw hm hd hz hi ht)

end PPAC.Migration.Internal.ProofForallQueries
