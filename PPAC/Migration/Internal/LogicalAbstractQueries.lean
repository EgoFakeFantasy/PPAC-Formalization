import PPAC.Migration.Internal.ProofForallQueries
import PPAC.Migration.Internal.LogicalStaticQueryList

/-! 原逻辑21／24的实际mode1及自由界后继查询；不限于外部标准公式码。 -/
namespace PPAC.Migration.Internal.LogicalAbstractQueries
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation
open YesMetaZFC.Automation.ObjectHorn (Expr)

def formulaQuery {a} (free input : Fin a) : Expr a :=
  (ObjectLogicalAxiom.grammar false (.literal 0) (.succ (.var free)) (.var input)).2

def transformQuery {a} (input output : Fin a) : Expr a :=
  (ObjectLogicalAxiom.transform 1 (.literal 0) (.var input) (.var output)).2

theorem formula_iff {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (free input : Fin a)
    (w z B : Fin m) (env : Fin a → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat a w env)) (hz : Derives Γ (empty z))
    (hs : Derives Γ (successor B (env free))) :
    Derives Γ ((PureSyntaxExprQuery.query (formulaQuery free input) w env).iff (FormulaCodeSyntax.formulaCode w (env input) z B)) := by
  have hv (j : Fin a) : Derives Γ (graph (.var j) w env (env j)) := .conjI (environmentNat_at w env hn j) (.eqRefl _)
  exact PureProofSubstitutionQueries.original_formula_query_iff hZ (.succ (.var free)) (.var input) w z B (env input) env hw hn hz
    (intro_succ (.var free) w B (env free) env (hv free) hs) (hv input)

theorem transform_at_one {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (input output : Fin a)
    (w z A : Fin m) (env : Fin a → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat a w env)) (hz : Derives Γ (empty z))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 A)) :
    Derives Γ ((OriginalTransformExprQuery.query (transformQuery input output) w env).iff (OriginalTransformRowSyntax.run 3 w A z z (env input) (env output))) := by
  have hv (j : Fin a) : Derives Γ (graph (.var j) w env (env j)) := .conjI (environmentNat_at w env hn j) (.eqRefl _)
  have hq := OriginalTransformExprQuery.constructor_query_iff hZ 5 3
    (HornRowFields.five (.literal 1) (.literal 0) (.literal 0) (.var input) (.var output)) w env
    (HornRowFields.five A z z (env input) (env output)) hw hn
    (fun i => Fin.cases hm (fun j => Fin.cases hz (fun k => Fin.cases hz (fun l => Fin.cases (hv input) (fun _ => hv output) l) k) j) i)
  change Derives Γ ((OriginalTransformExprQuery.query (transformQuery input output) w env).iff
    (OriginalTransformExprQuery.rowQuery 5 3 w (HornRowFields.five A z z (env input) (env output)))) at hq
  simpa only [OriginalTransformExprQuery.rowQuery, OriginalTransformRowSyntax.run, OriginalTransformRowSyntax.row, FreeWeakenResultSyntax.five_map] using hq

theorem typed_transform_iff {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (free input output : Fin a)
    (w z A B : Fin m) (env : Fin a → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat a w env)) (hz : Derives Γ (empty z))
    (hA : Derives Γ (successor A z)) (hs : Derives Γ (successor B (env free)))
    (hf : Derives Γ (FormulaCodeSyntax.formulaCode w (env input) z B)) :
    Derives Γ ((OriginalTransformExprQuery.query (transformQuery input output) w env).iff (SyntaxTopFormulaSyntax.abstracted w z (env free) A B (env input) (env output))) := by
  have hzn := HornExprRange.range hZ (.literal 0) w z env hw hn hz
  have hm := SyntaxNumeralSyntax.intro_succ 0 A z hz hA
  have hd : Derives Γ (OriginalTermTraceSyntax.metadata w z z) := .conjI hzn hzn
  have hi : Derives Γ (SyntaxTopEnvironmentSyntax.abstractInput w z (env free) A B) :=
    .conjI (.conjI hzn (environmentNat_at w env hn free)) (.conjI hA hs)
  exact SyntaxTypeLocalTransfer.iff_trans (transform_at_one hZ input output w z A env hw hn hz hm)
    (AbstractTopFormulaOperation.run_iff hZ w A z z z (env free) A B (env input) (env output) hw hm hd hz hi hf)

end PPAC.Migration.Internal.LogicalAbstractQueries
