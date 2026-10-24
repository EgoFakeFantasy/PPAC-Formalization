import PPAC.Migration.Internal.PureSyntaxQueryTyping
import PPAC.Migration.Internal.PureArgumentsModeThree
import YesMetaZFC.Automation.ObjectProofNode

/-! 原替换节点的确切语法查询及其mode3前提传输，不使用宿主类型或标准quotation。 -/
namespace PPAC.Migration.Internal.PureProofSubstitutionQueries
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation

def formulaFields {a} (free input : Expr a) : Fin 3 → Expr a :=
  Fin.cases (.literal 0) (Fin.cases free (Fin.cases input Fin.elim0))

def substitutionFormula : Expr 6 := (ObjectProofNode.substitutionShape.queries[0]).2

def substitutionArguments : Expr 6 := (ObjectProofNode.substitutionShape.queries[1]).2

def substitutionTransform : Expr 6 := (ObjectProofNode.substitutionShape.queries[4]).2

theorem actual_formula : ObjectProofNode.substitutionShape.queries[0] =
    ObjectProofNode.formula (.var 2) (.var 5) := rfl

theorem actual_arguments : ObjectProofNode.substitutionShape.queries[1] =
    (.syntax, ObjectProofNode.node 1 [.literal 0, .var 0, .var 2, .var 3]) := rfl

theorem actual_transform : ObjectProofNode.substitutionShape.queries[4] =
    ObjectProofNode.transform 3 (.var 3) (.var 5) (.var 1) := rfl

theorem original_formula_query_iff {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (free input : Expr a)
    (w z f n : Fin m) (env : Fin a → Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env))
    (hz : Derives Γ (empty z)) (hf : Derives Γ (graph free w env f)) (hi : Derives Γ (graph input w env n)) :
    Derives Γ ((PureSyntaxExprQuery.query (ObjectProofNode.formula free input).2 w env).iff (FormulaCodeSyntax.formulaCode w n z f)) := by
  exact PureSyntaxQueryTyping.formula_iff hZ (formulaFields free input) w z f n env hw hn
    (fun i => Fin.cases hz (fun j => Fin.cases hf (fun k => Fin.cases hi (fun v => Fin.elim0 v) k) j) i)

theorem substitution_formula_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((PureSyntaxExprQuery.query substitutionFormula w env).iff (FormulaCodeSyntax.formulaCode w (env 5) z (env 2))) :=
  original_formula_query_iff hZ (.var 2) (.var 5) w z (env 2) (env 5) env hw hn hz
    (.conjI (environmentNat_at w env hn 2) (.eqRefl _)) (.conjI (environmentNat_at w env hn 5) (.eqRefl _))

theorem substitution_arguments_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((PureSyntaxExprQuery.query substitutionArguments w env).iff (SyntaxMixedImageCodeSyntax.termList w (env 2) z (env 0) (env 3))) := by
  have hv (i : Fin 6) : Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl _)
  exact PureSyntaxQueryTyping.arguments_iff hZ (PureSyntaxTrace.four (.literal 0) (.var 0) (.var 2) (.var 3)) w z (env 0) (env 2) (env 3) env hw hn
    (fun i => Fin.cases hz (fun j => Fin.cases (hv 0) (fun k => Fin.cases (hv 2) (fun l => Fin.cases (hv 3) (fun v => Fin.elim0 v) l) k) j) i)

theorem guarded_run_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z mode : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) (hz : Derives Γ (empty z))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (hf : Derives Γ (PureSyntaxExprQuery.query substitutionFormula w env))
    (ha : Derives Γ (PureSyntaxExprQuery.query substitutionArguments w env)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode z (env 3) (env 5) (env 1)).iff
      (FreeSubstProgramSyntax.executed w z (env 2) (env 0) (env 3) (env 5) (env 1))) := by
  have htype := Derives.impE (.conjL (substitution_formula_iff hZ w z env hw hn hz)) hf
  have hlist := Derives.impE (.conjL (substitution_arguments_iff hZ w z env hw hn hz)) ha
  have hzn := HornExprRange.range hZ (.literal 0) w z env hw hn hz
  have hmeta : Derives Γ (OriginalTermTraceSyntax.metadata w z (env 3)) := .conjI hzn (environmentNat_at w env hn 3)
  exact OriginalFreeSubstFormulaRun.empty_bound_arguments_iff hZ w mode z z (env 2) z (env 0) (env 3) (env 5) (env 1) hw hm hmeta htype hz hlist

end PPAC.Migration.Internal.PureProofSubstitutionQueries
