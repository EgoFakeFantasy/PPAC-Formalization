import PPAC.Migration.Internal.PureProofSubstitutionQueries
import PPAC.Migration.Internal.OriginalTransformExprQuery

/-! 原替换节点的确切mode3查询与独立程序双条件；模式数码在对象EX中取得。 -/
namespace PPAC.Migration.Internal.PureProofSubstitutionTransform
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax PureProofSubstitutionQueries
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

theorem transform_query_at_mode {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z mode : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) (hz : Derives Γ (empty z))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode)) :
    Derives Γ ((OriginalTransformExprQuery.query substitutionTransform w env).iff
      (OriginalTransformRowSyntax.run 3 w mode z (env 3) (env 5) (env 1))) := by
  have hv (i : Fin 6) : Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl _)
  have hq := OriginalTransformExprQuery.constructor_query_iff hZ 5 3
    (HornRowFields.five (.literal 3) (.literal 0) (.var 3) (.var 5) (.var 1)) w env
    (HornRowFields.five mode z (env 3) (env 5) (env 1)) hw hn
    (fun i => Fin.cases hm (fun j => Fin.cases hz (fun k => Fin.cases (hv 3) (fun l => Fin.cases (hv 5) (fun _ => hv 1) l) k) j) i)
  change Derives Γ ((OriginalTransformExprQuery.query substitutionTransform w env).iff
    (OriginalTransformExprQuery.rowQuery 5 3 w (HornRowFields.five mode z (env 3) (env 5) (env 1)))) at hq
  simpa only [OriginalTransformExprQuery.rowQuery, OriginalTransformRowSyntax.run, OriginalTransformRowSyntax.row, FreeWeakenResultSyntax.five_map] using hq

theorem guarded_query_at_mode {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z mode : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) (hz : Derives Γ (empty z))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (hf : Derives Γ (PureSyntaxExprQuery.query substitutionFormula w env))
    (ha : Derives Γ (PureSyntaxExprQuery.query substitutionArguments w env)) :
    Derives Γ ((OriginalTransformExprQuery.query substitutionTransform w env).iff
      (FreeSubstProgramSyntax.executed w z (env 2) (env 0) (env 3) (env 5) (env 1))) :=
  SyntaxTypeLocalTransfer.iff_trans (transform_query_at_mode hZ w z mode env hw hn hz hm)
    (guarded_run_iff hZ w z mode env hw hn hz hm hf ha)

theorem guarded_query_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (PureSyntaxExprQuery.query substitutionFormula w env))
    (ha : Derives Γ (PureSyntaxExprQuery.query substitutionArguments w env)) :
    Derives Γ ((OriginalTransformExprQuery.query substitutionTransform w env).iff
      (FreeSubstProgramSyntax.executed w z (env 2) (env 0) (env 3) (env 5) (env 1))) := by
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral 3 (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxNumerals.exists_numeral hZ 3 w hw)
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (environmentNat 6 w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename 6 w env Fin.castSucc) (under hn B)
  have hz1 : Derives Δ (empty z.castSucc) := of_eq (empty_rename z Fin.castSucc) (under hz B)
  have hf1 : Derives Δ (PureSyntaxExprQuery.query substitutionFormula w.castSucc (fun i => (env i).castSucc)) := of_eq (PureSyntaxExprQuery.query_rename _ w env Fin.castSucc) (under hf B)
  have ha1 : Derives Δ (PureSyntaxExprQuery.query substitutionArguments w.castSucc (fun i => (env i).castSucc)) := of_eq (PureSyntaxExprQuery.query_rename _ w env Fin.castSucc) (under ha B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hout := guarded_query_at_mode hZ1 w.castSucc z.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hn1 hz1 (.conjR hB) hf1 ha1
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, OriginalTransformExprQuery.query_rename, FreeSubstProgramSyntax.executed_rename]) hout

def bundle {m} (w : Fin m) (env : Fin 6 → Fin m) : Formula m :=
  (PureSyntaxExprQuery.query substitutionFormula w env).conj
    ((PureSyntaxExprQuery.query substitutionArguments w env).conj (OriginalTransformExprQuery.query substitutionTransform w env))

def specification {m} (w z : Fin m) (env : Fin 6 → Fin m) : Formula m :=
  (FormulaCodeSyntax.formulaCode w (env 5) z (env 2)).conj
    (FreeSubstProgramSyntax.executed w z (env 2) (env 0) (env 3) (env 5) (env 1))

theorem bundle_rename {m l} (w : Fin m) (env : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (bundle w env).rename ρ = bundle (ρ w) (fun i => ρ (env i)) := by
  simp only [bundle, Formula.rename, PureSyntaxExprQuery.query_rename, OriginalTransformExprQuery.query_rename]

theorem specification_rename {m l} (w z : Fin m) (env : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (specification w z env).rename ρ = specification (ρ w) (ρ z) (fun i => ρ (env i)) := by
  simp only [specification, Formula.rename, FormulaCodeSyntax.formulaCode_rename, FreeSubstProgramSyntax.executed_rename]

theorem bundle_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((bundle w env).iff (specification w z env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := bundle w env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.add hZ E
    have htype := Derives.impE (.conjL (substitution_formula_iff hZ1 w z env (add hw E) (add hn E) (add hz E))) (.conjL hE)
    have hout := Derives.impE (.conjL (guarded_query_iff hZ1 w z env (add hw E) (add hn E) (add hz E) (.conjL hE) (.conjL (.conjR hE)))) (.conjR (.conjR hE))
    exact .conjI htype hout
  · apply Derives.impI
    let E := specification w z env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.add hZ E
    have hf := Derives.impE (.conjR (substitution_formula_iff hZ1 w z env (add hw E) (add hn E) (add hz E))) (.conjL hE)
    have hlist := Derives.impE (.conjR (EmptyBoundFreeInputs.list_iff hZ1 w (env 2) z (env 0) (env 3) (add hw E) (add hz E))) (.conjL (.conjR hE))
    have ha := Derives.impE (.conjR (substitution_arguments_iff hZ1 w z env (add hw E) (add hn E) (add hz E))) hlist
    have hq := Derives.impE (.conjR (guarded_query_iff hZ1 w z env (add hw E) (add hn E) (add hz E) hf ha)) (.conjR hE)
    exact .conjI hf (.conjI ha hq)

end PPAC.Migration.Internal.PureProofSubstitutionTransform
