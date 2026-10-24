import PPAC.Migration.Internal.ProofMPQueries

/-! 原MP全部六项实际查询按原顺序合并；接受定义不使用公式类型或字段规格作为预言机。 -/
namespace PPAC.Migration.Internal.ProofMPAllQueries
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax ProofMPSyntax

def formulaQueries {m} (w : Fin m) (env : Fin 5 → Fin m) : Formula m :=
  (PureSyntaxExprQuery.query conclusionQuery w env).conj (PureSyntaxExprQuery.query antecedentQuery w env)

def formulas {m} (w z : Fin m) (env : Fin 5 → Fin m) : Formula m :=
  (FormulaCodeSyntax.formulaCode w (env 1) z (env 0)).conj (FormulaCodeSyntax.formulaCode w (env 4) z (env 0))

def bundle {m} (w : Fin m) (env : Fin 5 → Fin m) : Formula m :=
  (PureSyntaxExprQuery.query conclusionQuery w env).conj ((PureSyntaxExprQuery.query antecedentQuery w env).conj (projections w env))

def specification {m} (w z : Fin m) (env : Fin 5 → Fin m) : Formula m := (formulas w z env).conj (metadata w z env)

theorem formulaQueries_rename {m l} (w : Fin m) (env : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (formulaQueries w env).rename ρ = formulaQueries (ρ w) (fun j => ρ (env j)) := by
  simp only [formulaQueries, Formula.rename, PureSyntaxExprQuery.query_rename]

theorem formulas_rename {m l} (w z : Fin m) (env : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (formulas w z env).rename ρ = formulas (ρ w) (ρ z) (fun j => ρ (env j)) := by
  simp only [formulas, Formula.rename, FormulaCodeSyntax.formulaCode_rename]

theorem bundle_rename {m l} (w : Fin m) (env : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (bundle w env).rename ρ = bundle (ρ w) (fun j => ρ (env j)) := by
  simp only [bundle, Formula.rename, PureSyntaxExprQuery.query_rename, projections_rename]

theorem specification_rename {m l} (w z : Fin m) (env : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (specification w z env).rename ρ = specification (ρ w) (ρ z) (fun j => ρ (env j)) := by
  simp only [specification, Formula.rename, formulas_rename, metadata_rename]

theorem formulas_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((formulaQueries w env).iff (formulas w z env)) :=
  FormulaCodeCongruence.conj_congr (ProofMPQueries.conclusion_iff hZ w z env hw hn hz) (ProofMPQueries.antecedent_iff hZ w z env hw hn hz)

theorem bundle_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((bundle w env).iff (specification w z env)) := by
  have hform := formulas_iff hZ w z env hw hn hz
  have hproj := ProofMPQueries.projections_iff hZ w z env hw hn hz
  apply Derives.conjI
  · apply Derives.impI
    let E := bundle w env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    exact .conjI (.impE (add (.conjL hform) E) (.conjI (.conjL hE) (.conjL (.conjR hE))))
      (.impE (add (.conjL hproj) E) (.conjR (.conjR hE)))
  · apply Derives.impI
    let E := specification w z env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hf := Derives.impE (add (.conjR hform) E) (.conjL hE)
    have hp := Derives.impE (add (.conjR hproj) E) (.conjR hE)
    exact .conjI (.conjL hf) (.conjI (.conjR hf) hp)

end PPAC.Migration.Internal.ProofMPAllQueries
