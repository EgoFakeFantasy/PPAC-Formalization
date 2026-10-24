import PPAC.Migration.Internal.ProofSubstitutionProjectionSlots
import PPAC.Migration.Internal.PureProofSubstitutionTransform

/-! 原替换节点全部五项真实查询按原顺序合并；完整节点head／赋值界另行处理。 -/
namespace PPAC.Migration.Internal.ProofSubstitutionAllQueries
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open PureProofSubstitutionQueries ProofSubstitutionProjectionSyntax

def bundle {m} (w : Fin m) (env : Fin 6 → Fin m) : Formula m :=
  (PureSyntaxExprQuery.query substitutionFormula w env).conj
    ((PureSyntaxExprQuery.query substitutionArguments w env).conj
      ((ProjectionExprQuery.query freeProjection w env).conj
        ((ProjectionExprQuery.query formulaProjection w env).conj
          (OriginalTransformExprQuery.query substitutionTransform w env))))

def specification {m} (w z : Fin m) (env : Fin 6 → Fin m) : Formula m :=
  (PureProofSubstitutionTransform.specification w z env).conj (metadata w z env)

theorem bundle_rename {m l} (w : Fin m) (env : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (bundle w env).rename ρ = bundle (ρ w) (fun j => ρ (env j)) := by
  simp only [bundle, Formula.rename, PureSyntaxExprQuery.query_rename, ProjectionExprQuery.query_rename, OriginalTransformExprQuery.query_rename]

theorem specification_rename {m l} (w z : Fin m) (env : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (specification w z env).rename ρ = specification (ρ w) (ρ z) (fun j => ρ (env j)) := by
  simp only [specification, Formula.rename, PureProofSubstitutionTransform.specification_rename, metadata_rename]

theorem bundle_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((bundle w env).iff (specification w z env)) := by
  have hthree := PureProofSubstitutionTransform.bundle_iff hZ w z env hw hn hz
  have hproj := ProofSubstitutionProjection.projections_iff hZ w z env hw hn hz
  apply Derives.conjI
  · apply Derives.impI
    let E := bundle w env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hf := Derives.conjL hE
    have ha := Derives.conjL (.conjR hE)
    have hp0 := Derives.conjL (.conjR (.conjR hE))
    have hp1 := Derives.conjL (.conjR (.conjR (.conjR hE)))
    have ht := Derives.conjR (.conjR (.conjR (.conjR hE)))
    exact .conjI (.impE (add (.conjL hthree) E) (.conjI hf (.conjI ha ht)))
      (.impE (add (.conjL hproj) E) (.conjI hp0 hp1))
  · apply Derives.impI
    let E := specification w z env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hthreeQ := Derives.impE (add (.conjR hthree) E) (.conjL hE)
    have hprojQ := Derives.impE (add (.conjR hproj) E) (.conjR hE)
    exact .conjI (.conjL hthreeQ) (.conjI (.conjL (.conjR hthreeQ))
      (.conjI (.conjL hprojQ) (.conjI (.conjR hprojQ) (.conjR (.conjR hthreeQ)))))

end PPAC.Migration.Internal.ProofSubstitutionAllQueries
