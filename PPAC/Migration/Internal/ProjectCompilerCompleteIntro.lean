import PPAC.Migration.Internal.ProjectCompilerCompleteSyntax

/-! Direct actual case constructors are introduced through the proved Compiler recursive equation. -/
namespace PPAC.Migration.Internal.ProjectCompilerCompleteIntro
open Source SourceAlgebra SourceLogic OmegaSyntax ProjectCompilerCompleteSyntax ProjectCompilerRecursiveSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem of_cases {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b q z : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hb : Derives Γ (.mem b w))
    (hq : Derives Γ (.mem q w)) (hz : Derives Γ (empty z)) (hc : Derives Γ (casesAt w b z n q)) :
    Derives Γ (ProjectCompilerCodeSyntax.compiled w n b q) := by
  apply Derives.impE (.conjR (ProjectCompilerRecursive.recursive_iff hZ w n b q hw))
  apply Derives.conjI hn
  apply Derives.conjI (Derives.conjI hb hq)
  apply Derives.exI z
  simpa only [body, Formula.instantiate, Formula.rename, empty_rename, casesAt_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hz hc

theorem query_output_natural {m} {Γ : Context m} (w n x b q : Fin m)
    (hc : Derives Γ (ProjectCompilerCaseSyntax.queried codeMatrix (parameters w) n x b q)) : Derives Γ (.mem q w) := by
  have hp := of_eq (codeMatrix_at (parameters w) x b q) (.conjR hc)
  exact .conjR (.conjR (ProjectCompilerCodeProperties.guards w x b q hp))

theorem advanced_output_natural {m} {Γ : Context m} (w n x b q : Fin m)
    (hc : Derives Γ (ProjectCompilerCaseSyntax.advanced codeMatrix (parameters w) n x b q)) : Derives Γ (.mem q w) := by
  let B := (successor (Fin.last m) b.castSucc).conj
    (ProjectCompilerCaseSyntax.queried codeMatrix (parameters w.castSucc) n.castSucc x.castSucc (Fin.last m) q.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hc
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact query_output_natural w.castSucc n.castSucc x.castSucc (Fin.last m) q.castSucc (.conjR hB)

theorem check_output_natural {m} {Γ : Context m} (advance : Bool) (w n x b q : Fin m)
    (hc : Derives Γ (ProjectCompilerCaseSyntax.check advance codeMatrix (parameters w) n x b q)) : Derives Γ (.mem q w) := by
  cases advance
  · exact query_output_natural w n x b q hc
  · exact advanced_output_natural w n x b q hc

end PPAC.Migration.Internal.ProjectCompilerCompleteIntro
