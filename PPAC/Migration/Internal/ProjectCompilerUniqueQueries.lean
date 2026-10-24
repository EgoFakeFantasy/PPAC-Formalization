import PPAC.Migration.Internal.ProjectCompilerUniquePadding

/-! Object member functionality controls actual child queries, including independently chosen successor scopes. -/
namespace PPAC.Migration.Internal.ProjectCompilerUniqueQueries
open Source SourceAlgebra SourceLogic OmegaSyntax ProjectCompilerRecursiveSyntax ProjectCompilerUniqueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem query_unique {m} {Γ : Context m} (w n x b q r : Fin m) (hI : Derives Γ (allIH w n))
    (hq : Derives Γ (ProjectCompilerCaseSyntax.queried codeMatrix (parameters w) n x b q))
    (hr : Derives Γ (ProjectCompilerCaseSyntax.queried codeMatrix (parameters w) n x b r)) : Derives Γ (.equal q r) := by
  have hp := of_eq (codeMatrix_at (parameters w) x b q) (.conjR hq)
  have hs := of_eq (codeMatrix_at (parameters w) x b r) (.conjR hr)
  exact unique_at w x b q r (below_functional w n x hI (.conjL hq)) hp hs

theorem advanced_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n x b q r : Fin m) (hI : Derives Γ (allIH w n))
    (hq : Derives Γ (ProjectCompilerCaseSyntax.advanced codeMatrix (parameters w) n x b q))
    (hr : Derives Γ (ProjectCompilerCaseSyntax.advanced codeMatrix (parameters w) n x b r)) : Derives Γ (.equal q r) := by
  let S := (successor (Fin.last m) b.castSucc).conj
    (ProjectCompilerCaseSyntax.queried codeMatrix (parameters w.castSucc) n.castSucc x.castSucc (Fin.last m) q.castSucc)
  let Ξ := Context.add S (Context.image Formula.raise Γ)
  apply Derives.exE (p := S) hq
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hr1 := of_eq (ProjectCompilerCaseSyntax.advanced_rename codeMatrix (parameters w) n x b r Fin.castSucc) (under hr S)
  let T := (successor (Fin.last (m+1)) b.castSucc.castSucc).conj
    (ProjectCompilerCaseSyntax.queried codeMatrix (parameters w.castSucc.castSucc) n.castSucc.castSucc x.castSucc.castSucc (Fin.last (m+1)) r.castSucc.castSucc)
  let Δ := Context.add T (Context.image Formula.raise Ξ)
  apply Derives.exE (p := T) hr1
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under (ZFContext.under hZ S) T
  have hI2 : Derives Δ (allIH w.castSucc.castSucc n.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, allIH_rename]) (under (under hI S) T)
  have hs2 := of_eq (successor_rename (Fin.last m) b.castSucc Fin.castSucc) (under (.conjL hS) T)
  have hq2 := of_eq (ProjectCompilerCaseSyntax.queried_rename codeMatrix (parameters w.castSucc)
    n.castSucc x.castSucc (Fin.last m) q.castSucc Fin.castSucc) (under (.conjR hS) T)
  have hp := of_eq (codeMatrix_at (parameters w.castSucc.castSucc) x.castSucc.castSucc (Fin.last m).castSucc q.castSucc.castSucc) (.conjR hq2)
  have ht := of_eq (codeMatrix_at (parameters w.castSucc.castSucc) x.castSucc.castSucc (Fin.last (m+1)) r.castSucc.castSucc) (.conjR (.conjR hT))
  have he := OmegaUniversal.successor_unique (Fin.last (m+1)) (Fin.last m).castSucc b.castSucc.castSucc
    (ZFContext.arithmetic hZ2).base.extensionality (.conjL hT) hs2
  have hs := ProjectCompilerCodeTransport.code_bound w.castSucc.castSucc x.castSucc.castSucc (Fin.last (m+1))
    r.castSucc.castSucc (Fin.last m).castSucc he ht
  exact unique_at w.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc q.castSucc.castSucc r.castSucc.castSucc
    (below_functional w.castSucc.castSucc n.castSucc.castSucc x.castSucc.castSucc hI2 (.conjL hq2)) hp hs

theorem check_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (advance : Bool) (w n x b q r : Fin m)
    (hI : Derives Γ (allIH w n))
    (hq : Derives Γ (ProjectCompilerCaseSyntax.check advance codeMatrix (parameters w) n x b q))
    (hr : Derives Γ (ProjectCompilerCaseSyntax.check advance codeMatrix (parameters w) n x b r)) : Derives Γ (.equal q r) := by
  cases advance
  · exact query_unique w n x b q r hI hq hr
  · exact advanced_unique hZ w n x b q r hI hq hr

end PPAC.Migration.Internal.ProjectCompilerUniqueQueries
