import PPAC.Migration.Internal.ProjectCompilerUniquePairs

/-! Actual scalar output comparison discharges both internal empty-zero witnesses. -/
namespace PPAC.Migration.Internal.ProjectCompilerUniqueStep
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax ProjectCompilerUniqueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem outputs_from_induction {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b q r : Fin m)
    (hw : Derives Γ (omega w)) (hI : Derives Γ (allIH w n))
    (hq : Derives Γ (ProjectCompilerCodeSyntax.compiled w n b q))
    (hr : Derives Γ (ProjectCompilerCodeSyntax.compiled w n b r)) : Derives Γ (.equal q r) := by
  have hqC := Derives.impE (.conjL (ProjectCompilerRecursive.recursive_iff hZ w n b q hw)) hq
  have hrC := Derives.impE (.conjL (ProjectCompilerRecursive.recursive_iff hZ w n b r hw)) hr
  let S := ProjectCompilerRecursiveSyntax.body w n b q
  let Ξ := Context.add S (Context.image Formula.raise Γ)
  apply Derives.exE (p := S) (.conjR (.conjR hqC))
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hr1 := of_eq (ProjectCompilerRecursiveSyntax.criterion_rename w n b r Fin.castSucc) (under hrC S)
  let T := ProjectCompilerRecursiveSyntax.body w.castSucc n.castSucc b.castSucc r.castSucc
  let Δ := Context.add T (Context.image Formula.raise Ξ)
  apply Derives.exE (p := T) (.conjR (.conjR hr1))
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under (ZFContext.under hZ S) T
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq
    (by simp only [Formula.raise, omega_rename]) (under (under hw S) T)
  have hI2 : Derives Δ (allIH w.castSucc.castSucc n.castSucc.castSucc) := of_eq
    (by simp only [Formula.raise, allIH_rename]) (under (under hI S) T)
  have hz2 := of_eq (empty_rename (Fin.last m) Fin.castSucc) (under (.conjL hS) T)
  have hq2 := of_eq (ProjectCompilerRecursiveSyntax.casesAt_rename w.castSucc b.castSucc (Fin.last m) n.castSucc q.castSucc Fin.castSucc)
    (under (.conjR hS) T)
  have he := OmegaUniversal.empty_unique (Fin.last (m+1)) (Fin.last m).castSucc (ZFContext.arithmetic hZ2).base.extensionality (.conjL hT) hz2
  have hr2 := ProjectCompilerUniqueTransport.cases_zero w.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1))
    n.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc he (.conjR hT)
  exact ProjectCompilerUniquePairs.actual_cases_unique hZ2 w.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc
    n.castSucc.castSucc q.castSucc.castSucc r.castSucc.castSucc hw2 hI2 hq2 hr2

theorem from_induction {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hI : Derives Γ (allIH w n)) : Derives Γ (functional w n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let Q := ProjectCompilerCodeSyntax.compiled (old 3 w) (old 3 n) (slot 3 0) (slot 3 1)
  let R := ProjectCompilerCodeSyntax.compiled (old 3 w) (old 3 n) (slot 3 0) (slot 3 2)
  let Δ := Context.add R (Context.add Q (raisedContext 3 Γ))
  have hq : Derives Δ Q := .hyp (Or.inr (Or.inl rfl))
  have hr : Derives Δ R := .hyp (Or.inl rfl)
  have hw3 := of_eq (omega_rename w (old 3)) (add (HornBinderRules.under_body 3 hw Q) R)
  have hI3 := of_eq (allIH_rename w n (old 3)) (add (HornBinderRules.under_body 3 hI Q) R)
  exact outputs_from_induction (ZFContext.add (HornBinderRules.zf_body 3 hZ Q) R)
    (old 3 w) (old 3 n) (slot 3 0) (slot 3 1) (slot 3 2) hw3 hI3 hq hr

end PPAC.Migration.Internal.ProjectCompilerUniqueStep
