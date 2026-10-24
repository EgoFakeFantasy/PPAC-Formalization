import PPAC.Migration.Internal.ProjectCompilerSourceIH

/-! Source validation from actual Compiled for one complete object member-induction step. -/
namespace PPAC.Migration.Internal.ProjectCompilerSourceStep
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax ProjectCompilerSourceSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem input_from_induction {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b q f : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (.mem f w)) (hI : Derives Γ (allIH w n))
    (hc : Derives Γ (ProjectCompilerCodeSyntax.compiled w n b q)) : Derives Γ (ProjectSourceCodeSyntax.sourceCode w n b f) := by
  have hr := Derives.impE (.conjL (ProjectCompilerRecursive.recursive_iff hZ w n b q hw)) hc
  have hn := Derives.conjL hr
  have hb := Derives.conjL (Derives.conjL (Derives.conjR hr))
  let B := ProjectCompilerRecursiveSyntax.body w n b q
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (.conjR (.conjR hr))
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (.mem n.castSucc w.castSucc) := under hn B
  have hb1 : Derives Δ (.mem b.castSucc w.castSucc) := under hb B
  have hf1 : Derives Δ (.mem f.castSucc w.castSucc) := under hf B
  have hI1 := of_eq (allIH_rename w n Fin.castSucc) (under hI B)
  have hg := ProjectCompilerSourceIH.supply_queries w.castSucc n.castSucc f.castSucc hf1 hI1
  have hs := ProjectCompilerSourceCases.actual_source_cases w.castSucc b.castSucc (Fin.last m) n.castSucc q.castSucc f.castSucc
    (.conjI hb1 hf1) hg (.conjR hB)
  have hv := Derives.impE (.conjR (ProjectSourceCodeRecursive.recursive_iff hZ1 w.castSucc n.castSucc b.castSucc f.castSucc hw1)) (.conjI hn1 hs)
  exact of_eq (ProjectSourceCodeSyntax.sourceCode_rename w n b f Fin.castSucc).symm hv

theorem from_induction {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hI : Derives Γ (allIH w n)) : Derives Γ (correct w n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let F := Formula.mem (slot 3 2 : Fin (m+3)) (old 3 w)
  let C := ProjectCompilerCodeSyntax.compiled (old 3 w) (old 3 n) (slot 3 0) (slot 3 1)
  let Δ := Context.add C (Context.add F (raisedContext 3 Γ))
  have hf : Derives Δ F := .hyp (Or.inr (Or.inl rfl))
  have hc : Derives Δ C := .hyp (Or.inl rfl)
  have hw3 := of_eq (omega_rename w (old 3)) (add (HornBinderRules.under_body 3 hw F) C)
  have hI3 := of_eq (allIH_rename w n (old 3)) (add (HornBinderRules.under_body 3 hI F) C)
  exact input_from_induction (ZFContext.add (HornBinderRules.zf_body 3 hZ F) C)
    (old 3 w) (old 3 n) (slot 3 0) (slot 3 1) (slot 3 2) hw3 hf hI3 hc

end PPAC.Migration.Internal.ProjectCompilerSourceStep
