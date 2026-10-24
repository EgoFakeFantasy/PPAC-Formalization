import PPAC.Migration.Internal.ProjectCompilerCompleteQuerySyntax

/-! Source child judgments obtain actual checked outputs from the object member hypothesis. -/
namespace PPAC.Migration.Internal.ProjectCompilerCompleteQueries
open Source SourceAlgebra SourceLogic OmegaSyntax ProjectCompilerCompleteSyntax ProjectCompilerCompleteQuerySyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem child_output {m} {Γ : Context m} (w n x b f z : Fin m)
    (hz : Derives Γ (empty z)) (hI : Derives Γ (allIH w n)) (hx : Derives Γ (.mem x n))
    (hc : Derives Γ (ProjectSourceCodeSyntax.sourceCode w x b f)) : Derives Γ (existsOutput w x b) :=
  at_correct w x b f z (below_correct w n x hI hx) hz hc

theorem ordinary_query {m} {Γ : Context m} (w n x b : Fin m) (hx : Derives Γ (.mem x n))
    (he : Derives Γ (existsOutput w x b)) : Derives Γ (someCheck false w n x b) := by
  let C := ProjectCompilerCodeSyntax.compiled w.castSucc x.castSucc b.castSucc (Fin.last m)
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply Derives.exE (p := C) he
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hx1 : Derives Δ (.mem x.castSucc n.castSucc) := under hx C
  have hi := intro_someCheck false w.castSucc n.castSucc x.castSucc b.castSucc (Fin.last m)
    (query_of_output w.castSucc n.castSucc x.castSucc b.castSucc (Fin.last m) hx1 hC)
  exact of_eq (someCheck_rename false w n x b Fin.castSucc).symm hi

theorem source_check_output {m} {Γ : Context m} (advance : Bool) (w n x b f z : Fin m)
    (hz : Derives Γ (empty z)) (hI : Derives Γ (allIH w n)) (hx : Derives Γ (.mem x n))
    (hc : Derives Γ (ProjectSourceCodeRecursiveSyntax.stepCheck advance w x b f)) :
    Derives Γ (someCheck advance w n x b) := by
  cases advance
  · exact ordinary_query w n x b hx (child_output w n x b f z hz hI hx hc)
  · let K := (successor (Fin.last m) b.castSucc).conj
      (ProjectSourceCodeSyntax.sourceCode w.castSucc x.castSucc (Fin.last m) f.castSucc)
    let Ξ := Context.add K (Context.image Formula.raise Γ)
    apply Derives.exE (p := K) hc
    have hK : Derives Ξ K := .hyp (Or.inl rfl)
    have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz K)
    have hI1 := of_eq (allIH_rename w n Fin.castSucc) (under hI K)
    have hx1 : Derives Ξ (.mem x.castSucc n.castSucc) := under hx K
    have he := child_output w.castSucc n.castSucc x.castSucc (Fin.last m) f.castSucc z.castSucc hz1 hI1 hx1 (.conjR hK)
    let C := ProjectCompilerCodeSyntax.compiled w.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    let Δ := Context.add C (Context.image Formula.raise Ξ)
    apply Derives.exE (p := C) he
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    have hx2 : Derives Δ (.mem x.castSucc.castSucc n.castSucc.castSucc) := under hx1 C
    have hs2 := of_eq (successor_rename (Fin.last m) b.castSucc Fin.castSucc) (under (.conjL hK) C)
    have hq := query_of_output w.castSucc.castSucc n.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hx2 hC
    have ha := intro_advanced w.castSucc.castSucc n.castSucc.castSucc x.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc hs2 hq
    have ho := intro_someCheck true w.castSucc.castSucc n.castSucc.castSucc x.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1)) ha
    exact of_eq (by simp only [someCheck_rename]) ho

end PPAC.Migration.Internal.ProjectCompilerCompleteQueries
