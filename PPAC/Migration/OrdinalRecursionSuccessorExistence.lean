import PPAC.Migration.OrdinalRecursionSuccessorSyntax

/-! 总算子给实际下一值，Pairing/Union给实际后继递归图；不抽取宿主见证。 -/
namespace PPAC.Migration.OrdinalRecursionSuccessorExistence
open Source SourceAlgebra SourceLogic GraphSyntax RestrictionSyntax OrdinalSyntax OrdinalRecursionSyntax
open OrdinalRecursionTotal OrdinalRecursionSuccessorSyntax
open ReplacementPredicates (paramsUp)

theorem exists_extension {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (f d : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hfoundation : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hp : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (hu : Derives Γ (Source.SetLanguage.union.rename Fin.elim0))
    (ht : Derives Γ (total p ρ)) (hd : Derives Γ (ordinal d)) (hf : Derives Γ (recursor p ρ f d)) :
    Derives Γ (extensionExists p ρ f d) := by
  have hex := evaluate p ρ d f ht hd hf
  let V := operator p (paramsUp ρ) d.castSucc f.castSucc (Fin.last m)
  let Ξ := Context.add V (Context.image Formula.raise Γ)
  change Derives Γ (.ex V) at hex
  apply Derives.exE (p := V) hex
  have he' : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he V
  have hfoundation' : Derives Ξ (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hfoundation V
  have hp' : Derives Ξ (Source.SetLanguage.pairing.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hp V
  have hu' : Derives Ξ (Source.SetLanguage.union.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hu V
  have hd' : Derives Ξ (ordinal d.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under hd V
  have hf' : Derives Ξ (recursor p (paramsUp ρ) f.castSucc d.castSucc) := by
    simpa only [Formula.raise, recursor_rename] using under hf V
  have hV : Derives Ξ V := .hyp (Or.inl rfl)
  have hn := OrdinalEmpty.no_self d.castSucc (.conjL (.conjR hd'))
  have hG := GraphInsertExistence.exists_extension f.castSucc d.castSucc d.castSucc (Fin.last m) hp' hu' he' (.conjL hf') hn
  let W := GraphInsertElimination.witnesses f.castSucc d.castSucc d.castSucc (Fin.last m)
  let Ψ := Context.add W (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Ξ)))
  have hout : Derives Ξ (extensionExists p (paramsUp ρ) f.castSucc d.castSucc) := by
    apply GraphInsertElimination.eliminate f.castSucc d.castSucc d.castSucc (Fin.last m) _ hG
    have heW : Derives Ψ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using GraphInsertElimination.under_three he' W
    have hfoundationW : Derives Ψ (Source.SetLanguage.foundation.rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using GraphInsertElimination.under_three hfoundation' W
    have hdW : Derives Ψ (ordinal d.castSucc.castSucc.castSucc.castSucc) := by
      simpa only [Formula.raise, ordinal_rename] using GraphInsertElimination.under_three hd' W
    have hfW : Derives Ψ (recursor p (paramsUp (paramsUp (paramsUp (paramsUp ρ)))) f.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc) := by
      simpa only [Formula.raise, recursor_rename] using GraphInsertElimination.under_three hf' W
    have hVW : Derives Ψ (operator p (paramsUp (paramsUp (paramsUp (paramsUp ρ))))
        d.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc) := by
      simpa only [Formula.raise, V, operator_rename] using GraphInsertElimination.under_three hV W
    have hW : Derives Ψ W := .hyp (Or.inl rfl)
    have hS : Derives Ψ (OmegaSyntax.successor (Fin.last (m+2)).castSucc d.castSucc.castSucc.castSucc.castSucc) := .conjL (.conjR hW)
    have hOrd := OrdinalSuccessor.ordinal (Fin.last (m+2)).castSucc d.castSucc.castSucc.castSucc.castSucc hfoundationW hS hdW
    have hRec := OrdinalRecursionExtension.recursor_preserved p (paramsUp (paramsUp (paramsUp (paramsUp ρ))))
      (Fin.last (m+3)) (Fin.last (m+2)).castSucc (Fin.last (m+1)).castSucc.castSucc
      f.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc
      heW hdW hfW hW hVW
    have hOld := GraphInsertRestriction.old_restriction (Fin.last (m+3)) f.castSucc.castSucc.castSucc.castSucc
      d.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc
      d.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc
      heW (.conjL hfW) (OrdinalEmpty.no_self _ (.conjL (.conjR hdW))) (.conjL (.conjR (.conjR hW))) (.conjL hW)
    have hr := intro_extension p (paramsUp (paramsUp (paramsUp (paramsUp ρ)))) (Fin.last (m+3)) (Fin.last (m+2)).castSucc
      f.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc (.conjI hS (.conjI hOrd (.conjI hRec hOld)))
    simpa only [Formula.raise, extensionExists_rename] using hr
  simpa only [Formula.raise, extensionExists_rename] using hout

theorem successor_from_extension {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (f d : Fin m)
    (hx : Derives Γ (extensionExists p ρ f d)) : Derives Γ (successorExists p ρ d) := by
  let E := extension p (paramsUp (paramsUp ρ)) (Fin.last (m+1)) (Fin.last m).castSucc f.castSucc.castSucc d.castSucc.castSucc
  let Γs := Context.add (.ex E) (Context.image Formula.raise Γ)
  let Γg := Context.add E (Context.image Formula.raise Γs)
  change Derives Γ (.ex (.ex E)) at hx
  apply Derives.exE hx
  apply Derives.exE (p := E) (Derives.hyp (Or.inl rfl))
  have hE : Derives Γg E := .hyp (Or.inl rfl)
  have hg := intro_successor p (paramsUp (paramsUp ρ)) d.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc
    (.conjL hE) (.conjL (.conjR (.conjR hE)))
  have hr : Derives Γg (successorExists p (paramsUp (paramsUp ρ)) d.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    simpa only [Formula.instantiate, successorGraph_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hg
  simpa only [Formula.raise, successorExists_rename] using hr

theorem successor_of_exists {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (d : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hfoundation : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hp : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (hu : Derives Γ (Source.SetLanguage.union.rename Fin.elim0))
    (ht : Derives Γ (total p ρ)) (hd : Derives Γ (ordinal d)) (hf : Derives Γ (recursorExists p ρ d)) :
    Derives Γ (successorExists p ρ d) := by
  let F := recursor p (paramsUp ρ) (Fin.last m) d.castSucc
  let Ξ := Context.add F (Context.image Formula.raise Γ)
  change Derives Γ (.ex F) at hf
  apply Derives.exE (p := F) hf
  have he' : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he F
  have hfoundation' : Derives Ξ (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hfoundation F
  have hp' : Derives Ξ (Source.SetLanguage.pairing.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hp F
  have hu' : Derives Ξ (Source.SetLanguage.union.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hu F
  have ht' : Derives Ξ (total p (paramsUp ρ)) := by
    simpa only [Formula.raise, total_rename] using under ht F
  have hd' : Derives Ξ (ordinal d.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under hd F
  have hF : Derives Ξ F := .hyp (Or.inl rfl)
  have hx := exists_extension p (paramsUp ρ) (Fin.last m) d.castSucc he' hfoundation' hp' hu' ht' hd' hF
  simpa only [Formula.raise, successorExists_rename] using successor_from_extension p (paramsUp ρ) (Fin.last m) d.castSucc hx
end PPAC.Migration.OrdinalRecursionSuccessorExistence
