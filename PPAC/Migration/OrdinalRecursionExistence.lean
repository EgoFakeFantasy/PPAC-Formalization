import PPAC.Migration.OrdinalRecursionExistenceSyntax

/-! 原Replacement实际收集和并图装配为对象集合归纳进步步，覆盖全部内部原序数。 -/
namespace PPAC.Migration.OrdinalRecursionExistence
open Source SourceAlgebra SourceLogic OrdinalSyntax OrdinalRecursionSyntax
open OrdinalRecursionTotal OrdinalRecursionDeterminism OrdinalRecursionFamilySyntax OrdinalRecursionExistenceSyntax
open ReplacementPredicates (paramsUp)

theorem step_from_predecessors {n m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (p : Formula (n+3)) (ρ : Fin n → Fin m) (a : Fin m)
    (hr : Derives Γ ((Source.SetLanguage.replacement (OrdinalRecursionSuccessorUnique.successorMatrix p)).rename Fin.elim0))
    (ht : Derives Γ (total p ρ)) (hdet : Derives Γ (deterministic p ρ))
    (ha : Derives Γ (ordinal a)) (hpred : Derives Γ (predecessors p ρ a)) : Derives Γ (recursorExists p ρ a) := by
  have hex := OrdinalRecursionCollection.exists_family hA p ρ a hr ht hdet ha hpred
  let C := family p (paramsUp ρ) (Fin.last m) a.castSucc
  let Ξ := Context.add C (Context.image Formula.raise Γ)
  change Derives Γ (.ex C) at hex
  apply Derives.exE (p := C) hex
  have hAC := OrdinalRecursionContext.under hA C
  have hdetC : Derives Ξ (deterministic p (paramsUp ρ)) := by
    simpa only [Formula.raise, deterministic_rename] using under hdet C
  have haC : Derives Ξ (ordinal a.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under ha C
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  simpa only [Formula.raise, recursorExists_rename] using OrdinalRecursionUnion.exists_union hAC p (paramsUp ρ)
    (Fin.last m) a.castSucc hdetC haC hC

theorem predecessors_from_below {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a : Fin m)
    (ha : Derives Γ (ordinal a))
    (hb : Derives Γ (SetInductionSyntax.below (existenceMatrix p) ρ a)) : Derives Γ (predecessors p ρ a) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have ha' : Derives Δ (ordinal a.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using Derives.rename Fin.castSucc ha
  have hb' : Derives Δ (SetInductionSyntax.below (existenceMatrix p) (paramsUp ρ) a.castSucc) := by
    simpa only [Formula.raise, SetInductionSyntax.below_rename] using Derives.rename Fin.castSucc hb
  apply Derives.impI
  let M := Formula.mem (Fin.last m) a.castSucc
  let Ξ := Context.add M Δ
  have hx : Derives Ξ M := .hyp (Or.inl rfl)
  have hpoint : Derives Ξ ((ordinal (Fin.last m)).imp (recursorExists p (paramsUp ρ) (Fin.last m))) := by
    simpa only [existence_pred, existsAt] using Derives.impE
      (add (SetInductionSyntax.below_at (existenceMatrix p) (paramsUp ρ) a.castSucc (Fin.last m) hb') M) hx
  exact .impE hpoint (OrdinalRestriction.member a.castSucc (Fin.last m) (add ha' M) hx)

theorem progressive {n m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (p : Formula (n+3)) (ρ : Fin n → Fin m)
    (hr : Derives Γ ((Source.SetLanguage.replacement (OrdinalRecursionSuccessorUnique.successorMatrix p)).rename Fin.elim0))
    (ht : Derives Γ (total p ρ)) (hdet : Derives Γ (deterministic p ρ)) :
    Derives Γ (SetInductionSyntax.progressive (existenceMatrix p) ρ) := by
  apply Derives.allI
  change Derives (Context.image Formula.raise Γ)
    ((SetInductionSyntax.below (existenceMatrix p) (paramsUp ρ) (Fin.last m)).imp
      (MinimalPredicates.pred (existenceMatrix p) (paramsUp ρ) (Fin.last m)))
  rw [existence_pred]
  let Δ := Context.image Formula.raise Γ
  have hA' := OrdinalRecursionContext.rename hA Fin.castSucc
  have hr' : Derives Δ ((Source.SetLanguage.replacement (OrdinalRecursionSuccessorUnique.successorMatrix p)).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hr
  have ht' : Derives Δ (total p (paramsUp ρ)) := by
    simpa only [Formula.raise, total_rename] using Derives.rename Fin.castSucc ht
  have hdet' : Derives Δ (deterministic p (paramsUp ρ)) := by
    simpa only [Formula.raise, deterministic_rename] using Derives.rename Fin.castSucc hdet
  apply Derives.impI
  apply Derives.impI
  let B := SetInductionSyntax.below (existenceMatrix p) (paramsUp ρ) (Fin.last m)
  let Ξ := Context.add (ordinal (Fin.last m)) (Context.add B Δ)
  have ha : Derives Ξ (ordinal (Fin.last m)) := .hyp (Or.inl rfl)
  have hb : Derives Ξ B := .hyp (Or.inr (Or.inl rfl))
  exact step_from_predecessors (OrdinalRecursionContext.add (OrdinalRecursionContext.add hA' B) _) p (paramsUp ρ) (Fin.last m)
    (add (add hr' B) _) (add (add ht' B) _) (add (add hdet' B) _) ha (predecessors_from_below p (paramsUp ρ) (Fin.last m) ha hb)

theorem all_exists {n m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (p : Formula (n+3)) (ρ : Fin n → Fin m)
    (hr : Derives Γ ((Source.SetLanguage.replacement (OrdinalRecursionSuccessorUnique.successorMatrix p)).rename Fin.elim0))
    (hs : Derives Γ ((Source.SetLanguage.separation (existenceMatrix p).neg).rename Fin.elim0))
    (hc : Derives Γ (ObjectTransitiveCover.coverSentence.rename Fin.elim0))
    (ht : Derives Γ (total p ρ)) (hdet : Derives Γ (deterministic p ρ)) : Derives Γ (holds p ρ) := by
  have hi := SetInduction.all_holds (existenceMatrix p) ρ hs hA.foundation hc (progressive hA p ρ hr ht hdet)
  simpa only [SetInductionSyntax.holds, existence_pred, holds] using hi
end PPAC.Migration.OrdinalRecursionExistence
