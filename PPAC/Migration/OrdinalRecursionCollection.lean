import PPAC.Migration.OrdinalRecursionFamilySyntax

/-! 原Replacement实际收集全部内部前驱的唯一后继图，并证明精确值域和逐前驱覆盖。 -/
namespace PPAC.Migration.OrdinalRecursionCollection
open Source SourceAlgebra SourceLogic OrdinalSyntax OrdinalRecursionSyntax OrdinalRecursionSuccessorSyntax
open OrdinalRecursionTotal OrdinalRecursionDeterminism OrdinalRecursionFamilySyntax
open ReplacementPredicates (paramsUp)

theorem total_fibers {n m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (p : Formula (n+3)) (ρ : Fin n → Fin m) (a : Fin m)
    (ht : Derives Γ (total p ρ)) (hdet : Derives Γ (deterministic p ρ))
    (ha : Derives Γ (ordinal a)) (hpred : Derives Γ (predecessors p ρ a)) :
    Derives Γ (ReplacementPredicates.total (OrdinalRecursionSuccessorUnique.successorMatrix p) ρ a) := by
  simp only [ReplacementPredicates.total, OrdinalRecursionSuccessorUnique.matrix_fiber]
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hA' := OrdinalRecursionContext.rename hA Fin.castSucc
  have ht' : Derives Δ (total p (paramsUp ρ)) := by
    simpa only [Formula.raise, total_rename] using Derives.rename Fin.castSucc ht
  have hdet' : Derives Δ (deterministic p (paramsUp ρ)) := by
    simpa only [Formula.raise, deterministic_rename] using Derives.rename Fin.castSucc hdet
  have ha' : Derives Δ (ordinal a.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using Derives.rename Fin.castSucc ha
  have hpred' : Derives Δ (predecessors p (paramsUp ρ) a.castSucc) := by
    simpa only [Formula.raise, predecessors_rename] using Derives.rename Fin.castSucc hpred
  apply Derives.impI
  let M := Formula.mem (Fin.last m) a.castSucc
  let Ξ := Context.add M Δ
  have hx : Derives Ξ M := .hyp (Or.inl rfl)
  have hAx := OrdinalRecursionContext.add hA' M
  exact OrdinalRecursionSuccessorUnique.exists_unique_successor p (paramsUp ρ) (Fin.last m)
    hAx.extensionality hAx.foundation hAx.pairing hAx.union hAx.agreementSeparation
    (add ht' M) (add hdet' M) (OrdinalRestriction.member a.castSucc (Fin.last m) (add ha' M) hx)
    (.impE (add (predecessors_at p (paramsUp ρ) a.castSucc (Fin.last m) hpred') M) hx)

theorem exists_range {n m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (p : Formula (n+3)) (ρ : Fin n → Fin m) (a : Fin m)
    (hr : Derives Γ ((Source.SetLanguage.replacement (OrdinalRecursionSuccessorUnique.successorMatrix p)).rename Fin.elim0))
    (ht : Derives Γ (total p ρ)) (hdet : Derives Γ (deterministic p ρ))
    (ha : Derives Γ (ordinal a)) (hpred : Derives Γ (predecessors p ρ a)) : Derives Γ (rangeExists p ρ a) := by
  have hi := Derives.impE (IterationValueCollection.replacement_instance
    (OrdinalRecursionSuccessorUnique.successorMatrix p) ρ a hr) (total_fibers hA p ρ a ht hdet ha hpred)
  simpa only [ReplacementPredicates.imageExists, matrix_range, rangeExists] using hi

theorem coverage_of_total {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (c a : Fin m)
    (ht : Derives Γ (ReplacementPredicates.total (OrdinalRecursionSuccessorUnique.successorMatrix p) ρ a))
    (hr : Derives Γ (range p ρ c a)) : Derives Γ (coverage p ρ c a) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have ht' : Derives Δ (ReplacementPredicates.total (OrdinalRecursionSuccessorUnique.successorMatrix p) (paramsUp ρ) a.castSucc) := by
    simpa only [Formula.raise, ReplacementPredicates.total_rename] using Derives.rename Fin.castSucc ht
  have hr' : Derives Δ (range p (paramsUp ρ) c.castSucc a.castSucc) := by
    simpa only [Formula.raise, range_rename] using Derives.rename Fin.castSucc hr
  apply Derives.impI
  let M := Formula.mem (Fin.last m) a.castSucc
  let Γb := Context.add M Δ
  have hb : Derives Γb M := .hyp (Or.inl rfl)
  have hF : Derives Γb (OrdinalRecursionSuccessorUnique.uniqueFiber p (paramsUp ρ) (Fin.last m)) := by
    simpa only [OrdinalRecursionSuccessorUnique.matrix_fiber] using
      Derives.impE (add (ReplacementPredicates.specialize_total (OrdinalRecursionSuccessorUnique.successorMatrix p)
        (paramsUp ρ) a.castSucc (Fin.last m) ht') M) hb
  let G := (successorGraph p (paramsUp (paramsUp ρ)) (Fin.last m).castSucc (Fin.last (m+1))).conj
    (OrdinalRecursionSuccessorUnique.uniqueAt p (paramsUp (paramsUp ρ)) (Fin.last m).castSucc (Fin.last (m+1)))
  let Ξ := Context.add G (Context.image Formula.raise Γb)
  change Derives Γb (.ex G) at hF
  apply Derives.exE (p := G) hF
  have hrG : Derives Ξ (range p (paramsUp (paramsUp ρ)) c.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, range_rename] using under (add hr' M) G
  have hbG : Derives Ξ (.mem (Fin.last m).castSucc a.castSucc.castSucc) := under hb G
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have himage := image_intro p (paramsUp (paramsUp ρ)) a.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc hbG (.conjL hG)
  have hmem := Derives.impE (.conjR (range_at p (paramsUp (paramsUp ρ)) c.castSucc.castSucc a.castSucc.castSucc (Fin.last (m+1)) hrG)) himage
  have hout : Derives Ξ (memberAt p (paramsUp (paramsUp ρ)) c.castSucc.castSucc (Fin.last m).castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    simpa only [Formula.instantiate, Formula.rename, successorGraph_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hmem (Derives.conjL hG)
  simpa only [Formula.raise, memberAt_rename] using hout

theorem exists_family {n m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (p : Formula (n+3)) (ρ : Fin n → Fin m) (a : Fin m)
    (hr : Derives Γ ((Source.SetLanguage.replacement (OrdinalRecursionSuccessorUnique.successorMatrix p)).rename Fin.elim0))
    (ht : Derives Γ (total p ρ)) (hdet : Derives Γ (deterministic p ρ))
    (ha : Derives Γ (ordinal a)) (hpred : Derives Γ (predecessors p ρ a)) : Derives Γ (familyExists p ρ a) := by
  have htotal := total_fibers hA p ρ a ht hdet ha hpred
  have hex := exists_range hA p ρ a hr ht hdet ha hpred
  let C := range p (paramsUp ρ) (Fin.last m) a.castSucc
  let Ξ := Context.add C (Context.image Formula.raise Γ)
  change Derives Γ (.ex C) at hex
  apply Derives.exE (p := C) hex
  have htC : Derives Ξ (ReplacementPredicates.total (OrdinalRecursionSuccessorUnique.successorMatrix p) (paramsUp ρ) a.castSucc) := by
    simpa only [Formula.raise, ReplacementPredicates.total_rename] using under htotal C
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hcover := coverage_of_total p (paramsUp ρ) (Fin.last m) a.castSucc htC hC
  have hout : Derives Ξ (familyExists p (paramsUp ρ) a.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, family_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hC hcover
  simpa only [Formula.raise, familyExists_rename] using hout
end PPAC.Migration.OrdinalRecursionCollection
