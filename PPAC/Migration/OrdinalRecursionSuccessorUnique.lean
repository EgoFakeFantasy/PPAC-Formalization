import PPAC.Migration.OrdinalRecursionSuccessorExistence

/-! 后继域唯一与给定递归图唯一共同给出后继图的唯一纤维，可供原Replacement收集。 -/
namespace PPAC.Migration.OrdinalRecursionSuccessorUnique
open Source SourceAlgebra SourceLogic GraphSyntax RestrictionSyntax OrdinalSyntax OrdinalRecursionSyntax
open OrdinalRecursionDeterminism OrdinalRecursionTotal OrdinalRecursionSuccessorSyntax
open ReplacementPredicates (paramsUp)

def uniqueAt {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (d g : Fin m) : Formula m := .all
  ((successorGraph p (paramsUp ρ) d.castSucc (Fin.last m)).imp (.equal (Fin.last m) g.castSucc))

def uniqueFiber {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (d : Fin m) : Formula m := .ex
  ((successorGraph p (paramsUp ρ) d.castSucc (Fin.last m)).conj (uniqueAt p (paramsUp ρ) d.castSucc (Fin.last m)))

def successorMatrix {n} (p : Formula (n+3)) : Formula (n+2) :=
  successorGraph p (fun i => i.castSucc.castSucc) (Fin.last n).castSucc (Fin.last (n+1))

theorem uniqueAt_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (d g : Fin m) (r : Fin m → Fin k) :
    (uniqueAt p ρ d g).rename r = uniqueAt p (fun i => r (ρ i)) (r d) (r g) := by
  simp only [uniqueAt, Formula.rename, successorGraph_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueFiber_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (d : Fin m) (r : Fin m → Fin k) :
    (uniqueFiber p ρ d).rename r = uniqueFiber p (fun i => r (ρ i)) (r d) := by
  simp only [uniqueFiber, Formula.rename, successorGraph_rename, uniqueAt_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_relation {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (d g : Fin m) :
    ReplacementPredicates.rel (successorMatrix p) ρ d g = successorGraph p ρ d g := by
  simp only [ReplacementPredicates.rel, Source.SetLanguage.relation, successorMatrix, successorGraph_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_unique {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (d g : Fin m) :
    ReplacementPredicates.unique (successorMatrix p) ρ d g = uniqueAt p ρ d g := by
  simp only [ReplacementPredicates.unique, matrix_relation, uniqueAt]

theorem matrix_fiber {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (d : Fin m) :
    ReplacementPredicates.fiber (successorMatrix p) ρ d = uniqueFiber p ρ d := by
  simp only [ReplacementPredicates.fiber, matrix_relation, matrix_unique, uniqueFiber]

theorem recursor_subst_domain {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (g d e : Fin m)
    (he : Derives Γ (.equal d e)) (hg : Derives Γ (recursor p ρ g d)) : Derives Γ (recursor p ρ g e) := by
  have hi : Derives Γ ((recursor p (paramsUp ρ) g.castSucc (Fin.last m)).instantiate d) := by
    simpa only [Formula.instantiate, recursor_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hg
  have hr := Derives.eqSubst (recursor p (paramsUp ρ) g.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, recursor_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hr

theorem graphs_unique {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (d g h : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hfoundation : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation IterationSyntax.agreementMatrix.neg).rename Fin.elim0))
    (hdet : Derives Γ (deterministic p ρ)) (hd : Derives Γ (ordinal d))
    (hg : Derives Γ (successorGraph p ρ d g)) (hh : Derives Γ (successorGraph p ρ d h)) : Derives Γ (.equal g h) := by
  let S := (OmegaSyntax.successor (Fin.last m) d.castSucc).conj (recursor p (paramsUp ρ) g.castSucc (Fin.last m))
  let Ξ := Context.add S (Context.image Formula.raise Γ)
  change Derives Γ (.ex S) at hg
  apply Derives.exE (p := S) hg
  have he1 : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he S
  have hfoundation1 : Derives Ξ (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hfoundation S
  have hsep1 : Derives Ξ ((Source.SetLanguage.separation IterationSyntax.agreementMatrix.neg).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hsep S
  have hdet1 : Derives Ξ (deterministic p (paramsUp ρ)) := by
    simpa only [Formula.raise, deterministic_rename] using under hdet S
  have hd1 : Derives Ξ (ordinal d.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under hd S
  have hh1 : Derives Ξ (successorGraph p (paramsUp ρ) d.castSucc h.castSucc) := by
    simpa only [Formula.raise, successorGraph_rename] using under hh S
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  let T := (OmegaSyntax.successor (Fin.last (m+1)) d.castSucc.castSucc).conj
    (recursor p (paramsUp (paramsUp ρ)) h.castSucc.castSucc (Fin.last (m+1)))
  let Ψ := Context.add T (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex T) at hh1
  apply Derives.exE (p := T) hh1
  have he2 : Derives Ψ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he1 T
  have hfoundation2 : Derives Ψ (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hfoundation1 T
  have hsep2 : Derives Ψ ((Source.SetLanguage.separation IterationSyntax.agreementMatrix.neg).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hsep1 T
  have hdet2 : Derives Ψ (deterministic p (paramsUp (paramsUp ρ))) := by
    simpa only [Formula.raise, deterministic_rename] using under hdet1 T
  have hd2 : Derives Ψ (ordinal d.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under hd1 T
  have hS2 : Derives Ψ ((OmegaSyntax.successor (Fin.last m).castSucc d.castSucc.castSucc).conj
      (recursor p (paramsUp (paramsUp ρ)) g.castSucc.castSucc (Fin.last m).castSucc)) := by
    simpa only [Formula.raise, S, Formula.rename, OmegaSyntax.successor_rename, recursor_rename] using under hS T
  have hT : Derives Ψ T := .hyp (Or.inl rfl)
  have hst := InsertLogic.unique (Fin.last m).castSucc (Fin.last (m+1)) d.castSucc.castSucc d.castSucc.castSucc
    he2 (.conjL hS2) (.conjL hT)
  have hRec := recursor_subst_domain p (paramsUp (paramsUp ρ)) h.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc
    (eq_symm hst) (.conjR hT)
  have hOrd := OrdinalSuccessor.ordinal (Fin.last m).castSucc d.castSucc.castSucc hfoundation2 (.conjL hS2) hd2
  exact OrdinalRecursionCompatibility.unique_same_domain p (paramsUp (paramsUp ρ)) g.castSucc.castSucc h.castSucc.castSucc
    (Fin.last m).castSucc he2 hfoundation2 hsep2 hdet2 hOrd (.conjR hS2) hRec

theorem unique_from_graph {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (d g : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hfoundation : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation IterationSyntax.agreementMatrix.neg).rename Fin.elim0))
    (hdet : Derives Γ (deterministic p ρ)) (hd : Derives Γ (ordinal d))
    (hg : Derives Γ (successorGraph p ρ d g)) : Derives Γ (uniqueAt p ρ d g) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have he' : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  have hfoundation' : Derives Δ (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hfoundation
  have hsep' : Derives Δ ((Source.SetLanguage.separation IterationSyntax.agreementMatrix.neg).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hsep
  have hdet' : Derives Δ (deterministic p (paramsUp ρ)) := by
    simpa only [Formula.raise, deterministic_rename] using Derives.rename Fin.castSucc hdet
  have hd' : Derives Δ (ordinal d.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using Derives.rename Fin.castSucc hd
  have hg' : Derives Δ (successorGraph p (paramsUp ρ) d.castSucc g.castSucc) := by
    simpa only [Formula.raise, successorGraph_rename] using Derives.rename Fin.castSucc hg
  apply Derives.impI
  exact graphs_unique p (paramsUp ρ) d.castSucc (Fin.last m) g.castSucc (add he' _) (add hfoundation' _)
    (add hsep' _) (add hdet' _) (add hd' _) (.hyp (Or.inl rfl)) (add hg' _)

theorem fiber_of_exists {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (d : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hfoundation : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation IterationSyntax.agreementMatrix.neg).rename Fin.elim0))
    (hdet : Derives Γ (deterministic p ρ)) (hd : Derives Γ (ordinal d))
    (hx : Derives Γ (successorExists p ρ d)) : Derives Γ (uniqueFiber p ρ d) := by
  let G := successorGraph p (paramsUp ρ) d.castSucc (Fin.last m)
  let Ξ := Context.add G (Context.image Formula.raise Γ)
  change Derives Γ (.ex G) at hx
  apply Derives.exE (p := G) hx
  have he' : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he G
  have hfoundation' : Derives Ξ (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hfoundation G
  have hsep' : Derives Ξ ((Source.SetLanguage.separation IterationSyntax.agreementMatrix.neg).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hsep G
  have hdet' : Derives Ξ (deterministic p (paramsUp ρ)) := by
    simpa only [Formula.raise, deterministic_rename] using under hdet G
  have hd' : Derives Ξ (ordinal d.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under hd G
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have huniq := unique_from_graph p (paramsUp ρ) d.castSucc (Fin.last m) he' hfoundation' hsep' hdet' hd' hG
  have hr : Derives Ξ (uniqueFiber p (paramsUp ρ) d.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, Formula.rename, successorGraph_rename, uniqueAt_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hG huniq
  simpa only [Formula.raise, uniqueFiber_rename] using hr

theorem exists_unique_successor {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (d : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hfoundation : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hp : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (hu : Derives Γ (Source.SetLanguage.union.rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation IterationSyntax.agreementMatrix.neg).rename Fin.elim0))
    (ht : Derives Γ (total p ρ)) (hdet : Derives Γ (deterministic p ρ))
    (hd : Derives Γ (ordinal d)) (hf : Derives Γ (recursorExists p ρ d)) : Derives Γ (uniqueFiber p ρ d) :=
  fiber_of_exists p ρ d he hfoundation hsep hdet hd
    (OrdinalRecursionSuccessorExistence.successor_of_exists p ρ d he hfoundation hp hu ht hd hf)
end PPAC.Migration.OrdinalRecursionSuccessorUnique
