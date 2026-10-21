import PPAC.Migration.OrdinalRecursionCollection

/-! 精确值域的族成员实际来自某个内部前驱及其后继域；保留完整对象见证。 -/
namespace PPAC.Migration.OrdinalRecursionFamilyMembers
open Source SourceAlgebra SourceLogic GraphSyntax RestrictionSyntax OrdinalSyntax OrdinalRecursionSyntax
open OrdinalRecursionFamilySyntax
open ReplacementPredicates (paramsUp)

abbrev witnesses {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a g : Fin m) : Formula (m+2) :=
  memberData p (paramsUp (paramsUp ρ)) a.castSucc.castSucc g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

theorem eliminate {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (c a g : Fin m) (q : Formula m)
    (hr : Derives Γ (range p ρ c a)) (hg : Derives Γ (.mem g c))
    (hc : Derives (Context.add (witnesses p ρ a g)
      (Context.image Formula.raise (Context.image Formula.raise Γ))) q.raise.raise) : Derives Γ q := by
  have hx := Derives.impE (.conjL (range_at p ρ c a g hr)) hg
  let A := (Formula.mem (Fin.last m) a.castSucc).conj
    (OrdinalRecursionSuccessorSyntax.successorGraph p (paramsUp ρ) (Fin.last m) g.castSucc)
  let Γb := Context.add A (Context.image Formula.raise Γ)
  change Derives Γ (.ex A) at hx
  apply Derives.exE (p := A) hx
  have hA : Derives Γb A := .hyp (Or.inl rfl)
  let B := (OmegaSyntax.successor (Fin.last (m+1)) (Fin.last m).castSucc).conj
    (recursor p (paramsUp (paramsUp ρ)) g.castSucc.castSucc (Fin.last (m+1)))
  let Γs := Context.add B (Context.image Formula.raise Γb)
  have hs : Derives Γb (.ex B) := .conjR hA
  apply Derives.exE (p := B) hs
  have hmem : Derives Γs (.mem (Fin.last m).castSucc a.castSucc.castSucc) := under (.conjL hA) B
  have hB : Derives Γs B := .hyp (Or.inl rfl)
  have hw : Derives Γs (witnesses p ρ a g) := .conjI hmem hB
  have himp : Derives Γs ((witnesses p ρ a g).imp q.raise.raise) := by
    refine Derives.weaken ?_ (Derives.impI hc)
    rintro r ⟨t, ht, heq⟩
    exact Or.inr ⟨t, Or.inr ht, heq⟩
  exact .impE himp hw

theorem domain_facts {n m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (p : Formula (n+3)) (ρ : Fin n → Fin m) (a g b s : Fin m)
    (ha : Derives Γ (ordinal a)) (hw : Derives Γ (memberData p ρ a g b s)) :
    Derives Γ ((ordinal s).conj (subset s a)) := by
  have hb := Derives.conjL hw
  have hs := Derives.conjL (Derives.conjR hw)
  have ho := OrdinalRestriction.member a b ha hb
  exact .conjI (OrdinalSuccessor.ordinal s b hA.foundation hs ho)
    (OmegaElementary.successor_subset s b a hs hb (OrdinalTransitivity.subset_of_member a b (.conjL ha) hb))

theorem graphs {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (c a : Fin m)
    (hr : Derives Γ (range p ρ c a)) : Derives Γ (GraphFamilySyntax.graphs c) := by
  apply Derives.allI
  have hr' : Derives (Context.image Formula.raise Γ) (range p (paramsUp ρ) c.castSucc a.castSucc) := by
    simpa only [Formula.raise, range_rename] using Derives.rename Fin.castSucc hr
  apply Derives.impI
  let M := Formula.mem (Fin.last m) c.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  let W := witnesses p (paramsUp ρ) a.castSucc (Fin.last m)
  let Ξ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Δ))
  apply eliminate p (paramsUp ρ) c.castSucc a.castSucc (Fin.last m) _ (add hr' M) (.hyp (Or.inl rfl))
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  have hout : Derives Ξ (GraphFamilySyntax.isGraph (Fin.last m).castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+2))
    simpa only [Formula.instantiate, GraphSyntax.functionOn_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
      using Derives.conjL (Derives.conjR (Derives.conjR hW))
  simpa only [Formula.raise, GraphFamilySyntax.isGraph_rename] using hout
end PPAC.Migration.OrdinalRecursionFamilyMembers
