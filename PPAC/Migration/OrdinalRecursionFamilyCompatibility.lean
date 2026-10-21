import PPAC.Migration.OrdinalRecursionFamilyMembers

/-! 精确前驱后继图族的相容性由已证递归图相容推得，不作为收集公理或结构字段。 -/
namespace PPAC.Migration.OrdinalRecursionFamilyCompatibility
open Source SourceAlgebra SourceLogic GraphSyntax OrdinalSyntax OrdinalRecursionSyntax
open OrdinalRecursionDeterminism OrdinalRecursionFamilySyntax OrdinalRecursionFamilyMembers
open ReplacementPredicates (paramsUp)

theorem data_compatible {n m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (p : Formula (n+3)) (ρ : Fin n → Fin m) (a g h b s k t : Fin m)
    (hdet : Derives Γ (deterministic p ρ)) (ha : Derives Γ (ordinal a))
    (hg : Derives Γ (memberData p ρ a g b s)) (hh : Derives Γ (memberData p ρ a h k t)) :
    Derives Γ (GraphFamilySyntax.agrees g h) :=
  OrdinalRecursionCompatibility.compatible p ρ g h s t hA.extensionality hA.foundation hA.agreementSeparation hdet
    (.conjL (domain_facts hA p ρ a g b s ha hg)) (.conjL (domain_facts hA p ρ a h k t ha hh))
    (.conjR (.conjR hg)) (.conjR (.conjR hh))

theorem member_compatible {n m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (p : Formula (n+3)) (ρ : Fin n → Fin m) (c a g h b s : Fin m)
    (hdet : Derives Γ (deterministic p ρ)) (ha : Derives Γ (ordinal a))
    (hr : Derives Γ (range p ρ c a)) (hg : Derives Γ (memberData p ρ a g b s)) (hh : Derives Γ (.mem h c)) :
    Derives Γ (GraphFamilySyntax.agrees g h) := by
  let W := witnesses p ρ a h
  let Ξ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate p ρ c a h _ hr hh
  have hAW := OrdinalRecursionContext.under_two hA W
  have hdetW : Derives Ξ (deterministic p (paramsUp (paramsUp ρ))) := by
    simpa only [Formula.raise, deterministic_rename] using OrderedPairElimination.under_two hdet W
  have haW : Derives Ξ (ordinal a.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using OrderedPairElimination.under_two ha W
  have hgW : Derives Ξ (memberData p (paramsUp (paramsUp ρ)) a.castSucc.castSucc g.castSucc.castSucc b.castSucc.castSucc s.castSucc.castSucc) := by
    simpa only [Formula.raise, memberData_rename] using OrderedPairElimination.under_two hg W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  simpa only [Formula.raise, GraphFamilySyntax.agrees_rename] using
    data_compatible hAW p (paramsUp (paramsUp ρ)) a.castSucc.castSucc g.castSucc.castSucc h.castSucc.castSucc
      b.castSucc.castSucc s.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hdetW haW hgW hW

theorem pair_compatible {n m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (p : Formula (n+3)) (ρ : Fin n → Fin m) (c a g h : Fin m)
    (hdet : Derives Γ (deterministic p ρ)) (ha : Derives Γ (ordinal a))
    (hr : Derives Γ (range p ρ c a)) (hg : Derives Γ (.mem g c)) (hh : Derives Γ (.mem h c)) :
    Derives Γ (GraphFamilySyntax.agrees g h) := by
  let W := witnesses p ρ a g
  let Ξ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate p ρ c a g _ hr hg
  have hAW := OrdinalRecursionContext.under_two hA W
  have hdetW : Derives Ξ (deterministic p (paramsUp (paramsUp ρ))) := by
    simpa only [Formula.raise, deterministic_rename] using OrderedPairElimination.under_two hdet W
  have haW : Derives Ξ (ordinal a.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using OrderedPairElimination.under_two ha W
  have hrW : Derives Ξ (range p (paramsUp (paramsUp ρ)) c.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, range_rename] using OrderedPairElimination.under_two hr W
  have hhW : Derives Ξ (.mem h.castSucc.castSucc c.castSucc.castSucc) := OrderedPairElimination.under_two hh W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  simpa only [Formula.raise, GraphFamilySyntax.agrees_rename] using
    member_compatible hAW p (paramsUp (paramsUp ρ)) c.castSucc.castSucc a.castSucc.castSucc
      g.castSucc.castSucc h.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hdetW haW hrW hW hhW

theorem compatible {n m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (p : Formula (n+3)) (ρ : Fin n → Fin m) (c a : Fin m)
    (hdet : Derives Γ (deterministic p ρ)) (ha : Derives Γ (ordinal a))
    (hr : Derives Γ (range p ρ c a)) : Derives Γ (GraphFamilySyntax.compatible c) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hA' := OrdinalRecursionContext.rename (OrdinalRecursionContext.rename hA Fin.castSucc) Fin.castSucc
  have hdet' : Derives Δ (deterministic p (paramsUp (paramsUp ρ))) := by
    simpa only [Formula.raise, deterministic_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hdet)
  have ha' : Derives Δ (ordinal a.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc ha)
  have hr' : Derives Δ (range p (paramsUp (paramsUp ρ)) c.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, range_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hr)
  apply Derives.impI
  apply Derives.impI
  exact pair_compatible (OrdinalRecursionContext.add (OrdinalRecursionContext.add hA' _) _) p (paramsUp (paramsUp ρ))
    c.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    (add (add hdet' _) _) (add (add ha' _) _) (add (add hr' _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
end PPAC.Migration.OrdinalRecursionFamilyCompatibility
