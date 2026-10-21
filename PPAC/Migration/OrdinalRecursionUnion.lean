import PPAC.Migration.OrdinalRecursionUnionFunction

/-! 实际后继图族并保留每个历史方程，取得整个目标序数上的实际递归图。 -/
namespace PPAC.Migration.OrdinalRecursionUnion
open Source SourceAlgebra SourceLogic GraphSyntax RestrictionSyntax InsertSyntax OrdinalSyntax OrdinalRecursionSyntax
open OrdinalRecursionDeterminism OrdinalRecursionFamilySyntax OrdinalRecursionFamilyMembers
open ReplacementPredicates (paramsUp)

theorem member_history {n m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (p : Formula (n+3)) (ρ : Fin n → Fin m) (g c a h x y : Fin m)
    (ha : Derives Γ (ordinal a)) (hr : Derives Γ (range p ρ c a))
    (hu : Derives Γ (unionOf g c)) (hcomp : Derives Γ (GraphFamilySyntax.compatible c))
    (hm : Derives Γ (.mem h c)) (hxy : Derives Γ (edge h x y)) : Derives Γ (history p ρ g x y) := by
  let W := witnesses p ρ a h
  let Ξ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate p ρ c a h _ hr hm
  have hAW := OrdinalRecursionContext.under_two hA W
  have haW : Derives Ξ (ordinal a.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using OrderedPairElimination.under_two ha W
  have huW : Derives Ξ (unionOf g.castSucc.castSucc c.castSucc.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using OrderedPairElimination.under_two hu W
  have hcompW : Derives Ξ (GraphFamilySyntax.compatible c.castSucc.castSucc) := by
    simpa only [Formula.raise, GraphFamilySyntax.compatible_rename] using OrderedPairElimination.under_two hcomp W
  have hmW : Derives Ξ (.mem h.castSucc.castSucc c.castSucc.castSucc) := OrderedPairElimination.under_two hm W
  have hxyW : Derives Ξ (edge h.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc) := by
    simpa only [Formula.raise, edge_rename] using OrderedPairElimination.under_two hxy W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  have hOrd := Derives.conjL (domain_facts hAW p (paramsUp (paramsUp ρ)) a.castSucc.castSucc h.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) haW hW)
  have hRec : Derives Ξ (recursor p (paramsUp (paramsUp ρ)) h.castSucc.castSucc (Fin.last (m+1))) := .conjR (.conjR hW)
  have hxs := GraphProperties.domain_of_edge h.castSucc.castSucc (Fin.last (m+1)) x.castSucc.castSucc y.castSucc.castSucc
    hAW.extensionality (.conjL hRec) hxyW
  have hhist := Derives.impE (Derives.impE (equations_at p (paramsUp (paramsUp ρ)) h.castSucc.castSucc
    (Fin.last (m+1)) x.castSucc.castSucc y.castSucc.castSucc (.conjR hRec)) hxs) hxyW
  have hrestrict := GraphFamilyRestriction.member_restriction g.castSucc.castSucc c.castSucc.castSucc h.castSucc.castSucc
    (Fin.last (m+1)) hAW.extensionality huW hcompW hmW (.conjL hRec)
  have hxsub := OrdinalTransitivity.subset_of_member (Fin.last (m+1)) x.castSucc.castSucc (.conjL hOrd) hxs
  simpa only [Formula.raise, history_rename] using OrdinalRecursionExtensionAlgebra.lift_history p (paramsUp (paramsUp ρ))
    g.castSucc.castSucc h.castSucc.castSucc (Fin.last (m+1)) x.castSucc.castSucc y.castSucc.castSucc hxsub hrestrict hhist

theorem point_history {n m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (p : Formula (n+3)) (ρ : Fin n → Fin m) (g c a x y : Fin m)
    (ha : Derives Γ (ordinal a)) (hr : Derives Γ (range p ρ c a))
    (hu : Derives Γ (unionOf g c)) (hcomp : Derives Γ (GraphFamilySyntax.compatible c))
    (hxy : Derives Γ (edge g x y)) : Derives Γ (history p ρ g x y) := by
  have hex := GraphFamilyEdges.edge_from_union g c x y hu hxy
  let H := (Formula.mem (Fin.last m) c.castSucc).conj (edge (Fin.last m) x.castSucc y.castSucc)
  let Ξ := Context.add H (Context.image Formula.raise Γ)
  change Derives Γ (.ex H) at hex
  apply Derives.exE (p := H) hex
  have hAH := OrdinalRecursionContext.under hA H
  have haH : Derives Ξ (ordinal a.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under ha H
  have hrH : Derives Ξ (range p (paramsUp ρ) c.castSucc a.castSucc) := by
    simpa only [Formula.raise, range_rename] using under hr H
  have huH : Derives Ξ (unionOf g.castSucc c.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using under hu H
  have hcH : Derives Ξ (GraphFamilySyntax.compatible c.castSucc) := by
    simpa only [Formula.raise, GraphFamilySyntax.compatible_rename] using under hcomp H
  have hH : Derives Ξ H := .hyp (Or.inl rfl)
  simpa only [Formula.raise, history_rename] using member_history hAH p (paramsUp ρ) g.castSucc c.castSucc a.castSucc
    (Fin.last m) x.castSucc y.castSucc haH hrH huH hcH (.conjL hH) (.conjR hH)

theorem equations {n m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (p : Formula (n+3)) (ρ : Fin n → Fin m) (g c a : Fin m)
    (ha : Derives Γ (ordinal a)) (hr : Derives Γ (range p ρ c a))
    (hu : Derives Γ (unionOf g c)) (hcomp : Derives Γ (GraphFamilySyntax.compatible c)) : Derives Γ (OrdinalRecursionSyntax.equations p ρ g a) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hA' := OrdinalRecursionContext.rename hA Fin.castSucc
  have ha' : Derives Δ (ordinal a.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using Derives.rename Fin.castSucc ha
  have hr' : Derives Δ (range p (paramsUp ρ) c.castSucc a.castSucc) := by
    simpa only [Formula.raise, range_rename] using Derives.rename Fin.castSucc hr
  have hu' : Derives Δ (unionOf g.castSucc c.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using Derives.rename Fin.castSucc hu
  have hcomp' : Derives Δ (GraphFamilySyntax.compatible c.castSucc) := by
    simpa only [Formula.raise, GraphFamilySyntax.compatible_rename] using Derives.rename Fin.castSucc hcomp
  apply Derives.impI
  let M := Formula.mem (Fin.last m) a.castSucc
  let Γx := Context.add M Δ
  apply Derives.allI
  let Γy := Context.image Formula.raise Γx
  have hAY := OrdinalRecursionContext.rename (OrdinalRecursionContext.add hA' M) Fin.castSucc
  have haY : Derives Γy (ordinal a.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using Derives.rename Fin.castSucc (add ha' M)
  have hrY : Derives Γy (range p (paramsUp (paramsUp ρ)) c.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, range_rename] using Derives.rename Fin.castSucc (add hr' M)
  have huY : Derives Γy (unionOf g.castSucc.castSucc c.castSucc.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using Derives.rename Fin.castSucc (add hu' M)
  have hcompY : Derives Γy (GraphFamilySyntax.compatible c.castSucc.castSucc) := by
    simpa only [Formula.raise, GraphFamilySyntax.compatible_rename] using Derives.rename Fin.castSucc (add hcomp' M)
  apply Derives.impI
  exact point_history (OrdinalRecursionContext.add hAY _) p (paramsUp (paramsUp ρ)) g.castSucc.castSucc
    c.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    (add haY _) (add hrY _) (add huY _) (add hcompY _) (.hyp (Or.inl rfl))

theorem recursor {n m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (p : Formula (n+3)) (ρ : Fin n → Fin m) (g c a : Fin m)
    (hdet : Derives Γ (deterministic p ρ)) (ha : Derives Γ (ordinal a))
    (hF : Derives Γ (family p ρ c a)) (hu : Derives Γ (unionOf g c)) : Derives Γ (OrdinalRecursionSyntax.recursor p ρ g a) := by
  have hcomp := OrdinalRecursionFamilyCompatibility.compatible hA p ρ c a hdet ha (.conjL hF)
  exact .conjI (OrdinalRecursionUnionFunction.function_on hA p ρ g c a ha hF hu hcomp)
    (equations hA p ρ g c a ha (.conjL hF) hu hcomp)

theorem exists_union {n m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (p : Formula (n+3)) (ρ : Fin n → Fin m) (c a : Fin m)
    (hdet : Derives Γ (deterministic p ρ)) (ha : Derives Γ (ordinal a))
    (hF : Derives Γ (family p ρ c a)) : Derives Γ (recursorExists p ρ a) := by
  have hex := union_instance c hA.union
  let G := unionOf (Fin.last m) c.castSucc
  let Ξ := Context.add G (Context.image Formula.raise Γ)
  change Derives Γ (.ex G) at hex
  apply Derives.exE (p := G) hex
  have hAG := OrdinalRecursionContext.under hA G
  have hdetG : Derives Ξ (deterministic p (paramsUp ρ)) := by
    simpa only [Formula.raise, deterministic_rename] using under hdet G
  have haG : Derives Ξ (ordinal a.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under ha G
  have hFG : Derives Ξ (family p (paramsUp ρ) c.castSucc a.castSucc) := by
    simpa only [Formula.raise, family_rename] using under hF G
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have hRec := recursor hAG p (paramsUp ρ) (Fin.last m) c.castSucc a.castSucc hdetG haG hFG hG
  have hout : Derives Ξ (recursorExists p (paramsUp ρ) a.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, recursor_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hRec
  simpa only [Formula.raise, recursorExists_rename] using hout
end PPAC.Migration.OrdinalRecursionUnion
