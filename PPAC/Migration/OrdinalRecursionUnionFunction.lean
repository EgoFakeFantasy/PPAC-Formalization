import PPAC.Migration.OrdinalRecursionFamilyCompatibility
import PPAC.Migration.GraphFamilyRestriction

/-! 精确后继图族的实际并在目标序数a上是完整原函数图；不先假定其定义域。 -/
namespace PPAC.Migration.OrdinalRecursionUnionFunction
open Source SourceAlgebra SourceLogic GraphSyntax GraphLogic RestrictionSyntax InsertSyntax OrdinalSyntax OrdinalRecursionSyntax
open OrdinalRecursionFamilySyntax OrdinalRecursionFamilyMembers
open ReplacementPredicates (paramsUp)

theorem member_entry {n m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (p : Formula (n+3)) (ρ : Fin n → Fin m) (c a h z : Fin m)
    (ha : Derives Γ (ordinal a)) (hr : Derives Γ (range p ρ c a))
    (hh : Derives Γ (.mem h c)) (hz : Derives Γ (.mem z h)) : Derives Γ (entryOn a z) := by
  let W := witnesses p ρ a h
  let Ξ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate p ρ c a h _ hr hh
  have hAW := OrdinalRecursionContext.under_two hA W
  have haW : Derives Ξ (ordinal a.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using OrderedPairElimination.under_two ha W
  have hzW : Derives Ξ (.mem z.castSucc.castSucc h.castSucc.castSucc) := OrderedPairElimination.under_two hz W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  have hs := Derives.conjR (domain_facts hAW p (paramsUp (paramsUp ρ)) a.castSucc.castSucc h.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) haW hW)
  have he := Derives.impE (entries_at h.castSucc.castSucc (Fin.last (m+1)) z.castSucc.castSucc
    (.conjL (.conjL (.conjR (.conjR hW))))) hzW
  simpa only [Formula.raise, entryOn_rename] using RestrictionAlgebra.entry_subset_domain
    (Fin.last (m+1)) a.castSucc.castSucc z.castSucc.castSucc hs he

theorem entries_on {n m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (p : Formula (n+3)) (ρ : Fin n → Fin m) (g c a : Fin m)
    (ha : Derives Γ (ordinal a)) (hr : Derives Γ (range p ρ c a))
    (hu : Derives Γ (unionOf g c)) : Derives Γ (entriesOn g a) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hA' := OrdinalRecursionContext.rename hA Fin.castSucc
  have ha' : Derives Δ (ordinal a.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using Derives.rename Fin.castSucc ha
  have hr' : Derives Δ (range p (paramsUp ρ) c.castSucc a.castSucc) := by
    simpa only [Formula.raise, range_rename] using Derives.rename Fin.castSucc hr
  have hu' : Derives Δ (unionOf g.castSucc c.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using Derives.rename Fin.castSucc hu
  apply Derives.impI
  let M := Formula.mem (Fin.last m) g.castSucc
  let Γz := Context.add M Δ
  have hz : Derives Γz M := .hyp (Or.inl rfl)
  have hex := Derives.impE (.conjL (add (union_at g.castSucc c.castSucc (Fin.last m) hu') M)) hz
  let H := (Formula.mem (Fin.last (m+1)) c.castSucc.castSucc).conj (.mem (Fin.last m).castSucc (Fin.last (m+1)))
  let Ξ := Context.add H (Context.image Formula.raise Γz)
  change Derives Γz (.ex H) at hex
  apply Derives.exE (p := H) hex
  have hAH := OrdinalRecursionContext.under (OrdinalRecursionContext.add hA' M) H
  have haH : Derives Ξ (ordinal a.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under (add ha' M) H
  have hrH : Derives Ξ (range p (paramsUp (paramsUp ρ)) c.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, range_rename] using under (add hr' M) H
  have hH : Derives Ξ H := .hyp (Or.inl rfl)
  simpa only [Formula.raise, entryOn_rename] using member_entry hAH p (paramsUp (paramsUp ρ)) c.castSucc.castSucc a.castSucc.castSucc
    (Fin.last (m+1)) (Fin.last m).castSucc haH hrH (.conjL hH) (.conjR hH)

theorem covered_input {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (g c a x : Fin m)
    (hu : Derives Γ (unionOf g c)) (hc : Derives Γ (coverage p ρ c a)) (hx : Derives Γ (.mem x a)) :
    Derives Γ (hasEdge g x) := by
  have hex := Derives.impE (coverage_at p ρ c a x hc) hx
  let H := (Formula.mem (Fin.last m) c.castSucc).conj
    (OrdinalRecursionSuccessorSyntax.successorGraph p (paramsUp ρ) x.castSucc (Fin.last m))
  let Γh := Context.add H (Context.image Formula.raise Γ)
  change Derives Γ (.ex H) at hex
  apply Derives.exE (p := H) hex
  have huH : Derives Γh (unionOf g.castSucc c.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using under hu H
  have hH : Derives Γh H := .hyp (Or.inl rfl)
  let S := (OmegaSyntax.successor (Fin.last (m+1)) x.castSucc.castSucc).conj
    (recursor p (paramsUp (paramsUp ρ)) (Fin.last m).castSucc (Fin.last (m+1)))
  let Ξ := Context.add S (Context.image Formula.raise Γh)
  have hs : Derives Γh (.ex S) := .conjR hH
  apply Derives.exE (p := S) hs
  have huS : Derives Ξ (unionOf g.castSucc.castSucc c.castSucc.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using under huH S
  have hmS : Derives Ξ (.mem (Fin.last m).castSucc c.castSucc.castSucc) := under (.conjL hH) S
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hxS := InsertLogic.new_member (Fin.last (m+1)) x.castSucc.castSucc x.castSucc.castSucc (.conjL hS)
  have hOut := GraphProperties.output_exists (Fin.last m).castSucc (Fin.last (m+1)) x.castSucc.castSucc
    (.conjL (.conjR hS)) hxS
  simpa only [Formula.raise, hasEdge_rename] using GraphFamilyRestriction.input_into_union
    g.castSucc.castSucc c.castSucc.castSucc (Fin.last m).castSucc x.castSucc.castSucc huS hmS hOut

theorem total_on {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (g c a : Fin m)
    (hu : Derives Γ (unionOf g c)) (hc : Derives Γ (coverage p ρ c a))
    (hcomp : Derives Γ (GraphFamilySyntax.compatible c)) : Derives Γ (totalOn g a) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hu' : Derives Δ (unionOf g.castSucc c.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using Derives.rename Fin.castSucc hu
  have hc' : Derives Δ (coverage p (paramsUp ρ) c.castSucc a.castSucc) := by
    simpa only [Formula.raise, coverage_rename] using Derives.rename Fin.castSucc hc
  have hcomp' : Derives Δ (GraphFamilySyntax.compatible c.castSucc) := by
    simpa only [Formula.raise, GraphFamilySyntax.compatible_rename] using Derives.rename Fin.castSucc hcomp
  apply Derives.impI
  let M := Formula.mem (Fin.last m) a.castSucc
  have hin := covered_input p (paramsUp ρ) g.castSucc c.castSucc a.castSucc (Fin.last m) (add hu' M) (add hc' M) (.hyp (Or.inl rfl))
  exact GraphFamilyFunction.value_exists_from_edge g.castSucc c.castSucc (Fin.last m) (add hu' M) (add hcomp' M) hin

theorem function_on {n m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (p : Formula (n+3)) (ρ : Fin n → Fin m) (g c a : Fin m)
    (ha : Derives Γ (ordinal a)) (hF : Derives Γ (family p ρ c a))
    (hu : Derives Γ (unionOf g c)) (hcomp : Derives Γ (GraphFamilySyntax.compatible c)) : Derives Γ (functionOn g a) :=
  .conjI (entries_on hA p ρ g c a ha (.conjL hF) hu) (total_on p ρ g c a hu (.conjR hF) hcomp)
end PPAC.Migration.OrdinalRecursionUnionFunction
