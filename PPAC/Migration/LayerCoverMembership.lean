import PPAC.Migration.LayerCoverInduction

/-! 实际层包含提升为实际后继层成员，全内部集合覆盖不只停在子集形式。 -/
namespace PPAC.Migration.LayerCoverMembership
open Source SourceAlgebra SourceLogic RestrictionSyntax OrdinalSyntax HierarchyLayerSyntax LayerCoverSyntax

theorem subset_to_member {m} {Γ : Context m} (x a v : Fin m)
    (hp : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (hu : Derives Γ (Source.SetLanguage.union.rename Fin.elim0))
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hEx : Derives Γ (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0))
    (hSucc : Derives Γ (ObjectHierarchyAlgebra.successorSentence.rename Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hl : Derives Γ (layer a v)) (hz : Derives Γ (subset x v)) :
    Derives Γ (memberCover x) := by
  have hs := InsertExistence.exists_insert a a hp hu
  let S := OmegaSyntax.successor (Fin.last m) a.castSucc
  let Γs := Context.add S (Context.image Formula.raise Γ)
  change Derives Γ (.ex S) at hs
  apply Derives.exE (p := S) hs
  have hfS : Derives Γs (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hf S
  have hExS : Derives Γs (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hEx S
  have hSuccS : Derives Γs (ObjectHierarchyAlgebra.successorSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hSucc S
  have haS : Derives Γs (ordinal a.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under ha S
  have hlS : Derives Γs (layer a.castSucc v.castSucc) := by
    simpa only [Formula.raise, layer_rename] using under hl S
  have hzS : Derives Γs (subset x.castSucc v.castSucc) := by
    simpa only [Formula.raise, subset_rename] using under hz S
  have hS : Derives Γs S := .hyp (Or.inl rfl)
  have hoS := OrdinalSuccessor.ordinal (Fin.last m) a.castSucc hfS hS haS
  have hv := HierarchyClosedInstances.existence (Fin.last m) hExS hoS
  let V := layer (Fin.last m).castSucc (Fin.last (m+1))
  let Ξ := Context.add V (Context.image Formula.raise Γs)
  change Derives Γs (.ex V) at hv
  apply Derives.exE (p := V) hv
  have hSuccV : Derives Ξ (ObjectHierarchyAlgebra.successorSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hSuccS V
  have haV : Derives Ξ (ordinal a.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under haS V
  have hlV : Derives Ξ (layer a.castSucc.castSucc v.castSucc.castSucc) := by
    simpa only [Formula.raise, layer_rename] using under hlS V
  have hzV : Derives Ξ (subset x.castSucc.castSucc v.castSucc.castSucc) := by
    simpa only [Formula.raise, subset_rename] using under hzS V
  have hsV : Derives Ξ (OmegaSyntax.successor (Fin.last m).castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, S, OmegaSyntax.successor_rename] using under hS V
  have hoV : Derives Ξ (ordinal (Fin.last m).castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under hoS V
  have hV : Derives Ξ V := .hyp (Or.inl rfl)
  have hpow := HierarchyClosedInstances.successor a.castSucc.castSucc (Fin.last m).castSucc v.castSucc.castSucc (Fin.last (m+1)) hSuccV haV hsV hlV hV
  have hx := Derives.impE (.conjR (PowerSetSyntax.power_at (Fin.last (m+1)) v.castSucc.castSucc x.castSucc.castSucc hpow)) hzV
  simpa only [Formula.raise, memberCover_rename] using intro_memberCover x.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hoV hV hx

theorem from_cover {m} {Γ : Context m} (x : Fin m)
    (hp : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (hu : Derives Γ (Source.SetLanguage.union.rename Fin.elim0))
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hEx : Derives Γ (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0))
    (hSucc : Derives Γ (ObjectHierarchyAlgebra.successorSentence.rename Fin.elim0))
    (hx : Derives Γ (cover x)) : Derives Γ (memberCover x) := by
  let A := atIndex x.castSucc (Fin.last m)
  let Γa := Context.add A (Context.image Formula.raise Γ)
  change Derives Γ (.ex A) at hx
  apply Derives.exE (p := A) hx
  have hpA : Derives Γa (Source.SetLanguage.pairing.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hp A
  have huA : Derives Γa (Source.SetLanguage.union.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hu A
  have hfA : Derives Γa (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hf A
  have hExA : Derives Γa (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hEx A
  have hSuccA : Derives Γa (ObjectHierarchyAlgebra.successorSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hSucc A
  have hA : Derives Γa A := .hyp (Or.inl rfl)
  have hc := Derives.conjR hA
  let V := (layer (Fin.last m).castSucc (Fin.last (m+1))).conj (subset x.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add V (Context.image Formula.raise Γa)
  change Derives Γa (.ex V) at hc
  apply Derives.exE (p := V) hc
  have hpV : Derives Ξ (Source.SetLanguage.pairing.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hpA V
  have huV : Derives Ξ (Source.SetLanguage.union.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under huA V
  have hfV : Derives Ξ (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hfA V
  have hExV : Derives Ξ (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hExA V
  have hSuccV : Derives Ξ (ObjectHierarchyAlgebra.successorSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hSuccA V
  have hoV : Derives Ξ (ordinal (Fin.last m).castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under (.conjL hA) V
  have hV : Derives Ξ V := .hyp (Or.inl rfl)
  simpa only [Formula.raise, memberCover_rename] using subset_to_member x.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    hpV huV hfV hExV hSuccV hoV (.conjL hV) (.conjR hV)
end PPAC.Migration.LayerCoverMembership
