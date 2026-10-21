import PPAC.Migration.OrdinalUnion

/-! 任意内部序数集合有实际严格序数上界；以实际并集的后继构造。 -/
namespace PPAC.Migration.OrdinalStrictBound
open Source SourceAlgebra SourceLogic OrdinalSyntax OrdinalFamilySyntax InsertSyntax

def strictUpper {m} (c b : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) c.castSucc).imp (.mem (Fin.last m) b.castSucc))

def boundExists {m} (c : Fin m) : Formula m := .ex
  ((ordinal (Fin.last m)).conj (strictUpper c.castSucc (Fin.last m)))

theorem strictUpper_rename {m k} (c b : Fin m) (ρ : Fin m → Fin k) :
    (strictUpper c b).rename ρ = strictUpper (ρ c) (ρ b) := by
  simp only [strictUpper, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem boundExists_rename {m k} (c : Fin m) (ρ : Fin m → Fin k) :
    (boundExists c).rename ρ = boundExists (ρ c) := by
  simp only [boundExists, Formula.rename, ordinal_rename, strictUpper_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem of_successor {m} {Γ : Context m} (s u c : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hs : Derives Γ ((Source.SetLanguage.separation OrdinalDifference.outsideMatrix).rename Fin.elim0))
    (hc : Derives Γ (ordinals c)) (ho : Derives Γ (ordinal u))
    (hb : Derives Γ (upperBound c u)) (hS : Derives Γ (OmegaSyntax.successor s u)) :
    Derives Γ (strictUpper c s) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have he' : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  have hf' : Derives Δ (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hf
  have hs' : Derives Δ ((Source.SetLanguage.separation OrdinalDifference.outsideMatrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hs
  have hc' : Derives Δ (ordinals c.castSucc) := by
    simpa only [Formula.raise, ordinals_rename] using Derives.rename Fin.castSucc hc
  have ho' : Derives Δ (ordinal u.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using Derives.rename Fin.castSucc ho
  have hb' : Derives Δ (upperBound c.castSucc u.castSucc) := by
    simpa only [Formula.raise, upperBound_rename] using Derives.rename Fin.castSucc hb
  have hS' : Derives Δ (OmegaSyntax.successor s.castSucc u.castSucc) := by
    simpa only [Formula.raise, OmegaSyntax.successor_rename] using Derives.rename Fin.castSucc hS
  apply Derives.impI
  let Ξ := Context.add (.mem (Fin.last m) c.castSucc) Δ
  have ha : Derives Ξ (ordinal (Fin.last m)) :=
    .impE (add (ordinals_at c.castSucc (Fin.last m) hc') _) (.hyp (Or.inl rfl))
  have hsub : Derives Ξ (RestrictionSyntax.subset (Fin.last m) u.castSucc) :=
    .impE (add (upperBound_at c.castSucc u.castSucc (Fin.last m) hb') _) (.hyp (Or.inl rfl))
  have hcmp := OrdinalInitialSegment.initial_segment u.castSucc (Fin.last m)
    (add he' _) (add hf' _) (add hs' _) (add ho' _) (.conjL ha) hsub
  apply Derives.disjE hcmp
  · exact mem_subst (eq_symm (.hyp (Or.inl rfl))) (InsertLogic.new_member s.castSucc u.castSucc u.castSucc (add (add hS' _) _))
  · exact InsertLogic.old_member s.castSucc u.castSucc u.castSucc (Fin.last m) (add (add hS' _) _) (.hyp (Or.inl rfl))

theorem exists_bound {m} {Γ : Context m} (c : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hs : Derives Γ ((Source.SetLanguage.separation OrdinalDifference.outsideMatrix).rename Fin.elim0))
    (hu : Derives Γ (Source.SetLanguage.union.rename Fin.elim0))
    (hp : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (hc : Derives Γ (ordinals c)) : Derives Γ (boundExists c) := by
  have hex := OrdinalUnion.exists_union c he hf hs hu hc
  let U := (unionOf (Fin.last m) c.castSucc).conj
    ((ordinal (Fin.last m)).conj (leastUpper (Fin.last m) c.castSucc))
  let Ξ := Context.add U (Context.image Formula.raise Γ)
  change Derives Γ (.ex U) at hex
  apply Derives.exE (p := U) hex
  have he' : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he U
  have hf' : Derives Ξ (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hf U
  have hs' : Derives Ξ ((Source.SetLanguage.separation OrdinalDifference.outsideMatrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hs U
  have hu' : Derives Ξ (Source.SetLanguage.union.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hu U
  have hp' : Derives Ξ (Source.SetLanguage.pairing.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hp U
  have hc' : Derives Ξ (ordinals c.castSucc) := by
    simpa only [Formula.raise, ordinals_rename] using under hc U
  have hU : Derives Ξ U := .hyp (Or.inl rfl)
  have ho : Derives Ξ (ordinal (Fin.last m)) := .conjL (.conjR hU)
  have hb : Derives Ξ (upperBound c.castSucc (Fin.last m)) := .conjL (.conjR (.conjR hU))
  have hsex := InsertExistence.exists_insert (Fin.last m) (Fin.last m) hp' hu'
  let S := OmegaSyntax.successor (Fin.last (m+1)) (Fin.last m).castSucc
  let Ψ := Context.add S (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex S) at hsex
  apply Derives.exE (p := S) hsex
  have heS : Derives Ψ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he' S
  have hfS : Derives Ψ (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hf' S
  have hsS : Derives Ψ ((Source.SetLanguage.separation OrdinalDifference.outsideMatrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hs' S
  have hcS : Derives Ψ (ordinals c.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinals_rename] using under hc' S
  have hoS : Derives Ψ (ordinal (Fin.last m).castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under ho S
  have hbS : Derives Ψ (upperBound c.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [Formula.raise, upperBound_rename] using under hb S
  have hS : Derives Ψ S := .hyp (Or.inl rfl)
  have hOrd := OrdinalSuccessor.ordinal (Fin.last (m+1)) (Fin.last m).castSucc hfS hS hoS
  have hBound := of_successor (Fin.last (m+1)) (Fin.last m).castSucc c.castSucc.castSucc heS hfS hsS hcS hoS hbS hS
  have hr : Derives Ψ (boundExists c.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    simpa only [Formula.instantiate, Formula.rename, ordinal_rename, strictUpper_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hOrd hBound
  simpa only [Formula.raise, boundExists_rename] using hr
end PPAC.Migration.OrdinalStrictBound
