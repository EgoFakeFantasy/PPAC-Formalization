import PPAC.Migration.UnionUpperBounds

/-! 任意内部原序数集合的实际并仍为原序数；不假定族外部可数或非空。 -/
namespace PPAC.Migration.OrdinalUnion
open Source SourceAlgebra SourceLogic RestrictionSyntax InsertSyntax OrdinalSyntax OrdinalFamilySyntax

theorem member_ordinal {m} {Γ : Context m} (u c x : Fin m)
    (hu : Derives Γ (unionOf u c)) (hc : Derives Γ (ordinals c)) (hx : Derives Γ (.mem x u)) :
    Derives Γ (ordinal x) := by
  have hex := Derives.impE (.conjL (union_at u c x hu)) hx
  let W := (Formula.mem (Fin.last m) c.castSucc).conj (.mem x.castSucc (Fin.last m))
  let Ξ := Context.add W (Context.image Formula.raise Γ)
  change Derives Γ (.ex W) at hex
  apply Derives.exE (p := W) hex
  have hc' : Derives Ξ (ordinals c.castSucc) := by
    simpa only [Formula.raise, ordinals_rename] using under hc W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  have ha := Derives.impE (ordinals_at c.castSucc (Fin.last m) hc') (.conjL hW)
  simpa only [Formula.raise, ordinal_rename] using OrdinalRestriction.member (Fin.last m) x.castSucc ha (.conjR hW)

theorem members {m} {Γ : Context m} (u c : Fin m)
    (hu : Derives Γ (unionOf u c)) (hc : Derives Γ (ordinals c)) : Derives Γ (ordinals u) := by
  apply Derives.allI
  have hu' : Derives (Context.image Formula.raise Γ) (unionOf u.castSucc c.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using Derives.rename Fin.castSucc hu
  have hc' : Derives (Context.image Formula.raise Γ) (ordinals c.castSucc) := by
    simpa only [Formula.raise, ordinals_rename] using Derives.rename Fin.castSucc hc
  apply Derives.impI
  exact member_ordinal u.castSucc c.castSucc (Fin.last m) (add hu' _) (add hc' _) (.hyp (Or.inl rfl))

theorem member_members {m} {Γ : Context m} (u c x y : Fin m)
    (hu : Derives Γ (unionOf u c)) (hc : Derives Γ (ordinals c))
    (hx : Derives Γ (.mem x u)) (hy : Derives Γ (.mem y x)) : Derives Γ (.mem y u) := by
  have hex := Derives.impE (.conjL (union_at u c x hu)) hx
  let W := (Formula.mem (Fin.last m) c.castSucc).conj (.mem x.castSucc (Fin.last m))
  let Ξ := Context.add W (Context.image Formula.raise Γ)
  change Derives Γ (.ex W) at hex
  apply Derives.exE (p := W) hex
  have hu' : Derives Ξ (unionOf u.castSucc c.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using under hu W
  have hc' : Derives Ξ (ordinals c.castSucc) := by
    simpa only [Formula.raise, ordinals_rename] using under hc W
  have hy' : Derives Ξ (.mem y.castSucc x.castSucc) := under hy W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  have ha := Derives.impE (ordinals_at c.castSucc (Fin.last m) hc') (.conjL hW)
  have hya := Derives.impE (Derives.impE (transitiveSet_at (Fin.last m) x.castSucc y.castSucc (.conjL ha)) (.conjR hW)) hy'
  exact .impE (.conjR (union_at u.castSucc c.castSucc y.castSucc hu'))
    (InsertLogic.fiber_intro c.castSucc y.castSucc (Fin.last m) (.conjL hW) hya)

theorem transitive {m} {Γ : Context m} (u c : Fin m)
    (hu : Derives Γ (unionOf u c)) (hc : Derives Γ (ordinals c)) : Derives Γ (transitiveSet u) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hu' : Derives Δ (unionOf u.castSucc.castSucc c.castSucc.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hu)
  have hc' : Derives Δ (ordinals c.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinals_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hc)
  apply Derives.impI
  apply Derives.impI
  exact member_members u.castSucc.castSucc c.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    (add (add hu' _) _) (add (add hc' _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem ordinal {m} {Γ : Context m} (u c : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hs : Derives Γ ((Source.SetLanguage.separation OrdinalDifference.outsideMatrix).rename Fin.elim0))
    (hu : Derives Γ (unionOf u c)) (hc : Derives Γ (ordinals c)) : Derives Γ (OrdinalSyntax.ordinal u) :=
  OrdinalFamilyOrder.ordinal_of_transitive u he hf hs (transitive u c hu hc) (members u c hu hc)

theorem exists_union {m} {Γ : Context m} (c : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hs : Derives Γ ((Source.SetLanguage.separation OrdinalDifference.outsideMatrix).rename Fin.elim0))
    (hu : Derives Γ (Source.SetLanguage.union.rename Fin.elim0))
    (hc : Derives Γ (ordinals c)) : Derives Γ (ordinalUnionExists c) := by
  have hex := union_instance c hu
  let U := unionOf (Fin.last m) c.castSucc
  let Ξ := Context.add U (Context.image Formula.raise Γ)
  change Derives Γ (.ex U) at hex
  apply Derives.exE (p := U) hex
  have he' : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he U
  have hf' : Derives Ξ (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hf U
  have hs' : Derives Ξ ((Source.SetLanguage.separation OrdinalDifference.outsideMatrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hs U
  have hc' : Derives Ξ (ordinals c.castSucc) := by
    simpa only [Formula.raise, ordinals_rename] using under hc U
  have hU : Derives Ξ U := .hyp (Or.inl rfl)
  have ho := ordinal (Fin.last m) c.castSucc he' hf' hs' hU hc'
  have hl := UnionUpperBounds.least (Fin.last m) c.castSucc hU
  have hr : Derives Ξ (ordinalUnionExists c.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, Formula.rename, unionOf_rename, ordinal_rename, leastUpper_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hU (Derives.conjI ho hl)
  simpa only [Formula.raise, ordinalUnionExists_rename] using hr
end PPAC.Migration.OrdinalUnion
