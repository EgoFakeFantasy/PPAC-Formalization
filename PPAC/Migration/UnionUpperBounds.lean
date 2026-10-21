import PPAC.Migration.OrdinalFamilyOrder

/-! 实际并集对任意内部集合族的最小包含上界性质；不要求族元素为序数。 -/
namespace PPAC.Migration.UnionUpperBounds
open Source SourceAlgebra SourceLogic RestrictionSyntax InsertSyntax OrdinalFamilySyntax

theorem upper_bound {m} {Γ : Context m} (u c : Fin m) (hu : Derives Γ (unionOf u c)) :
    Derives Γ (upperBound c u) := by
  apply Derives.allI
  have hu' : Derives (Context.image Formula.raise Γ) (unionOf u.castSucc c.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using Derives.rename Fin.castSucc hu
  apply Derives.impI
  exact TransitiveCoverLogic.subset_union u.castSucc c.castSucc (Fin.last m) (add hu' _) (.hyp (Or.inl rfl))

theorem least_member {m} {Γ : Context m} (u c b x : Fin m)
    (hu : Derives Γ (unionOf u c)) (hb : Derives Γ (upperBound c b)) (hx : Derives Γ (.mem x u)) :
    Derives Γ (.mem x b) := by
  have hex := Derives.impE (.conjL (union_at u c x hu)) hx
  let W := (Formula.mem (Fin.last m) c.castSucc).conj (.mem x.castSucc (Fin.last m))
  let Ξ := Context.add W (Context.image Formula.raise Γ)
  change Derives Γ (.ex W) at hex
  apply Derives.exE (p := W) hex
  have hb' : Derives Ξ (upperBound c.castSucc b.castSucc) := by
    simpa only [Formula.raise, upperBound_rename] using under hb W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  have hs := Derives.impE (upperBound_at c.castSucc b.castSucc (Fin.last m) hb') (.conjL hW)
  exact .impE (subset_at (Fin.last m) b.castSucc x.castSucc hs) (.conjR hW)

theorem least_at {m} {Γ : Context m} (u c b : Fin m)
    (hu : Derives Γ (unionOf u c)) (hb : Derives Γ (upperBound c b)) : Derives Γ (subset u b) := by
  apply Derives.allI
  have hu' : Derives (Context.image Formula.raise Γ) (unionOf u.castSucc c.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using Derives.rename Fin.castSucc hu
  have hb' : Derives (Context.image Formula.raise Γ) (upperBound c.castSucc b.castSucc) := by
    simpa only [Formula.raise, upperBound_rename] using Derives.rename Fin.castSucc hb
  apply Derives.impI
  exact least_member u.castSucc c.castSucc b.castSucc (Fin.last m) (add hu' _) (add hb' _) (.hyp (Or.inl rfl))

theorem least {m} {Γ : Context m} (u c : Fin m) (hu : Derives Γ (unionOf u c)) : Derives Γ (leastUpper u c) := by
  apply Derives.conjI (upper_bound u c hu)
  apply Derives.allI
  have hu' : Derives (Context.image Formula.raise Γ) (unionOf u.castSucc c.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using Derives.rename Fin.castSucc hu
  apply Derives.impI
  exact least_at u.castSucc c.castSucc (Fin.last m) (add hu' _) (.hyp (Or.inl rfl))

theorem unique {m} {Γ : Context m} (u v c : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hu : Derives Γ (leastUpper u c)) (hv : Derives Γ (leastUpper v c)) : Derives Γ (.equal u v) :=
  OmegaAlgebra.subset_antisymm u v he
    (.impE (leastUpper_at u c v hu) (.conjL hv)) (.impE (leastUpper_at v c u hv) (.conjL hu))
end PPAC.Migration.UnionUpperBounds
