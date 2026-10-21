import PPAC.Migration.TransitiveCoverSyntax

/-! 对取并封闭的实际集合族，其并集是传递集；只用原成员/量词推导。 -/
namespace PPAC.Migration.TransitiveCoverLogic
open Source SourceAlgebra SourceLogic InsertSyntax IterationRangeSyntax TransitiveCoverSyntax

theorem member_members {m} {Γ : Context m} (b c x y : Fin m)
    (hu : Derives Γ (unionOf b c)) (hc : Derives Γ (closedUnion c))
    (hx : Derives Γ (.mem x b)) (hy : Derives Γ (.mem y x)) : Derives Γ (.mem y b) := by
  have he := Derives.impE (.conjL (union_at b c x hu)) hx
  let R := (Formula.mem (Fin.last m) c.castSucc).conj (.mem x.castSucc (Fin.last m))
  let Γr := Context.add R (Context.image Formula.raise Γ)
  change Derives Γ (.ex R) at he
  apply Derives.exE (p := R) he
  have huR : Derives Γr (unionOf b.castSucc c.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using under hu R
  have hcR : Derives Γr (closedUnion c.castSucc) := by
    simpa only [Formula.raise, closedUnion_rename] using under hc R
  have hyR : Derives Γr (.mem y.castSucc x.castSucc) := under hy R
  have hR : Derives Γr R := .hyp (Or.inl rfl)
  have ht := Derives.impE (closed_at c.castSucc (Fin.last m) hcR) (.conjL hR)
  let T := (Formula.mem (Fin.last (m+1)) c.castSucc.castSucc).conj (unionOf (Fin.last (m+1)) (Fin.last m).castSucc)
  let Γt := Context.add T (Context.image Formula.raise Γr)
  change Derives Γr (.ex T) at ht
  apply Derives.exE (p := T) ht
  have huT : Derives Γt (unionOf b.castSucc.castSucc c.castSucc.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using under huR T
  have hyT : Derives Γt (.mem y.castSucc.castSucc x.castSucc.castSucc) := under hyR T
  have hRT : Derives Γt ((Formula.mem (Fin.last m).castSucc c.castSucc.castSucc).conj
      (.mem x.castSucc.castSucc (Fin.last m).castSucc)) := by
    simpa only [Formula.raise, R, Formula.rename] using under hR T
  have hT : Derives Γt T := .hyp (Or.inl rfl)
  have hyt := Derives.impE (.conjR (union_at (Fin.last (m+1)) (Fin.last m).castSucc y.castSucc.castSucc (.conjR hT)))
    (InsertLogic.fiber_intro (Fin.last m).castSucc y.castSucc.castSucc x.castSucc.castSucc (.conjR hRT) hyT)
  have hyb := Derives.impE (.conjR (union_at b.castSucc.castSucc c.castSucc.castSucc y.castSucc.castSucc huT))
    (InsertLogic.fiber_intro c.castSucc.castSucc y.castSucc.castSucc (Fin.last (m+1)) (.conjL hT) hyt)
  simpa only [Formula.raise, Formula.rename] using hyb

theorem transitive_union {m} {Γ : Context m} (b c : Fin m)
    (hu : Derives Γ (unionOf b c)) (hc : Derives Γ (closedUnion c)) : Derives Γ (OmegaStructureSyntax.transitive b) := by
  apply Derives.allI
  have hu' : Derives (Context.image Formula.raise Γ) (unionOf b.castSucc c.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using Derives.rename Fin.castSucc hu
  have hc' : Derives (Context.image Formula.raise Γ) (closedUnion c.castSucc) := by
    simpa only [Formula.raise, closedUnion_rename] using Derives.rename Fin.castSucc hc
  apply Derives.impI
  let M := Formula.mem (Fin.last m) b.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hx : Derives Δ M := .hyp (Or.inl rfl)
  apply Derives.allI
  have hu'' : Derives (Context.image Formula.raise Δ) (unionOf b.castSucc.castSucc c.castSucc.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using Derives.rename Fin.castSucc (add hu' M)
  have hc'' : Derives (Context.image Formula.raise Δ) (closedUnion c.castSucc.castSucc) := by
    simpa only [Formula.raise, closedUnion_rename] using Derives.rename Fin.castSucc (add hc' M)
  have hx' : Derives (Context.image Formula.raise Δ) (.mem (Fin.last m).castSucc b.castSucc.castSucc) := Derives.rename Fin.castSucc hx
  apply Derives.impI
  exact member_members b.castSucc.castSucc c.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    (add hu'' _) (add hc'' _) (add hx' _) (.hyp (Or.inl rfl))

theorem subset_union {m} {Γ : Context m} (b c a : Fin m)
    (hu : Derives Γ (unionOf b c)) (ha : Derives Γ (.mem a c)) : Derives Γ (RestrictionSyntax.subset a b) := by
  apply Derives.allI
  have hu' : Derives (Context.image Formula.raise Γ) (unionOf b.castSucc c.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using Derives.rename Fin.castSucc hu
  have ha' := Derives.rename Fin.castSucc ha
  apply Derives.impI
  exact .impE (.conjR (add (union_at b.castSucc c.castSucc (Fin.last m) hu') _))
    (InsertLogic.fiber_intro c.castSucc (Fin.last m) a.castSucc (add ha' _) (.hyp (Or.inl rfl)))

theorem from_union {m} {Γ : Context m} (b c a : Fin m)
    (hu : Derives Γ (unionOf b c)) (ha : Derives Γ (.mem a c)) (hc : Derives Γ (closedUnion c)) : Derives Γ (cover b a) :=
  .conjI (subset_union b c a hu ha) (transitive_union b c hu hc)
end PPAC.Migration.TransitiveCoverLogic
