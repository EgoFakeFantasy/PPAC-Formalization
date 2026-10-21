import PPAC.Migration.TaggedRowExistence

/-! 实际带标签行的非空性、标签唯一性及相交行相等。 -/
namespace PPAC.Migration.TaggedRowLogic
open Source SourceAlgebra SourceLogic PairSyntax TaggedRowSyntax

theorem subst_tag {m} {Γ : Context m} (r x y : Fin m)
    (he : Derives Γ (.equal x y)) (hr : Derives Γ (row r x)) : Derives Γ (row r y) := by
  have hi : Derives Γ ((row r.castSucc (Fin.last m)).instantiate x) := by
    simpa only [Formula.instantiate, row_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hr
  have hx := Derives.eqSubst (row r.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, row_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hx

theorem entry_tags_equal {m} {Γ : Context m} (x y p : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hx : Derives Γ (entry x p)) (hy : Derives Γ (entry y p)) : Derives Γ (.equal x y) := by
  let U := (Formula.mem (Fin.last m) x.castSucc).conj (ordered p.castSucc x.castSucc (Fin.last m))
  let Γu := Context.add U (Context.image Formula.raise Γ)
  change Derives Γ (.ex U) at hx
  apply Derives.exE (p := U) hx
  have heU : Derives Γu (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he U
  have hyU : Derives Γu (entry y.castSucc p.castSucc) := by
    simpa only [Formula.raise, entry_rename] using under hy U
  have hU : Derives Γu U := .hyp (Or.inl rfl)
  let V := (Formula.mem (Fin.last (m+1)) y.castSucc.castSucc).conj
    (ordered p.castSucc.castSucc y.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add V (Context.image Formula.raise Γu)
  change Derives Γu (.ex V) at hyU
  apply Derives.exE (p := V) hyU
  have heV : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under heU V
  have hoU : Derives Ξ (ordered p.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [Formula.raise, ordered_rename] using under (.conjR hU) V
  have hV : Derives Ξ V := .hyp (Or.inl rfl)
  exact .conjL (OrderedPairLogic.injective p.castSucc.castSucc p.castSucc.castSucc
    x.castSucc.castSucc (Fin.last m).castSucc y.castSucc.castSucc (Fin.last (m+1)) heV hoU (.conjR hV) (.eqRefl _))

theorem intersecting_rows_equal {m} {Γ : Context m} (r s x y p : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hr : Derives Γ (row r x)) (hs : Derives Γ (row s y))
    (hp : Derives Γ (.mem p r)) (hq : Derives Γ (.mem p s)) : Derives Γ (.equal r s) := by
  have hx := Derives.impE (.conjL (row_at r x p hr)) hp
  have hy := Derives.impE (.conjL (row_at s y p hs)) hq
  have hxy := entry_tags_equal x y p he hx hy
  exact TaggedRowExistence.unique r s y he (subst_tag r x y hxy hr) hs

theorem nonempty {m} {Γ : Context m} (r x : Fin m)
    (hp : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (hr : Derives Γ (row r x)) (hx : Derives Γ (MinimalPredicates.inhabited x)) : Derives Γ (MinimalPredicates.inhabited r) := by
  let Y := Formula.mem (Fin.last m) x.castSucc
  let Γy := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hx
  apply Derives.exE (p := Y) hx
  have hpY : Derives Γy (Source.SetLanguage.pairing.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hp Y
  have hrY : Derives Γy (row r.castSucc x.castSucc) := by
    simpa only [Formula.raise, row_rename] using under hr Y
  have hY : Derives Γy Y := .hyp (Or.inl rfl)
  have ho := OrderedPairExistence.exists_pair x.castSucc (Fin.last m) hpY
  let P := ordered (Fin.last (m+1)) x.castSucc.castSucc (Fin.last m).castSucc
  let Ξ := Context.add P (Context.image Formula.raise Γy)
  change Derives Γy (.ex P) at ho
  apply Derives.exE (p := P) ho
  have hrP : Derives Ξ (row r.castSucc.castSucc x.castSucc.castSucc) := by
    simpa only [Formula.raise, row_rename] using under hrY P
  have hyP : Derives Ξ (.mem (Fin.last m).castSucc x.castSucc.castSucc) := under hY P
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hi := intro_entry x.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc hyP hP
  have hm := Derives.impE (.conjR (row_at r.castSucc.castSucc x.castSucc.castSucc (Fin.last (m+1)) hrP)) hi
  have hout : Derives Ξ (MinimalPredicates.inhabited r.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    simpa only [Formula.instantiate, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hm
  simpa only [Formula.raise, MinimalPredicates.inhabited_rename] using hout
end PPAC.Migration.TaggedRowLogic
