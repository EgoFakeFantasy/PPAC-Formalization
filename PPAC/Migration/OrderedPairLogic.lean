import PPAC.Migration.OrderedPairWitnesses

/-! 消去全部Kuratowski见证，给出原对象有序对关系的完整刻画。 -/
namespace PPAC.Migration.OrderedPairLogic
open Source SourceAlgebra SourceLogic PairSyntax OrderedPairElimination OrderedPairWitnesses

theorem characterization {m} {Γ : Context m} (p q x y a b : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hp : Derives Γ (ordered p x y)) (hq : Derives Γ (ordered q a b)) :
    Derives Γ ((Formula.equal p q).iff ((Formula.equal x a).conj (.equal y b))) := by
  let R := (Formula.equal p q).iff ((Formula.equal x a).conj (.equal y b))
  let Bp := witnesses p x y
  let Γp := Context.add Bp (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate p x y R hp
  have heP : Derives Γp (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under_two he Bp
  have hqP : Derives Γp (ordered q.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc) := by
    simpa only [Formula.raise, ordered_rename] using under_two hq Bp
  have hpP : Derives Γp Bp := .hyp (Or.inl rfl)
  let Bq := witnesses q.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc
  let Γq := Context.add Bq (Context.image Formula.raise (Context.image Formula.raise Γp))
  apply eliminate q.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc R.raise.raise hqP
  have heQ : Derives Γq (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under_two heP Bq
  have hpQ : Derives Γq (bundle p.castSucc.castSucc.castSucc.castSucc
      x.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc) := by
    simpa only [Formula.raise, Bp, witnesses, bundle_rename] using under_two hpP Bq
  have hqQ : Derives Γq Bq := .hyp (Or.inl rfl)
  have hresult := characterization_bundle p.castSucc.castSucc.castSucc.castSucc
    q.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc
    y.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc
    (Fin.last (m+2)).castSucc (Fin.last (m+3)) heQ hpQ hqQ
  simpa only [R, Formula.raise, Formula.iff, Formula.rename] using hresult

theorem unique {m} {Γ : Context m} (p q x y : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hp : Derives Γ (ordered p x y)) (hq : Derives Γ (ordered q x y)) : Derives Γ (.equal p q) :=
  .impE (.conjR (characterization p q x y x y he hp hq)) (.conjI (.eqRefl x) (.eqRefl y))

theorem injective {m} {Γ : Context m} (p q x y a b : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hp : Derives Γ (ordered p x y)) (hq : Derives Γ (ordered q a b)) (hpq : Derives Γ (.equal p q)) :
    Derives Γ ((Formula.equal x a).conj (.equal y b)) :=
  .impE (.conjL (characterization p q x y a b he hp hq)) hpq
end PPAC.Migration.OrderedPairLogic
