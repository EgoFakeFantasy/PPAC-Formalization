import PPAC.Migration.InsertExistence
import PPAC.Migration.GraphProperties

/-! 把一个Kuratowski码插入图后的全部边刻画，不假设原图有限。 -/
namespace PPAC.Migration.GraphInsertEdges
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax GraphLogic InsertSyntax

theorem old_edge {m} {Γ : Context m} (g f p a b : Fin m)
    (hi : Derives Γ (insert g f p)) (he : Derives Γ (edge f a b)) : Derives Γ (edge g a b) := by
  let Q := (Formula.mem (Fin.last m) f.castSucc).conj (ordered (Fin.last m) a.castSucc b.castSucc)
  let Γq := Context.add Q (Context.image Formula.raise Γ)
  apply edge_elim f a b _ he
  have hiQ : Derives Γq (insert g.castSucc f.castSucc p.castSucc) := by
    simpa only [Formula.raise, insert_rename] using under hi Q
  have hQ : Derives Γq Q := .hyp (Or.inl rfl)
  have hr := edge_intro g.castSucc a.castSucc b.castSucc (Fin.last m)
    (InsertLogic.old_member _ _ _ _ hiQ (.conjL hQ)) (.conjR hQ)
  simpa only [Formula.raise, edge_rename] using hr

theorem new_edge {m} {Γ : Context m} (g f p x y : Fin m)
    (hi : Derives Γ (insert g f p)) (hp : Derives Γ (ordered p x y)) : Derives Γ (edge g x y) :=
  edge_intro g x y p (InsertLogic.new_member g f p hi) hp

theorem edge_cases {m} {Γ : Context m} (g f p x y a b : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hi : Derives Γ (insert g f p)) (hp : Derives Γ (ordered p x y)) (hab : Derives Γ (edge g a b)) :
    Derives Γ ((edge f a b).disj ((Formula.equal a x).conj (.equal b y))) := by
  let Q := (Formula.mem (Fin.last m) g.castSucc).conj (ordered (Fin.last m) a.castSucc b.castSucc)
  let Γq := Context.add Q (Context.image Formula.raise Γ)
  apply edge_elim g a b _ hab
  have heQ : Derives Γq (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he Q
  have hiQ : Derives Γq (insert g.castSucc f.castSucc p.castSucc) := by
    simpa only [Formula.raise, insert_rename] using under hi Q
  have hpQ : Derives Γq (ordered p.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, ordered_rename] using under hp Q
  have hQ : Derives Γq Q := .hyp (Or.inl rfl)
  have hc := InsertLogic.member_cases g.castSucc f.castSucc p.castSucc (Fin.last m) hiQ (.conjL hQ)
  apply Derives.disjE hc
  · have hr := edge_intro f.castSucc a.castSucc b.castSucc (Fin.last m) (.hyp (Or.inl rfl)) (add (.conjR hQ) _)
    simpa only [Formula.raise, Formula.rename, edge_rename] using Derives.disjL hr
  · have hr := OrderedPairLogic.injective (Fin.last m) p.castSucc a.castSucc b.castSucc x.castSucc y.castSucc
      (add heQ _) (add (.conjR hQ) _) (add hpQ _) (.hyp (Or.inl rfl))
    simpa only [Formula.raise, Formula.rename, edge_rename] using Derives.disjR hr

theorem edge_iff {m} {Γ : Context m} (g f p x y a b : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hi : Derives Γ (insert g f p)) (hp : Derives Γ (ordered p x y)) :
    Derives Γ ((edge g a b).iff ((edge f a b).disj ((Formula.equal a x).conj (.equal b y)))) := by
  apply Derives.conjI
  · apply Derives.impI
    exact edge_cases g f p x y a b (add he _) (add hi _) (add hp _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    apply Derives.disjE (Derives.hyp (Or.inl rfl))
    · exact old_edge g f p a b (add (add hi _) _) (.hyp (Or.inl rfl))
    · let E := (Formula.equal a x).conj (.equal b y)
      have hE : Derives (Context.add E (Context.add ((edge f a b).disj E) Γ)) E := .hyp (Or.inl rfl)
      have hpa := ordered_subst_left p x y a (eq_symm (.conjL hE)) (add (add hp _) E)
      have hpab := ordered_subst_right p a y b (eq_symm (.conjR hE)) hpa
      exact edge_intro g a b p (InsertLogic.new_member g f p (add (add hi _) E)) hpab
end PPAC.Migration.GraphInsertEdges
