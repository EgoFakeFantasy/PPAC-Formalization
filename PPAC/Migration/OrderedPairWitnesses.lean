import PPAC.Migration.OrderedPairElimination

/-! Kuratowski见证的唯一性和分量恢复，覆盖x=y的退化情况。 -/
namespace PPAC.Migration.OrderedPairWitnesses
open Source SourceLogic PairSyntax UnorderedPairLogic OrderedPairElimination

theorem unique_bundle {m} {Γ : Context m} (p q x y s t u v : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hp : Derives Γ (bundle p x y s t)) (hq : Derives Γ (bundle q x y u v)) :
    Derives Γ (.equal p q) := by
  have hs := unique s u x x he (.conjL hp) (.conjL hq)
  have ht := unique t v x y he (.conjL (.conjR hp)) (.conjL (.conjR hq))
  have hq1 := subst_left q u v s (eq_symm hs) (.conjR (.conjR hq))
  have hq2 := subst_right q s v t (eq_symm ht) hq1
  exact unique p q s t he (.conjR (.conjR hp)) hq2

/-- 单元素集在两层无序对中的位置给出第一分量；不假定两分量不同。 -/
theorem first_component {m} {Γ : Context m} (p s t u v x a b : Fin m)
    (hs : Derives Γ (pair s x x)) (hu : Derives Γ (pair u a a)) (hv : Derives Γ (pair v a b))
    (hp : Derives Γ (pair p s t)) (hq : Derives Γ (pair p u v)) : Derives Γ (.equal x a) := by
  have hc := member_cases p u v s hq (member_left p s t hp)
  apply Derives.disjE hc
  · exact singleton_component s u x a (add hs _) (add hu _) (.hyp (Or.inl rfl))
  · have ha := mem_container_subst v s a (eq_symm (.hyp (Or.inl rfl)))
        (member_left v a b (add hv (.equal s v)))
    have hcase := member_cases s x x a (add hs (.equal s v)) ha
    have hax := Derives.disjE hcase (Derives.hyp (Or.inl rfl)) (Derives.hyp (Or.inl rfl))
    exact eq_symm hax

/-- 同一有序对的两个Kuratowski表示确实恢复相同的两个分量。 -/
theorem components_bundle {m} {Γ : Context m} (p q x y a b s t u v : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hp : Derives Γ (bundle p x y s t)) (hq : Derives Γ (bundle q a b u v))
    (hpq : Derives Γ (.equal p q)) : Derives Γ ((Formula.equal x a).conj (.equal y b)) := by
  have hqP := subst_object q u v p (eq_symm hpq) (.conjR (.conjR hq))
  have hxa := first_component p s t u v x a b (.conjL hp) (.conjL hq)
    (.conjL (.conjR hq)) (.conjR (.conjR hp)) hqP
  have hux := subst_left u a a x (eq_symm hxa) (.conjL hq)
  have huxx := subst_right u x a x (eq_symm hxa) hux
  have hsu := unique s u x x he (.conjL hp) huxx
  have hqS := subst_left p u v s (eq_symm hsu) hqP
  have htv := cancel_right p s t v (.conjR (.conjR hp)) hqS
  have hvx := subst_left v a b x (eq_symm hxa) (.conjL (.conjR hq))
  have htX := subst_object v x b t (eq_symm htv) hvx
  exact .conjI hxa (cancel_right t x y b (.conjL (.conjR hp)) htX)

theorem subst_bundle_left {m} {Γ : Context m} (p x y s t a : Fin m)
    (he : Derives Γ (.equal x a)) (h : Derives Γ (bundle p x y s t)) :
    Derives Γ (bundle p a y s t) := by
  have hi : Derives Γ ((bundle p.castSucc (Fin.last m) y.castSucc s.castSucc t.castSucc).instantiate x) := by
    simpa only [Formula.instantiate, bundle_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h
  have hf := Derives.eqSubst (bundle p.castSucc (Fin.last m) y.castSucc s.castSucc t.castSucc) he hi
  simpa only [Formula.instantiate, bundle_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hf

theorem subst_bundle_right {m} {Γ : Context m} (p x y s t b : Fin m)
    (he : Derives Γ (.equal y b)) (h : Derives Γ (bundle p x y s t)) :
    Derives Γ (bundle p x b s t) := by
  have hi : Derives Γ ((bundle p.castSucc x.castSucc (Fin.last m) s.castSucc t.castSucc).instantiate y) := by
    simpa only [Formula.instantiate, bundle_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h
  have hf := Derives.eqSubst (bundle p.castSucc x.castSucc (Fin.last m) s.castSucc t.castSucc) he hi
  simpa only [Formula.instantiate, bundle_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hf

theorem characterization_bundle {m} {Γ : Context m} (p q x y a b s t u v : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hp : Derives Γ (bundle p x y s t)) (hq : Derives Γ (bundle q a b u v)) :
    Derives Γ ((Formula.equal p q).iff ((Formula.equal x a).conj (.equal y b))) := by
  apply Derives.conjI
  · apply Derives.impI
    exact components_bundle p q x y a b s t u v (add he _) (add hp _) (add hq _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    let E := (Formula.equal x a).conj (.equal y b)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hqx := subst_bundle_left q a b u v x (eq_symm (.conjL hE)) (add hq E)
    have hqxy := subst_bundle_right q x b u v y (eq_symm (.conjR hE)) hqx
    exact unique_bundle p q x y s t u v (add he E) (add hp E) hqxy
end PPAC.Migration.OrderedPairWitnesses
