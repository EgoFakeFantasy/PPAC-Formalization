import PPAC.Migration.GraphLogic

/-! 单点对象图的全部边与唯一取值；不以宿主函数替代对象图。 -/
namespace PPAC.Migration.SingletonGraphLogic
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax GraphLogic UnorderedPairLogic

theorem edge_output {m} {Γ : Context m} (f p x y a b : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (pair f p p)) (hp : Derives Γ (ordered p x y)) (hab : Derives Γ (edge f a b)) :
    Derives Γ ((Formula.equal a x).conj (.equal b y)) := by
  let Q := (Formula.mem (Fin.last m) f.castSucc).conj (ordered (Fin.last m) a.castSucc b.castSucc)
  let Γq := Context.add Q (Context.image Formula.raise Γ)
  apply edge_elim f a b _ hab
  have heQ : Derives Γq (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he Q
  have hfQ : Derives Γq (pair f.castSucc p.castSucc p.castSucc) := by
    simpa only [Formula.raise, pair_rename] using under hf Q
  have hpQ : Derives Γq (ordered p.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, ordered_rename] using under hp Q
  have hq : Derives Γq Q := .hyp (Or.inl rfl)
  have hqp := singleton_member f.castSucc p.castSucc (Fin.last m) hfQ (.conjL hq)
  have hr := OrderedPairLogic.injective (Fin.last m) p.castSucc a.castSucc b.castSucc x.castSucc y.castSucc
    heQ (.conjR hq) hpQ hqp
  simpa only [Formula.raise, Formula.rename] using hr

theorem edge_iff {m} {Γ : Context m} (f p x y a b : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (pair f p p)) (hp : Derives Γ (ordered p x y)) :
    Derives Γ ((edge f a b).iff ((Formula.equal a x).conj (.equal b y))) := by
  apply Derives.conjI
  · apply Derives.impI
    exact edge_output f p x y a b (add he _) (add hf _) (add hp _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    let E := (Formula.equal a x).conj (.equal b y)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hpa := ordered_subst_left p x y a (eq_symm (.conjL hE)) (add hp E)
    have hpab := ordered_subst_right p a y b (eq_symm (.conjR hE)) hpa
    exact edge_intro f a b p (member_left f p p (add hf E)) hpab

theorem singleton_value {m} {Γ : Context m} (f p x y : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (pair f p p)) (hp : Derives Γ (ordered p x y)) : Derives Γ (valueAt f x y) := by
  apply Derives.conjI (edge_intro f x y p (member_left f p p hf) hp)
  apply Derives.allI
  have he' : Derives (Context.image Formula.raise Γ) (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  have hf' : Derives (Context.image Formula.raise Γ) (pair f.castSucc p.castSucc p.castSucc) := by
    simpa only [Formula.raise, pair_rename] using Derives.rename Fin.castSucc hf
  have hp' : Derives (Context.image Formula.raise Γ) (ordered p.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, ordered_rename] using Derives.rename Fin.castSucc hp
  apply Derives.impI
  exact .conjR (edge_output f.castSucc p.castSucc x.castSucc y.castSucc x.castSucc (Fin.last m)
    (add he' _) (add hf' _) (add hp' _) (.hyp (Or.inl rfl)))

/-- 完整原functionOn：每个图成员是定义域内的对，且定义域每点有唯一输出。 -/
theorem function_on_singleton {m} {Γ : Context m} (f p d x y : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (pair f p p)) (hp : Derives Γ (ordered p x y)) (hd : Derives Γ (pair d x x)) :
    Derives Γ (functionOn f d) := by
  apply Derives.conjI
  · apply Derives.allI
    have hf' : Derives (Context.image Formula.raise Γ) (pair f.castSucc p.castSucc p.castSucc) := by
      simpa only [Formula.raise, pair_rename] using Derives.rename Fin.castSucc hf
    have hp' : Derives (Context.image Formula.raise Γ) (ordered p.castSucc x.castSucc y.castSucc) := by
      simpa only [Formula.raise, ordered_rename] using Derives.rename Fin.castSucc hp
    have hd' : Derives (Context.image Formula.raise Γ) (pair d.castSucc x.castSucc x.castSucc) := by
      simpa only [Formula.raise, pair_rename] using Derives.rename Fin.castSucc hd
    apply Derives.impI
    let M := Formula.mem (Fin.last m) f.castSucc
    have hzp := singleton_member f.castSucc p.castSucc (Fin.last m) (add hf' M) (.hyp (Or.inl rfl))
    have hzxy := ordered_subst_object p.castSucc x.castSucc y.castSucc (Fin.last m) (eq_symm hzp) (add hp' M)
    exact entry_intro d.castSucc (Fin.last m) x.castSucc y.castSucc (member_left _ _ _ (add hd' M)) hzxy
  · have hv := singleton_value f p x y he hf hp
    apply Derives.allI
    have hv' : Derives (Context.image Formula.raise Γ) (valueAt f.castSucc x.castSucc y.castSucc) := by
      simpa only [Formula.raise, valueAt_rename] using Derives.rename Fin.castSucc hv
    have hd' : Derives (Context.image Formula.raise Γ) (pair d.castSucc x.castSucc x.castSucc) := by
      simpa only [Formula.raise, pair_rename] using Derives.rename Fin.castSucc hd
    apply Derives.impI
    let M := Formula.mem (Fin.last m) d.castSucc
    have hax := singleton_member d.castSucc x.castSucc (Fin.last m) (add hd' M) (.hyp (Or.inl rfl))
    exact value_exists f.castSucc (Fin.last m) y.castSucc
      (value_subst_input f.castSucc x.castSucc y.castSucc (Fin.last m) (eq_symm hax) (add hv' M))
end PPAC.Migration.SingletonGraphLogic
