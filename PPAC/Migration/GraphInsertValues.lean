import PPAC.Migration.GraphInsertEntries

/-! 新输入不在旧定义域时，扩展保持旧值并给出新点唯一值。 -/
namespace PPAC.Migration.GraphInsertValues
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax GraphLogic GraphProperties InsertSyntax GraphInsertEdges

theorem old_value {m} {Γ : Context m} (g f d p x y a b : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hn : Derives Γ (Formula.mem x d).neg) (hg : Derives Γ (insert g f p))
    (hp : Derives Γ (ordered p x y)) (ha : Derives Γ (.mem a d)) (hv : Derives Γ (valueAt f a b)) :
    Derives Γ (valueAt g a b) := by
  apply Derives.conjI (old_edge g f p a b hg (.conjL hv))
  apply Derives.allI
  let Γ' := Context.image Formula.raise Γ
  have he' : Derives Γ' (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  have hn' : Derives Γ' (Formula.mem x.castSucc d.castSucc).neg := Derives.rename Fin.castSucc hn
  have hg' : Derives Γ' (insert g.castSucc f.castSucc p.castSucc) := by
    simpa only [Formula.raise, insert_rename] using Derives.rename Fin.castSucc hg
  have hp' : Derives Γ' (ordered p.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, ordered_rename] using Derives.rename Fin.castSucc hp
  have ha' : Derives Γ' (.mem a.castSucc d.castSucc) := Derives.rename Fin.castSucc ha
  have hv' : Derives Γ' (valueAt f.castSucc a.castSucc b.castSucc) := by
    simpa only [Formula.raise, valueAt_rename] using Derives.rename Fin.castSucc hv
  apply Derives.impI
  let E := edge g.castSucc a.castSucc (Fin.last m)
  have hc := edge_cases g.castSucc f.castSucc p.castSucc x.castSucc y.castSucc a.castSucc (Fin.last m)
    (add he' E) (add hg' E) (add hp' E) (.hyp (Or.inl rfl))
  apply Derives.disjE hc
  · exact .impE (unique_at f.castSucc a.castSucc b.castSucc (Fin.last m) (add (add hv' E) _)) (.hyp (Or.inl rfl))
  · have hax : Derives (Context.add ((Formula.equal a.castSucc x.castSucc).conj (.equal (Fin.last m) y.castSucc))
        (Context.add E Γ')) (.equal a.castSucc x.castSucc) := .conjL (.hyp (Or.inl rfl))
    exact .botE (.impE (add (add hn' E) _) (mem_subst hax (add (add ha' E) _)))

theorem new_value {m} {Γ : Context m} (g f d p x y : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f d)) (hn : Derives Γ (Formula.mem x d).neg)
    (hg : Derives Γ (insert g f p)) (hp : Derives Γ (ordered p x y)) : Derives Γ (valueAt g x y) := by
  apply Derives.conjI (new_edge g f p x y hg hp)
  apply Derives.allI
  let Γ' := Context.image Formula.raise Γ
  have he' : Derives Γ' (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  have hf' : Derives Γ' (functionOn f.castSucc d.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using Derives.rename Fin.castSucc hf
  have hn' : Derives Γ' (Formula.mem x.castSucc d.castSucc).neg := Derives.rename Fin.castSucc hn
  have hg' : Derives Γ' (insert g.castSucc f.castSucc p.castSucc) := by
    simpa only [Formula.raise, insert_rename] using Derives.rename Fin.castSucc hg
  have hp' : Derives Γ' (ordered p.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, ordered_rename] using Derives.rename Fin.castSucc hp
  apply Derives.impI
  let E := edge g.castSucc x.castSucc (Fin.last m)
  have hc := edge_cases g.castSucc f.castSucc p.castSucc x.castSucc y.castSucc x.castSucc (Fin.last m)
    (add he' E) (add hg' E) (add hp' E) (.hyp (Or.inl rfl))
  apply Derives.disjE hc
  · exact .botE (.impE (add (add hn' E) _)
      (domain_of_edge f.castSucc d.castSucc x.castSucc (Fin.last m) (add (add he' E) _) (add (add hf' E) _) (.hyp (Or.inl rfl))))
  · exact .conjR (.hyp (Or.inl rfl))

theorem old_total {m} {Γ : Context m} (g f d p x y a : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f d)) (hn : Derives Γ (Formula.mem x d).neg)
    (hg : Derives Γ (insert g f p)) (hp : Derives Γ (ordered p x y)) (ha : Derives Γ (.mem a d)) :
    Derives Γ (valueExists g a) := by
  have hv := Derives.impE (total_at f d a (.conjR hf)) ha
  let V := valueAt f.castSucc a.castSucc (Fin.last m)
  let Γv := Context.add V (Context.image Formula.raise Γ)
  change Derives Γ (.ex V) at hv
  apply Derives.exE (p := V) hv
  have heV : Derives Γv (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he V
  have hnV : Derives Γv (Formula.mem x.castSucc d.castSucc).neg := under hn V
  have hgV : Derives Γv (insert g.castSucc f.castSucc p.castSucc) := by
    simpa only [Formula.raise, insert_rename] using under hg V
  have hpV : Derives Γv (ordered p.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, ordered_rename] using under hp V
  have haV : Derives Γv (.mem a.castSucc d.castSucc) := under ha V
  have hV : Derives Γv V := .hyp (Or.inl rfl)
  have hr := value_exists g.castSucc a.castSucc (Fin.last m)
    (old_value g.castSucc f.castSucc d.castSucc p.castSucc x.castSucc y.castSucc a.castSucc (Fin.last m)
      heV hnV hgV hpV haV hV)
  simpa only [Formula.raise, valueExists_rename] using hr
end PPAC.Migration.GraphInsertValues
