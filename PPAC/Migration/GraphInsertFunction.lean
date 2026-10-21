import PPAC.Migration.GraphInsertValues

/-! 新输入不在旧域时，单点插入保持完整原functionOn。 -/
namespace PPAC.Migration.GraphInsertFunction
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax GraphLogic InsertSyntax GraphInsertValues

theorem function_insert {m} {Γ : Context m} (g e f d p x y : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f d)) (hn : Derives Γ (Formula.mem x d).neg)
    (hg : Derives Γ (insert g f p)) (hd : Derives Γ (insert e d x)) (hp : Derives Γ (ordered p x y)) :
    Derives Γ (functionOn g e) := by
  apply Derives.conjI (GraphInsertEntries.entries_insert g e f d p x y (.conjL hf) hg hd hp)
  apply Derives.allI
  let Γ' := Context.image Formula.raise Γ
  have he' : Derives Γ' (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  have hf' : Derives Γ' (functionOn f.castSucc d.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using Derives.rename Fin.castSucc hf
  have hn' : Derives Γ' (Formula.mem x.castSucc d.castSucc).neg := Derives.rename Fin.castSucc hn
  have hg' : Derives Γ' (insert g.castSucc f.castSucc p.castSucc) := by
    simpa only [Formula.raise, insert_rename] using Derives.rename Fin.castSucc hg
  have hd' : Derives Γ' (insert e.castSucc d.castSucc x.castSucc) := by
    simpa only [Formula.raise, insert_rename] using Derives.rename Fin.castSucc hd
  have hp' : Derives Γ' (ordered p.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, ordered_rename] using Derives.rename Fin.castSucc hp
  apply Derives.impI
  let M := Formula.mem (Fin.last m) e.castSucc
  have hc := InsertLogic.member_cases e.castSucc d.castSucc x.castSucc (Fin.last m) (add hd' M) (.hyp (Or.inl rfl))
  apply Derives.disjE hc
  · exact old_total g.castSucc f.castSucc d.castSucc p.castSucc x.castSucc y.castSucc (Fin.last m)
      (add (add he' M) _) (add (add hf' M) _) (add (add hn' M) _) (add (add hg' M) _) (add (add hp' M) _) (.hyp (Or.inl rfl))
  · have hv := new_value g.castSucc f.castSucc d.castSucc p.castSucc x.castSucc y.castSucc
      (add (add he' M) (.equal (Fin.last m) x.castSucc)) (add (add hf' M) _) (add (add hn' M) _) (add (add hg' M) _) (add (add hp' M) _)
    exact value_exists g.castSucc (Fin.last m) y.castSucc
      (value_subst_input g.castSucc x.castSucc y.castSucc (Fin.last m) (eq_symm (.hyp (Or.inl rfl))) hv)
end PPAC.Migration.GraphInsertFunction
