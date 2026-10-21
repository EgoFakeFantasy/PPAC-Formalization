import PPAC.Migration.GraphInsertEdges

/-! 图扩展保持原functionOn的无杂项/精确定义域成员条件。 -/
namespace PPAC.Migration.GraphInsertEntries
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax GraphLogic InsertSyntax OrderedPairElimination

theorem entry_insert_domain {m} {Γ : Context m} (e d x q : Fin m)
    (hi : Derives Γ (insert e d x)) (hq : Derives Γ (entryOn d q)) : Derives Γ (entryOn e q) := by
  let B := entryWitnesses d q
  let Γb := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply entry_elim d q _ hq
  have hiB : Derives Γb (insert e.castSucc.castSucc d.castSucc.castSucc x.castSucc.castSucc) := by
    simpa only [Formula.raise, insert_rename] using under_two hi B
  have hB : Derives Γb B := .hyp (Or.inl rfl)
  have hr := entry_intro e.castSucc.castSucc q.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    (InsertLogic.old_member _ _ _ _ hiB (.conjL hB)) (.conjR hB)
  simpa only [Formula.raise, entryOn_rename] using hr

theorem entries_insert {m} {Γ : Context m} (g e f d p x y : Fin m)
    (hf : Derives Γ (entriesOn f d)) (hg : Derives Γ (insert g f p))
    (hd : Derives Γ (insert e d x)) (hp : Derives Γ (ordered p x y)) : Derives Γ (entriesOn g e) := by
  apply Derives.allI
  let Γ' := Context.image Formula.raise Γ
  have hf' : Derives Γ' (entriesOn f.castSucc d.castSucc) := by
    simpa only [Formula.raise, entriesOn_rename] using Derives.rename Fin.castSucc hf
  have hg' : Derives Γ' (insert g.castSucc f.castSucc p.castSucc) := by
    simpa only [Formula.raise, insert_rename] using Derives.rename Fin.castSucc hg
  have hd' : Derives Γ' (insert e.castSucc d.castSucc x.castSucc) := by
    simpa only [Formula.raise, insert_rename] using Derives.rename Fin.castSucc hd
  have hp' : Derives Γ' (ordered p.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, ordered_rename] using Derives.rename Fin.castSucc hp
  apply Derives.impI
  let M := Formula.mem (Fin.last m) g.castSucc
  have hc := InsertLogic.member_cases g.castSucc f.castSucc p.castSucc (Fin.last m) (add hg' M) (.hyp (Or.inl rfl))
  apply Derives.disjE hc
  · have hentry := Derives.impE (entries_at f.castSucc d.castSucc (Fin.last m) (add (add hf' M) _)) (.hyp (Or.inl rfl))
    exact entry_insert_domain e.castSucc d.castSucc x.castSucc (Fin.last m) (add (add hd' M) _) hentry
  · have hcode := ordered_subst_object p.castSucc x.castSucc y.castSucc (Fin.last m)
      (eq_symm (.hyp (Or.inl rfl))) (add (add hp' M) (.equal (Fin.last m) p.castSucc))
    exact entry_intro e.castSucc (Fin.last m) x.castSucc y.castSucc
      (InsertLogic.new_member _ _ _ (add (add hd' M) _)) hcode
end PPAC.Migration.GraphInsertEntries
