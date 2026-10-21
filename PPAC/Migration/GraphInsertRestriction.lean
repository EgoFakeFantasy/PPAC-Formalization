import PPAC.Migration.GraphInsertExistence
import PPAC.Migration.RestrictionHistory

/-! 新鲜输入扩展后，旧完整函数图本身就是新图在旧域上的实际限制。 -/
namespace PPAC.Migration.GraphInsertRestriction
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax GraphLogic RestrictionSyntax InsertSyntax

theorem entry_subst_code {m} {Γ : Context m} (d q p : Fin m)
    (he : Derives Γ (.equal q p)) (hq : Derives Γ (entryOn d q)) : Derives Γ (entryOn d p) := by
  have hi : Derives Γ ((entryOn d.castSucc (Fin.last m)).instantiate q) := by
    simpa only [Formula.instantiate, entryOn_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hq
  have hr := Derives.eqSubst (entryOn d.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, entryOn_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hr

theorem old_restriction {m} {Γ : Context m} (g f d p x y : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f d)) (hn : Derives Γ (Formula.mem x d).neg)
    (hi : Derives Γ (insert g f p)) (hp : Derives Γ (ordered p x y)) : Derives Γ (restrict f g d) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have he' : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  have hf' : Derives Δ (functionOn f.castSucc d.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using Derives.rename Fin.castSucc hf
  have hn' : Derives Δ (Formula.mem x.castSucc d.castSucc).neg := Derives.rename Fin.castSucc hn
  have hi' : Derives Δ (insert g.castSucc f.castSucc p.castSucc) := by
    simpa only [Formula.raise, insert_rename] using Derives.rename Fin.castSucc hi
  have hp' : Derives Δ (ordered p.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, ordered_rename] using Derives.rename Fin.castSucc hp
  apply Derives.conjI
  · apply Derives.impI
    exact .conjI (InsertLogic.old_member g.castSucc f.castSucc p.castSucc (Fin.last m) (add hi' _) (.hyp (Or.inl rfl)))
      (.impE (add (entries_at f.castSucc d.castSucc (Fin.last m) (.conjL hf')) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    let B := (Formula.mem (Fin.last m) g.castSucc).conj (entryOn d.castSucc (Fin.last m))
    let Ξ := Context.add B Δ
    have hB : Derives Ξ B := .hyp (Or.inl rfl)
    have hc := InsertLogic.member_cases g.castSucc f.castSucc p.castSucc (Fin.last m) (add hi' B) (.conjL hB)
    apply Derives.disjE hc
    · exact .hyp (Or.inl rfl)
    · have hep : Derives (Context.add (.equal (Fin.last m) p.castSucc) Ξ) (entryOn d.castSucc p.castSucc) :=
        entry_subst_code d.castSucc (Fin.last m) p.castSucc (.hyp (Or.inl rfl)) (add (.conjR hB) _)
      exact .botE (.impE (add (add hn' B) _) (GraphProperties.entry_input d.castSucc p.castSucc x.castSucc y.castSucc
        (add (add he' B) _) (add (add hp' B) _) hep))
end PPAC.Migration.GraphInsertRestriction
