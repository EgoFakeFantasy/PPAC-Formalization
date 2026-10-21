import PPAC.Migration.TaggedRowSyntax

/-! 用实际唯一有序对和原Replacement取得每个内部集合的实际唯一带标签行。 -/
namespace PPAC.Migration.TaggedRowExistence
open Source SourceAlgebra SourceLogic TaggedRowSyntax

theorem total_pairs {m} {Γ : Context m} (x : Fin m)
    (hp : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0)) :
    Derives Γ (ReplacementPredicates.total pairMatrix (fun _ => x) x) := by
  simp only [ReplacementPredicates.total, pair_fiber, ReplacementPredicates.paramsUp]
  apply Derives.allI
  have hp' : Derives (Context.image Formula.raise Γ) (Source.SetLanguage.pairing.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hp
  have he' : Derives (Context.image Formula.raise Γ) (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  apply Derives.impI
  exact ObjectPairs.exists_unique x.castSucc (Fin.last m) (add hp' _) (add he' _)

theorem exists_row {m} {Γ : Context m} (x : Fin m)
    (hp : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hRep : Derives Γ ((Source.SetLanguage.replacement pairMatrix).rename Fin.elim0)) : Derives Γ (rowExists x) := by
  have hi := Derives.impE (IterationValueCollection.replacement_instance pairMatrix (fun _ => x) x hRep) (total_pairs x hp he)
  simpa only [ReplacementPredicates.imageExists, pair_range, rowExists] using hi

theorem unique {m} {Γ : Context m} (r s x : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hr : Derives Γ (row r x)) (hs : Derives Γ (row s x)) : Derives Γ (.equal r s) := by
  apply Derives.impE (PairSyntax.extensionality_instance r s he)
  apply Derives.allI
  have hr' : Derives (Context.image Formula.raise Γ) (row r.castSucc x.castSucc) := by
    simpa only [Formula.raise, row_rename] using Derives.rename Fin.castSucc hr
  have hs' : Derives (Context.image Formula.raise Γ) (row s.castSucc x.castSucc) := by
    simpa only [Formula.raise, row_rename] using Derives.rename Fin.castSucc hs
  have hc := row_at r.castSucc x.castSucc (Fin.last m) hr'
  have hd := row_at s.castSucc x.castSucc (Fin.last m) hs'
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (.conjR (add hd _)) (.impE (.conjL (add hc _)) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (.conjR (add hc _)) (.impE (.conjL (add hd _)) (.hyp (Or.inl rfl)))

theorem unique_formula {m} {Γ : Context m} (r x : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0)) (hr : Derives Γ (row r x)) : Derives Γ (uniqueRow r x) := by
  apply Derives.allI
  have he' : Derives (Context.image Formula.raise Γ) (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  have hr' : Derives (Context.image Formula.raise Γ) (row r.castSucc x.castSucc) := by
    simpa only [Formula.raise, row_rename] using Derives.rename Fin.castSucc hr
  apply Derives.impI
  exact unique (Fin.last m) r.castSucc x.castSucc (add he' _) (.hyp (Or.inl rfl)) (add hr' _)

theorem fiber {m} {Γ : Context m} (x : Fin m)
    (hp : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hRep : Derives Γ ((Source.SetLanguage.replacement pairMatrix).rename Fin.elim0)) : Derives Γ (rowFiber x) := by
  have hx := exists_row x hp he hRep
  let R := row (Fin.last m) x.castSucc
  let Ξ := Context.add R (Context.image Formula.raise Γ)
  change Derives Γ (.ex R) at hx
  apply Derives.exE (p := R) hx
  have heR : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he R
  have hR : Derives Ξ R := .hyp (Or.inl rfl)
  have hu := unique_formula (Fin.last m) x.castSucc heR hR
  have hout : Derives Ξ (rowFiber x.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, row_rename, uniqueRow_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hR hu
  simpa only [Formula.raise, rowFiber_rename] using hout
end PPAC.Migration.TaggedRowExistence
