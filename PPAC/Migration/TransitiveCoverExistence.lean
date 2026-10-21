import PPAC.Migration.TransitiveCoverLogic

/-! Replacement给出精确值域，原Union实际构造任意种子的传递覆盖。 -/
namespace PPAC.Migration.TransitiveCoverExistence
open Source SourceAlgebra SourceLogic OmegaSyntax InsertSyntax IterationValueSyntax IterationRangeSyntax TransitiveCoverSyntax

theorem exists_cover {m} {Γ : Context m} (hA : IterationContext.Evidence Γ) (z a w : Fin m)
    (hr : Derives Γ ((Source.SetLanguage.replacement matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) : Derives Γ (coverExists a) := by
  have he := IterationValueCollection.exists_range hA z a w hr hw hz
  let C := IterationValueSyntax.range (Fin.last m) w.castSucc z.castSucc a.castSucc
  let Γc := Context.add C (Context.image Formula.raise Γ)
  change Derives Γ (.ex C) at he
  apply Derives.exE (p := C) he
  have hAC := IterationContext.under hA C
  have hwC : Derives Γc (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under hw C
  have hzC : Derives Γc (empty z.castSucc) := by
    simpa only [Formula.raise, empty_rename] using under hz C
  have hC : Derives Γc C := .hyp (Or.inl rfl)
  have hseed := IterationRangeSeed.seed_member hAC (Fin.last m) w.castSucc z.castSucc a.castSucc hwC hzC hC
  have hclosed := IterationRangeClosed.closed_range hAC (Fin.last m) w.castSucc z.castSucc a.castSucc hwC hzC hC
  have hb := union_instance (Fin.last m) hAC.union
  let B := unionOf (Fin.last (m+1)) (Fin.last m).castSucc
  let Γb := Context.add B (Context.image Formula.raise Γc)
  change Derives Γc (.ex B) at hb
  apply Derives.exE (p := B) hb
  have hsB : Derives Γb (.mem a.castSucc.castSucc (Fin.last m).castSucc) := under hseed B
  have hcB : Derives Γb (closedUnion (Fin.last m).castSucc) := by
    simpa only [Formula.raise, closedUnion_rename] using under hclosed B
  have hB : Derives Γb B := .hyp (Or.inl rfl)
  have hcover := TransitiveCoverLogic.from_union (Fin.last (m+1)) (Fin.last m).castSucc a.castSucc.castSucc hB hsB hcB
  have hres : Derives Γb (coverExists a.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    simpa only [Formula.instantiate, cover_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hcover
  simpa only [Formula.raise, coverExists_rename] using hres
end PPAC.Migration.TransitiveCoverExistence
