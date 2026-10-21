import PPAC.Migration.PowerUnionSyntax

/-! 幂集精确像的并实际存在且唯一；不以宿主算子或数据选择代替。 -/
namespace PPAC.Migration.PowerUnionOperation
open Source SourceAlgebra SourceLogic GraphSyntax InsertSyntax PowerUnionSyntax

theorem exists_operation {m} {Γ : Context m} (a h : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hp : Derives Γ (Source.SetLanguage.powerSet.rename Fin.elim0))
    (hr : Derives Γ ((Source.SetLanguage.replacement PowerValueSyntax.matrix).rename Fin.elim0))
    (hu : Derives Γ (Source.SetLanguage.union.rename Fin.elim0))
    (hf : Derives Γ (functionOn h a)) : Derives Γ (existsOperation a h) := by
  have hex := PowerValueCollection.exists_range h a he hp hr hf
  let C := PowerValueSyntax.range (Fin.last m) a.castSucc h.castSucc
  let Γc := Context.add C (Context.image Formula.raise Γ)
  change Derives Γ (.ex C) at hex
  apply Derives.exE (p := C) hex
  have huC : Derives Γc (Source.SetLanguage.union.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hu C
  have hC : Derives Γc C := .hyp (Or.inl rfl)
  have hy := union_instance (Fin.last m) huC
  let Y := unionOf (Fin.last (m+1)) (Fin.last m).castSucc
  let Ξ := Context.add Y (Context.image Formula.raise Γc)
  change Derives Γc (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have hCY : Derives Ξ (PowerValueSyntax.range (Fin.last m).castSucc a.castSucc.castSucc h.castSucc.castSucc) := by
    simpa only [Formula.raise, C, PowerValueSyntax.range_rename] using under hC Y
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hop := intro_operation (Fin.last m).castSucc a.castSucc.castSucc h.castSucc.castSucc (Fin.last (m+1)) hCY hY
  have hout : Derives Ξ (existsOperation a.castSucc.castSucc h.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    simpa only [Formula.instantiate, operation_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hop
  simpa only [Formula.raise, existsOperation_rename] using hout

theorem unique {m} {Γ : Context m} (a h y z : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hy : Derives Γ (operation a h y)) (hz : Derives Γ (operation a h z)) : Derives Γ (.equal y z) := by
  let C := (PowerValueSyntax.range (Fin.last m) a.castSucc h.castSucc).conj (unionOf y.castSucc (Fin.last m))
  let Γc := Context.add C (Context.image Formula.raise Γ)
  change Derives Γ (.ex C) at hy
  apply Derives.exE (p := C) hy
  have heC : Derives Γc (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he C
  have hzC : Derives Γc (operation a.castSucc h.castSucc z.castSucc) := by
    simpa only [Formula.raise, operation_rename] using under hz C
  have hC : Derives Γc C := .hyp (Or.inl rfl)
  let D := (PowerValueSyntax.range (Fin.last (m+1)) a.castSucc.castSucc h.castSucc.castSucc).conj
    (unionOf z.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add D (Context.image Formula.raise Γc)
  change Derives Γc (.ex D) at hzC
  apply Derives.exE (p := D) hzC
  have heD : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under heC D
  have hCD : Derives Ξ ((PowerValueSyntax.range (Fin.last m).castSucc a.castSucc.castSucc h.castSucc.castSucc).conj
      (unionOf y.castSucc.castSucc (Fin.last m).castSucc)) := by
    simpa only [Formula.raise, C, Formula.rename, PowerValueSyntax.range_rename, unionOf_rename] using under hC D
  have hD : Derives Ξ D := .hyp (Or.inl rfl)
  have hEq := PowerValueCollection.range_unique (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc h.castSucc.castSucc
    heD (.conjL hCD) (.conjL hD)
  have hzUnion := IterationValues.union_subst_source z.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc (eq_symm hEq) (.conjR hD)
  exact GraphDomainAlgebra.union_unique y.castSucc.castSucc z.castSucc.castSucc (Fin.last m).castSucc heD (.conjR hCD) hzUnion
end PPAC.Migration.PowerUnionOperation
