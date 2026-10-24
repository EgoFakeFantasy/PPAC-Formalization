import PPAC.Migration.Internal.ProjectionFieldCases

/-! 原field闭轨迹查询在全部内部候选上的数值双条件；根／赋值／解码见证全部消去。 -/
namespace PPAC.Migration.Internal.ProjectionField
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_actual_set {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y V : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (ProjectionTraceSetSyntax.value w V))
    (hq : Derives Γ (ProjectionTraceSyntax.field w x i y)) : Derives Γ (RawCodeFieldSyntax.field w x i y) := by
  let B := (ProjectionTraceSyntax.fieldRow w.castSucc x.castSucc i.castSucc y.castSucc (Fin.last m)).conj
    (ProjectionTraceSyntax.condition w.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hq
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hv1 := of_eq (ProjectionTraceSetSyntax.value_rename w V Fin.castSucc) (under hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := ProjectionFieldCases.condition_sound (ZFContext.under hZ B) _ _ _ _ _ _ hw1 hv1 (.conjL hB) (.conjR hB)
  exact of_eq (RawCodeFieldSyntax.field_rename w x i y Fin.castSucc).symm ho

theorem checked_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (ProjectionTraceSyntax.field w x i y)) : Derives Γ (RawCodeFieldSyntax.field w x i y) := by
  let B := ProjectionTraceSetSyntax.value w.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (ProjectionTraceSet.exists_value hZ w)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hq1 := of_eq (ProjectionTraceSyntax.field_rename w x i y Fin.castSucc) (under hq B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := at_actual_set (ZFContext.under hZ B) _ _ _ _ _ hw1 hB hq1
  exact of_eq (RawCodeFieldSyntax.field_rename w x i y Fin.castSucc).symm ho

theorem positive_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (.mem x w)) (hi : Derives Γ (.mem i w)) (hpos : Derives Γ (empty x).neg)
    (hy : Derives Γ (RawCodeFieldSyntax.field w x i y)) : Derives Γ (ProjectionTraceSyntax.field w x i y) := by
  let B := StructuralNodeDecodeSyntax.witness w.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralNodeDecodeSyntax.eliminate_preimage w x _ (StructuralNodeDecodeExistence.preimage_exists hZ w x hw hx hpos)
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hi2 : Derives Δ (.mem i.castSucc.castSucc w.castSucc.castSucc) := SyntaxRenameBinders.under_2 hi B
  have hy2 : Derives Δ (RawCodeFieldSyntax.field w.castSucc.castSucc x.castSucc.castSucc i.castSucc.castSucc y.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, RawCodeFieldSyntax.field_rename]) (SyntaxRenameBinders.under_2 hy B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hraw := Derives.impE (.conjL (RawCodeField.on_raw_iff hZ2 _ _ _ _ _ _ hw2
    (.conjL (.conjL hB)) (.conjR (.conjL hB)) (.conjR hB))) hy2
  have hchild := ProjectionGetInduction.checked_complete hZ2 _ _ _ _ hw2 (.conjR (.conjL hB)) hi2 hraw
  have ho := ProjectionFieldConstructors.positive_checked hZ2 _ _ _ _ _ _ hw2 (.conjL (.conjL hB)) (.conjR (.conjL hB)) (.conjR hB) hchild
  exact of_eq (by simp only [Formula.raise, ProjectionTraceSyntax.field_rename]) ho

theorem checked_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (.mem x w)) (hi : Derives Γ (.mem i w))
    (hy : Derives Γ (RawCodeFieldSyntax.field w x i y)) : Derives Γ (ProjectionTraceSyntax.field w x i y) := by
  apply SourcePropositional.by_cases (empty x) (ProjectionTraceSyntax.field w x i y)
  · have hzero := Derives.impE (.conjL (RawCodeField.zero_iff (ZFContext.add hZ (empty x)) w x i y
      (add hw _) (.hyp (Or.inl rfl)) (add hi _))) (add hy _)
    exact ProjectionFieldConstructors.zero_checked (ZFContext.add hZ _) w x i y (add hw _) (add hi _) (.hyp (Or.inl rfl)) hzero
  · exact positive_complete (ZFContext.add hZ _) w x i y (add hw _) (add hx _) (add hi _) (.hyp (Or.inl rfl)) (add hy _)

theorem checked_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((ProjectionTraceSyntax.field w x i y).iff
      ((Formula.mem x w).conj ((Formula.mem i w).conj (RawCodeFieldSyntax.field w x i y)))) := by
  apply Derives.conjI
  · apply Derives.impI
    have hq : Derives (Context.add (ProjectionTraceSyntax.field w x i y) Γ) (ProjectionTraceSyntax.field w x i y) := .hyp (Or.inl rfl)
    exact .conjI (ProjectionNodeFields.field_natural_at (ZFContext.add hZ _) w x i y 0 (add hw _) hq)
      (.conjI (ProjectionNodeFields.field_natural_at (ZFContext.add hZ _) w x i y 1 (add hw _) hq) (checked_sound (ZFContext.add hZ _) w x i y (add hw _) hq))
  · apply Derives.impI
    have hB : Derives (Context.add ((Formula.mem x w).conj ((Formula.mem i w).conj (RawCodeFieldSyntax.field w x i y))) Γ)
        ((Formula.mem x w).conj ((Formula.mem i w).conj (RawCodeFieldSyntax.field w x i y))) := .hyp (Or.inl rfl)
    exact checked_complete (ZFContext.add hZ _) w x i y (add hw _) (.conjL hB) (.conjL (.conjR hB)) (.conjR (.conjR hB))

theorem checked_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y z : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (ProjectionTraceSyntax.field w x i y))
    (hz : Derives Γ (ProjectionTraceSyntax.field w x i z)) : Derives Γ (.equal y z) :=
  RawCodeField.unique hZ w x i y z hw (ProjectionNodeFields.field_natural_at hZ w x i y 1 hw hy)
    (checked_sound hZ w x i y hw hy) (checked_sound hZ w x i z hw hz)

end PPAC.Migration.Internal.ProjectionField
