import PPAC.Migration.Internal.StructuralListFieldDecode

/-! 真实字段读取直接对应原迹中Cons的实际head，反向索引与原顺序保持对象量词。 -/
namespace PPAC.Migration.Internal.StructuralListFieldTrace
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax NaturalAdditionSyntax StructuralListSyntax StructuralListProjectionSyntax StructuralListFieldSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem head_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e l d f n r j b a h : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (StructuralListTraceSyntax.trace w z e l d f n))
    (hr : Derives Γ (.mem r w)) (hj : Derives Γ (.mem j w)) (ha : Derives Γ (.mem a w)) (hh : Derives Γ (.mem h w))
    (hs : Derives Γ (sum w r j l)) (hb : Derives Γ (edge f j b)) (hc : Derives Γ (consCode w h a b)) : Derives Γ (field w n r h) := by
  have htail := StructuralListPositions.from_trace hZ w z e l d f n r j b hw ht hr hj hs hb
  exact intro_field w n r h b htail (.disjL (StructuralListProjection.selected_cons true w h a b hh ha hc))

theorem head_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e l d f n r j b a h y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (StructuralListTraceSyntax.trace w z e l d f n))
    (hr : Derives Γ (.mem r w)) (hj : Derives Γ (.mem j w)) (ha : Derives Γ (.mem a w)) (hh : Derives Γ (.mem h w))
    (hs : Derives Γ (sum w r j l)) (hb : Derives Γ (edge f j b)) (hc : Derives Γ (consCode w h a b)) :
    Derives Γ ((field w n r y).iff (.equal y h)) := by
  have hv := head_value hZ w z e l d f n r j b a h hw ht hr hj ha hh hs hb hc
  apply Derives.conjI
  · apply Derives.impI
    exact StructuralListFieldValues.unique (ZFContext.add hZ _) _ _ _ _ _ (add hw _) (add hr _) (.hyp (Or.inl rfl)) (add hv _)
  · apply Derives.impI
    exact output_subst w n r h y (eq_symm (.hyp (Or.inl rfl))) (add hv _)
end PPAC.Migration.Internal.StructuralListFieldTrace
