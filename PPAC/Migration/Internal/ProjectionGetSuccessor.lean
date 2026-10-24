import PPAC.Migration.Internal.ProjectionGetSuccessorSound

/-! 后继索引的真实父查询构造，解码及子查询见证均在对象层消去。 -/
namespace PPAC.Migration.Internal.ProjectionGetSuccessor
open Source SourceAlgebra SourceLogic OmegaSyntax ProjectionGetInductionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem positive_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i s y : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (.mem x w)) (hi : Derives Γ (.mem i w))
    (hs : Derives Γ (successor s i)) (hc : Derives Γ (correct w i)) (hpos : Derives Γ (empty x).neg)
    (hy : Derives Γ (RawCodeGetSyntax.get w x s y)) : Derives Γ (ProjectionTraceSyntax.get w x s y) := by
  let B := StructuralNodeDecodeSyntax.witness w.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Ξ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralNodeDecodeSyntax.eliminate_preimage w x _ (StructuralNodeDecodeExistence.preimage_exists hZ w x hw hx hpos)
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hi2 : Derives Ξ (.mem i.castSucc.castSucc w.castSucc.castSucc) := SyntaxRenameBinders.under_2 hi B
  have hs2 : Derives Ξ (successor s.castSucc.castSucc i.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, successor_rename]) (SyntaxRenameBinders.under_2 hs B)
  have hc2 : Derives Ξ (correct w.castSucc.castSucc i.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, correct_rename]) (SyntaxRenameBinders.under_2 hc B)
  have hy2 : Derives Ξ (RawCodeGetSyntax.get w.castSucc.castSucc x.castSucc.castSucc s.castSucc.castSucc y.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, RawCodeGetSyntax.get_rename]) (SyntaxRenameBinders.under_2 hy B)
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have he := GodelUnpairExistence.preimage_exists hZ2 w.castSucc.castSucc (Fin.last (m+1)) hw2 (.conjR (.conjL hB))
  let C := GodelUnpairSyntax.witness w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc
    (Fin.last (m+2)).castSucc (Fin.last (m+3))
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Ξ))
  apply GodelUnpairSyntax.eliminate_preimage w.castSucc.castSucc (Fin.last (m+1)) _ he
  have hZ4 := SyntaxRenameBinders.zf_under_2 hZ2 C
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw2 C)
  have hi4 : Derives Δ (.mem i.castSucc.castSucc.castSucc.castSucc w.castSucc.castSucc.castSucc.castSucc) := SyntaxRenameBinders.under_2 hi2 C
  have hs4 : Derives Δ (successor s.castSucc.castSucc.castSucc.castSucc i.castSucc.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, successor_rename]) (SyntaxRenameBinders.under_2 hs2 C)
  have hc4 : Derives Δ (correct w.castSucc.castSucc.castSucc.castSucc i.castSucc.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, correct_rename]) (SyntaxRenameBinders.under_2 hc2 C)
  have hy4 : Derives Δ (RawCodeGetSyntax.get w.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, RawCodeGetSyntax.get_rename]) (SyntaxRenameBinders.under_2 hy2 C)
  have hB4 : Derives Δ (StructuralNodeDecodeSyntax.witness w.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc) :=
    of_eq (by simp only [B, Formula.raise, StructuralNodeDecodeSyntax.witness_rename]) (SyntaxRenameBinders.under_2 hB C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have htail := RawCodeProjection.intro_raw_pair false _ _ _ _ _ _ (.conjL (.conjL hB4)) (.conjR (.conjL hB4))
    (.conjL (.conjL hC)) (.conjR (.conjL hC)) (.conjR hB4) (.conjR hC)
  have hraw := RawCodeGetLaws.successor_forward hZ4 _ _ _ _ _ _ hw4 hi4 hs4 htail hy4
  have hiff := at_value _ _ (Fin.last (m+3)) y.castSucc.castSucc.castSucc.castSucc hc4
  have hchild := Derives.impE (.conjR hiff) (Derives.conjI (.conjR (.conjL hC)) hraw)
  have ho := ProjectionGetConstructors.tail_checked hZ4 _ _ _ _ _ _ _ _ _ hw4 (.conjL (.conjL hB4))
    (.conjL (.conjL hC)) (.conjR (.conjL hC)) (.conjR hC) (.conjR hB4) hs4 hchild
  exact of_eq (by simp only [Formula.raise, ProjectionTraceSyntax.get_rename]) ho

theorem checked_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i s y : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (.mem x w)) (hi : Derives Γ (.mem i w))
    (hs : Derives Γ (successor s i)) (hc : Derives Γ (correct w i))
    (hy : Derives Γ (RawCodeGetSyntax.get w x s y)) : Derives Γ (ProjectionTraceSyntax.get w x s y) := by
  have hsn := OmegaStructureAlgebra.successor_member w s i (ZFContext.arithmetic hZ).base.extensionality hw hi hs
  apply SourcePropositional.by_cases (empty x) (ProjectionTraceSyntax.get w x s y)
  · have hzero := RawCodeGetZero.sound (ZFContext.add hZ (empty x)) w x s y (add hw _) (.hyp (Or.inl rfl)) (add hsn _) (add hy _)
    exact ProjectionGetConstructors.zero_checked (ZFContext.add hZ _) w x s y (add hw _) (add hsn _) (.hyp (Or.inl rfl)) hzero
  · exact positive_complete (ZFContext.add hZ _) w x i s y (add hw _) (add hx _) (add hi _) (add hs _) (add hc _) (.hyp (Or.inl rfl)) (add hy _)

theorem checked_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i s y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) (hs : Derives Γ (successor s i)) (hc : Derives Γ (correct w i)) :
    Derives Γ (point w x s y) := by
  apply Derives.conjI
  · apply Derives.impI
    have hq : Derives (Context.add (ProjectionTraceSyntax.get w x s y) Γ) (ProjectionTraceSyntax.get w x s y) := .hyp (Or.inl rfl)
    exact .conjI (ProjectionNodeFields.get_natural_at (ZFContext.add hZ _) w x s y 0 (add hw _) hq)
      (ProjectionGetSuccessorSound.checked_sound (ZFContext.add hZ _) w x i s y (add hw _) (add hi _) (add hs _) (add hc _) hq)
  · apply Derives.impI
    have hB : Derives (Context.add ((Formula.mem x w).conj (RawCodeGetSyntax.get w x s y)) Γ)
        ((Formula.mem x w).conj (RawCodeGetSyntax.get w x s y)) := .hyp (Or.inl rfl)
    exact checked_complete (ZFContext.add hZ _) w x i s y (add hw _) (.conjL hB) (add hi _) (add hs _) (add hc _) (.conjR hB)

theorem correct_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w i s : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) (hs : Derives Γ (successor s i)) (hc : Derives Γ (correct w i)) :
    Derives Γ (correct w s) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise.raise := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc h)
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (lift hw)
  have hs2 : Derives Δ (successor s.castSucc.castSucc i.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (lift hs)
  have hc2 : Derives Δ (correct w.castSucc.castSucc i.castSucc.castSucc) := of_eq (by simp only [Formula.raise, correct_rename]) (lift hc)
  exact checked_iff (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) _ (Fin.last m).castSucc _ _ (Fin.last (m+1)) hw2 (lift hi) hs2 hc2

end PPAC.Migration.Internal.ProjectionGetSuccessor
