import PPAC.Migration.Internal.ProjectionGetLocal
import PPAC.Migration.Internal.ProjectionRuleDispatch

/-! 原get零索引的全部内部输入／输出查询双条件；递归尾规则由实际空索引排除。 -/
namespace PPAC.Migration.Internal.ProjectionGetZeroIndex
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation

theorem tail_empty_index_absurd {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y row : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env)) (hz : Derives Γ (empty i))
    (hh : Derives Γ (graph ObjectProjection.getTail.head w env row)) (hr : Derives Γ (ProjectionTraceSyntax.getRow w x i y row)) : Derives Γ .bot := by
  have hi := HornNodeFields.field_3 hZ 1 ProjectionGetConstructors.tailFields w row env (SyntaxAtomSyntax.three x i y) 1 hw hn
    (of_eq (congrArg (fun e => graph e w env row) ProjectionGetConstructors.tail_head) hh) hr
  have hs := Derives.impE (.conjL (ProjectionRawPairExpr.successor_variable_iff (3 : Fin 5) w i env hn)) hi
  exact .impE (empty_at i (env 3) hz) (InsertLogic.new_member i (env 3) (env 3) hs)

theorem zero_application {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y row R : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (ProjectionTraceSyntax.getRow w x i y row))
    (ha : Derives Γ (HornApplicationSyntax.application ObjectProjection.getZero w row R)) : Derives Γ (RawCodeGetSyntax.get w x i y) := by
  let B := HornApplicationSyntax.body ObjectProjection.getZero w row R
  let Δ := Context.add B (raisedContext 1 Γ)
  apply HornApplicationRules.eliminate_application ObjectProjection.getZero w row R _ ha
  have hw1 : Derives Δ (omega (old 1 w)) := of_eq (omega_rename w (old 1)) (HornBinderRules.under_body 1 hw B)
  have hr1 : Derives Δ (ProjectionTraceSyntax.getRow (old 1 w) (old 1 x) (old 1 i) (old 1 y) (old 1 row)) :=
    of_eq (ProjectionTraceSyntax.getRow_rename w x i y row (old 1)) (HornBinderRules.under_body 1 hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := ProjectionGetLocal.zero_sound (HornBinderRules.zf_body 1 hZ B) _ _ _ _ _ _ hw1 (.conjL hB) (.conjL (.conjR (.conjR hB))) hr1
  exact of_eq (RawCodeGetSyntax.get_rename w x i y (old 1)).symm ho

theorem head_application {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y row R : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (ProjectionTraceSyntax.getRow w x i y row))
    (ha : Derives Γ (HornApplicationSyntax.application ObjectProjection.getHead w row R)) : Derives Γ (RawCodeGetSyntax.get w x i y) := by
  let B := HornApplicationSyntax.body ObjectProjection.getHead w row R
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornApplicationRules.eliminate_application ObjectProjection.getHead w row R _ ha
  have hw1 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw B)
  have hr1 : Derives Δ (ProjectionTraceSyntax.getRow (old 3 w) (old 3 x) (old 3 i) (old 3 y) (old 3 row)) :=
    of_eq (ProjectionTraceSyntax.getRow_rename w x i y row (old 3)) (HornBinderRules.under_body 3 hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := ProjectionGetLocal.head_sound (HornBinderRules.zf_body 3 hZ B) _ _ _ _ _ _ hw1 (.conjL hB) (.conjL (.conjR (.conjR hB))) hr1
  exact of_eq (RawCodeGetSyntax.get_rename w x i y (old 3)).symm ho

theorem tail_application {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y row R : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty i)) (hr : Derives Γ (ProjectionTraceSyntax.getRow w x i y row))
    (ha : Derives Γ (HornApplicationSyntax.application ObjectProjection.getTail w row R)) : Derives Γ .bot := by
  let B := HornApplicationSyntax.body ObjectProjection.getTail w row R
  let Δ := Context.add B (raisedContext 5 Γ)
  apply HornApplicationRules.eliminate_application ObjectProjection.getTail w row R _ ha
  have hw1 : Derives Δ (omega (old 5 w)) := of_eq (omega_rename w (old 5)) (HornBinderRules.under_body 5 hw B)
  have hr1 : Derives Δ (ProjectionTraceSyntax.getRow (old 5 w) (old 5 x) (old 5 i) (old 5 y) (old 5 row)) :=
    of_eq (ProjectionTraceSyntax.getRow_rename w x i y row (old 5)) (HornBinderRules.under_body 5 hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hz1 : Derives Δ (empty (old 5 i)) := of_eq (empty_rename i (old 5)) (HornBinderRules.under_body 5 hz B)
  exact tail_empty_index_absurd (HornBinderRules.zf_body 5 hZ B) _ _ _ _ _ _ hw1 (.conjL hB) hz1 (.conjL (.conjR (.conjR hB))) hr1

theorem condition_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y row : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty i)) (hr : Derives Γ (ProjectionTraceSyntax.getRow w x i y row))
    (hc : Derives Γ (ProjectionTraceSyntax.condition w row)) : Derives Γ (RawCodeGetSyntax.get w x i y) := by
  have hs := ProjectionRuleDispatch.get_step hZ 3 w row w (SyntaxAtomSyntax.three x i y) hw hr (ProjectionTraceSyntax.condition_step w row hc)
  apply HornStepSyntax.step_elim ProjectionRuleDispatch.getRules w row w _ hs
  intro rule hm
  apply Derives.impI
  simp only [ProjectionRuleDispatch.getRules, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · exact zero_application (ZFContext.add hZ _) w x i y row w (add hw _) (add hr _) (.hyp (Or.inl rfl))
  · exact head_application (ZFContext.add hZ _) w x i y row w (add hw _) (add hr _) (.hyp (Or.inl rfl))
  · exact .botE (tail_application (ZFContext.add hZ _) w x i y row w (add hw _) (add hz _) (add hr _) (.hyp (Or.inl rfl)))

theorem checked_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty i)) (hq : Derives Γ (ProjectionTraceSyntax.get w x i y)) :
    Derives Γ (RawCodeGetSyntax.get w x i y) := by
  let B := (ProjectionTraceSyntax.getRow w.castSucc x.castSucc i.castSucc y.castSucc (Fin.last m)).conj
    (ProjectionTraceSyntax.condition w.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hq
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hz1 := of_eq (empty_rename i Fin.castSucc) (under hz B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := condition_sound (ZFContext.under hZ B) w.castSucc x.castSucc i.castSucc y.castSucc (Fin.last m) hw1 hz1 (.conjL hB) (.conjR hB)
  exact of_eq (RawCodeGetSyntax.get_rename w x i y Fin.castSucc).symm ho

theorem positive_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (.mem x w)) (hz : Derives Γ (empty i)) (hpos : Derives Γ (empty x).neg)
    (hy : Derives Γ (RawCodeGetSyntax.get w x i y)) : Derives Γ (ProjectionTraceSyntax.get w x i y) := by
  let B := StructuralNodeDecodeSyntax.witness w.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Ξ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralNodeDecodeSyntax.eliminate_preimage w x _ (StructuralNodeDecodeExistence.preimage_exists hZ w x hw hx hpos)
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hz2 : Derives Ξ (empty i.castSucc.castSucc) := of_eq (by simp only [Formula.raise, empty_rename]) (SyntaxRenameBinders.under_2 hz B)
  have hy2 : Derives Ξ (RawCodeGetSyntax.get w.castSucc.castSucc x.castSucc.castSucc i.castSucc.castSucc y.castSucc.castSucc) := of_eq (by simp only [Formula.raise, RawCodeGetSyntax.get_rename]) (SyntaxRenameBinders.under_2 hy B)
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have he := GodelUnpairExistence.preimage_exists hZ2 w.castSucc.castSucc (Fin.last (m+1)) hw2 (.conjR (.conjL hB))
  let C := GodelUnpairSyntax.witness w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc
    (Fin.last (m+2)).castSucc (Fin.last (m+3))
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Ξ))
  apply GodelUnpairSyntax.eliminate_preimage w.castSucc.castSucc (Fin.last (m+1)) _ he
  have hZ4 := SyntaxRenameBinders.zf_under_2 hZ2 C
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw2 C)
  have hz4 : Derives Δ (empty i.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, empty_rename]) (SyntaxRenameBinders.under_2 hz2 C)
  have hy4 : Derives Δ (RawCodeGetSyntax.get w.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc i.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, RawCodeGetSyntax.get_rename]) (SyntaxRenameBinders.under_2 hy2 C)
  have hB4 : Derives Δ (StructuralNodeDecodeSyntax.witness w.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc) :=
    of_eq (by simp only [B, Formula.raise, StructuralNodeDecodeSyntax.witness_rename]) (SyntaxRenameBinders.under_2 hB C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hhead := RawCodeGetLaws.zero_forward _ _ _ _ hz4 hy4
  have heq := RawCodeProjection.on_raw_pair hZ4 true _ _ _ _ _ _ _ hw4 (.conjL (.conjL hB4)) (.conjR (.conjL hB4))
    (.conjL (.conjL hC)) (.conjR (.conjL hC)) (.conjR hB4) (.conjR hC) hhead
  have hparent := ProjectionGetConstructors.head_checked hZ4 _ _ _ _ _ _ _ hw4 (.conjL (.conjL hB4))
    (.conjL (.conjL hC)) (.conjR (.conjL hC)) (.conjR hC) (.conjR hB4) hz4
  have ho := ProjectionGetConstructors.output_subst _ _ _ _ _ (eq_symm heq) hparent
  exact of_eq (by simp only [Formula.raise, ProjectionTraceSyntax.get_rename]) ho

theorem checked_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (.mem x w)) (hz : Derives Γ (empty i))
    (hy : Derives Γ (RawCodeGetSyntax.get w x i y)) : Derives Γ (ProjectionTraceSyntax.get w x i y) := by
  apply SourcePropositional.by_cases (empty x) (ProjectionTraceSyntax.get w x i y)
  · have hi : Derives (Context.add (empty x) Γ) (.mem i w) := OmegaStructureAlgebra.zero_member w i
      (ZFContext.arithmetic (ZFContext.add hZ (empty x))).base.extensionality (add hw (empty x)) (add hz (empty x))
    have hzero := RawCodeGetZero.sound (ZFContext.add hZ _) w x i y (add hw _) (.hyp (Or.inl rfl)) hi (add hy _)
    exact ProjectionGetConstructors.zero_checked (ZFContext.add hZ _) w x i y (add hw _) hi (.hyp (Or.inl rfl)) hzero
  · exact positive_complete (ZFContext.add hZ _) w x i y (add hw _) (add hx _) (add hz _) (.hyp (Or.inl rfl)) (add hy _)

theorem checked_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty i)) :
    Derives Γ ((ProjectionTraceSyntax.get w x i y).iff ((Formula.mem x w).conj (RawCodeGetSyntax.get w x i y))) := by
  apply Derives.conjI
  · apply Derives.impI
    have hq : Derives (Context.add (ProjectionTraceSyntax.get w x i y) Γ) (ProjectionTraceSyntax.get w x i y) := .hyp (Or.inl rfl)
    exact .conjI (ProjectionNodeFields.get_natural_at (ZFContext.add hZ _) w x i y 0 (add hw _) hq)
      (checked_sound (ZFContext.add hZ _) w x i y (add hw _) (add hz _) hq)
  · apply Derives.impI
    have hB : Derives (Context.add ((Formula.mem x w).conj (RawCodeGetSyntax.get w x i y)) Γ)
        ((Formula.mem x w).conj (RawCodeGetSyntax.get w x i y)) := .hyp (Or.inl rfl)
    exact checked_complete (ZFContext.add hZ _) w x i y (add hw _) (.conjL hB) (add hz _) (.conjR hB)

end PPAC.Migration.Internal.ProjectionGetZeroIndex
