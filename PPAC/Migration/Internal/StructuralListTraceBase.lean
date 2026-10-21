import PPAC.Migration.Internal.StructuralListTraceRows

/-! 实际空序列追加内部Nil值，构造完整单点轨迹；没有宿主空列表见证。 -/
namespace PPAC.Migration.Internal.StructuralListTraceBase
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SequenceSyntax StructuralListSyntax StructuralListTraceSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem empty_links {m} {Γ : Context m} (w z f : Fin m) (hz : Derives Γ (empty z)) : Derives Γ (links w z f) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) z.castSucc
  have hz1 : Derives (Context.add M (Context.image Formula.raise Γ)) (empty z.castSucc) := by simpa only [Formula.raise, empty_rename] using under hz M
  exact .botE (.impE (empty_at z.castSucc (Fin.last m) hz1) (.hyp (Or.inl rfl)))

theorem exists_base {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) : Derives Γ (existsTrace w z e z e e) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have heW := StructuralListUnits.member hZ w z e hw hz he
  have hf := SequenceLogic.empty_sequence z w hz
  have hg := SequenceAppend.exists_append (ZFContext.arithmetic hZ).base e z z e w hf heW he
  let G := SequenceSyntax.append (Fin.last m) e.castSucc z.castSucc z.castSucc e.castSucc w.castSucc
  let Δ := Context.add G (Context.image Formula.raise Γ)
  change Derives Γ (.ex G) at hg
  apply Derives.exE (p := G) hg
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ G
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw G
  have hz1 : Derives Δ (empty z.castSucc) := by simpa only [Formula.raise, empty_rename] using under hz G
  have he1 : Derives Δ (successor e.castSucc z.castSucc) := by simpa only [Formula.raise, successor_rename] using under he G
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hedge := StructuralListTraceRows.new_edge _ _ _ _ (.conjL (.conjR hG))
  have hnil := StructuralNil.at_unit hZ1 _ _ _ hw1 hz1 he1
  have ht := intro_trace _ _ _ _ _ _ _ hz1 hnil (under hzW G) he1 (.conjL hG) hedge (empty_links _ _ _ hz1) hedge
  have hout := intro_existsTrace _ _ _ _ _ _ _ ht
  simpa only [Formula.raise, existsTrace_rename] using hout

theorem valid_unit {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) : Derives Γ (valid w e) := by
  have hf := exists_base hZ w z e hw hz he
  let F := trace w.castSucc z.castSucc e.castSucc z.castSucc e.castSucc (Fin.last m) e.castSucc
  let Δ := Context.add F (Context.image Formula.raise Γ)
  change Derives Γ (.ex F) at hf
  apply Derives.exE (p := F) hf
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have hout := intro_valid _ _ _ _ _ _ _ hF
  simpa only [Formula.raise, valid_rename] using hout

theorem valid_nil {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (nilCode w n)) : Derives Γ (valid w n) := by
  let U := unitWitness m
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralListUnits.with_units w _ hw
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw U
  have hn2 : Derives Δ (nilCode w.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, nilCode_rename] using OrderedPairElimination.under_two hn U
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have hne := StructuralNil.value hZ2 _ _ _ _ hw2 (.conjL hU) (.conjR hU) hn2
  have hv := valid_unit hZ2 _ _ _ hw2 (.conjL hU) (.conjR hU)
  have hout := output_subst _ _ _ (eq_symm hne) hv
  simpa only [Formula.raise, valid_rename] using hout
end PPAC.Migration.Internal.StructuralListTraceBase
