import PPAC.Migration.Internal.StructuralListFieldBounds

/-! 所有域内字段严格小于原列表码及父raw码的原核完整闭句。 -/
namespace PPAC.Migration.Internal.ObjectStructuralFieldBounds
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax StructuralNodeSyntax StructuralListFieldSyntax StructuralListLengthSyntax StructuralListFieldGraphSyntax

def fieldBoundSentence : Source.Sentence := ((((omega 0).imp ((hasLength 0 1 2).imp ((Formula.mem 3 2).imp ((field 0 1 3 4).imp (Formula.mem 4 1))))) : Formula 5)).close

def edgeBoundSentence : Source.Sentence := ((((omega 0).imp ((hasLength 0 1 2).imp ((fields 0 1 2 3).imp ((edge 3 4 5).imp (Formula.mem 5 1))))) : Formula 6)).close

def rawFieldBoundSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 1 0).imp ((raw 0 1 2 3).imp ((hasLength 0 2 4).imp ((Formula.mem 5 4).imp ((field 0 2 5 6).imp (Formula.mem 6 3))))))) : Formula 7)).close

def rawEdgeBoundSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 1 0).imp ((raw 0 1 2 3).imp ((hasLength 0 2 4).imp ((fields 0 2 4 5).imp ((edge 5 6 7).imp (Formula.mem 7 3))))))) : Formula 8)).close

theorem source_fieldBound : Derives (Source.SetLanguage.ZF.at 0) fieldBoundSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 5 := (Context.add (field 0 1 3 4) (Context.add (Formula.mem 3 2) (Context.add (hasLength 0 1 2) (Context.add (omega 0) (Source.SetLanguage.ZF.at 5)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 5
  exact StructuralListFieldBounds.field_member hZ 0 1 2 3 4 (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem fieldBound_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence fieldBoundSentence) := TheoryTransport.sentence source_fieldBound

theorem native_fieldBound : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence fieldBoundSentence) := ZFReplay.replay fieldBound_kernel_certificate

theorem source_edgeBound : Derives (Source.SetLanguage.ZF.at 0) edgeBoundSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 6 := (Context.add (edge 3 4 5) (Context.add (fields 0 1 2 3) (Context.add (hasLength 0 1 2) (Context.add (omega 0) (Source.SetLanguage.ZF.at 6)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6
  exact StructuralListFieldBounds.edge_member hZ 0 1 2 3 4 5 (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem edgeBound_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence edgeBoundSentence) := TheoryTransport.sentence source_edgeBound

theorem native_edgeBound : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence edgeBoundSentence) := ZFReplay.replay edgeBound_kernel_certificate

theorem source_rawFieldBound : Derives (Source.SetLanguage.ZF.at 0) rawFieldBoundSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 7 := (Context.add (field 0 2 5 6) (Context.add (Formula.mem 5 4) (Context.add (hasLength 0 2 4) (Context.add (raw 0 1 2 3) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 7)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 7
  exact StructuralListFieldBounds.raw_field_member hZ 0 1 2 3 4 5 6 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem rawFieldBound_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence rawFieldBoundSentence) := TheoryTransport.sentence source_rawFieldBound

theorem native_rawFieldBound : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence rawFieldBoundSentence) := ZFReplay.replay rawFieldBound_kernel_certificate

theorem source_rawEdgeBound : Derives (Source.SetLanguage.ZF.at 0) rawEdgeBoundSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 8 := (Context.add (edge 5 6 7) (Context.add (fields 0 2 4 5) (Context.add (hasLength 0 2 4) (Context.add (raw 0 1 2 3) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 8)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 8
  exact StructuralListFieldBounds.raw_edge_member hZ 0 1 2 3 4 5 6 7 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem rawEdgeBound_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence rawEdgeBoundSentence) := TheoryTransport.sentence source_rawEdgeBound

theorem native_rawEdgeBound : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence rawEdgeBoundSentence) := ZFReplay.replay rawEdgeBound_kernel_certificate

end PPAC.Migration.Internal.ObjectStructuralFieldBounds
