import PPAC.Migration.Internal.StructuralListPositions

/-! 全内部原迹位置与真实tail求值的双条件及每点实际反向索引的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectStructuralListPositions
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SequenceSyntax NaturalAdditionSyntax StructuralListProjectionSyntax StructuralListPositionSyntax
open StructuralListTraceSyntax (trace)

def reverseStepSentence : Source.Sentence := ((((Formula.mem 1 0).imp ((StructuralListTraceSyntax.step 0 1 2).imp (step false 0 2 1))) : Formula 3)).close

def advanceSentence (head : Bool) : Source.Sentence := ((((omega 0).imp ((Formula.mem 2 0).imp ((successor 3 2).imp ((iteration head 0 1 2 4).imp ((step head 0 4 5).imp (iteration head 0 1 3 5)))))) : Formula 6)).close

def oldIndexSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 1 0).imp ((Formula.mem 3 0).imp ((successor 2 1).imp ((sum 0 2 3 4).imp (Formula.mem 3 4)))))) : Formula 5)).close

def swapSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 1 0).imp ((Formula.mem 3 0).imp ((successor 2 1).imp ((successor 4 3).imp ((sum 0 2 3 5).imp (sum 0 1 4 5))))))) : Formula 6)).close

def allPositionsSentence : Source.Sentence := ((((omega 0).imp ((sequence 3 2 0).imp ((StructuralListTraceSyntax.links 0 1 3).imp ((edge 3 1 4).imp ((Formula.mem 5 0).imp (positions 0 1 3 4 5)))))) : Formula 6)).close

def atSentence : Source.Sentence := ((((omega 0).imp ((trace 0 1 2 3 4 5 6).imp ((Formula.mem 7 0).imp ((Formula.mem 8 0).imp ((sum 0 7 8 3).imp ((edge 5 8 9).imp (iteration false 0 6 7 9))))))) : Formula 10)).close

def iffSentence : Source.Sentence := ((((omega 0).imp ((trace 0 1 2 3 4 5 6).imp ((Formula.mem 7 0).imp ((Formula.mem 8 0).imp ((sum 0 7 8 3).imp ((edge 5 8 9).iff (iteration false 0 6 7 9))))))) : Formula 10)).close

def reverseExistsSentence : Source.Sentence := ((((omega 0).imp ((trace 0 1 2 3 4 5 6).imp ((Formula.mem 7 4).imp (reverseExists 0 3 5 6 7)))) : Formula 8)).close

theorem source_reverseStep : Derives (Source.SetLanguage.ZF.at 0) (reverseStepSentence) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI

  exact StructuralListPositionLogic.reverse_cons_step 0 1 2 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem reverseStep_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (reverseStepSentence)) := TheoryTransport.sentence (source_reverseStep)

theorem native_reverseStep : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (reverseStepSentence)) := ZFReplay.replay (reverseStep_kernel_certificate)

theorem source_advance (head : Bool) : Derives (Source.SetLanguage.ZF.at 0) (advanceSentence head) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 6 := Context.add (step head 0 4 5) (Context.add (iteration head 0 1 2 4) (Context.add (successor 3 2) (Context.add (Formula.mem 2 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 6)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6

  exact StructuralListPositionLogic.advance hZ head 0 1 2 3 4 5 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem advance_kernel_certificate (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (advanceSentence head)) := TheoryTransport.sentence (source_advance head)

theorem native_advance (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (advanceSentence head)) := ZFReplay.replay (advance_kernel_certificate head)

theorem source_oldIndex : Derives (Source.SetLanguage.ZF.at 0) (oldIndexSentence) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 5 := Context.add (sum 0 2 3 4) (Context.add (successor 2 1) (Context.add (Formula.mem 3 0) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 5)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 5

  exact StructuralListPositionArithmetic.old_index hZ 0 1 2 3 4 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem oldIndex_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (oldIndexSentence)) := TheoryTransport.sentence (source_oldIndex)

theorem native_oldIndex : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (oldIndexSentence)) := ZFReplay.replay (oldIndex_kernel_certificate)

theorem source_swap : Derives (Source.SetLanguage.ZF.at 0) (swapSentence) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 6 := Context.add (sum 0 2 3 5) (Context.add (successor 4 3) (Context.add (successor 2 1) (Context.add (Formula.mem 3 0) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 6))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6

  exact StructuralListPositionArithmetic.swap_successors hZ 0 1 2 3 4 5 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem swap_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (swapSentence)) := TheoryTransport.sentence (source_swap)

theorem native_swap : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (swapSentence)) := ZFReplay.replay (swap_kernel_certificate)

theorem source_allPositions : Derives (Source.SetLanguage.ZF.at 0) (allPositionsSentence) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 6 := Context.add (Formula.mem 5 0) (Context.add (edge 3 1 4) (Context.add (StructuralListTraceSyntax.links 0 1 3) (Context.add (sequence 3 2 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 6)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6

  exact StructuralListPositionInduction.at_index hZ 0 1 2 3 4 5 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem allPositions_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allPositionsSentence)) := TheoryTransport.sentence (source_allPositions)

theorem native_allPositions : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allPositionsSentence)) := ZFReplay.replay (allPositions_kernel_certificate)

theorem source_at : Derives (Source.SetLanguage.ZF.at 0) (atSentence) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 10 := Context.add (edge 5 8 9) (Context.add (sum 0 7 8 3) (Context.add (Formula.mem 8 0) (Context.add (Formula.mem 7 0) (Context.add (trace 0 1 2 3 4 5 6) (Context.add (omega 0) (Source.SetLanguage.ZF.at 10))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 10

  exact StructuralListPositions.from_trace hZ 0 1 2 3 4 5 6 7 8 9 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem at_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atSentence)) := TheoryTransport.sentence (source_at)

theorem native_at : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atSentence)) := ZFReplay.replay (at_kernel_certificate)

theorem source_iff : Derives (Source.SetLanguage.ZF.at 0) (iffSentence) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 10 := Context.add (sum 0 7 8 3) (Context.add (Formula.mem 8 0) (Context.add (Formula.mem 7 0) (Context.add (trace 0 1 2 3 4 5 6) (Context.add (omega 0) (Source.SetLanguage.ZF.at 10)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 10

  exact StructuralListPositions.trace_iff hZ 0 1 2 3 4 5 6 7 8 9 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem iff_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (iffSentence)) := TheoryTransport.sentence (source_iff)

theorem native_iff : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (iffSentence)) := ZFReplay.replay (iff_kernel_certificate)

theorem source_reverseExists : Derives (Source.SetLanguage.ZF.at 0) (reverseExistsSentence) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 8 := Context.add (Formula.mem 7 4) (Context.add (trace 0 1 2 3 4 5 6) (Context.add (omega 0) (Source.SetLanguage.ZF.at 8)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 8

  exact StructuralListPositions.trace_reverse_exists hZ 0 1 2 3 4 5 6 7 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem reverseExists_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (reverseExistsSentence)) := TheoryTransport.sentence (source_reverseExists)

theorem native_reverseExists : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (reverseExistsSentence)) := ZFReplay.replay (reverseExists_kernel_certificate)

end PPAC.Migration.Internal.ObjectStructuralListPositions
