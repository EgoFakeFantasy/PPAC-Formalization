import PPAC.Migration.Internal.StructuralListEndExistence

/-! 全内部投影移位及实际列表长度处的Nil终端、唯一端点和原迹种子恢复。 -/
namespace PPAC.Migration.Internal.ObjectStructuralListEnd
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListProjectionSyntax StructuralListLengthSyntax StructuralListShiftSyntax StructuralListEndSyntax
open StructuralListTraceSyntax (valid trace)

def coupledSentence (head : Bool) : Source.Sentence := ((((omega 0).imp ((Formula.mem 3 0).imp ((step head 0 1 2).imp (coupled head 0 1 2 3)))) : Formula 4)).close

def shiftEqualSentence (head : Bool) : Source.Sentence := ((((omega 0).imp ((Formula.mem 3 0).imp ((successor 4 3).imp ((step head 0 1 2).imp ((iteration head 0 1 4 5).imp ((iteration head 0 2 3 6).imp (Formula.equal 5 6))))))) : Formula 7)).close

def shiftIffSentence (head : Bool) : Source.Sentence := ((((omega 0).imp ((Formula.mem 3 0).imp ((successor 4 3).imp ((step head 0 1 2).imp ((iteration head 0 1 4 5).iff (iteration head 0 2 3 5)))))) : Formula 6)).close

def consShiftSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp ((Formula.mem 4 0).imp ((successor 5 4).imp ((consCode 0 1 2 3).imp ((iteration false 0 3 5 6).iff (iteration false 0 2 4 6)))))))) : Formula 7)).close

def terminalSentence : Source.Sentence := ((((omega 0).imp ((hasLength 0 1 2).imp ((iteration false 0 1 2 3).imp (nilCode 0 3)))) : Formula 4)).close

def existsTerminalSentence : Source.Sentence := ((((omega 0).imp ((valid 0 1).imp (existsTerminal 0 1))) : Formula 2)).close

def uniquePairSentence : Source.Sentence := ((((omega 0).imp ((hasLength 0 1 2).imp ((hasLength 0 1 3).imp ((iteration false 0 1 2 4).imp ((iteration false 0 1 3 5).imp ((Formula.equal 2 3).conj (.equal 4 5))))))) : Formula 6)).close

def traceSeedSentence : Source.Sentence := ((((omega 0).imp ((trace 0 1 2 3 4 5 6).imp ((iteration false 0 6 3 7).imp (Formula.equal 7 2)))) : Formula 8)).close

def traceRecoverySentence : Source.Sentence := ((((omega 0).imp ((trace 0 1 2 3 4 5 6).imp (iteration false 0 6 3 2))) : Formula 7)).close

theorem source_coupled (head : Bool) : Derives (Source.SetLanguage.ZF.at 0) (coupledSentence head) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 4 := Context.add (step head 0 1 2) (Context.add (Formula.mem 3 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4

  exact StructuralListShiftInduction.at_index hZ head 0 1 2 3 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem coupled_kernel_certificate (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (coupledSentence head)) := TheoryTransport.sentence (source_coupled head)

theorem native_coupled (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (coupledSentence head)) := ZFReplay.replay (coupled_kernel_certificate head)

theorem source_shiftEqual (head : Bool) : Derives (Source.SetLanguage.ZF.at 0) (shiftEqualSentence head) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 7 := Context.add (iteration head 0 2 3 6) (Context.add (iteration head 0 1 4 5) (Context.add (step head 0 1 2) (Context.add (successor 4 3) (Context.add (Formula.mem 3 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 7))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 7

  exact StructuralListShift.shift_equal hZ head 0 1 2 3 4 5 6 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem shiftEqual_kernel_certificate (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (shiftEqualSentence head)) := TheoryTransport.sentence (source_shiftEqual head)

theorem native_shiftEqual (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (shiftEqualSentence head)) := ZFReplay.replay (shiftEqual_kernel_certificate head)

theorem source_shiftIff (head : Bool) : Derives (Source.SetLanguage.ZF.at 0) (shiftIffSentence head) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 6 := Context.add (step head 0 1 2) (Context.add (successor 4 3) (Context.add (Formula.mem 3 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 6))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6

  exact StructuralListShift.shift_iff hZ head 0 1 2 3 4 5 (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem shiftIff_kernel_certificate (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (shiftIffSentence head)) := TheoryTransport.sentence (source_shiftIff head)

theorem native_shiftIff (head : Bool) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (shiftIffSentence head)) := ZFReplay.replay (shiftIff_kernel_certificate head)

theorem source_consShift : Derives (Source.SetLanguage.ZF.at 0) (consShiftSentence) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 7 := Context.add (consCode 0 1 2 3) (Context.add (successor 5 4) (Context.add (Formula.mem 4 0) (Context.add (Formula.mem 2 0) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 7))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 7

  exact StructuralListShift.shift_iff hZ false 0 3 2 4 5 6 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.disjL (StructuralListProjection.selected_cons false 0 1 2 3 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inl rfl))))

theorem consShift_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (consShiftSentence)) := TheoryTransport.sentence (source_consShift)

theorem native_consShift : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (consShiftSentence)) := ZFReplay.replay (consShift_kernel_certificate)

theorem source_terminal : Derives (Source.SetLanguage.ZF.at 0) (terminalSentence) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 4 := Context.add (iteration false 0 1 2 3) (Context.add (hasLength 0 1 2) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4

  exact StructuralListEndInduction.terminal hZ 0 1 2 3 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem terminal_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (terminalSentence)) := TheoryTransport.sentence (source_terminal)

theorem native_terminal : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (terminalSentence)) := ZFReplay.replay (terminal_kernel_certificate)

theorem source_existsTerminal : Derives (Source.SetLanguage.ZF.at 0) (existsTerminalSentence) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 2 := Context.add (valid 0 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2

  exact StructuralListEndExistence.exists_terminal hZ 0 1 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem existsTerminal_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsTerminalSentence)) := TheoryTransport.sentence (source_existsTerminal)

theorem native_existsTerminal : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsTerminalSentence)) := ZFReplay.replay (existsTerminal_kernel_certificate)

theorem source_uniquePair : Derives (Source.SetLanguage.ZF.at 0) (uniquePairSentence) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 6 := Context.add (iteration false 0 1 3 5) (Context.add (iteration false 0 1 2 4) (Context.add (hasLength 0 1 3) (Context.add (hasLength 0 1 2) (Context.add (omega 0) (Source.SetLanguage.ZF.at 6)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6

  exact StructuralListEndExistence.unique_pair hZ 0 1 2 3 4 5 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem uniquePair_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniquePairSentence)) := TheoryTransport.sentence (source_uniquePair)

theorem native_uniquePair : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniquePairSentence)) := ZFReplay.replay (uniquePair_kernel_certificate)

theorem source_traceSeed : Derives (Source.SetLanguage.ZF.at 0) (traceSeedSentence) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 8 := Context.add (iteration false 0 6 3 7) (Context.add (trace 0 1 2 3 4 5 6) (Context.add (omega 0) (Source.SetLanguage.ZF.at 8)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 8

  exact StructuralListEndExistence.trace_seed hZ 0 1 2 3 4 5 6 7 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem traceSeed_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (traceSeedSentence)) := TheoryTransport.sentence (source_traceSeed)

theorem native_traceSeed : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (traceSeedSentence)) := ZFReplay.replay (traceSeed_kernel_certificate)

theorem source_traceRecovery : Derives (Source.SetLanguage.ZF.at 0) (traceRecoverySentence) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 7 := Context.add (trace 0 1 2 3 4 5 6) (Context.add (omega 0) (Source.SetLanguage.ZF.at 7))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 7

  exact StructuralListEndExistence.trace_recovery hZ 0 1 2 3 4 5 6 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem traceRecovery_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (traceRecoverySentence)) := TheoryTransport.sentence (source_traceRecovery)

theorem native_traceRecovery : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (traceRecoverySentence)) := ZFReplay.replay (traceRecovery_kernel_certificate)

end PPAC.Migration.Internal.ObjectStructuralListEnd
