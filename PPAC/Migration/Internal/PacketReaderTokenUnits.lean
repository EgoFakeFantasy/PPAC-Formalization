import PPAC.Migration.Internal.ObjectPacketReaderVarintSegment

/-! Actual zero/unit normalization and the original reader empty-input equation for any genuine accumulator and reverse payload. -/
namespace PPAC.Migration.Internal.PacketReaderTokenUnits
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem equation_zero_unit {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z o n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hn : Derives Γ (.mem n w)) : Derives Γ (PacketAffineSyntax.equation w n z o n) := by
  have hzN := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have hProduct := NaturalMultiplicationAlgebraLaws.right_unit hZ w n z o hw hn hz ho
  have hZero := ZFArithmetic.add_zero hZ w n z hw hn hz
  have hSum := ZFArithmetic.add_commute hZ w n z n hw hn hzN hZero
  exact PacketAffineSyntax.intro_equation w n z o n n hProduct hSum

theorem empty_eval_exact {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L a R p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z))
    (ho : Derives Γ (successor o z)) (ha : Derives Γ (StructuralListTraceSyntax.valid w a))
    (hL : Derives Γ (StructuralListSyntax.nilCode w L)) (hR : Derives Γ (StructuralListReverseSyntax.reverses w a R)) :
    Derives Γ ((PacketReaderEvalSyntax.eval w B z o L z o a p).iff (PacketReaderReturnSyntax.some w R p)) := by
  have hzN := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have hoN := StructuralListUnits.member hZ w z o hw hz ho
  have hState : Derives Γ (PacketReaderStepSyntax.state w L z o a) :=
    .conjI (StructuralListTraceBase.valid_nil hZ w L hw hL) (.conjI hzN (.conjI hoN ha))
  have hSuccess : Derives Γ (PacketReaderInputSyntax.eofSuccess w z o L z o a) :=
    .conjI hState (.conjI hL (.conjI (.eqRefl o) (.eqRefl z)))
  have hTerminal : Derives Γ (PacketReaderTerminalSyntax.raw w B z o L z o a) := .disjL hSuccess
  have hEval := PacketReaderEval.at_terminal hZ w B z o L z o a p hw hB hz ho hTerminal
  have hValue := PacketReaderFixedReturn.at_success hZ w B z o L z o a R p hw hSuccess hR
  exact StructuralListSuffixArithmetic.iff_trans hEval hValue

end PPAC.Migration.Internal.PacketReaderTokenUnits
