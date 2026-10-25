import PPAC.Migration.Internal.PacketReaderHistoryAgreementInduction

/-! Actual common-index values and equal-length endpoints are unique for all internally finite reader histories, without external standardness. -/
namespace PPAC.Migration.Internal.PacketReaderHistoryUnique
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax PacketReaderHistorySyntax PacketReaderHistoryLaws PacketReaderHistoryAgreementSyntax

theorem at_index {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d k e f g i : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hf : Derives Γ (history w B z o n r l d f)) (hg : Derives Γ (history w B z o n t k e g))
    (hi : Derives Γ (.mem i w)) : Derives Γ (agree f g i) :=
  all_at w f g i (PacketReaderHistoryAgreementInduction.all_agreement hZ w B z o n r t l d k e f g hw hB hf hg) hi

theorem common_values {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d k e f g i a b : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hf : Derives Γ (history w B z o n r l d f)) (hg : Derives Γ (history w B z o n t k e g))
    (ha : Derives Γ (edge f i a)) (hb : Derives Γ (edge g i b)) : Derives Γ (.equal a b) := by
  have hiD := GraphProperties.domain_of_edge f d i a (ZFContext.arithmetic hZ).base.extensionality
    (.conjL (sequence_at _ _ _ _ _ _ _ _ _ hf)) ha
  have hdN := OmegaStructureAlgebra.successor_member w d l (ZFContext.arithmetic hZ).base.extensionality hw
    (length_at _ _ _ _ _ _ _ _ _ hf) (successor_at _ _ _ _ _ _ _ _ _ hf)
  have hiN := StructuralListTraceOrder.member_member hZ w i d hw hdN hiD
  exact at_values f g i a b (at_index hZ w B z o n r t l d k e f g i hw hB hf hg hiN) ha hb

theorem endpoints {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d e f g : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hf : Derives Γ (history w B z o n r l d f)) (hg : Derives Γ (history w B z o n t l e g)) : Derives Γ (.equal r t) :=
  common_values hZ w B z o n r t l d l e f g l r t hw hB hf hg (last_at _ _ _ _ _ _ _ _ _ hf) (last_at _ _ _ _ _ _ _ _ _ hg)

end PPAC.Migration.Internal.PacketReaderHistoryUnique
