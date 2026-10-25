import PPAC.Migration.Internal.PacketReaderHistoryAgreementPoint

/-! Full Separation for the fixed Formula3 drives original omega induction and discharges every graph-agreement IH. -/
namespace PPAC.Migration.Internal.PacketReaderHistoryAgreementInduction
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderHistorySyntax PacketReaderHistoryAgreementSyntax
open ReplacementPredicates (paramsUp)
open SyntaxRenameQuerySyntax (of_eq)

theorem base {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d k e f g : Fin m)
    (hf : Derives Γ (history w B z o n r l d f)) (hg : Derives Γ (history w B z o n t k e g)) :
    Derives Γ (OmegaInductionSyntax.base PacketReaderHistoryAgreementSyntax.matrix (Source.SetLanguage.args2 f g)) := by
  simp only [OmegaInductionSyntax.base,PacketReaderHistoryAgreementSyntax.matrix_pred,paramsUp,PairSyntax.args2_first,PairSyntax.args2_second]
  apply Derives.allI
  apply Derives.impI
  let H := empty (Fin.last m)
  have hZ1 := ZFContext.under hZ H
  have hf1 := of_eq (history_rename w B z o n r l d f Fin.castSucc) (under hf H)
  have hg1 := of_eq (history_rename w B z o n t k e g Fin.castSucc) (under hg H)
  exact PacketReaderHistoryAgreementPoint.zero_point hZ1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf1 hg1 (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d k e f g : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hf : Derives Γ (history w B z o n r l d f)) (hg : Derives Γ (history w B z o n t k e g)) :
    Derives Γ (OmegaInductionSyntax.step PacketReaderHistoryAgreementSyntax.matrix (Source.SetLanguage.args2 f g) w) := by
  simp only [OmegaInductionSyntax.step,PacketReaderHistoryAgreementSyntax.matrix_pred,paramsUp,PairSyntax.args2_first,PairSyntax.args2_second]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let N := Formula.mem (slot 2 0) (old 2 w)
  let P := agree (old 2 f) (old 2 g) (slot 2 0)
  let S : Formula (m+2) := successor (slot 2 1) (slot 2 0)
  let Δ := Context.add S (Context.add P (Context.add N (raisedContext 2 Γ)))
  have lift2 {q : Formula m} (hq : Derives Γ q) : Derives Δ (q.rename (old 2)) := add (add (add (HornBinderRules.under_many 2 hq) N) P) S
  have hZ2 := ZFContext.add (ZFContext.add (ZFContext.add (HornBinderRules.zf_many 2 hZ) N) P) S
  have hw2 := of_eq (omega_rename w (old 2)) (lift2 hw)
  have hB2 : Derives Δ (.mem (old 2 B) (old 2 w)) := lift2 hB
  have hf2 := of_eq (history_rename w B z o n r l d f (old 2)) (lift2 hf)
  have hg2 := of_eq (history_rename w B z o n t k e g (old 2)) (lift2 hg)
  have hP : Derives Δ P := .hyp (Or.inr (Or.inl rfl))
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  exact PacketReaderHistoryAgreementPoint.successor_point hZ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw2 hB2 hf2 hg2 hP hS

theorem all_agreement {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d k e f g : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hf : Derives Γ (history w B z o n r l d f)) (hg : Derives Γ (history w B z o n t k e g)) :
    Derives Γ (allAgreement w f g) := by
  have hall := ZFArithmetic.induction hZ PacketReaderHistoryAgreementSyntax.matrix (Source.SetLanguage.args2 f g) w hw
    (base hZ w B z o n r t l d k e f g hf hg) (step hZ w B z o n r t l d k e f g hw hB hf hg)
  simpa only [allAgreement,OmegaInductionSyntax.holds,PacketReaderHistoryAgreementSyntax.matrix_pred,paramsUp,PairSyntax.args2_first,PairSyntax.args2_second] using hall

end PPAC.Migration.Internal.PacketReaderHistoryAgreementInduction
