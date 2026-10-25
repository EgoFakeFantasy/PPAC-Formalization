import PPAC.Migration.Internal.PacketReaderLengthPoint

/-! Fixed Formula4, full Separation, and original internal omega induction discharge the entire balance IH. -/
namespace PPAC.Migration.Internal.PacketReaderLengthInduction
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderHistorySyntax PacketReaderLengthSyntax PacketReaderConsumptionSyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)
open ReplacementPredicates (paramsUp)
open SyntaxRenameQuerySyntax (of_eq)

theorem base {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f L N : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o n r l d f))
    (hL : Derives Γ (input w n L)) (hN : Derives Γ (hasLength w L N)) :
    Derives Γ (OmegaInductionSyntax.base PacketReaderLengthSyntax.matrix (NaturalAdditionTransport.params3 w f N)) := by
  simp only [OmegaInductionSyntax.base,PacketReaderLengthSyntax.matrix_pred,paramsUp,NaturalAdditionTransport.params3_0,NaturalAdditionTransport.params3_1,NaturalAdditionTransport.params3_2]
  apply Derives.allI
  apply Derives.impI
  let H := empty (Fin.last m)
  have hZ1 := ZFContext.under hZ H
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw H)
  have hh1 := of_eq (history_rename w B z o n r l d f Fin.castSucc) (under hh H)
  have hL1 := of_eq (input_rename w n L Fin.castSucc) (under hL H)
  have hN1 := of_eq (hasLength_rename w L N Fin.castSucc) (under hN H)
  exact PacketReaderLengthPoint.zero_point hZ1 _ _ _ _ _ _ _ _ _ _ _ _ hw1 hh1 hL1 hN1 (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f N : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o n r l d f)) :
    Derives Γ (OmegaInductionSyntax.step PacketReaderLengthSyntax.matrix (NaturalAdditionTransport.params3 w f N) w) := by
  simp only [OmegaInductionSyntax.step,PacketReaderLengthSyntax.matrix_pred,paramsUp,NaturalAdditionTransport.params3_0,NaturalAdditionTransport.params3_1,NaturalAdditionTransport.params3_2]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let I := Formula.mem (slot 2 0) (old 2 w)
  let P := balance (old 2 w) (old 2 f) (old 2 N) (slot 2 0)
  let S : Formula (m+2) := successor (slot 2 1) (slot 2 0)
  let Δ := Context.add S (Context.add P (Context.add I (raisedContext 2 Γ)))
  have lift2 {q : Formula m} (hq : Derives Γ q) : Derives Δ (q.rename (old 2)) := add (add (add (HornBinderRules.under_many 2 hq) I) P) S
  have hZ2 := ZFContext.add (ZFContext.add (ZFContext.add (HornBinderRules.zf_many 2 hZ) I) P) S
  have hw2 := of_eq (omega_rename w (old 2)) (lift2 hw)
  have hh2 := of_eq (history_rename w B z o n r l d f (old 2)) (lift2 hh)
  have hP : Derives Δ P := .hyp (Or.inr (Or.inl rfl))
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  exact PacketReaderLengthPoint.successor_point hZ2 _ _ _ _ _ _ _ _ _ _ _ _ hw2 hh2 hP hS

theorem all_balance {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f L N : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o n r l d f))
    (hL : Derives Γ (input w n L)) (hN : Derives Γ (hasLength w L N)) : Derives Γ (allBalance w f N) := by
  have hall := ZFArithmetic.induction hZ PacketReaderLengthSyntax.matrix (NaturalAdditionTransport.params3 w f N) w hw
    (base hZ w B z o n r l d f L N hw hh hL hN) (step hZ w B z o n r l d f N hw hh)
  simpa only [allBalance,OmegaInductionSyntax.holds,PacketReaderLengthSyntax.matrix_pred,paramsUp,NaturalAdditionTransport.params3_0,NaturalAdditionTransport.params3_1,NaturalAdditionTransport.params3_2] using hall

end PPAC.Migration.Internal.PacketReaderLengthInduction
