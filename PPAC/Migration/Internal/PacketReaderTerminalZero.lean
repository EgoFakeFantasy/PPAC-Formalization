import PPAC.Migration.Internal.PacketReaderFixedReturn

/-! A genuine zero-step singleton history implements the original reader terminal equation at every actual state code. -/
namespace PPAC.Migration.Internal.PacketReaderTerminalZero
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderReturnCodedSyntax PacketReaderHistorySyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem from_local {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L v s a n q : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hc : Derives Γ (PacketReaderStateSyntax.code w L v s a n)) (hr : Derives Γ (PacketReaderReturnSyntax.result w B z o L v s a q)) :
    Derives Γ (run w B z o n q) := by
  have hN := PacketReaderStateCode.range hZ _ _ _ _ _ _ hw hc
  have hC := PacketReaderStateSyntax.intro_carrier _ _ _ _ _ _ hc
  let R := history w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc n.castSucc z.castSucc o.castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (PacketReaderHistoryBase.exists_zero hZ w B z o n o hw hz ho hN hC)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hc1 := of_eq (PacketReaderStateSyntax.code_rename w L v s a n Fin.castSucc) (under hc R)
  have hr1 := of_eq (PacketReaderReturnSyntax.result_rename w B z o L v s a q Fin.castSucc) (under hr R)
  simpa only [Formula.raise,run_rename] using intro_run _ _ _ _ _ _ _ _ _ _ hR (intro_coded _ _ _ _ _ _ _ _ _ _ hc1 hr1)

theorem at_terminal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L v s a n q : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hc : Derives Γ (PacketReaderStateSyntax.code w L v s a n)) (ht : Derives Γ (PacketReaderTerminalSyntax.raw w B z o L v s a)) :
    Derives Γ ((run w B z o n q).iff (PacketReaderReturnSyntax.result w B z o L v s a q)) := by
  have hN := PacketReaderStateCode.range hZ _ _ _ _ _ _ hw hc
  have hC := PacketReaderStateSyntax.intro_carrier _ _ _ _ _ _ hc
  have hStop := PacketReaderTerminalRaw.no_next_of_raw hZ _ _ _ _ _ _ _ _ _ hw hB hc ht
  let R := history w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc n.castSucc z.castSucc o.castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (PacketReaderHistoryBase.exists_zero hZ w B z o n o hw hz ho hN hC)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hc1 := of_eq (PacketReaderStateSyntax.code_rename w L v s a n Fin.castSucc) (under hc R)
  have hStop1 : Derives Δ (PacketReaderCodedSyntax.existsNext w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc).neg := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,PacketReaderCodedSyntax.existsNext_rename] using under hStop R
  have hh : Derives Δ (PacketReaderStoppingSyntax.halted w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc n.castSucc z.castSucc o.castSucc (Fin.last m)) := .conjI hR hStop1
  simpa only [Formula.raise,Formula.rename,run_rename,PacketReaderReturnSyntax.result_rename] using
    PacketReaderReturnRunNormalize.at_endpoint hZ1 w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc n.castSucc z.castSucc o.castSucc (Fin.last m) q.castSucc L.castSucc v.castSucc s.castSucc a.castSucc hw1 (under hB R) hh hc1

end PPAC.Migration.Internal.PacketReaderTerminalZero
