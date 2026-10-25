import PPAC.Migration.Internal.PacketReaderHistoryLaws

/-! A real singleton sequence constructs every zero-step history; no complete-run existence is assumed. -/
namespace PPAC.Migration.Internal.PacketReaderHistoryBase
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax PacketReaderHistorySyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem exists_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n d : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hd : Derives Γ (successor d z))
    (hn : Derives Γ (.mem n w)) (hc : Derives Γ (PacketReaderStateSyntax.carrier w n)) :
    Derives Γ (existsHistory w B z o n n z d) := by
  have he := SequenceAppend.exists_append (ZFContext.arithmetic hZ).base d z z n w (SequenceLogic.empty_sequence z w hz) hn hd
  let R := SequenceSyntax.append (Fin.last m) d.castSucc z.castSucc z.castSucc n.castSucc w.castSucc
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) he
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz R)
  have hc1 := of_eq (PacketReaderStateSyntax.carrier_rename w n Fin.castSucc) (under hc R)
  have hzw := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have hd1 := of_eq (successor_rename d z Fin.castSucc) (under hd R)
  have hedge := StructuralListTraceRows.new_edge _ _ _ _ (.conjL (.conjR hR))
  have hl := empty_links w.castSucc B.castSucc z.castSucc o.castSucc z.castSucc (Fin.last m) hz1
  have hhist : Derives Δ (history w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc n.castSucc z.castSucc d.castSucc (Fin.last m)) :=
    .conjI hc1 (.conjI hz1 (.conjI (under hzw R) (.conjI hd1 (.conjI (.conjL hR) (.conjI hedge (.conjI hedge hl))))))
  have hout : Derives Δ (existsHistory w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc n.castSucc z.castSucc d.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate,history_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) hhist
  simpa only [Formula.raise,existsHistory_rename] using hout

end PPAC.Migration.Internal.PacketReaderHistoryBase
