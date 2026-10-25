import PPAC.Migration.Internal.PacketReaderHistoryPrepend

/-! A genuine step followed by any genuine returning history constructs a genuine whole returning run. All new graph/domain witnesses are object existentials. -/
namespace PPAC.Migration.Internal.PacketReaderRunPrepend
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax HornBinderSyntax PacketReaderHistorySyntax PacketReaderReturnCodedSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem from_history {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d f q : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (PacketReaderCodedSyntax.step w B z o n r))
    (hh : Derives Γ (history w B z o r t l d f)) (hq : Derives Γ (coded w B z o t q)) : Derives Γ (run w B z o n q) := by
  let E := successor (Fin.last m) d.castSucc
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (InsertExistence.exists_insert d d (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ E
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have ht1 := of_eq (PacketReaderCodedSyntax.step_rename w B z o n r Fin.castSucc) (under ht E)
  have hh1 := of_eq (history_rename w B z o r t l d f Fin.castSucc) (under hh E)
  have hExt := PacketReaderHistoryPrepend.exists_extension hZ1 w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc r.castSucc t.castSucc l.castSucc d.castSucc (Fin.last m) f.castSucc hw1 hh1 ht1 hE
  let G := (SequencePrependSyntax.graph f.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    (history w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc n.castSucc.castSucc t.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Ξ := Context.add G (Context.image Formula.raise Δ)
  apply Derives.exE (p := G) hExt
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have hq1 := of_eq (coded_rename w B z o t q Fin.castSucc) (under hq E)
  have hq2 := of_eq (coded_rename w.castSucc B.castSucc z.castSucc o.castSucc t.castSucc q.castSucc Fin.castSucc) (under hq1 G)
  simpa only [Formula.raise,run_rename] using intro_run _ _ _ _ _ _ _ _ _ _ (.conjR hG) hq2

theorem backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r q : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (PacketReaderCodedSyntax.step w B z o n r))
    (hr : Derives Γ (run w B z o r q)) : Derives Γ (run w B z o n q) := by
  let R := runBody w B z o r q
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  have ht4 := of_eq (PacketReaderCodedSyntax.step_rename w B z o n r (old 4)) (HornBinderRules.under_body 4 ht R)
  exact of_eq (run_rename w B z o n q (old 4)).symm
    (from_history hZ4 (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 n) (old 4 r) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) (old 4 q) hw4 ht4 (.conjL hR) (.conjR hR))

end PPAC.Migration.Internal.PacketReaderRunPrepend
