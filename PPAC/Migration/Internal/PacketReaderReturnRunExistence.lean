import PPAC.Migration.Internal.PacketReaderReturnCoded

/-! Original real histories and actual terminal returns construct an actual return for every real source carrier. -/
namespace PPAC.Migration.Internal.PacketReaderReturnRunExistence
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderReturnCodedSyntax PacketReaderHistorySyntax PacketReaderHistoryLaws
open SyntaxRenameQuerySyntax (of_eq)

theorem halted_history {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f q : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hh : Derives Γ (history w B z o n r l d f))
    (hr : Derives Γ (coded w B z o r q)) : Derives Γ (PacketReaderStoppingSyntax.halted w B z o n r l d f) :=
  .conjI hh (.conjR (PacketReaderTerminalObservation.domain hZ w B z o r hw hB (PacketReaderReturnCoded.observation_domain w B z o r q hr)))

theorem on_history {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o n r l d f))
    (ho : Derives Γ (PacketReaderTerminalSyntax.observation w B z o r)) : Derives Γ (existsRun w B z o n) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (coded w.castSucc B.castSucc z.castSucc o.castSucc r.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (PacketReaderReturnCoded.exists_from_observation hZ w B z o r hw ho)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hh1 := of_eq (history_rename w B z o n r l d f Fin.castSucc) (under hh R)
  have hRun := intro_run _ _ _ _ _ _ _ _ _ _ hh1 (.conjR hR)
  have hout : Derives Δ (existsRun w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate,Formula.rename,run_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI (.conjL hR) hRun)
  simpa only [Formula.raise,existsRun_rename] using hout

theorem exists_run {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (.mem o w))
    (hc : Derives Γ (PacketReaderStateSyntax.carrier w n)) : Derives Γ (existsRun w B z o n) := by
  let R := PacketReaderTerminalSyntax.classifiedBody w B z o n
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ (PacketReaderTerminalHistory.exists_classified hZ w B z o n hw hB hz ho hc)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  exact of_eq (existsRun_rename w B z o n (old 4)).symm
    (on_history hZ4 (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 n) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) hw4 (.conjL hR) (.conjR hR))

theorem source_carrier {m} {Γ : Context m} (w B z o n q : Fin m) (hr : Derives Γ (run w B z o n q)) :
    Derives Γ (PacketReaderStateSyntax.carrier w n) := by
  let R := runBody w B z o n q
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact of_eq (PacketReaderStateSyntax.carrier_rename w n (old 4)).symm (source_at _ _ _ _ _ _ _ _ _ (.conjL hR))

theorem exact_domain {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (.mem o w)) :
    Derives Γ ((existsRun w B z o n).iff (PacketReaderStateSyntax.carrier w n)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := existsRun w B z o n
    let R := (Formula.mem (Fin.last m) w.castSucc).conj (run w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc (Fin.last m))
    let Δ := Context.add R (Context.image Formula.raise (Context.add H Γ))
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    simpa only [Formula.raise,PacketReaderStateSyntax.carrier_rename] using source_carrier _ _ _ _ _ _ (.conjR hR)
  · apply Derives.impI
    exact exists_run (ZFContext.add hZ _) _ _ _ _ _ (add hw _) (add hB _) (add hz _) (add ho _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PacketReaderReturnRunExistence
