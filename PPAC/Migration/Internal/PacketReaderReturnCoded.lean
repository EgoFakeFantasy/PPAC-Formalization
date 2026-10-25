import PPAC.Migration.Internal.PacketReaderReturnNormalize

/-! Actual coded returns normalize at every real source state and exist exactly on the independent terminal-observation domain. -/
namespace PPAC.Migration.Internal.PacketReaderReturnCoded
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderReturnSyntax PacketReaderReturnCodedSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_source {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n q L v s a : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (PacketReaderStateSyntax.code w L v s a n)) :
    Derives Γ ((coded w B z o n q).iff (result w B z o L v s a q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := coded w B z o n q
    let R := codedBody w B z o n q
    let Δ := Context.add R (raisedContext 4 (Context.add H Γ))
    apply HornBinderRules.eliminate_many 4 R _ (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ4 := HornBinderRules.zf_body 4 (ZFContext.add hZ H) R
    have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 (add hw H) R)
    have hc4 := of_eq (PacketReaderStateSyntax.code_rename w L v s a n (old 4)) (HornBinderRules.under_body 4 (add hc H) R)
    have he := PacketReaderStateCode.fields_unique hZ4 _ _ _ _ _ _ _ _ _ _ hw4 (.conjL hR) hc4
    exact of_eq (result_rename w B z o L v s a q (old 4)).symm (PacketReaderReturnTransport.align_result _ _ _ _ _ _ _ _ _ _ _ _ _ he (.conjR hR))
  · apply Derives.impI
    exact intro_coded w B z o n q L v s a (add hc _) (.hyp (Or.inl rfl))

theorem observation_domain {m} {Γ : Context m} (w B z o n q : Fin m) (hr : Derives Γ (coded w B z o n q)) :
    Derives Γ (PacketReaderTerminalSyntax.observation w B z o n) := by
  let R := codedBody w B z o n q
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hRaw := PacketReaderReturnExistence.domain _ _ _ _ _ _ _ _ _ (.conjR hR)
  exact of_eq (PacketReaderTerminalSyntax.observation_rename w B z o n (old 4)).symm (PacketReaderTerminalSyntax.intro_observation _ _ _ _ _ _ _ _ _ (.conjL hR) hRaw)

theorem exists_at_source {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n L v s a : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (PacketReaderStateSyntax.code w L v s a n))
    (hr : Derives Γ (PacketReaderTerminalSyntax.raw w B z o L v s a)) : Derives Γ (existsCoded w B z o n) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (result w.castSucc B.castSucc z.castSucc o.castSucc L.castSucc v.castSucc s.castSucc a.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (PacketReaderReturnExistence.from_terminal hZ w B z o L v s a hw hr)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hc1 := of_eq (PacketReaderStateSyntax.code_rename w L v s a n Fin.castSucc) (under hc R)
  have hRet := intro_coded _ _ _ _ _ _ _ _ _ _ hc1 (.conjR hR)
  have hout : Derives Δ (existsCoded w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate,Formula.rename,coded_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI (.conjL hR) hRet)
  simpa only [Formula.raise,existsCoded_rename] using hout

theorem exists_from_observation {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (PacketReaderTerminalSyntax.observation w B z o n)) : Derives Γ (existsCoded w B z o n) := by
  let R := PacketReaderTerminalSyntax.observationBody w B z o n
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  exact of_eq (existsCoded_rename w B z o n (old 4)).symm
    (exists_at_source hZ4 (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 n) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) hw4 (.conjL hR) (.conjR hR))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n p q : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (coded w B z o n p)) (hq : Derives Γ (coded w B z o n q)) : Derives Γ (.equal p q) := by
  let R := codedBody w B z o n p
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hp
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  have hq4 := of_eq (coded_rename w B z o n q (old 4)) (HornBinderRules.under_body 4 hq R)
  have hNorm := at_source hZ4 (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 n) (old 4 q) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) hw4 (.conjL hR)
  have hLocal := Derives.impE (.conjL hNorm) hq4
  exact PacketReaderReturnUnique.unique hZ4 _ _ _ _ _ _ _ _ _ _ hw4 (.conjR hR) hLocal

theorem natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n q : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (coded w B z o n q)) : Derives Γ (.mem q w) := by
  let R := codedBody w B z o n q
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  exact PacketReaderReturnNormalize.natural hZ4 _ _ _ _ _ _ _ _ _ hw4 (.conjR hR)

theorem exact_domain {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((existsCoded w B z o n).iff (PacketReaderTerminalSyntax.observation w B z o n)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := existsCoded w B z o n
    let R := (Formula.mem (Fin.last m) w.castSucc).conj (coded w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc (Fin.last m))
    let Δ := Context.add R (Context.image Formula.raise (Context.add H Γ))
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    simpa only [Formula.raise,PacketReaderTerminalSyntax.observation_rename] using observation_domain _ _ _ _ _ _ (.conjR hR)
  · apply Derives.impI
    exact exists_from_observation (ZFContext.add hZ _) _ _ _ _ _ (add hw _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PacketReaderReturnCoded
