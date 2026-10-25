import PPAC.Migration.Internal.PacketReaderTerminalRaw

/-! Actual endpoint observations have exactly the carrier-and-no-successor domain, including all internal invalid candidates. -/
namespace PPAC.Migration.Internal.PacketReaderTerminalObservation
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderTerminalSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem domain {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hh : Derives Γ (observation w B z o n)) :
    Derives Γ ((PacketReaderStateSyntax.carrier w n).conj (PacketReaderCodedSyntax.existsNext w B z o n).neg) := by
  let R := observationBody w B z o n
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hh
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  have hB4 : Derives Δ (.mem (old 4 B) (old 4 w)) := HornBinderRules.under_body 4 hB R
  have hn := PacketReaderTerminalRaw.no_next_of_raw hZ4 (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 n) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) hw4 hB4 (.conjL hR) (.conjR hR)
  have hc := PacketReaderStateSyntax.intro_carrier _ _ _ _ _ _ (.conjL hR)
  exact of_eq (by simp only [Formula.rename,Formula.neg,PacketReaderStateSyntax.carrier_rename,PacketReaderCodedSyntax.existsNext_rename]) (.conjI hc hn)

theorem from_carrier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (.mem z w)) (ho : Derives Γ (.mem o w))
    (hc : Derives Γ (PacketReaderStateSyntax.carrier w n)) (hn : Derives Γ (PacketReaderCodedSyntax.existsNext w B z o n).neg) :
    Derives Γ (observation w B z o n) := by
  let R := PacketReaderStateSyntax.carrierBody w n
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hc
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  have hB4 : Derives Δ (.mem (old 4 B) (old 4 w)) := HornBinderRules.under_body 4 hB R
  have hz4 : Derives Δ (.mem (old 4 z) (old 4 w)) := HornBinderRules.under_body 4 hz R
  have ho4 : Derives Δ (.mem (old 4 o) (old 4 w)) := HornBinderRules.under_body 4 ho R
  have hn4 : Derives Δ (PacketReaderCodedSyntax.existsNext (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 n)).neg :=
    of_eq (by simp only [Formula.rename,Formula.neg,PacketReaderCodedSyntax.existsNext_rename]) (HornBinderRules.under_body 4 hn R)
  have hr := PacketReaderTerminalRaw.raw_of_no_next hZ4 _ _ _ _ _ _ _ _ _ hw4 hB4 hz4 ho4 hR hn4
  exact of_eq (observation_rename w B z o n (old 4)).symm (intro_observation _ _ _ _ _ _ _ _ _ hR hr)

theorem exact_domain {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (.mem z w)) (ho : Derives Γ (.mem o w)) :
    Derives Γ ((observation w B z o n).iff ((PacketReaderStateSyntax.carrier w n).conj (PacketReaderCodedSyntax.existsNext w B z o n).neg)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact domain (ZFContext.add hZ _) _ _ _ _ _ (add hw _) (add hB _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    have hH : Derives (Context.add ((PacketReaderStateSyntax.carrier w n).conj (PacketReaderCodedSyntax.existsNext w B z o n).neg) Γ) ((PacketReaderStateSyntax.carrier w n).conj (PacketReaderCodedSyntax.existsNext w B z o n).neg) := .hyp (Or.inl rfl)
    exact from_carrier (ZFContext.add hZ _) _ _ _ _ _ (add hw _) (add hB _) (add hz _) (add ho _) (.conjL hH) (.conjR hH)

theorem at_actual_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n L v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (.mem z w)) (ho : Derives Γ (.mem o w))
    (hc : Derives Γ (PacketReaderStateSyntax.code w L v s a n)) :
    Derives Γ ((observation w B z o n).iff (raw w B z o L v s a)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := observation w B z o n
    have hn := Derives.conjR (domain (ZFContext.add hZ H) w B z o n (add hw H) (add hB H) (.hyp (Or.inl rfl)))
    exact PacketReaderTerminalRaw.raw_of_no_next (ZFContext.add hZ H) _ _ _ _ _ _ _ _ _ (add hw H) (add hB H) (add hz H) (add ho H) (add hc H) hn
  · apply Derives.impI
    exact intro_observation w B z o n L v s a (add hc _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PacketReaderTerminalObservation
