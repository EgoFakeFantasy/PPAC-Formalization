import PPAC.Migration.Internal.PacketReaderTerminalObservation

/-! Every real halted history has actual terminal fields; conversely a classified real history is halted. -/
namespace PPAC.Migration.Internal.PacketReaderTerminalHistory
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderTerminalSyntax PacketReaderStoppingSyntax PacketReaderHistorySyntax PacketReaderHistoryLaws
open SyntaxRenameQuerySyntax (of_eq)

theorem from_halted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (.mem z w)) (ho : Derives Γ (.mem o w))
    (hh : Derives Γ (halted w B z o n r l d f)) : Derives Γ (classifiedHistory w B z o n r l d f) := by
  have hc := PacketReaderHistoryStates.at_edge hZ w B z o n r l d f l r hw (.conjL hh) (last_at _ _ _ _ _ _ _ _ _ (.conjL hh))
  exact .conjI (.conjL hh) (PacketReaderTerminalObservation.from_carrier hZ w B z o r hw hB hz ho hc (.conjR hh))

theorem to_halted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hh : Derives Γ (classifiedHistory w B z o n r l d f)) : Derives Γ (halted w B z o n r l d f) :=
  .conjI (.conjL hh) (.conjR (PacketReaderTerminalObservation.domain hZ w B z o r hw hB (.conjR hh)))

theorem exact_history {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (.mem z w)) (ho : Derives Γ (.mem o w)) :
    Derives Γ ((classifiedHistory w B z o n r l d f).iff (halted w B z o n r l d f)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact to_halted (ZFContext.add hZ _) _ _ _ _ _ _ _ _ _ (add hw _) (add hB _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact from_halted (ZFContext.add hZ _) _ _ _ _ _ _ _ _ _ (add hw _) (add hB _) (add hz _) (add ho _) (.hyp (Or.inl rfl))

theorem exists_classified {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (.mem o w))
    (hc : Derives Γ (PacketReaderStateSyntax.carrier w n)) : Derives Γ (classifiedComplete w B z o n) := by
  have hzN := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  let R := stopBody w B z o n
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ (PacketReaderStoppingExistence.exists_complete hZ w B z o n hw hz hc)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  have hB4 : Derives Δ (.mem (old 4 B) (old 4 w)) := HornBinderRules.under_body 4 hB R
  have hz4 : Derives Δ (.mem (old 4 z) (old 4 w)) := HornBinderRules.under_body 4 hzN R
  have ho4 : Derives Δ (.mem (old 4 o) (old 4 w)) := HornBinderRules.under_body 4 ho R
  have ht := from_halted hZ4 _ _ _ _ _ _ _ _ _ hw4 hB4 hz4 ho4 hR
  exact of_eq (classifiedComplete_rename w B z o n (old 4)).symm (intro_classified _ _ _ _ _ _ _ _ _ ht)

end PPAC.Migration.Internal.PacketReaderTerminalHistory
