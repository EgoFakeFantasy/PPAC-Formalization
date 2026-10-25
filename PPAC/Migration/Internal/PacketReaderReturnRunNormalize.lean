import PPAC.Migration.Internal.PacketReaderReturnRunUnique

/-! Normalize the whole real run at any actual stopped history, then at its decoded endpoint and exact option value. -/
namespace PPAC.Migration.Internal.PacketReaderReturnRunNormalize
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderReturnCodedSyntax PacketReaderReturnSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_history {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f q : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hh : Derives Γ (PacketReaderStoppingSyntax.halted w B z o n r l d f)) :
    Derives Γ ((run w B z o n q).iff (coded w B z o r q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := run w B z o n q
    let R := runBody w B z o n q
    let Δ := Context.add R (raisedContext 4 (Context.add H Γ))
    apply HornBinderRules.eliminate_many 4 R _ (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ4 := HornBinderRules.zf_body 4 (ZFContext.add hZ H) R
    have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 (add hw H) R)
    have hB4 : Derives Δ (.mem (old 4 B) (old 4 w)) := HornBinderRules.under_body 4 (add hB H) R
    have hh4 := of_eq (PacketReaderStoppingSyntax.halted_rename w B z o n r l d f (old 4)) (HornBinderRules.under_body 4 (add hh H) R)
    have hStop := PacketReaderReturnRunExistence.halted_history hZ4 _ _ _ _ _ _ _ _ _ _ hw4 hB4 (.conjL hR) (.conjR hR)
    have he := PacketReaderStoppingUnique.endpoints hZ4 (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 n) (slot 4 0) (old 4 r) (slot 4 1) (slot 4 2) (old 4 l) (old 4 d) (slot 4 3) (old 4 f) hw4 hB4 hStop hh4
    exact of_eq (coded_rename w B z o r q (old 4)).symm (PacketReaderReturnTransport.coded_source _ _ _ _ _ _ _ he (.conjR hR))
  · apply Derives.impI
    exact intro_run w B z o n q r l d f (.conjL (add hh _)) (.hyp (Or.inl rfl))

theorem at_endpoint {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f q L v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hh : Derives Γ (PacketReaderStoppingSyntax.halted w B z o n r l d f))
    (hc : Derives Γ (PacketReaderStateSyntax.code w L v s a r)) :
    Derives Γ ((run w B z o n q).iff (result w B z o L v s a q)) :=
  StructuralListSuffixArithmetic.iff_trans (at_history hZ _ _ _ _ _ _ _ _ _ _ hw hB hh)
    (PacketReaderReturnCoded.at_source hZ _ _ _ _ _ _ _ _ _ _ hw hc)

theorem at_some {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f q L v s a u : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hh : Derives Γ (PacketReaderStoppingSyntax.halted w B z o n r l d f))
    (hc : Derives Γ (PacketReaderStateSyntax.code w L v s a r)) (hu : Derives Γ (some w u q)) :
    Derives Γ ((run w B z o n q).iff ((PacketReaderInputSyntax.eofSuccess w z o L v s a).conj (StructuralListReverseSyntax.reverses w a u))) :=
  StructuralListSuffixArithmetic.iff_trans (at_endpoint hZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw hB hh hc)
    (PacketReaderReturnNormalize.at_some hZ _ _ _ _ _ _ _ _ _ _ hw hu)

theorem at_none {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f q L v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hh : Derives Γ (PacketReaderStoppingSyntax.halted w B z o n r l d f))
    (hc : Derives Γ (PacketReaderStateSyntax.code w L v s a r)) (hn : Derives Γ (none w q)) :
    Derives Γ ((run w B z o n q).iff (rejection w B z o L v s a)) :=
  StructuralListSuffixArithmetic.iff_trans (at_endpoint hZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw hB hh hc)
    (PacketReaderReturnNormalize.at_none hZ _ _ _ _ _ _ _ _ _ hw hn)

end PPAC.Migration.Internal.PacketReaderReturnRunNormalize
