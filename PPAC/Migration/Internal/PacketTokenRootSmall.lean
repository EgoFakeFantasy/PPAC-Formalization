import PPAC.Migration.Internal.PacketTokenRootSyntax

/-! The original EX3 small fields are aligned by actual object constructor injectivity. -/
namespace PPAC.Migration.Internal.PacketTokenRootSmall
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketTokenSyntax PacketTokenRootSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B V n t a r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row w n t a r))
    (hs : Derives Γ (PacketTokenApplicationSyntax.smallOutcome w B V r)) : Derives Γ (smallCase w B V n t a) := by
  let L := PacketTokenApplicationSyntax.smallBody w B V r
  let Δ := Context.add L (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 L _ hs
  have hZ3 := HornBinderRules.zf_body 3 hZ L
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw L)
  have hr3 := of_eq (row_rename w n t a r (old 3)) (HornBinderRules.under_body 3 hr L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have he (i : Fin 3) := SyntaxNodeInjective.constructor_input_eq hZ3 3 2 2 (old 3 w)
    (SyntaxAtomSyntax.three (slot 3 0) (slot 3 1) (slot 3 2)) (SyntaxAtomSyntax.three (old 3 n) (old 3 t) (old 3 a))
    (old 3 r) i hw3 (.conjL hL) hr3
  have hp0 := PacketTokenRootTransport.entry_first 1 (old 3 w) (old 3 V) (slot 3 0) (slot 3 1) (slot 3 2) (old 3 n) (he 0) (.conjR (.conjR hL))
  have hp1 := PacketTokenRootTransport.entry_second 1 (old 3 w) (old 3 V) (old 3 n) (slot 3 1) (slot 3 2) (old 3 t) (he 1) hp0
  have hp2 := PacketTokenRootTransport.entry_third 1 (old 3 w) (old 3 V) (old 3 n) (old 3 t) (slot 3 2) (old 3 a) (he 2) hp1
  exact of_eq (smallCase_rename w B V n t a (old 3)).symm (.conjI (mem_subst (he 0) (.conjL (.conjR hL))) hp2)

theorem backward {m} {Γ : Context m} (w B V n t a r : Fin m) (hr : Derives Γ (row w n t a r))
    (hs : Derives Γ (smallCase w B V n t a)) : Derives Γ (PacketTokenApplicationSyntax.smallOutcome w B V r) :=
  PacketTokenApplicationSyntax.intro_small w B V r n t a (.conjI hr hs)

theorem small_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B V n t a r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row w n t a r)) :
    Derives Γ ((PacketTokenApplicationSyntax.smallOutcome w B V r).iff (smallCase w B V n t a)) := by
  apply Derives.conjI
  · exact .impI (forward (ZFContext.add hZ _) w B V n t a r (add hw _) (add hr _) (.hyp (Or.inl rfl)))
  · exact .impI (backward w B V n t a r (add hr _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketTokenRootSmall
