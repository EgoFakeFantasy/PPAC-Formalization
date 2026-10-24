import PPAC.Migration.Internal.PacketTokenRootSmall

/-! The original EX6 followed by EX2 is retained as eight real witnesses before field alignment. -/
namespace PPAC.Migration.Internal.PacketTokenRootLarge
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketTokenSyntax PacketTokenRootSyntax
open SyntaxRenameQuerySyntax (of_eq)

def witnessBody {m} (w B V r : Fin m) : Formula (m+8) :=
  (empty (slot 8 6)).conj ((NaturalAdditionSyntax.sum (old 8 w) (slot 8 3) (old 8 B) (slot 8 7)).conj
    ((row (old 8 w) (slot 8 0) (slot 8 1) (slot 8 2) (old 8 r)).conj
      (((Formula.mem (slot 8 6) (slot 8 4)).conj (.mem (slot 8 3) (old 8 B))).conj
        ((tagEntry 0 (old 8 w) (old 8 V) (slot 8 3) (slot 8 4) (slot 8 0)).conj
          ((entry (old 8 w) (old 8 V) (slot 8 4) (slot 8 1) (slot 8 5)).conj
            (tagEntry 1 (old 8 w) (old 8 V) (slot 8 7) (slot 8 5) (slot 8 2)))))))

theorem actual_witness {m} (w B V r : Fin m) :
    PacketTokenApplicationSyntax.largeOutcome w B V r = existsMany 8 (witnessBody w B V r) := rfl

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B V n t a r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row w n t a r))
    (hl : Derives Γ (PacketTokenApplicationSyntax.largeOutcome w B V r)) : Derives Γ (largeCase w B V n t a) := by
  let L := witnessBody w B V r
  let Δ := Context.add L (raisedContext 8 Γ)
  apply HornBinderRules.eliminate_many 8 L _ (of_eq (actual_witness w B V r) hl)
  have hZ8 := HornBinderRules.zf_body 8 hZ L
  have hw8 := of_eq (omega_rename w (old 8)) (HornBinderRules.under_body 8 hw L)
  have hr8 := of_eq (row_rename w n t a r (old 8)) (HornBinderRules.under_body 8 hr L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hA := Derives.conjR (.conjR hL)
  have he (i : Fin 3) := SyntaxNodeInjective.constructor_input_eq hZ8 3 2 2 (old 8 w)
    (SyntaxAtomSyntax.three (slot 8 0) (slot 8 1) (slot 8 2)) (SyntaxAtomSyntax.three (old 8 n) (old 8 t) (old 8 a))
    (old 8 r) i hw8 (.conjL hA) hr8
  have hprems := Derives.conjR (.conjR hA)
  have h0 := PacketTokenRootTransport.entry_third 0 (old 8 w) (old 8 V) (slot 8 3) (slot 8 4) (slot 8 0) (old 8 n)
    (he 0) (.conjL hprems)
  have h1 := PacketTokenRootTransport.entry_second 2 (old 8 w) (old 8 V) (slot 8 4) (slot 8 1) (slot 8 5) (old 8 t)
    (he 1) (.conjL (.conjR hprems))
  have h2 := PacketTokenRootTransport.entry_third 1 (old 8 w) (old 8 V) (slot 8 7) (slot 8 5) (slot 8 2) (old 8 a)
    (he 2) (.conjR (.conjR hprems))
  exact of_eq (largeCase_rename w B V n t a (old 8)).symm
    (PacketTokenRootSyntax.intro_large (old 8 w) (old 8 B) (old 8 V) (old 8 n) (old 8 t) (old 8 a)
      (slot 8 3) (slot 8 4) (slot 8 5) (slot 8 6) (slot 8 7) (.conjL hL) (.conjL (.conjR hL))
      (.conjL (.conjR hA)) (.conjI h0 (.conjI h1 h2)))

theorem backward {m} {Γ : Context m} (w B V n t a r : Fin m) (hr : Derives Γ (row w n t a r))
    (hl : Derives Γ (largeCase w B V n t a)) : Derives Γ (PacketTokenApplicationSyntax.largeOutcome w B V r) := by
  let L := PacketTokenRootSyntax.largeBody w B V n t a
  let Δ := Context.add L (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 L _ hl
  have hr5 := of_eq (row_rename w n t a r (old 5)) (HornBinderRules.under_body 5 hr L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  let env : Fin 6 → Fin (m+5) := Fin.cases (old 5 n) (Fin.cases (old 5 t) (Fin.cases (old 5 a)
    (Fin.cases (slot 5 0) (Fin.cases (slot 5 1) (Fin.cases (slot 5 2) Fin.elim0)))))
  have ha : Derives Δ (largeAt (old 5 w) (old 5 B) (old 5 V) (slot 5 3) (slot 5 4) (old 5 r) env) :=
    .conjI hr5 (.conjR (.conjR hL))
  have hloc := PacketTokenSyntax.intro_large (old 5 w) (old 5 B) (old 5 V) (old 5 r) (slot 5 3) (slot 5 4) env
    (.conjL hL) (.conjL (.conjR hL)) ha
  exact of_eq (PacketTokenApplicationSyntax.largeOutcome_rename w B V r (old 5)).symm
    (PacketTokenApplicationSyntax.intro_large (old 5 w) (old 5 B) (old 5 V) (old 5 r) env hloc)

theorem large_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B V n t a r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row w n t a r)) :
    Derives Γ ((PacketTokenApplicationSyntax.largeOutcome w B V r).iff (largeCase w B V n t a)) := by
  apply Derives.conjI
  · exact .impI (forward (ZFContext.add hZ _) w B V n t a r (add hw _) (add hr _) (.hyp (Or.inl rfl)))
  · exact .impI (backward w B V n t a r (add hr _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketTokenRootLarge
