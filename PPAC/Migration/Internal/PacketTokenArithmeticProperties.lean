import PPAC.Migration.Internal.PacketTokenArithmeticEquation

/-! The actual stopping test selects exactly one branch; all invalid input fields are rejected. -/
namespace PPAC.Migration.Internal.PacketTokenArithmeticProperties
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketTokenAcceptedSyntax PacketTokenArithmeticSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem large_not_small {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (largeCase w B C n t a)) : Derives Γ (Formula.mem n B).neg := by
  apply Derives.impI
  let H := Formula.mem n B
  let L := largeBody w B C n t a
  let Δ := Context.add L (raisedContext 4 (Context.add H Γ))
  apply HornBinderRules.eliminate_many 4 L _ (add hl H)
  have hZ4 := HornBinderRules.zf_body 4 (ZFContext.add hZ H) L
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 (add hw H) L)
  have hn4 : Derives Δ (.mem (old 4 n) (old 4 B)) := HornBinderRules.under_body 4 (Derives.hyp (Γ := Context.add H Γ) (Or.inl rfl)) L
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hq := Derives.impE (.conjR (PacketDivisionDescentCore.terminal_iff hZ4 (old 4 w) (old 4 B) (slot 4 0) (slot 4 1) (old 4 n) hw4 (.conjL hL))) hn4
  exact .impE (.conjL (.conjR hL)) hq

theorem small_criterion_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n B)) :
    Derives Γ ((criterion w B C n t a).iff (PacketAffineSyntax.affine w C n t a)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := criterion w B C n t a
    apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .conjR (.hyp (Or.inl rfl))
    · let L := largeCase w B C n t a
      have hL : Derives (Context.add L (Context.add H Γ)) L := .hyp (Or.inl rfl)
      exact .botE (.impE (large_not_small (ZFContext.add (ZFContext.add hZ H) L) w B C n t a (add (add hw H) L) hL) (add (add hn H) L))
  · apply Derives.impI
    exact .disjL (.conjI (add hn _) (.hyp (Or.inl rfl)))

theorem large_criterion_iff {m} {Γ : Context m} (w B C n t a : Fin m) (hn : Derives Γ (Formula.mem n B).neg) :
    Derives Γ ((criterion w B C n t a).iff (largeCase w B C n t a)) := by
  apply Derives.conjI
  · apply Derives.impI
    apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .botE (.impE (add (add hn _) _) (.conjL (.hyp (Or.inl rfl))))
    · exact .hyp (Or.inl rfl)
  · exact .impI (.disjR (.hyp (Or.inl rfl)))

theorem accepted_small_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hn : Derives Γ (.mem n B)) :
    Derives Γ ((accepted w n t a).iff (PacketAffineSyntax.affine w C n t a)) :=
  SyntaxTypeLocalTransfer.iff_trans (PacketTokenArithmeticEquation.accepted_iff hZ w B C n t a hw hB hC)
    (small_criterion_iff hZ w B C n t a hw hn)

theorem accepted_large_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hn : Derives Γ (Formula.mem n B).neg) :
    Derives Γ ((accepted w n t a).iff (largeCase w B C n t a)) :=
  SyntaxTypeLocalTransfer.iff_trans (PacketTokenArithmeticEquation.accepted_iff hZ w B C n t a hw hB hC)
    (large_criterion_iff w B C n t a hn)

theorem reject_field {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m) (i : Fin 3)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (Formula.mem (SyntaxAtomSyntax.three n t a i) w).neg) :
    Derives Γ (accepted w n t a).neg := by
  apply Derives.impI
  have hn := PacketTokenAcceptedNatural.accepted_environment (ZFContext.add hZ _) w n t a (add hw _) (.hyp (Or.inl rfl))
  exact .impE (add hi _) (HornExprSyntax.environmentNat_at w (SyntaxAtomSyntax.three n t a) hn i)

end PPAC.Migration.Internal.PacketTokenArithmeticProperties
