import PPAC.Migration.Internal.PacketTokenArithmeticBridge

/-! Actual and recursive token rows supply all internal naturality guards. -/
namespace PPAC.Migration.Internal.PacketTokenAcceptedNatural
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax PacketTokenSyntax PacketTokenAcceptedSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem accepted_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (accepted w n t a)) :
    Derives Γ (environmentNat 3 w (SyntaxAtomSyntax.three n t a)) := by
  let R := (row w.castSucc n.castSucc t.castSucc a.castSucc (Fin.last m)).conj (PacketTraceSyntax.condition w.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) ha
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have he := PacketTokenNatural.row_environment (ZFContext.under hZ R) 2 w.castSucc n.castSucc t.castSucc a.castSucc (Fin.last m) hw1 (.conjL hR)
  simpa only [Formula.raise,environmentNat_rename,SyntaxAtomSyntax.three_map] using he

theorem criterion_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (PacketTokenArithmeticSyntax.criterion w B C n t a)) :
    Derives Γ (environmentNat 3 w (SyntaxAtomSyntax.three n t a)) := by
  apply Derives.disjE hc
  · let S := PacketTokenArithmeticSyntax.smallCase w B C n t a
    have hS : Derives (Context.add S Γ) S := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.add hZ S
    have hw1 := add hw S
    have hA := Derives.conjR hS
    exact .conjI (PacketAffineCore.digit_natural hZ1 w C n t a hw1 hA)
      (.conjI (PacketAffineCore.tail_guard _ _ _ _ _ hA) (.conjI (PacketAffineCore.output_guard _ _ _ _ _ hA) HornRuleSyntax.truth_proved))
  · let H := PacketTokenArithmeticSyntax.largeCase w B C n t a
    let M := PacketTokenArithmeticSyntax.largeBody w B C n t a
    let Δ := Context.add M (raisedContext 4 (Context.add H Γ))
    apply HornBinderRules.eliminate_many 4 M _ (.hyp (Or.inl rfl))
    have hZ4 := HornBinderRules.zf_body 4 (ZFContext.add hZ H) M
    have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 (add hw H) M)
    have hM : Derives Δ M := .hyp (Or.inl rfl)
    have hn := PacketAffineCore.output_guard (old 4 w) (old 4 B) (slot 4 0) (slot 4 1) (old 4 n) (.conjL hM)
    have ha := PacketAffineCore.output_guard (old 4 w) (old 4 C) (slot 4 3) (slot 4 2) (old 4 a) (.conjR (.conjR (.conjR (.conjR hM))))
    have ht := environmentNat_at (old 4 w) (SyntaxAtomSyntax.three (slot 4 1) (old 4 t) (slot 4 2))
      (accepted_environment hZ4 (old 4 w) (slot 4 1) (old 4 t) (slot 4 2) hw4 (.conjL (.conjR (.conjR (.conjR hM))))) 1
    have he : Derives Δ (environmentNat 3 (old 4 w) (SyntaxAtomSyntax.three (old 4 n) (old 4 t) (old 4 a))) :=
      .conjI hn (.conjI ht (.conjI ha HornRuleSyntax.truth_proved))
    exact of_eq (by simp only [environmentNat_rename,SyntaxAtomSyntax.three_map]) he

end PPAC.Migration.Internal.PacketTokenAcceptedNatural
