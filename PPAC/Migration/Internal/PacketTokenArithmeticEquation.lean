import PPAC.Migration.Internal.PacketTokenAcceptedNatural

/-! Canonical value and actual root witnesses are eliminated from the full arithmetic token equation. -/
namespace PPAC.Migration.Internal.PacketTokenArithmeticEquation
open Source SourceAlgebra SourceLogic OmegaSyntax PacketTokenSyntax PacketTokenAcceptedSyntax PacketTokenArithmeticSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem condition_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a r : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hr : Derives Γ (row w n t a r)) :
    Derives Γ ((PacketTraceSyntax.condition w r).iff (criterion w B C n t a)) := by
  let V := PacketTraceCore.value w.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  apply Derives.exE (p := V) (PacketTraceCore.exists_value hZ w)
  have hZ1 := ZFContext.under hZ V
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw V)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under hB V)
  have hC1 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C Fin.castSucc) (under hC V)
  have hr1 := of_eq (row_rename w n t a r Fin.castSucc) (under hr V)
  have hv : Derives Δ V := .hyp (Or.inl rfl)
  have he := SyntaxTypeLocalTransfer.iff_trans
    (PacketTokenRootEquation.condition_iff hZ1 w.castSucc B.castSucc C.castSucc (Fin.last m) n.castSucc t.castSucc a.castSucc r.castSucc hw1 hB1 hC1 hv hr1)
    (PacketTokenArithmeticBridge.criterion_iff hZ1 w.castSucc B.castSucc C.castSucc (Fin.last m) n.castSucc t.castSucc a.castSucc hw1 hB1 hC1 hv)
  exact of_eq (by simp only [Formula.raise,Formula.iff,Formula.rename,PacketTraceSyntax.condition_rename,criterion_rename]) he

theorem accepted_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) : Derives Γ ((accepted w n t a).iff (criterion w B C n t a)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := accepted w n t a
    let R := (row w.castSucc n.castSucc t.castSucc a.castSucc (Fin.last m)).conj (PacketTraceSyntax.condition w.castSucc (Fin.last m))
    let Δ := Context.add R (Context.image Formula.raise (Context.add H Γ))
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ H) R
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw H) R)
    have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under (add hB H) R)
    have hC1 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C Fin.castSucc) (under (add hC H) R)
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    exact of_eq (criterion_rename w B C n t a Fin.castSucc).symm
      (.impE (.conjL (condition_iff hZ1 w.castSucc B.castSucc C.castSucc n.castSucc t.castSucc a.castSucc (Fin.last m) hw1 hB1 hC1 (.conjL hR))) (.conjR hR))
  · apply Derives.impI
    let H := criterion w B C n t a
    let ΓH := Context.add H Γ
    have hH : Derives ΓH H := .hyp (Or.inl rfl)
    have hZH := ZFContext.add hZ H
    have hwH := add hw H
    let env := SyntaxAtomSyntax.three n t a
    have hn := PacketTokenAcceptedNatural.criterion_environment hZH w B C n t a hwH hH
    have hi := SyntaxForestSyntax.intro_inputs 3 w env (fun i => HornExprSyntax.environmentNat_at w env hn i)
    have he := SyntaxConstructors.exists_constructor hZH 3 2 w env hwH hi
    let R := (Formula.mem (Fin.last m) w.castSucc).conj (row w.castSucc n.castSucc t.castSucc a.castSucc (Fin.last m))
    let Δ := Context.add R (Context.image Formula.raise ΓH)
    apply Derives.exE (p := R) he
    have hZ1 := ZFContext.under hZH R
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under hwH R)
    have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under (add hB H) R)
    have hC1 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C Fin.castSucc) (under (add hC H) R)
    have hH1 := of_eq (criterion_rename w B C n t a Fin.castSucc) (under hH R)
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hc := Derives.impE (.conjR (condition_iff hZ1 w.castSucc B.castSucc C.castSucc n.castSucc t.castSucc a.castSucc (Fin.last m) hw1 hB1 hC1 (.conjR hR))) hH1
    exact of_eq (accepted_rename w n t a Fin.castSucc).symm
      (intro_accepted w.castSucc n.castSucc t.castSucc a.castSucc (Fin.last m) (.conjR hR) hc)

end PPAC.Migration.Internal.PacketTokenArithmeticEquation
