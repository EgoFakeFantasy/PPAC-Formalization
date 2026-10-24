import PPAC.Migration.Internal.PacketTokenBoundsPoint

/-! Original Foundation/Separation quotient induction discharges all quantitative runtime IH. -/
namespace PPAC.Migration.Internal.PacketTokenBoundsInduction
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketTokenBoundsSyntax PacketTokenAcceptedSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem small_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hn : Derives Γ (.mem n B)) : Derives Γ (property w n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := accepted (old 2 w : Fin (m+2)) (old 2 n) (slot 2 0) (slot 2 1)
  have hZ2 := HornBinderRules.zf_body 2 hZ H
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw H)
  have hB2 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 2)) (HornBinderRules.under_body 2 hB H)
  have hC2 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 2)) (HornBinderRules.under_body 2 hC H)
  have hn2 : Derives (Context.add H (raisedContext 2 Γ)) (.mem (old 2 n) (old 2 B)) := HornBinderRules.under_body 2 hn H
  exact PacketTokenBoundsPoint.small_point hZ2 (old 2 w) (old 2 B) (old 2 C) (old 2 n) (slot 2 0) (slot 2 1) hw2 hB2 hC2 hn2 (.hyp (Or.inl rfl))

theorem large_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n d q : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (h0 : Derives Γ (PacketAffineSyntax.affine w B d q n))
    (hn : Derives Γ (Formula.mem n B).neg) (hp : Derives Γ (property w q)) : Derives Γ (property w n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := accepted (old 2 w : Fin (m+2)) (old 2 n) (slot 2 0) (slot 2 1)
  have hZ2 := HornBinderRules.zf_body 2 hZ H
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw H)
  have hB2 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 2)) (HornBinderRules.under_body 2 hB H)
  have hC2 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 2)) (HornBinderRules.under_body 2 hC H)
  have h02 := of_eq (PacketAffineSyntax.affine_rename w B d q n (old 2)) (HornBinderRules.under_body 2 h0 H)
  have hp2 := of_eq (property_rename w q (old 2)) (HornBinderRules.under_body 2 hp H)
  have hn2 : Derives (Context.add H (raisedContext 2 Γ)) (Formula.mem (old 2 n) (old 2 B)).neg := HornBinderRules.under_body 2 hn H
  exact PacketTokenBoundsPoint.large_point hZ2 (old 2 w) (old 2 B) (old 2 C) (old 2 n) (old 2 d) (old 2 q) (slot 2 0) (slot 2 1)
    hw2 hB2 hC2 h02 hn2 hp2 (.hyp (Or.inl rfl))

theorem base {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) :
    Derives Γ (PacketQuotientInductionSyntax.base PacketTokenBoundsSyntax.matrix (fun _ : Fin 1 => w) w B) := by
  simp only [PacketQuotientInductionSyntax.base,PacketTokenBoundsSyntax.matrix_pred,ReplacementPredicates.paramsUp]
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let N := Formula.mem (Fin.last m) w.castSucc
  let S := Formula.mem (Fin.last m) B.castSucc
  have hZ1 := ZFContext.add (ZFContext.add (ZFContext.rename hZ Fin.castSucc) N) S
  have hw1 := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (Derives.rename Fin.castSucc hB)
  have hC1 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C Fin.castSucc) (Derives.rename Fin.castSucc hC)
  exact small_property hZ1 w.castSucc B.castSucc C.castSucc (Fin.last m) (add (add hw1 N) S) (add (add hB1 N) S)
    (add (add hC1 N) S) (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) :
    Derives Γ (PacketQuotientInductionSyntax.step PacketTokenBoundsSyntax.matrix (fun _ : Fin 1 => w) w B) := by
  simp only [PacketQuotientInductionSyntax.step,PacketQuotientInductionSyntax.stepBody,PacketTokenBoundsSyntax.matrix_pred]
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let N := Formula.mem (slot 3 0 : Fin (m+3)) (old 3 w)
  let S := (Formula.mem (slot 3 0 : Fin (m+3)) (old 3 B)).neg
  let A := PacketAffineSyntax.affine (old 3 w : Fin (m+3)) (old 3 B) (slot 3 1) (slot 3 2) (slot 3 0)
  let I := property (old 3 w : Fin (m+3)) (slot 3 2)
  let Δ := Context.add I (Context.add A (Context.add S (Context.add N (raisedContext 3 Γ))))
  have hZ3 := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (HornBinderRules.zf_many 3 hZ) N) S) A) I
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_many 3 hw)
  have hB3 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 3)) (HornBinderRules.under_many 3 hB)
  have hC3 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 3)) (HornBinderRules.under_many 3 hC)
  have hS : Derives Δ S := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have hA : Derives Δ A := .hyp (Or.inr (Or.inl rfl))
  have hI : Derives Δ I := .hyp (Or.inl rfl)
  exact large_property hZ3 (old 3 w) (old 3 B) (old 3 C) (slot 3 0) (slot 3 1) (slot 3 2)
    (add (add (add (add hw3 N) S) A) I) (add (add (add (add hB3 N) S) A) I) (add (add (add (add hC3 N) S) A) I) hA hS hI

theorem all_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc (Fin.last m)))) := by
  have hi := PacketQuotientInduction.all_holds hZ false PacketTokenBoundsSyntax.matrix (fun _ : Fin 1 => w) w B hw hB
    (base hZ w B C hw hB hC) (step hZ w B C hw hB hC)
  simpa only [BoundedInduction.holds,PacketTokenBoundsSyntax.matrix_pred,ReplacementPredicates.paramsUp] using hi

theorem bounds_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (ha : Derives Γ (accepted w n t a)) : Derives Γ (bounds n t a) := by
  have hn := HornExprSyntax.environmentNat_at w (SyntaxAtomSyntax.three n t a)
    (PacketTokenAcceptedNatural.accepted_environment hZ w n t a hw ha) 0
  have hi : Derives Γ ((Formula.mem n w).imp (property w n)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq])
      (Derives.allE n (all_property hZ w B C hw hB hC))
  exact property_at w n t a (.impE hi hn) ha

end PPAC.Migration.Internal.PacketTokenBoundsInduction
