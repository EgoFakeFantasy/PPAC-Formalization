import PPAC.Migration.Internal.PacketTokenPrefixPoint

/-! Original quotient induction discharges all internal IH for actual token prefix inversion. -/
namespace PPAC.Migration.Internal.PacketTokenPrefixInduction
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketTokenPrefixSyntax PacketTokenAcceptedSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem small_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hn : Derives Γ (.mem n B)) : Derives Γ (property w n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let H := accepted (old 4 w : Fin (m+4)) (old 4 n) (slot 4 0) (slot 4 1)
  let K := accepted (old 4 w : Fin (m+4)) (slot 4 2) (slot 4 3) (slot 4 1)
  let Δ := Context.add K (Context.add H (raisedContext 4 Γ))
  have hZ3 := ZFContext.add (ZFContext.add (HornBinderRules.zf_many 4 hZ) H) K
  have hw3 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_many 4 hw)
  have hB3 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 4)) (HornBinderRules.under_many 4 hB)
  have hC3 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 4)) (HornBinderRules.under_many 4 hC)
  have hn3 : Derives (raisedContext 4 Γ) (.mem (old 4 n) (old 4 B)) := HornBinderRules.under_many 4 hn
  have hH : Derives Δ H := .hyp (Or.inr (Or.inl rfl))
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  exact PacketTokenPrefixPoint.small_point hZ3 (old 4 w) (old 4 B) (old 4 C) (old 4 n) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
    (add (add hw3 H) K) (add (add hB3 H) K) (add (add hC3 H) K) (add (add hn3 H) K) hH hK

theorem large_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n d q : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (h0 : Derives Γ (PacketAffineSyntax.affine w B d q n))
    (hn : Derives Γ (Formula.mem n B).neg) (hp : Derives Γ (property w q)) : Derives Γ (property w n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let H := accepted (old 4 w : Fin (m+4)) (old 4 n) (slot 4 0) (slot 4 1)
  let K := accepted (old 4 w : Fin (m+4)) (slot 4 2) (slot 4 3) (slot 4 1)
  let Δ := Context.add K (Context.add H (raisedContext 4 Γ))
  have hZ3 := ZFContext.add (ZFContext.add (HornBinderRules.zf_many 4 hZ) H) K
  have hw3 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_many 4 hw)
  have hB3 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 4)) (HornBinderRules.under_many 4 hB)
  have hC3 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 4)) (HornBinderRules.under_many 4 hC)
  have h03 := of_eq (PacketAffineSyntax.affine_rename w B d q n (old 4)) (HornBinderRules.under_many 4 h0)
  have hp3 := of_eq (property_rename w q (old 4)) (HornBinderRules.under_many 4 hp)
  have hn3 : Derives (raisedContext 4 Γ) (Formula.mem (old 4 n) (old 4 B)).neg := HornBinderRules.under_many 4 hn
  have hH : Derives Δ H := .hyp (Or.inr (Or.inl rfl))
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  exact PacketTokenPrefixPoint.large_point hZ3 (old 4 w) (old 4 B) (old 4 C) (old 4 n) (old 4 d) (old 4 q) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
    (add (add hw3 H) K) (add (add hB3 H) K) (add (add hC3 H) K) (add (add h03 H) K)
    (add (add hn3 H) K) (add (add hp3 H) K) hH hK

theorem base {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) :
    Derives Γ (PacketQuotientInductionSyntax.base PacketTokenPrefixSyntax.matrix (fun _ : Fin 1 => w) w B) := by
  simp only [PacketQuotientInductionSyntax.base,PacketTokenPrefixSyntax.matrix_pred,ReplacementPredicates.paramsUp]
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
    Derives Γ (PacketQuotientInductionSyntax.step PacketTokenPrefixSyntax.matrix (fun _ : Fin 1 => w) w B) := by
  simp only [PacketQuotientInductionSyntax.step,PacketQuotientInductionSyntax.stepBody,PacketTokenPrefixSyntax.matrix_pred]
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
  have hi := PacketQuotientInduction.all_holds hZ false PacketTokenPrefixSyntax.matrix (fun _ : Fin 1 => w) w B hw hB
    (base hZ w B C hw hB hC) (step hZ w B C hw hB hC)
  simpa only [BoundedInduction.holds,PacketTokenPrefixSyntax.matrix_pred,ReplacementPredicates.paramsUp] using hi

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a k s : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (ha : Derives Γ (accepted w n t a)) (hb : Derives Γ (accepted w k s a)) : Derives Γ ((Formula.equal n k).conj (.equal t s)) := by
  have hn := HornExprSyntax.environmentNat_at w (SyntaxAtomSyntax.three n t a)
    (PacketTokenAcceptedNatural.accepted_environment hZ w n t a hw ha) 0
  have hi : Derives Γ ((Formula.mem n w).imp (property w n)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq])
      (Derives.allE n (all_property hZ w B C hw hB hC))
  exact property_at w n t a k s (.impE hi hn) ha hb

end PPAC.Migration.Internal.PacketTokenPrefixInduction
