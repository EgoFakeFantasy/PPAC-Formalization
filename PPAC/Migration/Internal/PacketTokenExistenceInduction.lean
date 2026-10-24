import PPAC.Migration.Internal.PacketTokenExistencePoint

/-! Original quotient induction discharges every internal input IH of actual token existence. -/
namespace PPAC.Migration.Internal.PacketTokenExistenceInduction
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketTokenExistenceSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem small_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hn : Derives Γ (.mem n B)) : Derives Γ (property w n) := by
  apply Derives.allI
  apply Derives.impI
  let H := Formula.mem (Fin.last m) w.castSucc
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw H)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under hB H)
  have hC1 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C Fin.castSucc) (under hC H)
  exact PacketTokenExistencePoint.small_point (ZFContext.under hZ H) w.castSucc B.castSucc C.castSucc n.castSucc (Fin.last m)
    hw1 hB1 hC1 (under hn H) (.hyp (Or.inl rfl))

theorem large_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n d q : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (h0 : Derives Γ (PacketAffineSyntax.affine w B d q n))
    (hn : Derives Γ (Formula.mem n B).neg) (hp : Derives Γ (property w q)) : Derives Γ (property w n) := by
  apply Derives.allI
  apply Derives.impI
  let H := Formula.mem (Fin.last m) w.castSucc
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw H)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under hB H)
  have hC1 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C Fin.castSucc) (under hC H)
  have h01 := of_eq (PacketAffineSyntax.affine_rename w B d q n Fin.castSucc) (under h0 H)
  have hp1 := of_eq (property_rename w q Fin.castSucc) (under hp H)
  exact PacketTokenExistencePoint.large_point (ZFContext.under hZ H) w.castSucc B.castSucc C.castSucc n.castSucc d.castSucc q.castSucc (Fin.last m)
    hw1 hB1 hC1 h01 (under hn H) hp1 (.hyp (Or.inl rfl))

theorem base {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) :
    Derives Γ (PacketQuotientInductionSyntax.base PacketTokenExistenceSyntax.matrix (fun _ : Fin 1 => w) w B) := by
  simp only [PacketQuotientInductionSyntax.base,PacketTokenExistenceSyntax.matrix_pred,ReplacementPredicates.paramsUp]
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
    Derives Γ (PacketQuotientInductionSyntax.step PacketTokenExistenceSyntax.matrix (fun _ : Fin 1 => w) w B) := by
  simp only [PacketQuotientInductionSyntax.step,PacketQuotientInductionSyntax.stepBody,PacketTokenExistenceSyntax.matrix_pred]
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
  have hi := PacketQuotientInduction.all_holds hZ false PacketTokenExistenceSyntax.matrix (fun _ : Fin 1 => w) w B hw hB
    (base hZ w B C hw hB hC) (step hZ w B C hw hB hC)
  simpa only [BoundedInduction.holds,PacketTokenExistenceSyntax.matrix_pred,ReplacementPredicates.paramsUp] using hi

theorem exists_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hn : Derives Γ (.mem n w)) (ht : Derives Γ (.mem t w)) : Derives Γ (existsOutput w n t) := by
  have hi : Derives Γ ((Formula.mem n w).imp (property w n)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq])
      (Derives.allE n (all_property hZ w B C hw hB hC))
  exact property_at w n t (.impE hi hn) ht

end PPAC.Migration.Internal.PacketTokenExistenceInduction
