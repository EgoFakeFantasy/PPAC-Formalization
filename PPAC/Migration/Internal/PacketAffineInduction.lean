import PPAC.Migration.Internal.PacketAffineInductionPoint

/-! Original object omega induction discharges the full internal tail IH; no host Nat induction. -/
namespace PPAC.Migration.Internal.PacketAffineInduction
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketAffineInductionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem zero_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B V z : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hv : Derives Γ (PacketTraceCore.value w V)) (hz : Derives Γ (empty z)) : Derives Γ (correct wide w B V z) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let R := PacketHornAffineSyntax.row wide (old 3 w : Fin (m+3)) (slot 3 0) (old 3 z) (slot 3 1) (slot 3 2)
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hB3 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B (old 3)) (HornBinderRules.under_body 3 hB R)
  have hv3 := of_eq (PacketTraceCore.value_rename w V (old 3)) (HornBinderRules.under_body 3 hv R)
  have hz3 := of_eq (empty_rename z (old 3)) (HornBinderRules.under_body 3 hz R)
  exact PacketAffineInductionPoint.zero (HornBinderRules.zf_body 3 hZ R) wide (old 3 w) (old 3 B) (old 3 V)
    (slot 3 0) (old 3 z) (slot 3 1) (slot 3 2) hw3 hB3 hv3 hz3 (.hyp (Or.inl rfl))

theorem successor_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B V t s : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hv : Derives Γ (PacketTraceCore.value w V)) (ht : Derives Γ (.mem t w)) (hI : Derives Γ (correct wide w B V t))
    (hs : Derives Γ (successor s t)) : Derives Γ (correct wide w B V s) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let R := PacketHornAffineSyntax.row wide (old 3 w : Fin (m+3)) (slot 3 0) (old 3 s) (slot 3 1) (slot 3 2)
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hB3 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B (old 3)) (HornBinderRules.under_body 3 hB R)
  have hv3 := of_eq (PacketTraceCore.value_rename w V (old 3)) (HornBinderRules.under_body 3 hv R)
  have ht3 : Derives (Context.add R (raisedContext 3 Γ)) (.mem (old 3 t) (old 3 w)) := HornBinderRules.under_body 3 ht R
  have hI3 := of_eq (correct_rename wide w B V t (old 3)) (HornBinderRules.under_body 3 hI R)
  have hs3 := of_eq (successor_rename s t (old 3)) (HornBinderRules.under_body 3 hs R)
  exact PacketAffineInductionPoint.successor (HornBinderRules.zf_body 3 hZ R) wide (old 3 w) (old 3 B) (old 3 V)
    (slot 3 0) (old 3 t) (old 3 s) (slot 3 1) (slot 3 2) hw3 hB3 hv3 ht3 hI3 hs3 (.hyp (Or.inl rfl))

theorem base {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B V : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hv : Derives Γ (PacketTraceCore.value w V)) :
    Derives Γ (OmegaInductionSyntax.base (matrix wide) (NaturalAdditionTransport.params3 w B V)) := by
  simp only [OmegaInductionSyntax.base, PacketAffineInductionSyntax.matrix_pred, ReplacementPredicates.paramsUp,
    NaturalAdditionTransport.params3_0, NaturalAdditionTransport.params3_1, NaturalAdditionTransport.params3_2]
  apply Derives.allI
  apply Derives.impI
  let Z := empty (Fin.last m)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw Z)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B Fin.castSucc) (under hB Z)
  have hv1 := of_eq (PacketTraceCore.value_rename w V Fin.castSucc) (under hv Z)
  exact zero_property (ZFContext.under hZ Z) wide w.castSucc B.castSucc V.castSucc (Fin.last m) hw1 hB1 hv1 (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B V : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hv : Derives Γ (PacketTraceCore.value w V)) :
    Derives Γ (OmegaInductionSyntax.step (matrix wide) (NaturalAdditionTransport.params3 w B V) w) := by
  simp only [OmegaInductionSyntax.step, PacketAffineInductionSyntax.matrix_pred, ReplacementPredicates.paramsUp,
    NaturalAdditionTransport.params3_0, NaturalAdditionTransport.params3_1, NaturalAdditionTransport.params3_2]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let N := Formula.mem (slot 2 0 : Fin (m+2)) (old 2 w)
  let I := correct wide (old 2 w) (old 2 B) (old 2 V) (slot 2 0)
  let S := successor (slot 2 1 : Fin (m+2)) (slot 2 0)
  let Δ := Context.add S (Context.add I (Context.add N (raisedContext 2 Γ)))
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_many 2 hw)
  have hB2 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B (old 2)) (HornBinderRules.under_many 2 hB)
  have hv2 := of_eq (PacketTraceCore.value_rename w V (old 2)) (HornBinderRules.under_many 2 hv)
  have hZ2 := ZFContext.add (ZFContext.add (ZFContext.add (HornBinderRules.zf_many 2 hZ) N) I) S
  have hN : Derives Δ N := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have hI : Derives Δ I := .hyp (Or.inr (Or.inl rfl))
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  exact successor_property hZ2 wide (old 2 w) (old 2 B) (old 2 V) (slot 2 0) (slot 2 1)
    (add (add (add hw2 N) I) S) (add (add (add hB2 N) I) S) (add (add (add hv2 N) I) S) hN hI hS

theorem all_correct {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B V : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hv : Derives Γ (PacketTraceCore.value w V)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (correct wide w.castSucc B.castSucc V.castSucc (Fin.last m)))) := by
  have hi := ZFArithmetic.induction hZ (matrix wide) (NaturalAdditionTransport.params3 w B V) w hw
    (base hZ wide w B V hw hB hv) (step hZ wide w B V hw hB hv)
  simpa only [OmegaInductionSyntax.holds, PacketAffineInductionSyntax.matrix_pred, ReplacementPredicates.paramsUp,
    NaturalAdditionTransport.params3_0, NaturalAdditionTransport.params3_1, NaturalAdditionTransport.params3_2] using hi

theorem membership_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B V d t n r : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hv : Derives Γ (PacketTraceCore.value w V)) (hr : Derives Γ (PacketHornAffineSyntax.row wide w d t n r)) :
    Derives Γ ((Formula.mem r V).iff (PacketAffineSyntax.affine w B d t n)) := by
  have ht : Derives Γ (.mem t w) := HornExprSyntax.environmentNat_at w (SyntaxAtomSyntax.three d t n)
    (PacketAffineApplicationNatural.row_environment hZ wide w d t n r hw hr) 1
  have hi := Derives.allE t (all_correct hZ wide w B V hw hB hv)
  have hI : Derives Γ (correct wide w B V t) := .impE
    (of_eq (by simp only [Formula.instantiate, Formula.rename, correct_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hi) ht
  exact at_correct wide w B V t d n r hI hr

end PPAC.Migration.Internal.PacketAffineInduction
