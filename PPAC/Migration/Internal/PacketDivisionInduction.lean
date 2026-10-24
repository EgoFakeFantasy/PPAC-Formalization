import PPAC.Migration.Internal.PacketDivisionStep

/-! Original object omega induction on the output constructs every internal radix decomposition. -/
namespace PPAC.Migration.Internal.PacketDivisionInduction
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketDivisionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem zero_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B z : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hz : Derives Γ (empty z)) : Derives Γ (decomposes w B z) := by
  have hBN := SyntaxNumerals.range hZ (PacketAffineRuleData.radix wide) w B hw hB
  have hzN := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have hzB := PacketAffineLiteral.zero_below hZ wide w B z (.conjI hBN hB) hz
  have hp := ZFArithmetic.mul_zero hZ w B z z hw hBN hz hz
  have hs := ZFArithmetic.add_zero hZ w z z hw hzN hz
  exact intro_decomposes w B z z z (PacketAffineSyntax.intro_affine w B z z z z hBN hzB hzN hzN hp hs)

theorem base {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B)) :
    Derives Γ (OmegaInductionSyntax.base PacketDivisionSyntax.matrix (Source.SetLanguage.args2 w B)) := by
  simp only [OmegaInductionSyntax.base, PacketDivisionSyntax.matrix_pred, ReplacementPredicates.paramsUp, PairSyntax.args2_first, PairSyntax.args2_second]
  apply Derives.allI
  apply Derives.impI
  let Z := empty (Fin.last m)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw Z)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B Fin.castSucc) (under hB Z)
  exact zero_point (ZFContext.under hZ Z) wide w.castSucc B.castSucc (Fin.last m) hw1 hB1 (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B)) :
    Derives Γ (OmegaInductionSyntax.step PacketDivisionSyntax.matrix (Source.SetLanguage.args2 w B) w) := by
  simp only [OmegaInductionSyntax.step, PacketDivisionSyntax.matrix_pred, ReplacementPredicates.paramsUp, PairSyntax.args2_first, PairSyntax.args2_second]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let N := Formula.mem (slot 2 0 : Fin (m+2)) (old 2 w)
  let I := decomposes (old 2 w) (old 2 B) (slot 2 0)
  let S := successor (slot 2 1 : Fin (m+2)) (slot 2 0)
  let Δ := Context.add S (Context.add I (Context.add N (raisedContext 2 Γ)))
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_many 2 hw)
  have hB2 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B (old 2)) (HornBinderRules.under_many 2 hB)
  have hZ2 := ZFContext.add (ZFContext.add (ZFContext.add (HornBinderRules.zf_many 2 hZ) N) I) S
  have hI : Derives Δ I := .hyp (Or.inr (Or.inl rfl))
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  exact PacketDivisionStep.from_decomposition hZ2 wide (old 2 w) (old 2 B) (slot 2 0) (slot 2 1)
    (add (add (add hw2 N) I) S) (add (add (add hB2 N) I) S) hI hS

theorem all_decomposes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (decomposes w.castSucc B.castSucc (Fin.last m)))) := by
  have hi := ZFArithmetic.induction hZ PacketDivisionSyntax.matrix (Source.SetLanguage.args2 w B) w hw (base hZ wide w B hw hB) (step hZ wide w B hw hB)
  simpa only [OmegaInductionSyntax.holds, PacketDivisionSyntax.matrix_pred, ReplacementPredicates.paramsUp, PairSyntax.args2_first, PairSyntax.args2_second] using hi

theorem exists_decomposition {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hn : Derives Γ (.mem n w)) : Derives Γ (decomposes w B n) := by
  have hi := Derives.allE n (all_decomposes hZ wide w B hw hB)
  have hh : Derives Γ ((Formula.mem n w).imp (decomposes w B n)) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, decomposes_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hi
  exact .impE hh hn

end PPAC.Migration.Internal.PacketDivisionInduction
