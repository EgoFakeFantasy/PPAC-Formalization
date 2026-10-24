import PPAC.Migration.Internal.PacketAffineApplicationNatural

/-! Complete original arity blocks are eliminated in both directions, with real search bounds discharged. -/
namespace PPAC.Migration.Internal.PacketAffineApplication
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax PacketAffineApplicationSyntax
open SyntaxRenameQuerySyntax (of_eq)
open PacketAffineRuleData (baseRule stepRule radix)

theorem base_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B r V : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (radix wide) B))
    (ha : Derives Γ (HornApplicationSyntax.application (baseRule wide) w r V)) : Derives Γ (baseOutcome wide w B r) := by
  let C := HornApplicationSyntax.body (baseRule wide) w r V
  let Δ := Context.add C (raisedContext 1 Γ)
  apply HornApplicationRules.eliminate_application (baseRule wide) w r V _ ha
  have hw1 := of_eq (omega_rename w (old 1)) (HornBinderRules.under_body 1 hw C)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename (radix wide) B (old 1)) (HornBinderRules.under_body 1 hB C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hb := PacketHornAffineLocal.base_forward (HornBinderRules.zf_body 1 hZ C) wide (old 1 w) (old 1 B)
    (old 1 r) (old 1 V) (slot 1) hw1 (.conjL hC) hB1 (.conjR (.conjR hC))
  exact of_eq (baseOutcome_rename wide w B r (old 1)).symm
    (PacketAffineApplicationSyntax.intro_base wide (old 1 w) (old 1 B) (old 1 r) (slot 1 0) hb)

theorem base_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B r V : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (radix wide) B))
    (hb : Derives Γ (baseOutcome wide w B r)) : Derives Γ (HornApplicationSyntax.application (baseRule wide) w r V) := by
  let P := PacketHornAffineSyntax.base wide w.castSucc B.castSucc (Fin.last m) r.castSucc
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) hb
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename (radix wide) B Fin.castSucc) (under hB P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hd := PacketAffineApplicationNatural.base_digit hZ1 wide w.castSucc B.castSucc (Fin.last m) r.castSucc hw1 hP
  have hn : Derives Δ (environmentNat 1 w.castSucc (fun _ => Fin.last m)) := .conjI hd HornRuleSyntax.truth_proved
  have hm := PacketHornAffineLocal.base_backward hZ1 wide w.castSucc B.castSucc r.castSucc V.castSucc
    (fun _ => Fin.last m) hw1 hn hB1 hP
  exact of_eq (HornApplicationSyntax.application_rename (baseRule wide) w r V Fin.castSucc).symm
    (PacketAffineApplicationBounds.base_intro hZ1 wide w.castSucc r.castSucc V.castSucc (fun _ => Fin.last m) hw1 hn hm)

theorem base_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B r V : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (radix wide) B)) :
    Derives Γ ((HornApplicationSyntax.application (baseRule wide) w r V).iff (baseOutcome wide w B r)) := by
  apply Derives.conjI
  · exact .impI (base_forward (ZFContext.add hZ _) wide w B r V (add hw _) (add hB _) (.hyp (Or.inl rfl)))
  · exact .impI (base_backward (ZFContext.add hZ _) wide w B r V (add hw _) (add hB _) (.hyp (Or.inl rfl)))

theorem step_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B r V : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (radix wide) B))
    (ha : Derives Γ (HornApplicationSyntax.application (stepRule wide) w r V)) : Derives Γ (stepOutcome wide w B V r) := by
  let C := HornApplicationSyntax.body (stepRule wide) w r V
  let Δ := Context.add C (raisedContext 3 Γ)
  apply HornApplicationRules.eliminate_application (stepRule wide) w r V _ ha
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw C)
  have hB3 := of_eq (SyntaxNumeralSyntax.numeral_rename (radix wide) B (old 3)) (HornBinderRules.under_body 3 hB C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hs := PacketHornAffineLocal.step_forward (HornBinderRules.zf_body 3 hZ C) wide (old 3 w) (old 3 B)
    (old 3 r) (old 3 V) (slot 3) hw3 (.conjL hC) hB3 (.conjR (.conjR hC))
  exact of_eq (stepOutcome_rename wide w B V r (old 3)).symm
    (PacketAffineApplicationSyntax.intro_step wide (old 3 w) (old 3 B) (old 3 V) (old 3 r) (slot 3 0) (slot 3 1) (slot 3 2) hs)

theorem step_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B r V : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (radix wide) B))
    (hs : Derives Γ (stepOutcome wide w B V r)) : Derives Γ (HornApplicationSyntax.application (stepRule wide) w r V) := by
  let C := stepOutcomeBody wide w B V r
  let Δ := Context.add C (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 C _ hs
  have hZ3 := HornBinderRules.zf_body 3 hZ C
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw C)
  have hB3 := of_eq (SyntaxNumeralSyntax.numeral_rename (radix wide) B (old 3)) (HornBinderRules.under_body 3 hB C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hn := PacketAffineApplicationNatural.step_environment hZ3 wide (old 3 w) (old 3 B) (old 3 V)
    (slot 3 0) (slot 3 1) (slot 3 2) (old 3 r) hw3 hC
  have hm := PacketHornAffineLocal.step_backward hZ3 wide (old 3 w) (old 3 B) (old 3 r) (old 3 V)
    (SyntaxAtomSyntax.three (slot 3 0) (slot 3 1) (slot 3 2)) hw3 hn hB3 hC
  exact of_eq (HornApplicationSyntax.application_rename (stepRule wide) w r V (old 3)).symm
    (PacketAffineApplicationBounds.step_intro hZ3 wide (old 3 w) (old 3 r) (old 3 V)
      (SyntaxAtomSyntax.three (slot 3 0) (slot 3 1) (slot 3 2)) hw3 hn hm)

theorem step_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B r V : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (radix wide) B)) :
    Derives Γ ((HornApplicationSyntax.application (stepRule wide) w r V).iff (stepOutcome wide w B V r)) := by
  apply Derives.conjI
  · exact .impI (step_forward (ZFContext.add hZ _) wide w B r V (add hw _) (add hB _) (.hyp (Or.inl rfl)))
  · exact .impI (step_backward (ZFContext.add hZ _) wide w B r V (add hw _) (add hB _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketAffineApplication
