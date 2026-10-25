import PPAC.Migration.Internal.PacketTokenCanonicalStep

/-! Original Foundation and Separation on the fixed comparison matrix discharge all smaller token-prefix IH. -/
namespace PPAC.Migration.Internal.PacketTokenCanonicalInduction
open Source SourceAlgebra SourceLogic OmegaSyntax PacketTokenCanonicalSyntax
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) :
    Derives Γ (BoundedInduction.progressive PacketTokenCanonicalSyntax.matrix (fun _ : Fin 1 => w) w) := by
  simp only [BoundedInduction.progressive,BoundedInduction.below,PacketTokenCanonicalSyntax.matrix_pred,paramsUp]
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let N := Formula.mem (Fin.last m) w.castSucc
  let I := earlier w.castSucc (Fin.last m)
  let Δ := Context.add I (Context.add N (Context.image Formula.raise Γ))
  have hZ1 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.rename hZ Fin.castSucc) N) I
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise,omega_rename] using add (add (Derives.rename Fin.castSucc hw) N) I
  have hB1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B.castSucc) := by simpa only [Formula.raise,SyntaxNumeralSyntax.numeral_rename] using add (add (Derives.rename Fin.castSucc hB) N) I
  have hC1 : Derives Δ (SyntaxNumeralSyntax.numeral 256 C.castSucc) := by simpa only [Formula.raise,SyntaxNumeralSyntax.numeral_rename] using add (add (Derives.rename Fin.castSucc hC) N) I
  exact PacketTokenCanonicalStep.property_step hZ1 w.castSucc B.castSucc C.castSucc (Fin.last m) hw1 hB1 hC1 (.hyp (Or.inl rfl))

theorem all_properties_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) : Derives Γ (allProperties w) := by
  have h := BoundedInduction.induction_on_set PacketTokenCanonicalSyntax.matrix (fun _ : Fin 1 => w) w
    (ZFContext.separation hZ PacketTokenCanonicalSyntax.matrix.neg) (ZFContext.arithmetic hZ).base.foundation (progressive hZ w B C hw hB hC)
  simpa only [allProperties,BoundedInduction.holds,PacketTokenCanonicalSyntax.matrix_pred,paramsUp] using h

end PPAC.Migration.Internal.PacketTokenCanonicalInduction
