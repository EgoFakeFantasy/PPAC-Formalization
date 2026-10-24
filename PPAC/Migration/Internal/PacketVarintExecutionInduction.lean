import PPAC.Migration.Internal.PacketVarintExecutionUnique

/-! Original Foundation and full Separation discharge the joint existence/byte-domain/uniqueness IH. -/
namespace PPAC.Migration.Internal.PacketVarintExecutionInduction
open Source SourceAlgebra SourceLogic OmegaSyntax PacketVarintExecutionSyntax
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def allProperties {m} (w : Fin m) : Formula m := .all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc (Fin.last m)))

theorem allProperties_rename {m k} (w : Fin m) (ρ : Fin m → Fin k) : (allProperties w).rename ρ = allProperties (ρ w) := by
  simp only [allProperties,Formula.rename,property_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem property_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hn : Derives Γ (.mem n w)) (hi : Derives Γ (earlier w n)) : Derives Γ (property w n) :=
  .conjI (PacketVarintExecutionTotal.point hZ w B n hw hB hn hi)
    (.conjI (PacketVarintExecutionDomain.domain_property hZ w B C n hw hB hC hi) (PacketVarintExecutionUnique.unique_property hZ w B n hw hB hi))

theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) :
    Derives Γ (BoundedInduction.progressive PacketVarintExecutionSyntax.matrix (fun _ : Fin 1 => w) w) := by
  simp only [BoundedInduction.progressive,BoundedInduction.below,PacketVarintExecutionSyntax.matrix_pred,paramsUp]
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
  exact property_from_earlier hZ1 w.castSucc B.castSucc C.castSucc (Fin.last m) hw1 hB1 hC1 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem all_properties_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) : Derives Γ (allProperties w) := by
  have h := BoundedInduction.induction_on_set PacketVarintExecutionSyntax.matrix (fun _ : Fin 1 => w) w
    (ZFContext.separation hZ PacketVarintExecutionSyntax.matrix.neg) (ZFContext.arithmetic hZ).base.foundation (progressive hZ w B C hw hB hC)
  simpa only [allProperties,BoundedInduction.holds,PacketVarintExecutionSyntax.matrix_pred,paramsUp] using h

end PPAC.Migration.Internal.PacketVarintExecutionInduction
