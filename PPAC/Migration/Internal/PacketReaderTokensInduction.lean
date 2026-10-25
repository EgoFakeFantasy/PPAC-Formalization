import PPAC.Migration.Internal.PacketReaderTokensStep

/-! Full original Separation and Foundation discharge all token-tail assumptions; exact multitoken output order holds on every internal code and return candidate. -/
namespace PPAC.Migration.Internal.PacketReaderTokensInduction
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderTokensSyntax
open ReplacementPredicates (paramsUp)
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z)) :
    Derives Γ (BoundedInduction.progressive PacketReaderTokensSyntax.matrix (PacketVarintPrefixRecursionSyntax.four w B z o) w) := by
  simp only [BoundedInduction.progressive,BoundedInduction.below,PacketReaderTokensSyntax.matrix_pred,paramsUp,PacketVarintPrefixRecursionSyntax.four]
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let N := Formula.mem (Fin.last m) w.castSucc
  let I := earlier w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m)
  let Δ := Context.add I (Context.add N (Context.image Formula.raise Γ))
  have hZ1 := ZFContext.add (ZFContext.add (ZFContext.rename hZ Fin.castSucc) N) I
  have lift {φ : Formula m} (hh : Derives Γ φ) : Derives Δ φ.raise := add (add (Derives.rename Fin.castSucc hh) N) I
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise,omega_rename] using lift hw
  have hB1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B.castSucc) := by simpa only [Formula.raise,SyntaxNumeralSyntax.numeral_rename] using lift hB
  have hz1 : Derives Δ (empty z.castSucc) := by simpa only [Formula.raise,empty_rename] using lift hz
  have ho1 : Derives Δ (successor o.castSucc z.castSucc) := by simpa only [Formula.raise,successor_rename] using lift ho
  exact PacketReaderTokensStep.property_from_earlier hZ1 w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m) hw1 hB1 hz1 ho1 (.hyp (Or.inl rfl))

theorem all_properties {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z)) :
    Derives Γ (allProperties w B z o) := by
  have h := BoundedInduction.induction_on_set PacketReaderTokensSyntax.matrix (PacketVarintPrefixRecursionSyntax.four w B z o) w
    (ZFContext.separation hZ PacketReaderTokensSyntax.matrix.neg) (ZFContext.arithmetic hZ).base.foundation (progressive hZ w B z o hw hB hz ho)
  have h0 : PacketVarintPrefixRecursionSyntax.four w B z o (0 : Fin 4) = w := rfl
  have h1 : PacketVarintPrefixRecursionSyntax.four w B z o (1 : Fin 4) = B := rfl
  have h2 : PacketVarintPrefixRecursionSyntax.four w B z o (2 : Fin 4) = z := rfl
  have h3 : PacketVarintPrefixRecursionSyntax.four w B z o (3 : Fin 4) = o := rfl
  simpa only [allProperties,BoundedInduction.holds,PacketReaderTokensSyntax.matrix_pred,paramsUp,h0,h1,h2,h3] using h

theorem at_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hn : Derives Γ (.mem n w)) : Derives Γ (property w B z o n) := by
  have hh : Derives Γ ((Formula.mem n w).imp (property w B z o n)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE n (all_properties hZ w B z o hw hB hz ho))
  exact .impE hh hn

theorem tokens {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n bytes A O p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hn : Derives Γ (StructuralListTraceSyntax.valid w n)) (ha : Derives Γ (StructuralListTraceSyntax.valid w A))
    (he : Derives Γ (PacketTokensBytes.encoded w n bytes)) (hOut : Derives Γ (PacketReaderOutputOrder.output w A n O)) :
    Derives Γ (agreement w B z o bytes A O p) := by
  have hProp := at_code hZ w B z o n hw hB hz ho (StructuralListValidity.range w n hn)
  have hCase := at_fields w B z o n bytes A O p hProp hn
  exact .impE (.impE (.impE hCase ha) he) hOut

end PPAC.Migration.Internal.PacketReaderTokensInduction
