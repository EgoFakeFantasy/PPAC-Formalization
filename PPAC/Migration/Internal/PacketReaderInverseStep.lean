import PPAC.Migration.Internal.PacketReaderInverseCases

/-! One fixed Formula5 is progressive for every internal accumulator, payload and return candidate. -/
namespace PPAC.Migration.Internal.PacketReaderInverseStep
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderInverseSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem property_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hi : Derives Γ (earlier w B z o L)) : Derives Γ (property w B z o L) := by
  apply OriginalUniversalBlock.intro_many 3 (body w B z o L)
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let X0 := PacketByteInputSyntax.byteList (old 3 w) (old 3 L)
  let X1 := PacketReaderEvalSyntax.eval (old 3 w) (old 3 B) (old 3 z) (old 3 o) (old 3 L)
    (old 3 z) (old 3 o) (slot 3 0) (slot 3 2)
  let X2 := PacketReaderReturnSyntax.some (old 3 w) (slot 3 1) (slot 3 2)
  let Δ := Context.add X2 (Context.add X1 (Context.add X0 (raisedContext 3 Γ)))
  have hZ3 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (HornBinderRules.zf_many 3 hZ) X0) X1) X2
  have lift3 {φ : Formula m} (hh : Derives Γ φ) : Derives Δ (φ.rename (old 3)) :=
    add (add (add (HornBinderRules.under_many 3 hh) X0) X1) X2
  have hw3 := of_eq (omega_rename w (old 3)) (lift3 hw)
  have hB3 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 3)) (lift3 hB)
  have hz3 := of_eq (empty_rename z (old 3)) (lift3 hz)
  have ho3 := of_eq (successor_rename o z (old 3)) (lift3 ho)
  have hi3 := of_eq (earlier_rename w B z o L (old 3)) (lift3 hi)
  have hX0 : Derives Δ X0 := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have hX1 : Derives Δ X1 := .hyp (Or.inr (Or.inl rfl))
  have hX2 : Derives Δ X2 := .hyp (Or.inl rfl)
  exact PacketReaderInverseCases.from_earlier_point hZ3 (old 3 w) (old 3 B) (old 3 z) (old 3 o)
    (old 3 L) (slot 3 0) (slot 3 1) (slot 3 2) hw3 hB3 hz3 ho3 hi3 hX0 hX1 hX2

end PPAC.Migration.Internal.PacketReaderInverseStep
