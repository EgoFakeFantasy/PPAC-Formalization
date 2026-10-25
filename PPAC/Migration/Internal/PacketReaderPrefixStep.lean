import PPAC.Migration.Internal.PacketReaderPrefixCases

/-! One fixed universally quantified prefix formula is progressive under actual smaller-input-code assumptions. Every input, state, successful payload and return candidate remains inside the object quantifiers. -/
namespace PPAC.Migration.Internal.PacketReaderPrefixStep
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderPrefixSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem property_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w B z o L : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hi : Derives Γ (earlier w B z o L)) : Derives Γ (property w B z o L) := by
  apply OriginalUniversalBlock.intro_many 5 (body w B z o L)
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let X0 := PacketByteInputSyntax.byteList (old 5 w) (old 5 L)
  let X1 := PacketReaderStepSyntax.state (old 5 w) (old 5 L) (slot 5 0) (slot 5 1) (slot 5 2)
  let X2 : Formula (m+5) := (empty (slot 5 1)).neg
  let X3 := (StructuralListSyntax.nilCode (old 5 w) (old 5 L)).neg
  let X4 := PacketReaderEvalSyntax.eval (old 5 w) (old 5 B) (old 5 z) (old 5 o)
    (old 5 L) (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 4)
  let X5 := PacketReaderReturnSyntax.some (old 5 w) (slot 5 3) (slot 5 4)
  let Δ := Context.add X5 (Context.add X4 (Context.add X3 (Context.add X2
    (Context.add X1 (Context.add X0 (raisedContext 5 Γ))))))
  have hZ5 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add
    (ZFContext.add (ZFContext.add (ZFContext.add (HornBinderRules.zf_many 5 hZ) X0) X1) X2) X3) X4) X5
  have lift5 {φ : Formula m} (hh : Derives Γ φ) : Derives Δ (φ.rename (old 5)) :=
    add (add (add (add (add (add (HornBinderRules.under_many 5 hh) X0) X1) X2) X3) X4) X5
  have hw5 := of_eq (omega_rename w (old 5)) (lift5 hw)
  have hB5 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 5)) (lift5 hB)
  have hz5 := of_eq (empty_rename z (old 5)) (lift5 hz)
  have ho5 := of_eq (successor_rename o z (old 5)) (lift5 ho)
  have hi5 := of_eq (earlier_rename w B z o L (old 5)) (lift5 hi)
  have hX0 : Derives Δ X0 := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have hX1 : Derives Δ X1 := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hX2 : Derives Δ X2 := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hX3 : Derives Δ X3 := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have hX4 : Derives Δ X4 := .hyp (Or.inr (Or.inl rfl))
  have hX5 : Derives Δ X5 := .hyp (Or.inl rfl)
  exact PacketReaderPrefixCases.from_earlier_point hZ5
    (old 5 w) (old 5 B) (old 5 z) (old 5 o) (old 5 L)
    (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4)
    hw5 hB5 hz5 ho5 hi5 hX0 hX1 hX2 hX3 hX4 hX5

end PPAC.Migration.Internal.PacketReaderPrefixStep
