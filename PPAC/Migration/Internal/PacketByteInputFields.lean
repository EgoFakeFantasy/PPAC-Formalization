import PPAC.Migration.Internal.PacketVarintExecutionLiterals

/-! The existing full ByteList guard bounds every actual field at every genuine internal length; the bound numeral can be kept or eliminated inside the original derivation. -/
namespace PPAC.Migration.Internal.PacketByteInputFields
open Source SourceAlgebra SourceLogic OmegaSyntax PacketByteInputSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem bounds_at_length {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n l : Fin m)
    (hw : Derives Γ (omega w)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hb : Derives Γ (byteList w n)) (hl : Derives Γ (StructuralListLengthSyntax.hasLength w n l)) :
    Derives Γ (bounds w C n l) :=
  PacketByteInputProperties.at_length hZ w C n l hw (PacketByteInputBridge.actual_at hZ w C n hC hb) hl

theorem at_radix {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n l i y : Fin m)
    (hw : Derives Γ (omega w)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hb : Derives Γ (byteList w n)) (hl : Derives Γ (StructuralListLengthSyntax.hasLength w n l))
    (hi : Derives Γ (.mem i l)) (hy : Derives Γ (StructuralListFieldSyntax.field w n i y)) : Derives Γ (.mem y C) :=
  bounds_at w C n l i y (bounds_at_length hZ w C n l hw hC hb hl) hi hy

theorem byte_at_field {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l i y : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (byteList w n))
    (hl : Derives Γ (StructuralListLengthSyntax.hasLength w n l)) (hi : Derives Γ (.mem i l))
    (hy : Derives Γ (StructuralListFieldSyntax.field w n i y)) : Derives Γ (byte y) := by
  let R := (SyntaxNumeralSyntax.numeral 256 (Fin.last m)).conj (inputAt w.castSucc (Fin.last m) n.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hb
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hl1 := of_eq (StructuralListLengthSyntax.hasLength_rename w n l Fin.castSucc) (under hl R)
  have hy1 := of_eq (StructuralListFieldSyntax.field_rename w n i y Fin.castSucc) (under hy R)
  have hBounds := PacketByteInputProperties.at_length hZ1 w.castSucc (Fin.last m) n.castSucc l.castSucc hw1 (.conjR hR) hl1
  have hByte := intro_byte (Fin.last m) y.castSucc (.conjL hR) (bounds_at _ _ _ _ _ _ hBounds (under hi R) hy1)
  simpa only [Formula.raise,byte_rename] using hByte

end PPAC.Migration.Internal.PacketByteInputFields
