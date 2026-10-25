import PPAC.Migration.Internal.PacketReaderPrefixSyntax
import PPAC.Migration.Internal.PacketReaderPrefixReconstruct

/-! Explicit actual continuation witnesses combine into the original-input prefix certificate while retaining the exact emitted value and final reader candidate. -/
namespace PPAC.Migration.Internal.PacketReaderPrefixContinuePoint
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem combine {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w B z o L b X d v s A y S k Q T u c n C p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hState : Derives Γ (PacketReaderStepSyntax.state w L v s A))
    (hHead : Derives Γ (StructuralListSyntax.consCode w b X L))
    (hAff : Derives Γ (PacketAffineSyntax.affine w B d k n)) (hk : Derives Γ (empty k).neg)
    (hSum : Derives Γ (NaturalAdditionSyntax.sum w B d b))
    (hQ : Derives Γ (PacketVarintSyntax.canonical w k Q))
    (hC : Derives Γ (StructuralListSyntax.consCode w b Q C))
    (hSp : Derives Γ (StructuralListSpliceSyntax.splice w Q T X))
    (hByte : Derives Γ (PacketByteInputSyntax.byteList w T)) (hTX : Derives Γ (.mem T X))
    (hDigit : Derives Γ (PacketAffineSyntax.equation w d v s y))
    (hScale : Derives Γ (NaturalMultiplicationSyntax.product w s B S))
    (hValue : Derives Γ (PacketAffineSyntax.equation w k y S u))
    (hCons : Derives Γ (StructuralListSyntax.consCode w u A c))
    (hEval : Derives Γ (PacketReaderEvalSyntax.eval w B z o T z o c p)) :
    Derives Γ (PacketReaderPrefixSyntax.result w B z o L v s A p) := by
  have hBN := SyntaxNumerals.range hZ 128 w B hw hB
  have hd := PacketAffineCore.digit_natural hZ w B d k n hw hAff
  have hkN := PacketAffineCore.tail_guard w B d k n hAff
  have hb := ZFArithmetic.add_range hZ w B d b hw hBN hSum
  have hXN := StructuralListValidity.range w X (StructuralListSplice.joined_valid w Q T X hSp)
  have hXL := Derives.conjR (StructuralConsCore.components hZ w b X L hw hb hXN hHead)
  have hLN := StructuralListValidity.range w L (.conjL hState)
  have hBelow := PacketReaderPrefixReconstruct.suffix_member hZ w L X T hw hLN hXL hTX
  have hCanonical := PacketReaderPrefixReconstruct.canonical_cons hZ w B d k n b Q C hw hB hAff hk hSum hQ hC
  have hJoined := PacketReaderPrefixReconstruct.splice_cons hZ w b Q C X T L hw hb hC hSp hHead
  have hGuard := PacketReaderPrefixReconstruct.nonzero_guard hZ w B d k n o s hw hB hAff hk
  have hEquation := PacketReaderAffineCompose.compose hZ w B d k n v s y S u hw hBN hd hkN
    (.conjL (.conjR hState)) (.conjL (.conjR (.conjR hState)))
    (PacketAffineCore.equation_of_affine w B d k n hAff) hDigit hScale hValue
  exact PacketReaderPrefixSyntax.intro_result w B z o L v s A p n C T u c hCanonical hJoined hByte hBelow hGuard hEquation hCons hEval

end PPAC.Migration.Internal.PacketReaderPrefixContinuePoint
