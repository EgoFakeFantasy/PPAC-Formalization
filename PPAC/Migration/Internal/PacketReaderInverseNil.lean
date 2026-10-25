import PPAC.Migration.Internal.PacketReaderInverseSyntax
import PPAC.Migration.Internal.PacketReaderSuccess

/-! Successful actual Nil input is the encoding of actual Nil tokens, with the original reverse accumulator as its exact ordered output. -/
namespace PPAC.Migration.Internal.PacketReaderInverseNil
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderInverseSyntax

theorem nil_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L A O p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hL : Derives Γ (StructuralListSyntax.nilCode w L))
    (hEval : Derives Γ (PacketReaderEvalSyntax.eval w B z o L z o A p))
    (hSome : Derives Γ (PacketReaderReturnSyntax.some w O p)) :
    Derives Γ (result w L A O) := by
  have hBN := SyntaxNumerals.range hZ 128 w B hw hB
  have hRev := PacketReaderSuccess.nil_reverse hZ w B z o L z o A O p hw hBN hz ho hL hEval hSome
  have hNil := StructuralNil.at_unit hZ w z o hw hz ho
  have hEncoded := Derives.impE (.conjR (PacketTokensBytes.nil_iff hZ w o L hw hNil)) hL
  have hOV := StructuralListReverseUnique.valid_output w A O hRev
  have hSplice := StructuralListSpliceAlgebra.right_nil hZ w O o hw hOV hNil
  have hOutput := PacketReaderOutputOrder.intro_output w A o O O hRev hSplice
  exact intro_result w L A O o hEncoded hOutput

end PPAC.Migration.Internal.PacketReaderInverseNil
