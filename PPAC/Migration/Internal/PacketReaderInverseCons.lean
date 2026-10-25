import PPAC.Migration.Internal.PacketReaderInverseConsPoint
import PPAC.Migration.Internal.PacketReaderPrefixSyntax

/-! The actual strict suffix-code IH reconstructs the reader inverse Cons case. Initial arithmetic, token-head substitution and all token witnesses use the original object kernel. -/
namespace PPAC.Migration.Internal.PacketReaderInverseCons
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open PacketReaderInverseSyntax (result result_rename earlier earlier_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem at_prefix {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w B z o L A O p n C T u c : Fin m)
    (hw : Derives Γ (omega w))
    (hz : Derives Γ (empty z))
    (ho : Derives Γ (successor o z))
    (hEarlier : Derives Γ (earlier w B z o L))
    (hEval : Derives Γ (PacketReaderEvalSyntax.eval w B z o L z o A p))
    (hSome : Derives Γ (PacketReaderReturnSyntax.some w O p))
    (hC : Derives Γ (PacketVarintSyntax.canonical w n C))
    (hSp : Derives Γ (StructuralListSpliceSyntax.splice w C T L))
    (hByte : Derives Γ (PacketByteInputSyntax.byteList w T))
    (hBelow : Derives Γ (Formula.mem T L))
    (hEquation : Derives Γ (PacketAffineSyntax.equation w n z o u))
    (hCons : Derives Γ (StructuralListSyntax.consCode w u A c))
    (hTailEval : Derives Γ (PacketReaderEvalSyntax.eval w B z o T z o c p))
    : Derives Γ (result w L A O) := by
  have hn := Derives.conjL (PacketVarintDomain.domain w n C hC)
  have hoN := StructuralListUnits.member hZ w z o hw hz ho
  have hUnit := PacketReaderTokenUnits.equation_zero_unit hZ w z o n hw hz ho hn
  have hEq := PacketAffineCore.equation_unique hZ w n z o u n hw hn hoN hEquation hUnit
  have hAcc := PacketVarintCanonicalPieces.cons_head w u A c n hEq hCons
  have hA := Derives.conjR (.conjR (.conjR (PacketReaderSuccess.state w B z o L z o A p hEval)))
  have hTN := PacketByteInputLaws.natural w T hByte
  have hIH := PacketReaderInverseSyntax.earlier_at w B z o L T hEarlier hTN hBelow
  have hCase := PacketReaderInverseSyntax.at_fields w B z o T c O p hIH
  have hTail := Derives.impE (Derives.impE (Derives.impE hCase hByte) hTailEval) hSome
  exact PacketReaderInverseConsPoint.from_tail_result hZ w z o L A O n C T c
    hw hz ho hA hC hSp hAcc hTail

theorem from_prefix {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w B z o L A O p : Fin m)
    (hw : Derives Γ (omega w))
    (_hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hz : Derives Γ (empty z))
    (ho : Derives Γ (successor o z))
    (hEarlier : Derives Γ (earlier w B z o L))
    (hEval : Derives Γ (PacketReaderEvalSyntax.eval w B z o L z o A p))
    (hSome : Derives Γ (PacketReaderReturnSyntax.some w O p))
    (hPrefix : Derives Γ (PacketReaderPrefixSyntax.result w B z o L z o A p)) :
    Derives Γ (result w L A O) := by
  let R := PacketReaderPrefixSyntax.resultBody w B z o L z o A p
  let Δ := Context.add R (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 R _ hPrefix
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := HornBinderRules.zf_body 5 hZ R
  have lift {φ : Formula m} (hh : Derives Γ φ) : Derives Δ (φ.rename (old 5)) := HornBinderRules.under_body 5 hh R
  have hw1 := of_eq (omega_rename w (old 5)) (lift hw)
  have hz1 := of_eq (empty_rename z (old 5)) (lift hz)
  have ho1 := of_eq (successor_rename o z (old 5)) (lift ho)
  have hEarlier1 := of_eq (earlier_rename w B z o L (old 5)) (lift hEarlier)
  have hEval1 := of_eq (PacketReaderEvalSyntax.eval_rename w B z o L z o A p (old 5)) (lift hEval)
  have hSome1 := of_eq (PacketReaderReturnSyntax.some_rename w O p (old 5)) (lift hSome)
  have hCanonical := Derives.conjL hR
  have hSplice := Derives.conjL (.conjR hR)
  have hBytes := Derives.conjL (.conjR (.conjR hR))
  have hBelow := Derives.conjL (.conjR (.conjR (.conjR hR)))
  have hEquation := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hR)))))
  have hAcc := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hR))))))
  have hTailEval := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hR))))))
  have hout := at_prefix hZ1
    (old 5 w) (old 5 B) (old 5 z) (old 5 o) (old 5 L) (old 5 A) (old 5 O) (old 5 p) (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4)
    hw1 hz1 ho1 hEarlier1 hEval1 hSome1 hCanonical hSplice hBytes hBelow hEquation hAcc hTailEval
  exact of_eq (result_rename w L A O (old 5)).symm hout

end PPAC.Migration.Internal.PacketReaderInverseCons
