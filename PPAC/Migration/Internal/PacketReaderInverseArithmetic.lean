import PPAC.Migration.Internal.PacketByteInputLaws
import PPAC.Migration.Internal.PacketTokenByteBounds
import PPAC.Migration.Internal.PacketDivisionDescentOrder

/-! Actual continuation bytes yield a bounded low digit and a strictly enlarged positive scale. Literal 256 is obtained and eliminated inside the original object derivation. These lemmas do not assert reader inverse correctness. -/
namespace PPAC.Migration.Internal.PacketReaderInverseArithmetic
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem continuation_digit_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w B b d : Fin m) (hw : Derives Γ (omega w))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hb : Derives Γ (PacketByteInputSyntax.byte b))
    (hd : Derives Γ (.mem d w))
    (hSum : Derives Γ (NaturalAdditionSyntax.sum w B d b)) : Derives Γ (.mem d B) := by
  let R := PacketAffineLiteralSyntax.frame true w.castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (SyntaxNumerals.exists_numeral hZ 256 w hw)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under hB R)
  have hb1 := of_eq (PacketByteInputSyntax.byte_rename b Fin.castSucc) (under hb R)
  have hSum1 := of_eq (NaturalAdditionSyntax.sum_rename w B d b Fin.castSucc) (under hSum R)
  have hBN := SyntaxNumerals.range hZ1 128 w.castSucc B.castSucc hw1 hB1
  have hByte := PacketByteInputBridge.byte_at hZ1 (Fin.last m) b.castSucc (.conjR hR) hb1
  have hRadix := PacketTokenByteBounds.radix_sum hZ1 w.castSucc B.castSucc (Fin.last m)
    hw1 hB1 (.conjR hR)
  have hDigitSum := ZFArithmetic.add_commute hZ1 w.castSucc B.castSucc d.castSucc b.castSucc
    hw1 hBN (under hd R) hSum1
  exact NaturalAdditionMonotone.strict_reflect hZ1 w.castSucc d.castSucc B.castSucc B.castSucc
    b.castSucc (Fin.last m) hw1 (under hd R) hBN hBN hDigitSum hRadix hByte

theorem continuation_scale_growth {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w B z o s S : Fin m) (hw : Derives Γ (omega w))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hs : Derives Γ (.mem s w)) (hs0 : Derives Γ (empty s).neg)
    (hScale : Derives Γ (NaturalMultiplicationSyntax.product w s B S)) :
    Derives Γ ((empty S).neg.conj (Formula.equal S o).neg) := by
  have hBN := SyntaxNumerals.range hZ 128 w B hw hB
  have hProduct := NaturalMultiplicationCommutative.commute hZ w s B S hw hs hBN hScale
  have hStrict := Derives.impE
    (.conjR (PacketDivisionDescentOrder.product_bounds hZ false w B s S hw hB hs hProduct)) hs0
  apply Derives.conjI
  · apply Derives.impI
    exact Derives.impE (empty_at S s (.hyp (Or.inl rfl))) (add hStrict _)
  · apply Derives.impI
    let E := Formula.equal S o
    let Δ := Context.add E Γ
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    have hMember := UnorderedPairLogic.mem_container_subst S o s hE (add hStrict E)
    apply Derives.disjE (InsertLogic.member_cases o z z s (add ho E) hMember)
    · exact Derives.impE (empty_at z s (add (add hz E) _)) (.hyp (Or.inl rfl))
    · have hEmpty := NaturalMultiplicationLaws.empty_subst z s
        (eq_symm (.hyp (Or.inl rfl))) (add (add hz E) _)
      exact Derives.impE (add (add hs0 E) _) hEmpty

end PPAC.Migration.Internal.PacketReaderInverseArithmetic
