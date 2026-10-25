import PPAC.Migration.Internal.PacketReaderLengthAt

/-! A real consumed Cons makes the old actual list length the successor of the new actual list length. -/
namespace PPAC.Migration.Internal.PacketReaderTailLength
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderConsumptionSyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem successor_length {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w L K a b : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (tail w L K))
    (ha : Derives Γ (hasLength w L a)) (hb : Derives Γ (hasLength w K b)) : Derives Γ (successor a b) := by
  let R := PacketReaderInputSyntax.headRest w.castSucc L.castSucc (Fin.last m) K.castSucc
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) ht
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have ha1 := of_eq (hasLength_rename w L a Fin.castSucc) (under ha R)
  have hb1 := of_eq (hasLength_rename w K b Fin.castSucc) (under hb R)
  have hp := StructuralListLengthRules.cons_predecessor hZ1 _ _ _ _ _ hw1 (.conjL hR)
    (StructuralListLengthBasic.code_member _ _ _ hb1) (.conjR (.conjR hR)) ha1
  let T := ((Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (successor a.castSucc.castSucc (Fin.last (m+1)))).conj
    (hasLength w.castSucc.castSucc K.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add T (Context.image Formula.raise Δ)
  apply Derives.exE (p := T) hp
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 T
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 T)
  have hb2 := of_eq (hasLength_rename w.castSucc K.castSucc b.castSucc Fin.castSucc) (under hb1 T)
  have he := StructuralListLengthUnique.unique hZ2 _ _ _ _ hw2 (.conjR hT) hb2
  have hout := NaturalAdditionTransport.successor_input_subst _ _ _ he (.conjR (.conjL hT))
  simpa only [Formula.raise,successor_rename] using hout

end PPAC.Migration.Internal.PacketReaderTailLength
