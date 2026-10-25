import PPAC.Migration.Internal.StructuralListSpliceByteSyntax

/-! Actual Nil and Cons splice equations transfer the original byte predicate and reconstruct the joined ByteList without any host list recursion. -/
namespace PPAC.Migration.Internal.StructuralListSpliceBytePoint
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSpliceByteSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem byteList_subst {m} {Γ : Context m} (w t a : Fin m)
    (he : Derives Γ (.equal t a)) (ht : Derives Γ (PacketByteInputSyntax.byteList w t)) :
    Derives Γ (PacketByteInputSyntax.byteList w a) := by
  let P := PacketByteInputSyntax.byteList w.castSucc (Fin.last m)
  have h0 : P.instantiate t = PacketByteInputSyntax.byteList w t := by
    simp only [P,Formula.instantiate,PacketByteInputSyntax.byteList_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate a = PacketByteInputSyntax.byteList w a := by
    simp only [P,Formula.instantiate,PacketByteInputSyntax.byteList_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm ht))

theorem nil_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (StructuralListSyntax.nilCode w n))
    (ht : Derives Γ (PacketByteInputSyntax.byteList w t))
    (hs : Derives Γ (StructuralListSpliceSyntax.splice w n t a)) :
    Derives Γ (PacketByteInputSyntax.byteList w a) := by
  have he := Derives.conjR (Derives.impE (.conjL (StructuralListSplice.nil_iff hZ w n t a hw hn)) hs)
  exact byteList_subst w t a he ht

theorem cons_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x n t a : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (PacketByteInputSyntax.byte h))
    (hx : Derives Γ (PacketByteInputSyntax.byteList w x))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x n))
    (hIH : Derives Γ (property w x)) (ht : Derives Γ (PacketByteInputSyntax.byteList w t))
    (hs : Derives Γ (StructuralListSpliceSyntax.splice w n t a)) :
    Derives Γ (PacketByteInputSyntax.byteList w a) := by
  have hhN := PacketByteInputLaws.byte_natural hZ w h hw hh
  have hxN := PacketByteInputLaws.natural w x hx
  let R := (StructuralListSpliceSyntax.splice w.castSucc x.castSucc t.castSucc (Fin.last m)).conj
    (StructuralListSyntax.consCode w.castSucc h.castSucc (Fin.last m) a.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (StructuralListSplice.cons_forward hZ w h x n t a hw hhN hxN hc hs)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hh1 := of_eq (PacketByteInputSyntax.byte_rename h Fin.castSucc) (under hh R)
  have hx1 := of_eq (PacketByteInputSyntax.byteList_rename w x Fin.castSucc) (under hx R)
  have ht1 := of_eq (PacketByteInputSyntax.byteList_rename w t Fin.castSucc) (under ht R)
  have hIH1 := of_eq (property_rename w x Fin.castSucc) (under hIH R)
  have hCase := at_fields w.castSucc x.castSucc t.castSucc (Fin.last m) hIH1 hx1
  have hu := Derives.impE (Derives.impE hCase ht1) (.conjL hR)
  simpa only [Formula.raise,PacketByteInputSyntax.byteList_rename] using
    PacketVarintExecutionHelpers.cons_input hZ1 w.castSucc a.castSucc h.castSucc (Fin.last m) hw1 (.conjR hR) hh1 hu

end PPAC.Migration.Internal.StructuralListSpliceBytePoint
