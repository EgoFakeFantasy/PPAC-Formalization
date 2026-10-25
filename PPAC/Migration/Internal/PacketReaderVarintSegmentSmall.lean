import PPAC.Migration.Internal.PacketReaderVarintSegmentSyntax

/-! An actual singleton canonical byte segment consumes exactly its head, retaining arbitrary trailing input and original canonical guard. -/
namespace PPAC.Migration.Internal.PacketReaderVarintSegmentSmall
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderVarintSegmentSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem singleton_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n C T L : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hC : Derives Γ (PacketVarintCanonicalRecursionSyntax.singleton w n C))
    (hSp : Derives Γ (StructuralListSpliceSyntax.splice w C T L)) : Derives Γ (StructuralListSyntax.consCode w n T L) := by
  let R := (StructuralListSyntax.nilCode w.castSucc (Fin.last m)).conj (StructuralListSyntax.consCode w.castSucc n.castSucc (Fin.last m) C.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hC
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hSp1 := of_eq (StructuralListSpliceSyntax.splice_rename w C T L Fin.castSucc) (under hSp R)
  have heN := StructuralNil.range hZ1 _ _ hw1 (.conjL hR)
  have hRem := StructuralListSplice.cons_forward hZ1 w.castSucc n.castSucc (Fin.last m) C.castSucc T.castSucc L.castSucc hw1 (under hn R) heN (.conjR hR) hSp1
  let S := (StructuralListSpliceSyntax.splice w.castSucc.castSucc (Fin.last m).castSucc T.castSucc.castSucc (Fin.last (m+1))).conj
    (StructuralListSyntax.consCode w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) L.castSucc.castSucc)
  let Ξ := Context.add S (Context.image Formula.raise Δ)
  apply Derives.exE (p := S) hRem
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 S
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 S)
  have heNil := of_eq (StructuralListSyntax.nilCode_rename w.castSucc (Fin.last m) Fin.castSucc) (under (.conjL hR) S)
  have hEq := Derives.conjR (.impE (.conjL (StructuralListSplice.nil_iff hZ2 w.castSucc.castSucc (Fin.last m).castSucc T.castSucc.castSucc (Fin.last (m+1)) hw2 heNil)) (.conjL hS))
  simpa only [Formula.raise,StructuralListSyntax.consCode_rename] using PacketVarintExecutionHelpers.cons_tail _ _ _ _ _ (eq_symm hEq) (.conjR hS)

theorem small {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n C T L v s a u c p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (.mem o w))
    (hn : Derives Γ (.mem n B)) (hC : Derives Γ (PacketVarintCanonicalRecursionSyntax.singleton w n C))
    (hSp : Derives Γ (StructuralListSpliceSyntax.splice w C T L)) (hT : Derives Γ (PacketReaderStepSyntax.state w T v s a))
    (hG : Derives Γ (guard o n s)) (hu : Derives Γ (PacketAffineSyntax.equation w n v s u))
    (hc : Derives Γ (StructuralListSyntax.consCode w u a c)) : Derives Γ (agreement w B z o L T v s a c p) := by
  have hnN := StructuralListTraceOrder.member_member hZ w n B hw hB hn
  have hCons := singleton_input hZ w n C T L hw hnN hC hSp
  have hHead : Derives Γ (PacketReaderInputSyntax.headRest w L n T) := .conjI hnN (.conjI (.conjL hT) hCons)
  exact PacketReaderVarintBranches.terminal_digit hZ _ _ _ _ _ _ _ _ _ _ _ _ _ hw hB hz ho hT hHead hn hG hu hc

end PPAC.Migration.Internal.PacketReaderVarintSegmentSmall
