import PPAC.Migration.Internal.PacketReaderPrefixSmall
import PPAC.Migration.Internal.PacketReaderPrefixContinue
import PPAC.Migration.Internal.PacketReaderSuccess

/-! Complete original byte dispatch for successful nonempty bounded input. The true smaller input code supplies the prefix IH, and the original terminal-zero rejection is excluded by actual Some success. -/
namespace PPAC.Migration.Internal.PacketReaderPrefixCases
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderPrefixSyntax
open PacketReaderVarintSegmentSyntax (guard guard_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem finish_guard {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (B z o b s : Fin m) (hz : Derives Γ (empty z))
    (hFinish : Derives Γ (PacketReaderStepSyntax.finish B z o b s)) :
    Derives Γ (guard o b s) := by
  apply Derives.disjE (.conjR hFinish)
  · exact .disjL (.hyp (Or.inl rfl))
  · apply Derives.disjR
    apply Derives.impI
    let H := (Formula.equal b z).neg
    let E := empty b
    let Δ := Context.add E (Context.add H Γ)
    have hH : Derives Δ H := .hyp (Or.inr (Or.inl rfl))
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    have hZ2 := ZFContext.add (ZFContext.add hZ H) E
    have hEq := OmegaUniversal.empty_unique b z (ZFContext.arithmetic hZ2).base.extensionality
      hE (add (add hz H) E)
    exact .impE hH hEq

theorem cons_dispatch {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w B z o L b X v s A O p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hState : Derives Γ (PacketReaderStepSyntax.state w L v s A))
    (hb : Derives Γ (PacketByteInputSyntax.byte b))
    (hX : Derives Γ (PacketByteInputSyntax.byteList w X))
    (hCons : Derives Γ (StructuralListSyntax.consCode w b X L))
    (hPositive : Derives Γ (empty s).neg)
    (hIH : Derives Γ (property w B z o X))
    (hEval : Derives Γ (PacketReaderEvalSyntax.eval w B z o L v s A p))
    (hSome : Derives Γ (PacketReaderReturnSyntax.some w O p)) :
    Derives Γ (result w B z o L v s A p) := by
  have hBN := SyntaxNumerals.range hZ 128 w B hw hB
  have hbN := PacketByteInputLaws.byte_natural hZ w b hw hb
  have hHead : Derives Γ (PacketReaderInputSyntax.headRest w L b X) :=
    .conjI hbN (.conjI (PacketByteInputLaws.valid w X hX) hCons)
  apply Derives.disjE (PacketReaderGuards.partition hZ w B z o b s hw hBN hbN)
  · let H := (PacketReaderStepSyntax.finish B z o b s).disj (PacketReaderStepSyntax.reject B z o b s)
    apply Derives.disjE (.hyp (Or.inl rfl) : Derives (Context.add H Γ) H)
    · let F := PacketReaderStepSyntax.finish B z o b s
      let Δ := Context.add F (Context.add H Γ)
      have hF : Derives Δ F := .hyp (Or.inl rfl)
      have hZ2 := ZFContext.add (ZFContext.add hZ H) F
      have lift2 {φ : Formula m} (hh : Derives Γ φ) : Derives Δ φ := add (add hh H) F
      have hGuard := finish_guard hZ2 B z o b s (lift2 hz) hF
      exact PacketReaderPrefixSmall.small hZ2 w B z o L b X v s A p
        (lift2 hw) (lift2 hB) (lift2 hz) (lift2 ho) (lift2 hCons) (lift2 hX)
        (.conjL hF) hGuard (lift2 hState) (lift2 hEval)
    · let R := PacketReaderStepSyntax.reject B z o b s
      let Δ := Context.add R (Context.add H Γ)
      have hR : Derives Δ R := .hyp (Or.inl rfl)
      have hZ2 := ZFContext.add (ZFContext.add hZ H) R
      have lift2 {φ : Formula m} (hh : Derives Γ φ) : Derives Δ φ := add (add hh H) R
      exact .botE (PacketReaderSuccess.reject_at_cons hZ2 w B z o L b X v s A O p
        (lift2 hw) (lift2 hBN) (lift2 hz) (lift2 ho) (lift2 hHead) hR (lift2 hEval) (lift2 hSome))
  · let M := PacketReaderStepSyntax.more B b
    have hM : Derives (Context.add M Γ) M := .hyp (Or.inl rfl)
    exact PacketReaderPrefixContinue.point (ZFContext.add hZ M) w B z o L b X v s A O p
      (add hw M) (add hB M) (add hz M) (add ho M) (add hState M) (add hb M)
      (add hX M) (add hCons M) hM (add hPositive M) (add hIH M) (add hEval M) (add hSome M)

theorem from_earlier_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w B z o L v s A O p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hi : Derives Γ (earlier w B z o L))
    (hBytes : Derives Γ (PacketByteInputSyntax.byteList w L))
    (hState : Derives Γ (PacketReaderStepSyntax.state w L v s A))
    (hPositive : Derives Γ (empty s).neg) (hNonempty : Derives Γ (StructuralListSyntax.nilCode w L).neg)
    (hEval : Derives Γ (PacketReaderEvalSyntax.eval w B z o L v s A p))
    (hSome : Derives Γ (PacketReaderReturnSyntax.some w O p)) :
    Derives Γ (result w B z o L v s A p) := by
  have hCases := Derives.impE (.conjL (PacketByteInputLaws.actual_iff hZ w L hw)) hBytes
  apply Derives.disjE hCases
  · exact .botE (.impE (add hNonempty _) (.hyp (Or.inl rfl)))
  · let C := PacketByteInputRecursionSyntax.actualCons w L
    let R := PacketByteInputRecursionSyntax.actualBody w L
    let Δ := Context.add R (raisedContext 2 (Context.add C Γ))
    apply HornBinderRules.eliminate_many 2 R _ (.hyp (Or.inl rfl) : Derives (Context.add C Γ) C)
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ2 := HornBinderRules.zf_body 2 (ZFContext.add hZ C) R
    have lift2 {φ : Formula m} (hh : Derives Γ φ) : Derives Δ (φ.rename (old 2)) :=
      HornBinderRules.under_body 2 (add hh C) R
    have hw2 := of_eq (omega_rename w (old 2)) (lift2 hw)
    have hB2 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 2)) (lift2 hB)
    have hz2 := of_eq (empty_rename z (old 2)) (lift2 hz)
    have ho2 := of_eq (successor_rename o z (old 2)) (lift2 ho)
    have hi2 := of_eq (earlier_rename w B z o L (old 2)) (lift2 hi)
    have hState2 := of_eq (PacketReaderStepSyntax.state_rename w L v s A (old 2)) (lift2 hState)
    have hPositive2 : Derives Δ (empty (old 2 s)).neg :=
      of_eq (by simp only [Formula.neg,Formula.rename,empty_rename]) (lift2 hPositive)
    have hEval2 := of_eq (PacketReaderEvalSyntax.eval_rename w B z o L v s A p (old 2)) (lift2 hEval)
    have hSome2 := of_eq (PacketReaderReturnSyntax.some_rename w O p (old 2)) (lift2 hSome)
    have hb := Derives.conjL (.conjR hR)
    have hX := Derives.conjR (.conjR hR)
    have hbN := PacketByteInputLaws.byte_natural hZ2 (old 2 w) (slot 2 0) hw2 hb
    have hXN := PacketByteInputLaws.natural (old 2 w) (slot 2 1) hX
    have hBelow := Derives.conjR (StructuralConsCore.components hZ2 (old 2 w) (slot 2 0)
      (slot 2 1) (old 2 L) hw2 hbN hXN (.conjL hR))
    have hIH := earlier_at (old 2 w) (old 2 B) (old 2 z) (old 2 o) (old 2 L)
      (slot 2 1) hi2 hXN hBelow
    exact of_eq (result_rename w B z o L v s A p (old 2)).symm
      (cons_dispatch hZ2 (old 2 w) (old 2 B) (old 2 z) (old 2 o) (old 2 L)
        (slot 2 0) (slot 2 1) (old 2 v) (old 2 s) (old 2 A) (old 2 O) (old 2 p)
        hw2 hB2 hz2 ho2 hState2 hb hX (.conjL hR) hPositive2 hIH hEval2 hSome2)

end PPAC.Migration.Internal.PacketReaderPrefixCases
