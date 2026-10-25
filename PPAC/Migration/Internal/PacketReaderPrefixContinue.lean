import PPAC.Migration.Internal.PacketReaderPrefixContinueWitness
import PPAC.Migration.Internal.PacketReaderContinuation

/-! The high-byte prefix case invokes the actual smaller input-code property after the original continuation update, and eliminates every reconstructed witness internally. -/
namespace PPAC.Migration.Internal.PacketReaderPrefixContinue
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open PacketReaderPrefixSyntax (result result_rename property property_rename)
open PacketReaderStepSyntax (continuation continuation_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem at_digit {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w B z o L b X v s A O p y S d : Fin m)
    (hw : Derives Γ (omega w))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hz : Derives Γ (empty z))
    (ho : Derives Γ (successor o z))
    (hState : Derives Γ (PacketReaderStepSyntax.state w L v s A))
    (hb : Derives Γ (PacketByteInputSyntax.byte b))
    (hX : Derives Γ (PacketByteInputSyntax.byteList w X))
    (hHead : Derives Γ (StructuralListSyntax.consCode w b X L))
    (hs : Derives Γ ((empty s).neg))
    (hIH : Derives Γ (property w B z o X))
    (hEval : Derives Γ (PacketReaderEvalSyntax.eval w B z o L v s A p))
    (hSome : Derives Γ (PacketReaderReturnSyntax.some w O p))
    (hy : Derives Γ (Formula.mem y w))
    (hS : Derives Γ (Formula.mem S w))
    (hd : Derives Γ (Formula.mem d w))
    (hSum : Derives Γ (NaturalAdditionSyntax.sum w B d b))
    (hDigit : Derives Γ (PacketAffineSyntax.equation w d v s y))
    (hScale : Derives Γ (NaturalMultiplicationSyntax.product w s B S)) :
    Derives Γ (result w B z o L v s A p) := by
  have hBN := SyntaxNumerals.range hZ 128 w B hw hB
  have hoN := StructuralListUnits.member hZ w z o hw hz ho
  have hbN := PacketByteInputLaws.byte_natural hZ w b hw hb
  have hXV := PacketByteInputLaws.valid w X hX
  have hdB := PacketReaderInverseArithmetic.continuation_digit_bound hZ w B b d hw hB hb hd hSum
  have hGrowth := PacketReaderInverseArithmetic.continuation_scale_growth hZ w B z o s S
    hw hB hz ho (.conjL (.conjR (.conjR hState))) hs hScale
  have hOldX : Derives Γ (PacketReaderStepSyntax.state w X v s A) := .conjI hXV (.conjR hState)
  have hHeadRest : Derives Γ (PacketReaderInputSyntax.headRest w L b X) := .conjI hbN (.conjI hXV hHead)
  have hCont := PacketReaderContinuation.intro_continuation w B b v s y S d hd hSum hDigit hScale
  have hAdvance := PacketReaderVarintBranches.continuation_byte hZ w B z o L b X v s A y S p
    hw hBN hz hoN hOldX hHeadRest hCont
  have hEvalX := Derives.impE (.conjL hAdvance) hEval
  have hNotNil := PacketReaderSuccess.nonunit_not_nil hZ w B z o X y S A O p
    hw hBN hz ho hEvalX hSome (.conjR hGrowth)
  have hUpdated : Derives Γ (PacketReaderStepSyntax.state w X y S A) :=
    .conjI hXV (.conjI hy (.conjI hS (.conjR (.conjR (.conjR hState)))))
  have hCase := PacketReaderPrefixSyntax.at_fields w B z o X y S A O p hIH
  have hResult := Derives.impE (Derives.impE (Derives.impE (Derives.impE (Derives.impE (Derives.impE
    hCase hX) hUpdated) (.conjL hGrowth)) hNotNil) hEvalX) hSome
  exact PacketReaderPrefixContinueWitness.from_result hZ w B z o L b X d v s A y S p
    hw hB hState hHead hdB hSum hDigit hScale (.conjR hGrowth) hResult

theorem at_update {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w B z o L b X v s A O p y S : Fin m)
    (hw : Derives Γ (omega w))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hz : Derives Γ (empty z))
    (ho : Derives Γ (successor o z))
    (hState : Derives Γ (PacketReaderStepSyntax.state w L v s A))
    (hb : Derives Γ (PacketByteInputSyntax.byte b))
    (hX : Derives Γ (PacketByteInputSyntax.byteList w X))
    (hHead : Derives Γ (StructuralListSyntax.consCode w b X L))
    (hs : Derives Γ ((empty s).neg))
    (hIH : Derives Γ (property w B z o X))
    (hEval : Derives Γ (PacketReaderEvalSyntax.eval w B z o L v s A p))
    (hSome : Derives Γ (PacketReaderReturnSyntax.some w O p))
    (hy : Derives Γ (Formula.mem y w))
    (hS : Derives Γ (Formula.mem S w))
    (hContinuation : Derives Γ (continuation w B b v s y S))
    : Derives Γ (result w B z o L v s A p) := by
  let D := (Formula.mem (Fin.last m) w.castSucc).conj
    ((NaturalAdditionSyntax.sum w.castSucc B.castSucc (Fin.last m) b.castSucc).conj
      ((PacketAffineSyntax.equation w.castSucc (Fin.last m) v.castSucc s.castSucc y.castSucc).conj
        (NaturalMultiplicationSyntax.product w.castSucc s.castSucc B.castSucc S.castSucc)))
  let Δ := Context.add D (Context.image Formula.raise Γ)
  apply Derives.exE (p := D) hContinuation
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ D
  have lift {φ : Formula m} (hh : Derives Γ φ) : Derives Δ φ.raise := under hh D
  have hw1 : Derives Δ (omega w.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,omega_rename] using lift hw
  have hB1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,SyntaxNumeralSyntax.numeral_rename] using lift hB
  have hz1 : Derives Δ (empty z.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,empty_rename] using lift hz
  have ho1 : Derives Δ (successor o.castSucc z.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,successor_rename] using lift ho
  have hState1 : Derives Δ (PacketReaderStepSyntax.state w.castSucc L.castSucc v.castSucc s.castSucc A.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,PacketReaderStepSyntax.state_rename] using lift hState
  have hb1 : Derives Δ (PacketByteInputSyntax.byte b.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,PacketByteInputSyntax.byte_rename] using lift hb
  have hX1 : Derives Δ (PacketByteInputSyntax.byteList w.castSucc X.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,PacketByteInputSyntax.byteList_rename] using lift hX
  have hHead1 : Derives Δ (StructuralListSyntax.consCode w.castSucc b.castSucc X.castSucc L.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,StructuralListSyntax.consCode_rename] using lift hHead
  have hs1 : Derives Δ ((empty s.castSucc).neg) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,empty_rename] using lift hs
  have hIH1 : Derives Δ (property w.castSucc B.castSucc z.castSucc o.castSucc X.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,property_rename] using lift hIH
  have hEval1 : Derives Δ (PacketReaderEvalSyntax.eval w.castSucc B.castSucc z.castSucc o.castSucc L.castSucc v.castSucc s.castSucc A.castSucc p.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,PacketReaderEvalSyntax.eval_rename] using lift hEval
  have hSome1 : Derives Δ (PacketReaderReturnSyntax.some w.castSucc O.castSucc p.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,PacketReaderReturnSyntax.some_rename] using lift hSome
  have hy1 : Derives Δ (Formula.mem y.castSucc w.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename] using lift hy
  have hS1 : Derives Δ (Formula.mem S.castSucc w.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename] using lift hS
  have hout := at_digit hZ1
    w.castSucc B.castSucc z.castSucc o.castSucc L.castSucc b.castSucc X.castSucc v.castSucc s.castSucc A.castSucc O.castSucc p.castSucc y.castSucc S.castSucc (Fin.last m)
    hw1 hB1 hz1 ho1 hState1 hb1 hX1 hHead1 hs1 hIH1 hEval1 hSome1 hy1 hS1
    (.conjL hD) (.conjL (.conjR hD)) (.conjL (.conjR (.conjR hD))) (.conjR (.conjR (.conjR hD)))
  simpa only [Formula.raise,result_rename] using hout

theorem point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w B z o L b X v s A O p : Fin m)
    (hw : Derives Γ (omega w))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hz : Derives Γ (empty z))
    (ho : Derives Γ (successor o z))
    (hState : Derives Γ (PacketReaderStepSyntax.state w L v s A))
    (hb : Derives Γ (PacketByteInputSyntax.byte b))
    (hX : Derives Γ (PacketByteInputSyntax.byteList w X))
    (hHead : Derives Γ (StructuralListSyntax.consCode w b X L))
    (hMore : Derives Γ (PacketReaderStepSyntax.more B b))
    (hs : Derives Γ ((empty s).neg))
    (hIH : Derives Γ (property w B z o X))
    (hEval : Derives Γ (PacketReaderEvalSyntax.eval w B z o L v s A p))
    (hSome : Derives Γ (PacketReaderReturnSyntax.some w O p))
    : Derives Γ (result w B z o L v s A p) := by
  have hBN := SyntaxNumerals.range hZ 128 w B hw hB
  have hbN := PacketByteInputLaws.byte_natural hZ w b hw hb
  have hUpdate := PacketReaderContinuation.exists_update hZ w B b v s hw hBN hbN
    (.conjL (.conjR hState)) (.conjL (.conjR (.conjR hState))) hMore
  let R := PacketReaderContinuation.resultBody w B b v s
  let Δ := Context.add R (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 R _ hUpdate
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := HornBinderRules.zf_body 2 hZ R
  have lift {φ : Formula m} (hh : Derives Γ φ) : Derives Δ (φ.rename (old 2)) := HornBinderRules.under_body 2 hh R
  have hw2 : Derives Δ (omega (old 2 w)) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,omega_rename] using lift hw
  have hB2 : Derives Δ (SyntaxNumeralSyntax.numeral 128 (old 2 B)) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,SyntaxNumeralSyntax.numeral_rename] using lift hB
  have hz2 : Derives Δ (empty (old 2 z)) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,empty_rename] using lift hz
  have ho2 : Derives Δ (successor (old 2 o) (old 2 z)) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,successor_rename] using lift ho
  have hState2 : Derives Δ (PacketReaderStepSyntax.state (old 2 w) (old 2 L) (old 2 v) (old 2 s) (old 2 A)) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,PacketReaderStepSyntax.state_rename] using lift hState
  have hb2 : Derives Δ (PacketByteInputSyntax.byte (old 2 b)) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,PacketByteInputSyntax.byte_rename] using lift hb
  have hX2 : Derives Δ (PacketByteInputSyntax.byteList (old 2 w) (old 2 X)) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,PacketByteInputSyntax.byteList_rename] using lift hX
  have hHead2 : Derives Δ (StructuralListSyntax.consCode (old 2 w) (old 2 b) (old 2 X) (old 2 L)) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,StructuralListSyntax.consCode_rename] using lift hHead
  have hs2 : Derives Δ ((empty (old 2 s)).neg) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,empty_rename] using lift hs
  have hIH2 : Derives Δ (property (old 2 w) (old 2 B) (old 2 z) (old 2 o) (old 2 X)) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,property_rename] using lift hIH
  have hEval2 : Derives Δ (PacketReaderEvalSyntax.eval (old 2 w) (old 2 B) (old 2 z) (old 2 o) (old 2 L) (old 2 v) (old 2 s) (old 2 A) (old 2 p)) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,PacketReaderEvalSyntax.eval_rename] using lift hEval
  have hSome2 : Derives Δ (PacketReaderReturnSyntax.some (old 2 w) (old 2 O) (old 2 p)) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,PacketReaderReturnSyntax.some_rename] using lift hSome
  have hout := at_update hZ1
    (old 2 w) (old 2 B) (old 2 z) (old 2 o) (old 2 L) (old 2 b) (old 2 X) (old 2 v) (old 2 s) (old 2 A) (old 2 O) (old 2 p) (slot 2 0) (slot 2 1)
    hw2 hB2 hz2 ho2 hState2 hb2 hX2 hHead2 hs2 hIH2 hEval2 hSome2
    (.conjL hR) (.conjL (.conjR hR)) (.conjR (.conjR hR))
  exact of_eq (result_rename w B z o L v s A p (old 2)).symm hout

end PPAC.Migration.Internal.PacketReaderPrefixContinue
