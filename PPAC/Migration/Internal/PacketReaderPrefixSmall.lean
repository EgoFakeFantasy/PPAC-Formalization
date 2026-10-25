import PPAC.Migration.Internal.PacketReaderPrefixSyntax
import PPAC.Migration.Internal.PacketVarintCanonicalRecursionBridge

/-! A genuine terminal digit yields an actual canonical singleton prefix, a strict actual suffix-code descent and the precise emitted accumulator on arbitrary value/scale/return candidates. -/
namespace PPAC.Migration.Internal.PacketReaderPrefixSmall
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderPrefixSyntax
open PacketReaderVarintSegmentSyntax (guard guard_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem at_witnesses {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w B z o L b X v s A p C u c : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hCons : Derives Γ (StructuralListSyntax.consCode w b X L))
    (hX : Derives Γ (PacketByteInputSyntax.byteList w X)) (hb : Derives Γ (.mem b B))
    (hGuard : Derives Γ (guard o b s))
    (hState : Derives Γ (PacketReaderStepSyntax.state w L v s A))
    (hEval : Derives Γ (PacketReaderEvalSyntax.eval w B z o L v s A p))
    (hC : Derives Γ (StructuralListSyntax.consCode w b o C))
    (hEquation : Derives Γ (PacketAffineSyntax.equation w b v s u))
    (hAcc : Derives Γ (StructuralListSyntax.consCode w u A c)) :
    Derives Γ (result w B z o L v s A p) := by
  have hBN := SyntaxNumerals.range hZ 128 w B hw hB
  have hbN := StructuralListTraceOrder.member_member hZ w b B hw hBN hb
  have hoN := StructuralListUnits.member hZ w z o hw hz ho
  have hNil := StructuralNil.at_unit hZ w z o hw hz ho
  have hXV := PacketByteInputLaws.valid w X hX
  have hXN := PacketByteInputLaws.natural w X hX
  have hSingleton := PacketVarintCanonicalRecursionSyntax.intro_singleton w b C o hNil hC
  have hCase : Derives Γ (PacketVarintCanonicalRecursionSyntax.atCriterion true w B b C) :=
    .disjL (.conjI hb hSingleton)
  have hAt := Derives.impE
    (.conjR (PacketVarintCanonicalRecursionBridge.at_actual_iff hZ w B b C hw hB)) hCase
  have hCanonical := PacketVarintSyntax.intro_actual w B b C hB hAt
  have hNilSplice := Derives.impE (.conjR (StructuralListSplice.nil_iff hZ w o X X hw hNil))
    (.conjI hXV (.eqRefl X))
  have hRemaining := StructuralListSplice.intro_remaining w b o X L X hNilSplice hCons
  have hSplice := StructuralListSplice.cons_backward hZ w b o C X L hw hbN hC hRemaining
  have hBelow := Derives.conjR (StructuralConsCore.components hZ w b X L hw hbN hXN hCons)
  have hTailState : Derives Γ (PacketReaderStepSyntax.state w X v s A) := .conjI hXV (.conjR hState)
  have hHead : Derives Γ (PacketReaderInputSyntax.headRest w L b X) := .conjI hbN (.conjI hXV hCons)
  have hStep := PacketReaderVarintBranches.terminal_digit hZ w B z o L b X v s A u c p
    hw hBN hz hoN hTailState hHead hb hGuard hEquation hAcc
  have hTailEval := Derives.impE (.conjL hStep) hEval
  exact intro_result w B z o L v s A p b C X u c
    hCanonical hSplice hX hBelow hGuard hEquation hAcc hTailEval

theorem small {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w B z o L b X v s A p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hCons : Derives Γ (StructuralListSyntax.consCode w b X L))
    (hX : Derives Γ (PacketByteInputSyntax.byteList w X)) (hb : Derives Γ (.mem b B))
    (hGuard : Derives Γ (guard o b s))
    (hState : Derives Γ (PacketReaderStepSyntax.state w L v s A))
    (hEval : Derives Γ (PacketReaderEvalSyntax.eval w B z o L v s A p)) :
    Derives Γ (result w B z o L v s A p) := by
  have hBN := SyntaxNumerals.range hZ 128 w B hw hB
  have hbN := StructuralListTraceOrder.member_member hZ w b B hw hBN hb
  have hoN := StructuralListUnits.member hZ w z o hw hz ho
  have hAN := StructuralListValidity.range w A (.conjR (.conjR (.conjR hState)))
  let R := (Formula.mem (Fin.last m) w.castSucc).conj
    (PacketAffineSyntax.equation w.castSucc b.castSucc v.castSucc s.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (PacketReaderArithmetic.exists_equation hZ w b v s hw hbN
    (.conjL (.conjR hState)) (.conjL (.conjR (.conjR hState))))
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  let S := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (StructuralListSyntax.consCode w.castSucc.castSucc (Fin.last m).castSucc A.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add S (Context.image Formula.raise Δ)
  apply Derives.exE (p := S) (StructuralConsCore.exists_cons hZ1 w.castSucc (Fin.last m) A.castSucc
    hw1 (.conjL hR) (under hAN R))
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 S
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 S)
  let U := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj
    (StructuralListSyntax.consCode w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc
      o.castSucc.castSucc.castSucc (Fin.last (m+2)))
  let Θ := Context.add U (Context.image Formula.raise Ξ)
  apply Derives.exE (p := U) (StructuralConsCore.exists_cons hZ2 w.castSucc.castSucc b.castSucc.castSucc
    o.castSucc.castSucc hw2 (under (under hbN R) S) (under (under hoN R) S))
  have hU : Derives Θ U := .hyp (Or.inl rfl)
  have hZ3 := ZFContext.under hZ2 U
  have lift3 {φ : Formula m} (hh : Derives Γ φ) : Derives Θ φ.raise.raise.raise :=
    under (under (under hh R) S) U
  have hw3 : Derives Θ (omega w.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise,omega_rename] using lift3 hw
  have hB3 : Derives Θ (SyntaxNumeralSyntax.numeral 128 B.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise,SyntaxNumeralSyntax.numeral_rename] using lift3 hB
  have hz3 : Derives Θ (empty z.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise,empty_rename] using lift3 hz
  have ho3 : Derives Θ (successor o.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise,successor_rename] using lift3 ho
  have hCons3 : Derives Θ (StructuralListSyntax.consCode w.castSucc.castSucc.castSucc
      b.castSucc.castSucc.castSucc X.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise,StructuralListSyntax.consCode_rename] using lift3 hCons
  have hX3 : Derives Θ (PacketByteInputSyntax.byteList w.castSucc.castSucc.castSucc X.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise,PacketByteInputSyntax.byteList_rename] using lift3 hX
  have hGuard3 : Derives Θ (guard o.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise,guard_rename] using lift3 hGuard
  have hState3 : Derives Θ (PacketReaderStepSyntax.state w.castSucc.castSucc.castSucc
      L.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise,PacketReaderStepSyntax.state_rename] using lift3 hState
  have hEval3 : Derives Θ (PacketReaderEvalSyntax.eval w.castSucc.castSucc.castSucc
      B.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc o.castSucc.castSucc.castSucc
      L.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc
      A.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise,PacketReaderEvalSyntax.eval_rename] using lift3 hEval
  have hEquation3 : Derives Θ (PacketAffineSyntax.equation w.castSucc.castSucc.castSucc
      b.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc) := by
    simpa only [Formula.raise,PacketAffineSyntax.equation_rename] using under (under (.conjR hR) S) U
  have hAcc3 : Derives Θ (StructuralListSyntax.consCode w.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc A.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) :=
    of_eq (StructuralListSyntax.consCode_rename w.castSucc.castSucc (Fin.last m).castSucc
      A.castSucc.castSucc (Fin.last (m+1)) Fin.castSucc) (under (.conjR hS) U)
  simpa only [Formula.raise,result_rename] using at_witnesses hZ3
    w.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc
    o.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc
    X.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc
    A.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc
    (Fin.last (m+2)) (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc
    hw3 hB3 hz3 ho3 hCons3 hX3 (lift3 hb) hGuard3 hState3 hEval3 (.conjR hU) hEquation3 hAcc3

end PPAC.Migration.Internal.PacketReaderPrefixSmall
