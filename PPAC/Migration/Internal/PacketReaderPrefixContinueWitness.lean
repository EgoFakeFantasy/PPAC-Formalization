import PPAC.Migration.Internal.PacketReaderPrefixContinuePoint
import PPAC.Migration.Internal.PacketReaderInverseArithmetic
import PPAC.Migration.Internal.PacketReaderSuccess

/-! All continuation reconstruction witnesses remain under original object existential elimination. -/
namespace PPAC.Migration.Internal.PacketReaderPrefixContinueWitness
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open PacketReaderPrefixSyntax (result resultBody result_rename property property_rename)
open PacketReaderVarintSegmentSyntax (guard guard_rename)
open PacketReaderStepSyntax (continuation continuation_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem at_witnesses {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w B z o L b X d v s A y S k Q T u c p : Fin m)
    (hw : Derives Γ (omega w))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hState : Derives Γ (PacketReaderStepSyntax.state w L v s A))
    (hHead : Derives Γ (StructuralListSyntax.consCode w b X L))
    (hd : Derives Γ (Formula.mem d B))
    (hk : Derives Γ ((empty k).neg))
    (hSum : Derives Γ (NaturalAdditionSyntax.sum w B d b))
    (hQ : Derives Γ (PacketVarintSyntax.canonical w k Q))
    (hSp : Derives Γ (StructuralListSpliceSyntax.splice w Q T X))
    (hByte : Derives Γ (PacketByteInputSyntax.byteList w T))
    (hTX : Derives Γ (Formula.mem T X))
    (hDigit : Derives Γ (PacketAffineSyntax.equation w d v s y))
    (hScale : Derives Γ (NaturalMultiplicationSyntax.product w s B S))
    (hValue : Derives Γ (PacketAffineSyntax.equation w k y S u))
    (hCons : Derives Γ (StructuralListSyntax.consCode w u A c))
    (hEval : Derives Γ (PacketReaderEvalSyntax.eval w B z o T z o c p))
    : Derives Γ (result w B z o L v s A p) := by
  have hBN := SyntaxNumerals.range hZ 128 w B hw hB
  have hkN := Derives.conjL (PacketVarintDomain.domain w k Q hQ)
  have hQN := PacketVarintExecutionHelpers.list_natural w k Q hQ
  have hbN := ZFArithmetic.add_range hZ w B d b hw hBN hSum
  let R := (Formula.mem (Fin.last m) w.castSucc).conj
    (PacketAffineSyntax.affine w.castSucc B.castSucc d.castSucc k.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (PacketAffineCore.exists_value hZ w B d k hw hBN hd hkN)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  let F := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (StructuralListSyntax.consCode w.castSucc.castSucc b.castSucc.castSucc Q.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add F (Context.image Formula.raise Δ)
  apply Derives.exE (p := F) (StructuralConsCore.exists_cons hZ1 w.castSucc b.castSucc Q.castSucc hw1 (under hbN R) (under hQN R))
  have hF : Derives Ξ F := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 F
  have lift {φ : Formula m} (hh : Derives Γ φ) : Derives Ξ φ.raise.raise := under (under hh R) F
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,omega_rename] using lift hw
  have hB2 : Derives Ξ (SyntaxNumeralSyntax.numeral 128 B.castSucc.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,SyntaxNumeralSyntax.numeral_rename] using lift hB
  have hState2 : Derives Ξ (PacketReaderStepSyntax.state w.castSucc.castSucc L.castSucc.castSucc v.castSucc.castSucc s.castSucc.castSucc A.castSucc.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,PacketReaderStepSyntax.state_rename] using lift hState
  have hHead2 : Derives Ξ (StructuralListSyntax.consCode w.castSucc.castSucc b.castSucc.castSucc X.castSucc.castSucc L.castSucc.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,StructuralListSyntax.consCode_rename] using lift hHead
  have hk2 : Derives Ξ ((empty k.castSucc.castSucc).neg) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,empty_rename] using lift hk
  have hSum2 : Derives Ξ (NaturalAdditionSyntax.sum w.castSucc.castSucc B.castSucc.castSucc d.castSucc.castSucc b.castSucc.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,NaturalAdditionSyntax.sum_rename] using lift hSum
  have hQ2 : Derives Ξ (PacketVarintSyntax.canonical w.castSucc.castSucc k.castSucc.castSucc Q.castSucc.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,PacketVarintSyntax.canonical_rename] using lift hQ
  have hSp2 : Derives Ξ (StructuralListSpliceSyntax.splice w.castSucc.castSucc Q.castSucc.castSucc T.castSucc.castSucc X.castSucc.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,StructuralListSpliceSyntax.splice_rename] using lift hSp
  have hByte2 : Derives Ξ (PacketByteInputSyntax.byteList w.castSucc.castSucc T.castSucc.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,PacketByteInputSyntax.byteList_rename] using lift hByte
  have hTX2 : Derives Ξ (Formula.mem T.castSucc.castSucc X.castSucc.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename] using lift hTX
  have hDigit2 : Derives Ξ (PacketAffineSyntax.equation w.castSucc.castSucc d.castSucc.castSucc v.castSucc.castSucc s.castSucc.castSucc y.castSucc.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,PacketAffineSyntax.equation_rename] using lift hDigit
  have hScale2 : Derives Ξ (NaturalMultiplicationSyntax.product w.castSucc.castSucc s.castSucc.castSucc B.castSucc.castSucc S.castSucc.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,NaturalMultiplicationSyntax.product_rename] using lift hScale
  have hValue2 : Derives Ξ (PacketAffineSyntax.equation w.castSucc.castSucc k.castSucc.castSucc y.castSucc.castSucc S.castSucc.castSucc u.castSucc.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,PacketAffineSyntax.equation_rename] using lift hValue
  have hCons2 : Derives Ξ (StructuralListSyntax.consCode w.castSucc.castSucc u.castSucc.castSucc A.castSucc.castSucc c.castSucc.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,StructuralListSyntax.consCode_rename] using lift hCons
  have hEval2 : Derives Ξ (PacketReaderEvalSyntax.eval w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc T.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc c.castSucc.castSucc p.castSucc.castSucc) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,PacketReaderEvalSyntax.eval_rename] using lift hEval
  have hAff2 : Derives Ξ (PacketAffineSyntax.affine w.castSucc.castSucc B.castSucc.castSucc d.castSucc.castSucc k.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [Formula.raise,PacketAffineSyntax.affine_rename] using under (.conjR hR) F
  have hout := PacketReaderPrefixContinuePoint.combine hZ2
    w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc L.castSucc.castSucc b.castSucc.castSucc X.castSucc.castSucc d.castSucc.castSucc v.castSucc.castSucc s.castSucc.castSucc A.castSucc.castSucc y.castSucc.castSucc S.castSucc.castSucc k.castSucc.castSucc Q.castSucc.castSucc T.castSucc.castSucc u.castSucc.castSucc c.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) p.castSucc.castSucc
    hw2 hB2 hState2 hHead2 hAff2 hk2 hSum2 hQ2 (.conjR hF) hSp2 hByte2 hTX2 hDigit2 hScale2 hValue2 hCons2 hEval2
  simpa only [Formula.raise,result_rename] using hout

theorem from_result {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w B z o L b X d v s A y S p : Fin m)
    (hw : Derives Γ (omega w))
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hState : Derives Γ (PacketReaderStepSyntax.state w L v s A))
    (hHead : Derives Γ (StructuralListSyntax.consCode w b X L))
    (hd : Derives Γ (Formula.mem d B))
    (hSum : Derives Γ (NaturalAdditionSyntax.sum w B d b))
    (hDigit : Derives Γ (PacketAffineSyntax.equation w d v s y))
    (hScale : Derives Γ (NaturalMultiplicationSyntax.product w s B S))
    (hSneq : Derives Γ ((Formula.equal S o).neg))
    (hResult : Derives Γ (result w B z o X y S A p))
    : Derives Γ (result w B z o L v s A p) := by
  let R := resultBody w B z o X y S A p
  let Δ := Context.add R (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 R _ hResult
  have hZ1 := HornBinderRules.zf_body 5 hZ R
  have lift {φ : Formula m} (hh : Derives Γ φ) : Derives Δ (φ.rename (old 5)) := HornBinderRules.under_body 5 hh R
  have hw5 : Derives Δ (omega (old 5 w)) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,omega_rename] using lift hw
  have hB5 : Derives Δ (SyntaxNumeralSyntax.numeral 128 (old 5 B)) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,SyntaxNumeralSyntax.numeral_rename] using lift hB
  have hState5 : Derives Δ (PacketReaderStepSyntax.state (old 5 w) (old 5 L) (old 5 v) (old 5 s) (old 5 A)) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,PacketReaderStepSyntax.state_rename] using lift hState
  have hHead5 : Derives Δ (StructuralListSyntax.consCode (old 5 w) (old 5 b) (old 5 X) (old 5 L)) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,StructuralListSyntax.consCode_rename] using lift hHead
  have hd5 : Derives Δ (Formula.mem (old 5 d) (old 5 B)) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename] using lift hd
  have hSum5 : Derives Δ (NaturalAdditionSyntax.sum (old 5 w) (old 5 B) (old 5 d) (old 5 b)) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,NaturalAdditionSyntax.sum_rename] using lift hSum
  have hDigit5 : Derives Δ (PacketAffineSyntax.equation (old 5 w) (old 5 d) (old 5 v) (old 5 s) (old 5 y)) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,PacketAffineSyntax.equation_rename] using lift hDigit
  have hScale5 : Derives Δ (NaturalMultiplicationSyntax.product (old 5 w) (old 5 s) (old 5 B) (old 5 S)) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename,NaturalMultiplicationSyntax.product_rename] using lift hScale
  have hSneq5 : Derives Δ ((Formula.equal (old 5 S) (old 5 o)).neg) := by
    simpa only [Formula.raise,Formula.neg,Formula.rename] using lift hSneq
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hCanonical := Derives.conjL hR
  have hSplice := Derives.conjL (.conjR hR)
  have hBytes := Derives.conjL (.conjR (.conjR hR))
  have hBelow := Derives.conjL (.conjR (.conjR (.conjR hR)))
  have hGuard := Derives.conjL (.conjR (.conjR (.conjR (.conjR hR))))
  have hEquation := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hR)))))
  have hAccumulator := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hR))))))
  have hTailEval := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hR))))))
  have hk : Derives Δ (empty (slot 5 0)).neg := by
    apply Derives.disjE hGuard
    · exact .botE (.impE (add hSneq5 _) (.hyp (Or.inl rfl)))
    · exact .hyp (Or.inl rfl)
  have hout := at_witnesses hZ1
    (old 5 w) (old 5 B) (old 5 z) (old 5 o) (old 5 L) (old 5 b) (old 5 X) (old 5 d) (old 5 v) (old 5 s) (old 5 A) (old 5 y) (old 5 S) (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4) (old 5 p)
    hw5 hB5 hState5 hHead5 hd5 hk hSum5 hCanonical hSplice hBytes hBelow hDigit5 hScale5 hEquation hAccumulator hTailEval
  exact of_eq (result_rename w B z o L v s A p (old 5)).symm hout

end PPAC.Migration.Internal.PacketReaderPrefixContinueWitness
