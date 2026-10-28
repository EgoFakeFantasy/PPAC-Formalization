import PPAC

/-! 第四步当前验收内部有限序列、自然递推及基本数值加乘；不是完整ProofZF/U或Con验收。 -/
namespace PPAC.Migration.Step4Checks
open Source GraphSyntax OmegaSyntax Internal
open FormulaCodeAllowedAritySyntax (expectedArity)
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
attribute [local implicit_reducible] SetTheory.signature

example {m} (f n b : Fin m) : SequenceSyntax.sequence f n b =
    (GraphSyntax.functionOn f n).conj (SequenceSyntax.bounded f b) := rfl

example {m} (f b : Fin m) : SequenceSyntax.bounded f b = Source.Formula.all (.all
    ((GraphSyntax.edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
      (.mem (Fin.last (m+1)) b.castSucc.castSucc))) := rfl

/-- 全部内部自然数长度，结论的序列图也是内部存在量词。 -/
example : ObjectSequences.naturalSentence = ((OmegaSyntax.omega (0 : Fin 1)).imp
    (.all ((Source.Formula.mem (Fin.last 1) (0 : Fin 1).castSucc).imp
      (Source.Formula.ex (SequenceSyntax.sequence (Fin.last 2) (Fin.last 1).castSucc (0 : Fin 1).castSucc.castSucc))))).close := rfl

/-- 完整域、精确边、实际旧域限制同时包含在追加结果。 -/
example {m} (g k f n y b : Fin m) : SequenceSyntax.append g k f n y b =
    (SequenceSyntax.sequence g k b).conj ((GraphInsertSyntax.edgeLaw g f n y).conj (RestrictionSyntax.restrict f g n)) := rfl

example : Source.Derives (ObjectSequences.assumptions.at 0) ObjectSequences.naturalSentence := ObjectSequences.source_natural
example : Source.Derives (ObjectSequences.assumptions.at 0) ObjectSequences.appendSentence := ObjectSequences.source_append
example : Source.Derives (ObjectSequences.assumptions.at 0) ObjectSequences.prefixSentence := ObjectSequences.source_prefix
example : FirstOrder.Derives (TheoryTransport.theory ObjectSequences.assumptions) []
    (Translation.sentence ObjectSequences.naturalSentence) := ObjectSequences.natural_kernel_certificate
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectSequences.naturalSentence) := ObjectSequences.native_natural
example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectSequences.naturalAppendSentence) := ObjectSequences.native_naturalAppend

/-- 模式索引是外部任意有限公式，每一实例返回完整闭句的原核Derives。 -/
example {n} (p : Source.Formula (n+2)) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectCheckedSequences.appendSentence p)) := ObjectCheckedSequences.native_append p
example {n} (p : Source.Formula (n+2)) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectCheckedSequences.prefixSentence p)) := ObjectCheckedSequences.native_prefix p

example {m k n} (p : Source.Formula (n+2)) (ρ : Fin n → Fin m) (f d b : Fin m) (r : Fin m → Fin k) :
    (CheckedSequence.checked p ρ f d b).rename r = CheckedSequence.checked p (fun i => r (ρ i)) (r f) (r d) (r b) :=
  CheckedSequence.checked_rename p ρ f d b r

/-- 步进总性量化全部内部集合，不借用宿主总函数。 -/
example {n m} (p : Source.Formula (n+2)) (ρ : Fin n → Fin m) :
    NaturalRecursionSyntax.relationTotal p ρ = Source.Formula.all (.ex
      (ReplacementPredicates.rel p (ReplacementPredicates.paramsUp (ReplacementPredicates.paramsUp ρ))
        (Fin.last m).castSucc (Fin.last (m+1)))) := rfl

/-- 原递归矩阵确实展开成实际自然前驱/历史图算子。 -/
example {n m} (p : Source.Formula (n+2)) (ρ : Fin n → Fin m) (w a x h y : Fin m) :
    OrdinalRecursionSyntax.operator (NaturalRecursionSyntax.matrix p) (NaturalRecursionSyntax.extend ρ w a) x h y =
      NaturalRecursionSyntax.operation p ρ w a x h y := NaturalRecursionSyntax.matrix_operator p ρ w a x h y

example : FirstOrder.Derives nativeZF [] (Translation.sentence OmegaOrdinals.sentence) := OmegaOrdinals.native_proof
example {n} (p : Source.Formula (n+2)) : FirstOrder.Derives nativeZF []
    (Translation.sentence (NaturalRecursion.totalSentence p)) := NaturalRecursion.native_total p
example {n} (p : Source.Formula (n+2)) : FirstOrder.Derives nativeZF []
    (Translation.sentence (NaturalRecursion.deterministicSentence p)) := NaturalRecursion.native_deterministic p
example {n} (p : Source.Formula (n+2)) : FirstOrder.Derives nativeZF []
    (Translation.sentence (NaturalRecursion.existenceSentence p)) := NaturalRecursion.native_existence p
example {n} (p : Source.Formula (n+2)) : FirstOrder.Derives nativeZF []
    (Translation.sentence (NaturalRecursion.uniquenessSentence p)) := NaturalRecursion.native_uniqueness p
example {n} (p : Source.Formula (n+2)) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectNaturalRecursion.sentence p)) := ObjectNaturalRecursion.native_proof p

/-- 具体实例的步进是原后继定义，总性/单值义务已实际消去。 -/
example {m} (ρ : Fin 0 → Fin m) (x y : Fin m) :
    ReplacementPredicates.rel SuccessorRecursion.stepMatrix ρ x y = OmegaSyntax.successor y x := SuccessorRecursion.step_rel ρ x y
example : FirstOrder.Derives nativeZF [] (Translation.sentence SuccessorRecursion.sentence) := SuccessorRecursion.native_proof
example : FirstOrder.Derives nativeZF [] (Translation.sentence SuccessorRecursion.zeroSentence) := SuccessorRecursion.native_zero

/-- 乘法初值是内部存在量化的实际空集，非宿主固定对象。 -/
example {m} (w a n y : Fin m) : NaturalMultiplicationSyntax.product w a n y = Source.Formula.ex
  ((OmegaSyntax.empty (Fin.last m)).conj (NaturalEvaluationSyntax.evaluation NaturalMultiplicationStep.matrix
    (fun i => (NaturalMultiplicationSyntax.params w a i).castSucc) w.castSucc (Fin.last m) n.castSucc y.castSucc)) := rfl

/-- 全域总化的后继步在内部自然数上严格等于原后继。 -/
example {m} {Γ : Source.Context m} (w x y : Fin m)
    (hx : Source.Derives Γ (.mem x w)) (hy : Source.Derives Γ (NaturalSuccessorStep.step w x y)) :
    Source.Derives Γ (OmegaSyntax.successor y x) := NaturalSuccessorStep.on_natural w x y hx hy

/-- 乘法自然输入的实际步进就是已证明的内部加法。 -/
example {m} {Γ : Source.Context m} (w a x y : Fin m)
    (hx : Source.Derives Γ (.mem x w)) (hy : Source.Derives Γ (NaturalMultiplicationStep.step w a x y)) :
    Source.Derives Γ (NaturalAdditionSyntax.sum w x a y) := NaturalMultiplicationStep.on_natural w a x y hx hy

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalAddition.fiberSentence) := ObjectNaturalAddition.native_fiber

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalAddition.closureSentence) := ObjectNaturalAddition.native_closure

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalAddition.zeroSentence) := ObjectNaturalAddition.native_zero

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalAddition.successorSentence) := ObjectNaturalAddition.native_successor

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalAddition.leftZeroSentence) := ObjectNaturalAddition.native_leftZero

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalMultiplication.fiberSentence) := ObjectNaturalMultiplication.native_fiber

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalMultiplication.closureSentence) := ObjectNaturalMultiplication.native_closure

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalMultiplication.zeroSentence) := ObjectNaturalMultiplication.native_zero

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalMultiplication.successorSentence) := ObjectNaturalMultiplication.native_successor

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalMultiplication.leftZeroSentence) := ObjectNaturalMultiplication.native_leftZero

/-- 自然顺序界直接使用对象相等或成员关系。 -/
example {m} (a y : Fin m) : NaturalAdditionBounds.below a y =
    (Source.Formula.equal a y).disj (.mem a y) := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalAdditionAlgebra.leftSuccessorSentence) := ObjectNaturalAdditionAlgebra.native_leftSuccessor

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalAdditionAlgebra.commutativeSentence) := ObjectNaturalAdditionAlgebra.native_commutative

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalAdditionAlgebra.associativeSentence) := ObjectNaturalAdditionAlgebra.native_associative

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalAdditionAlgebra.cancelRightSentence) := ObjectNaturalAdditionAlgebra.native_cancelRight

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalAdditionAlgebra.cancelLeftSentence) := ObjectNaturalAdditionAlgebra.native_cancelLeft

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalAdditionOrder.boundsSentence) := ObjectNaturalAdditionOrder.native_bounds

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalAdditionOrder.zeroSentence) := ObjectNaturalAdditionOrder.native_zero

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalAdditionOrder.strictRightSentence) := ObjectNaturalAdditionOrder.native_strictRight

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalAdditionOrder.strictLeftSentence) := ObjectNaturalAdditionOrder.native_strictLeft

/-- 原ZF上下文接口仅映射原公理；没有将乘法结论放入假设字段。 -/
example {m} (Γ : Source.Context m) : ZFContext.Evidence Γ =
    (∀ q, Source.SetLanguage.ZF.at m q → Γ q) := rfl

/-- 单位元由实际对象空集及其原后继指定。 -/
example : ObjectNaturalMultiplicationAlgebra.unitSentence = ((OmegaSyntax.omega (0 : Fin 5)).imp
  ((Source.Formula.mem 1 0).imp ((OmegaSyntax.empty 2).imp ((OmegaSyntax.successor 3 2).imp
    (((NaturalMultiplicationSyntax.product 0 1 3 4).iff (.equal 4 1)).conj
      ((NaturalMultiplicationSyntax.product 0 3 1 4).iff (.equal 4 1))))))).close := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalAdditionReassociation.swapSentence) := ObjectNaturalAdditionReassociation.native_swap

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalAdditionReassociation.interchangeSentence) := ObjectNaturalAdditionReassociation.native_interchange

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalMultiplicationAlgebra.sumRightSentence) := ObjectNaturalMultiplicationAlgebra.native_sumRight

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalMultiplicationAlgebra.sumLeftSentence) := ObjectNaturalMultiplicationAlgebra.native_sumLeft

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalMultiplicationAlgebra.leftSuccessorSentence) := ObjectNaturalMultiplicationAlgebra.native_leftSuccessor

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalMultiplicationAlgebra.commutativeSentence) := ObjectNaturalMultiplicationAlgebra.native_commutative

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalMultiplicationAlgebra.associativeSentence) := ObjectNaturalMultiplicationAlgebra.native_associative

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalMultiplicationAlgebra.unitSentence) := ObjectNaturalMultiplicationAlgebra.native_unit

/-- 差值见证及唯一性候选均明确限制在内部ω中。 -/
example {m} (w a b d : Fin m) : NaturalDifferenceSyntax.witness w a b d =
    (Source.Formula.mem d w).conj (NaturalAdditionSyntax.sum w a d b) := rfl
example {m} (w a b : Fin m) : NaturalDifferenceSyntax.fiber w a b = Source.Formula.ex
  ((NaturalDifferenceSyntax.witness w.castSucc a.castSucc b.castSucc (Fin.last m)).conj (Source.Formula.all
    ((NaturalDifferenceSyntax.witness w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc)))) := rfl

/-- 正公共乘数前提属于公开对象句子，不把零乘数纳入反射/消去。 -/
example : ObjectNaturalMultiplicativeOrder.rightWeakSentence = ((OmegaSyntax.omega (0 : Fin 6)).imp
  ((Source.Formula.mem 1 0).imp ((Source.Formula.mem 2 0).imp ((Source.Formula.mem 3 0).imp
    ((OmegaSyntax.empty 3).neg.imp ((NaturalMultiplicationSyntax.product 0 1 3 4).imp
      ((NaturalMultiplicationSyntax.product 0 2 3 5).imp
        ((NaturalAdditionBounds.below 1 2).iff (NaturalAdditionBounds.below 4 5))))))))).close := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalOrder.totalSentence) := ObjectNaturalOrder.native_total

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalOrder.transitiveSentence) := ObjectNaturalOrder.native_transitive

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalOrder.antisymmetricSentence) := ObjectNaturalOrder.native_antisymmetric

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalOrder.successorSentence) := ObjectNaturalOrder.native_successor

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalDifference.orderSentence) := ObjectNaturalDifference.native_order

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalDifference.fiberSentence) := ObjectNaturalDifference.native_fiber

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalDifference.strictSentence) := ObjectNaturalDifference.native_strict

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalDifference.zeroSentence) := ObjectNaturalDifference.native_zero

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalAdditiveOrder.rightWeakSentence) := ObjectNaturalAdditiveOrder.native_rightWeak

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalAdditiveOrder.rightStrictSentence) := ObjectNaturalAdditiveOrder.native_rightStrict

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalAdditiveOrder.leftWeakSentence) := ObjectNaturalAdditiveOrder.native_leftWeak

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalAdditiveOrder.leftStrictSentence) := ObjectNaturalAdditiveOrder.native_leftStrict

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalMultiplicativeOrder.zeroSentence) := ObjectNaturalMultiplicativeOrder.native_zero

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalMultiplicativeOrder.rightMonotoneSentence) := ObjectNaturalMultiplicativeOrder.native_rightMonotone

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalMultiplicativeOrder.rightWeakSentence) := ObjectNaturalMultiplicativeOrder.native_rightWeak

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalMultiplicativeOrder.rightStrictSentence) := ObjectNaturalMultiplicativeOrder.native_rightStrict

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalMultiplicativeOrder.rightCancelSentence) := ObjectNaturalMultiplicativeOrder.native_rightCancel

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalMultiplicativeOrder.leftMonotoneSentence) := ObjectNaturalMultiplicativeOrder.native_leftMonotone

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalMultiplicativeOrder.leftWeakSentence) := ObjectNaturalMultiplicativeOrder.native_leftWeak

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalMultiplicativeOrder.leftStrictSentence) := ObjectNaturalMultiplicativeOrder.native_leftStrict

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalMultiplicativeOrder.leftCancelSentence) := ObjectNaturalMultiplicativeOrder.native_leftCancel

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalNumericBounds.unitSentence) := ObjectNaturalNumericBounds.native_unit

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalNumericBounds.factorsSentence) := ObjectNaturalNumericBounds.native_factors

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalNumericBounds.squareSentence) := ObjectNaturalNumericBounds.native_square

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalNumericBounds.squareStrictSentence) := ObjectNaturalNumericBounds.native_squareStrict

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectNaturalNumericBounds.squareInjectiveSentence) := ObjectNaturalNumericBounds.native_squareInjective

/-- 固定原配数分支及实际中间值；这些是对象AST等式。 -/
example {m} (w a b p : Fin m) : GodelPairSyntax.code w a b p =
    ((Source.Formula.mem a b).conj (GodelPairSyntax.lower w a b p)).disj
      ((Source.Formula.mem a b).neg.conj (GodelPairSyntax.upper w a b p)) := rfl

example {m} (w a b p : Fin m) : GodelPairSyntax.lower w a b p = .ex
    ((NaturalMultiplicationSyntax.product w.castSucc b.castSucc b.castSucc (Fin.last m)).conj
      (NaturalAdditionSyntax.sum w.castSucc (Fin.last m) a.castSucc p.castSucc)) := rfl

example {m} (w a b p : Fin m) : GodelPairSyntax.upper w a b p = .ex (.ex
    ((NaturalMultiplicationSyntax.product w.castSucc.castSucc a.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc).conj
      ((NaturalAdditionSyntax.sum w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc (Fin.last (m+1))).conj
        (NaturalAdditionSyntax.sum w.castSucc.castSucc (Fin.last (m+1)) b.castSucc.castSucc p.castSucc.castSucc)))) := rfl

/-- 单值性不把候选编码值限制在外部标准自然数；源闭句保留全部对象量词。 -/
example : ObjectGodelPair.injectiveSentence = ((OmegaSyntax.omega (0 : Fin 6)).imp
    ((Source.Formula.mem 1 0).imp ((Source.Formula.mem 2 0).imp ((Source.Formula.mem 3 0).imp
      ((Source.Formula.mem 4 0).imp ((GodelPairSyntax.code 0 1 2 5).imp
        ((GodelPairSyntax.code 0 3 4 5).imp ((Source.Formula.equal 1 3).conj (.equal 2 4))))))))).close := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGodelPair.fiberSentence) := ObjectGodelPair.native_fiber

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGodelPair.closureSentence) := ObjectGodelPair.native_closure

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGodelPair.valueUniqueSentence) := ObjectGodelPair.native_valueUnique

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGodelPair.componentsSentence) := ObjectGodelPair.native_components

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGodelPair.injectiveSentence) := ObjectGodelPair.native_injective

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGodelPair.lowerBandSentence) := ObjectGodelPair.native_lowerBand

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGodelPair.upperBandSentence) := ObjectGodelPair.native_upperBand

/-- 解码候选明确为内部自然对象；编码关系仍为固定原配数。 -/
example {m} (w p a b : Fin m) : GodelUnpairSyntax.witness w p a b =
    ((Source.Formula.mem a w).conj (.mem b w)).conj (GodelPairSyntax.code w a b p) := rfl

example {m} (w p : Fin m) : GodelUnpairSyntax.preimage w p = .ex (.ex
    (GodelUnpairSyntax.witness w.castSucc.castSucc p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))) := rfl

/-- 双向刻画量化全部对象候选，左侧自然范围没有被省略。 -/
example {m} (w p a b : Fin m) : GodelUnpairSyntax.exactAt w p a b = .all (.all
    ((GodelUnpairSyntax.witness w.castSucc.castSucc p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
      ((Source.Formula.equal (Fin.last m).castSucc a.castSucc.castSucc).conj (.equal (Fin.last (m+1)) b.castSucc.castSucc)))) := rfl

example : ObjectGodelUnpair.totalSentence = ((OmegaSyntax.omega (0 : Fin 2)).imp
    ((Source.Formula.mem 1 0).imp (GodelUnpairSyntax.preimage 0 1))).close := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGodelUnpair.zeroSentence) := ObjectGodelUnpair.native_zero

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGodelUnpair.successorSentence) := ObjectGodelUnpair.native_successor

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGodelUnpair.totalSentence) := ObjectGodelUnpair.native_total

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGodelUnpair.characterizationSentence) := ObjectGodelUnpair.native_characterization

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGodelUnpair.fiberSentence) := ObjectGodelUnpair.native_fiber

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectGodelUnpair.boundedSentence) := ObjectGodelUnpair.native_bounded

/-- 原raw_node严格是先原配数、再对象后继，未交换参数或省去见证。 -/
example {m} (w tag payload n : Fin m) : StructuralNodeSyntax.raw w tag payload n = .ex
    ((GodelPairSyntax.code w.castSucc tag.castSucc payload.castSucc (Fin.last m)).conj
      (OmegaSyntax.successor n.castSucc (Fin.last m))) := rfl

/-- 节点解码候选均在内部ω；有界纤维保存严格成员子码界。 -/
example {m} (w n a b : Fin m) : StructuralNodeDecodeSyntax.witness w n a b =
    ((Source.Formula.mem a w).conj (.mem b w)).conj (StructuralNodeSyntax.raw w a b n) := rfl

example {m} (w n : Fin m) : StructuralNodeDecodeSyntax.boundedFiber w n = .ex (.ex
    (((StructuralNodeDecodeSyntax.witness w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
      (StructuralNodeDecodeSyntax.exactAt w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))).conj
        ((Source.Formula.mem (Fin.last m).castSucc n.castSucc.castSucc).conj (.mem (Fin.last (m+1)) n.castSucc.castSucc)))) := rfl

/-- 仅正码是raw_node；不能将原始节点分解等同于有效语法树检查。 -/
example : ObjectStructuralNode.positiveIffSentence = ((OmegaSyntax.omega (0 : Fin 2)).imp
    ((Source.Formula.mem 1 0).imp ((OmegaSyntax.empty 1).neg.iff (StructuralNodeDecodeSyntax.preimage 0 1)))).close := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralNode.encodeFiberSentence) := ObjectStructuralNode.native_encodeFiber

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralNode.closureSentence) := ObjectStructuralNode.native_closure

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralNode.positiveSentence) := ObjectStructuralNode.native_positive

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralNode.componentsSentence) := ObjectStructuralNode.native_components

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralNode.injectiveSentence) := ObjectStructuralNode.native_injective

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralNode.positiveIffSentence) := ObjectStructuralNode.native_positiveIff

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralNode.decodeTotalSentence) := ObjectStructuralNode.native_decodeTotal

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralNode.decodeFiberSentence) := ObjectStructuralNode.native_decodeFiber

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralNode.decodeBoundsSentence) := ObjectStructuralNode.native_decodeBounds

/-- 原Nil保留零标签及零载荷；Cons保留单位标签与内层原配数。 -/
example {m} (w n : Fin m) : StructuralListSyntax.nilCode w n = .ex
    ((OmegaSyntax.empty (Fin.last m)).conj (StructuralNodeSyntax.raw w.castSucc (Fin.last m) (Fin.last m) n.castSucc)) := rfl

example {m} (w h t n : Fin m) : StructuralListSyntax.consCode w h t n = .ex (.ex
    ((OmegaSyntax.empty (Fin.last m).castSucc).conj ((OmegaSyntax.successor (Fin.last (m+1)) (Fin.last m).castSucc).conj (.ex
      ((GodelPairSyntax.code w.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc (Fin.last (m+2))).conj
        (StructuralNodeSyntax.raw w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) n.castSucc.castSucc.castSucc)))))) := rfl

/-- 头尾是任意内部自然对象；原构造器值定理没有预设尾码已是有效列表。 -/
example : ObjectStructuralList.boundsSentence = ((OmegaSyntax.omega (0 : Fin 4)).imp
    ((Source.Formula.mem 1 0).imp ((Source.Formula.mem 2 0).imp ((StructuralListSyntax.consCode 0 1 2 3).imp
      ((Source.Formula.mem 1 3).conj (.mem 2 3)))))).close := rfl

/-- Nil/Cons互斥不需要额外自然头尾前提。 -/
example : ObjectStructuralList.disjointSentence = ((OmegaSyntax.omega (0 : Fin 4)).imp
    ((StructuralListSyntax.nilCode 0 3).imp ((StructuralListSyntax.consCode 0 1 2 3).imp Source.Formula.bot))).close := rfl

/-- 实际内部零、单位及单位后继给出空字段列与叶零的数值封装。 -/
example : ObjectStructuralList.leafZeroSentence = ((OmegaSyntax.omega (0 : Fin 4)).imp
    ((OmegaSyntax.empty 1).imp ((OmegaSyntax.successor 2 1).imp ((OmegaSyntax.successor 3 2).imp
      ((StructuralListSyntax.nilCode 0 2).conj (StructuralNodeSyntax.raw 0 1 2 3)))))).close := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralList.nilValueSentence) := ObjectStructuralList.native_nilValue

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralList.nilFiberSentence) := ObjectStructuralList.native_nilFiber

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralList.consTagSentence) := ObjectStructuralList.native_consTag

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralList.consFiberSentence) := ObjectStructuralList.native_consFiber

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralList.closureSentence) := ObjectStructuralList.native_closure

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralList.boundsSentence) := ObjectStructuralList.native_bounds

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralList.injectiveSentence) := ObjectStructuralList.native_injective

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralList.disjointSentence) := ObjectStructuralList.native_disjoint

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralList.leafZeroSentence) := ObjectStructuralList.native_leafZero

/-- 实际内部长度、后继域、完整序列图、Nil种子和相邻Cons步均属于公开纯公式。 -/
example {m} (w z e l d f n : Fin m) : StructuralListTraceSyntax.trace w z e l d f n =
    (((OmegaSyntax.empty z).conj (StructuralListSyntax.nilCode w e)).conj (((Source.Formula.mem l w).conj (OmegaSyntax.successor d l)).conj ((SequenceSyntax.sequence f d w).conj ((GraphSyntax.edge f z e).conj (StructuralListTraceSyntax.links w l f))))).conj (GraphSyntax.edge f l n) := rfl

/-- 有效性存在量化五个内部对象；不以宿主有限列表或外部长度范围代替。 -/
example {m} (w n : Fin m) : StructuralListTraceSyntax.valid w n = .ex (.ex (.ex (.ex (.ex
    (StructuralListTraceSyntax.trace w.castSucc.castSucc.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc
      (Fin.last (m+2)).castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+4))
      n.castSucc.castSucc.castSucc.castSucc.castSucc))))) := rfl

/-- 精确分解保留有效尾码和实际自然head；不是只解析原始节点。 -/
example {m} (w n : Fin m) : StructuralListDecodeSyntax.decomposition w n =
    (StructuralListSyntax.nilCode w n).disj (.ex
      ((StructuralListTraceSyntax.valid w.castSucc (Fin.last m)).conj (.ex
        ((Source.Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
          (StructuralListSyntax.consCode w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc))))) := rfl

example : ObjectStructuralListTrace.consIffSentence = ((OmegaSyntax.omega (0 : Fin 4)).imp ((Source.Formula.mem 1 0).imp ((Source.Formula.mem 2 0).imp ((StructuralListSyntax.consCode 0 1 2 3).imp ((StructuralListTraceSyntax.valid 0 3).iff (StructuralListTraceSyntax.valid 0 2)))))).close := rfl

example : ObjectStructuralListTrace.zeroRejectedSentence = ((OmegaSyntax.omega (0 : Fin 2)).imp ((OmegaSyntax.empty 1).imp ((StructuralListTraceSyntax.valid 0 1).neg))).close := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListTrace.baseSentence) := ObjectStructuralListTrace.native_base

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListTrace.appendSentence) := ObjectStructuralListTrace.native_append

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListTrace.nilValidSentence) := ObjectStructuralListTrace.native_nilValid

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListTrace.consValidSentence) := ObjectStructuralListTrace.native_consValid

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListTrace.rangeSentence) := ObjectStructuralListTrace.native_range

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListTrace.recursiveSentence) := ObjectStructuralListTrace.native_recursive

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListTrace.consIffSentence) := ObjectStructuralListTrace.native_consIff

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListTrace.positiveSentence) := ObjectStructuralListTrace.native_positive

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListTrace.zeroRejectedSentence) := ObjectStructuralListTrace.native_zeroRejected

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListTrace.prefixSentence) := ObjectStructuralListTrace.native_prefix

/-- 实际长度关系保留四个内部轨迹见证，l始终是对象变量。 -/
example {m} (w n l : Fin m) : StructuralListLengthSyntax.hasLength w n l =
    .ex (.ex (.ex (.ex (StructuralListTraceSyntax.trace w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc l.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) n.castSucc.castSucc.castSucc.castSucc)))) := rfl

/-- 唯一性比较任意具有实际长度见证的对象候选，不限制为外部标准长度。 -/
example {m} (w n : Fin m) : StructuralListLengthSyntax.fiber w n =
    .ex (((Source.Formula.mem (Fin.last m) w.castSucc).conj (StructuralListLengthSyntax.hasLength w.castSucc n.castSucc (Fin.last m))).conj (.all ((StructuralListLengthSyntax.hasLength w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp (Source.Formula.equal (Fin.last (m+1)) (Fin.last m).castSucc)))) := rfl

/-- 归纳假设只覆盖内部w与当前码的实际成员。 -/
example {m} (w n : Fin m) : StructuralListLengthStep.earlier w n =
    .all ((Source.Formula.mem (Fin.last m) w.castSucc).imp ((Source.Formula.mem (Fin.last m) n.castSucc).imp (StructuralListLengthSyntax.property w.castSucc (Fin.last m)))) := rfl

example : ObjectStructuralListLength.uniqueSentence = ((OmegaSyntax.omega (0 : Fin 4)).imp ((StructuralListLengthSyntax.hasLength 0 1 2).imp ((StructuralListLengthSyntax.hasLength 0 1 3).imp (Source.Formula.equal 2 3)))).close := rfl

example : ObjectStructuralListLength.traceUniqueSentence = ((OmegaSyntax.omega (0 : Fin 12)).imp ((StructuralListTraceSyntax.trace 0 1 2 3 4 5 6).imp ((StructuralListTraceSyntax.trace 0 7 8 9 10 11 6).imp (Source.Formula.equal 3 9)))).close := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListLength.prefixTraceSentence) := ObjectStructuralListLength.native_prefixTrace

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListLength.knownTailEdgeSentence) := ObjectStructuralListLength.native_knownTailEdge

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListLength.nilEmptySentence) := ObjectStructuralListLength.native_nilEmpty

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListLength.consPredecessorSentence) := ObjectStructuralListLength.native_consPredecessor

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListLength.uniqueSentence) := ObjectStructuralListLength.native_unique

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListLength.traceUniqueSentence) := ObjectStructuralListLength.native_traceUnique

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListLength.fiberSentence) := ObjectStructuralListLength.native_fiber

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListLength.rangeSentence) := ObjectStructuralListLength.native_range

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListLength.existsSentence) := ObjectStructuralListLength.native_exists

/-- 两个模式实例明确是原head/tail分量，Bool仅为外部公式模式索引。 -/
example {m} (w x y a : Fin m) : StructuralListProjectionSyntax.body true w x y a =
    ((Source.Formula.mem y w).conj (.mem a w)).conj (StructuralListSyntax.consCode w y a x) := rfl

example {m} (w x y a : Fin m) : StructuralListProjectionSyntax.body false w x y a =
    ((Source.Formula.mem y w).conj (.mem a w)).conj (StructuralListSyntax.consCode w a y x) := rfl

/-- 非Cons的任何内部集合输入均有原空集分支，不要求输入有效或自然。 -/
example {m} (head : Bool) (w x y : Fin m) : StructuralListProjectionSyntax.step head w x y =
    (StructuralListProjectionSyntax.selected head w x y).disj
      ((StructuralListProjectionSyntax.hasCons head w x).neg.conj (OmegaSyntax.empty y)) := rfl

/-- 实际迭代仍由后继域与完整原递归图见证。 -/
example {m} (head : Bool) (w a r y : Fin m) : StructuralListProjectionSyntax.iteration head w a r y =
    NaturalEvaluationSyntax.evaluation (StructuralListProjectionSyntax.matrix head) (fun _ : Fin 1 => w) w a r y := rfl

/-- 全内部自然索引纤维没有把算子总性或单值性留作闭句前提。 -/
example (head : Bool) : ObjectStructuralListProjection.fiberSentence head =
    ((OmegaSyntax.omega (0 : Fin 3)).imp ((Source.Formula.mem 2 0).imp (StructuralListProjectionSyntax.iterationFiber head 0 1 2))).close := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListProjection.totalSentence true)) := ObjectStructuralListProjection.native_total true

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListProjection.totalSentence false)) := ObjectStructuralListProjection.native_total false

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListProjection.functionalSentence true)) := ObjectStructuralListProjection.native_functional true

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListProjection.functionalSentence false)) := ObjectStructuralListProjection.native_functional false

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListProjection.rangeSentence true)) := ObjectStructuralListProjection.native_range true

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListProjection.rangeSentence false)) := ObjectStructuralListProjection.native_range false

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListProjection.consSentence true)) := ObjectStructuralListProjection.native_cons true

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListProjection.consSentence false)) := ObjectStructuralListProjection.native_cons false

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListProjection.nilSentence true)) := ObjectStructuralListProjection.native_nil true

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListProjection.nilSentence false)) := ObjectStructuralListProjection.native_nil false

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListProjection.offConsSentence true)) := ObjectStructuralListProjection.native_offCons true

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListProjection.offConsSentence false)) := ObjectStructuralListProjection.native_offCons false

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListProjection.recursorsSentence true)) := ObjectStructuralListProjection.native_recursors true

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListProjection.recursorsSentence false)) := ObjectStructuralListProjection.native_recursors false

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListProjection.fiberSentence true)) := ObjectStructuralListProjection.native_fiber true

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListProjection.fiberSentence false)) := ObjectStructuralListProjection.native_fiber false

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListProjection.closureSentence true)) := ObjectStructuralListProjection.native_closure true

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListProjection.closureSentence false)) := ObjectStructuralListProjection.native_closure false

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListProjection.zeroSentence true)) := ObjectStructuralListProjection.native_zero true

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListProjection.zeroSentence false)) := ObjectStructuralListProjection.native_zero false

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListProjection.nextSentence true)) := ObjectStructuralListProjection.native_next true

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListProjection.nextSentence false)) := ObjectStructuralListProjection.native_next false

/-- 终端性质比较所有实际长度与真实tail求值，无外部标准长度限制。 -/
example {m} (w n : Fin m) : StructuralListEndSyntax.ends w n = .all (.all
    ((StructuralListLengthSyntax.hasLength w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc).imp
      ((StructuralListProjectionSyntax.iteration false w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
        (StructuralListSyntax.nilCode w.castSucc.castSucc (Fin.last (m+1)))))) := rfl

/-- 闭句中已消去成员归纳假设，只保留实际长度与求值。 -/
example : ObjectStructuralListEnd.terminalSentence = ((OmegaSyntax.omega (0 : Fin 4)).imp
    ((StructuralListLengthSyntax.hasLength 0 1 2).imp ((StructuralListProjectionSyntax.iteration false 0 1 2 3).imp (StructuralListSyntax.nilCode 0 3)))).close := rfl

/-- 原完整迹的Nil种子由同一个实际长度下的真实tail递归恢复。 -/
example : ObjectStructuralListEnd.traceRecoverySentence = ((OmegaSyntax.omega (0 : Fin 7)).imp
    ((StructuralListTraceSyntax.trace 0 1 2 3 4 5 6).imp (StructuralListProjectionSyntax.iteration false 0 6 3 2))).close := rfl

/-- 端点见证同时保留内部长度、完整构造迹、真实递归图求值和Nil。 -/
example {m} (w n : Fin m) : StructuralListEndSyntax.existsTerminal w n = .ex (.ex
    ((((Source.Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj
      (StructuralListLengthSyntax.hasLength w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc)).conj
      (StructuralListProjectionSyntax.iteration false w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))).conj
      (StructuralListSyntax.nilCode w.castSucc.castSucc (Fin.last (m+1))))) := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListEnd.coupledSentence true)) := ObjectStructuralListEnd.native_coupled true

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListEnd.coupledSentence false)) := ObjectStructuralListEnd.native_coupled false

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListEnd.shiftEqualSentence true)) := ObjectStructuralListEnd.native_shiftEqual true

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListEnd.shiftEqualSentence false)) := ObjectStructuralListEnd.native_shiftEqual false

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListEnd.shiftIffSentence true)) := ObjectStructuralListEnd.native_shiftIff true

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListEnd.shiftIffSentence false)) := ObjectStructuralListEnd.native_shiftIff false

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListEnd.consShiftSentence)) := ObjectStructuralListEnd.native_consShift

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListEnd.terminalSentence)) := ObjectStructuralListEnd.native_terminal

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListEnd.existsTerminalSentence)) := ObjectStructuralListEnd.native_existsTerminal

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListEnd.uniquePairSentence)) := ObjectStructuralListEnd.native_uniquePair

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListEnd.traceSeedSentence)) := ObjectStructuralListEnd.native_traceSeed

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListEnd.traceRecoverySentence)) := ObjectStructuralListEnd.native_traceRecovery

/-- 每个域内原位置实际取得一个内部自然反向索引和全值精确双条件。 -/
example {m} (w l f n k : Fin m) : StructuralListPositionSyntax.reverseExists w l f n k = .ex
    (((Source.Formula.mem (Fin.last m) w.castSucc).conj (NaturalAdditionSyntax.sum w.castSucc (Fin.last m) k.castSucc l.castSucc)).conj
      (.all ((GraphSyntax.edge f.castSucc.castSucc k.castSucc.castSucc (Fin.last (m+1))).iff
        (StructuralListProjectionSyntax.iteration false w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))))) := rfl

/-- 完整位置双条件的闭句无归纳性质前提，求值对象y任意。 -/
example : ObjectStructuralListPositions.iffSentence = ((OmegaSyntax.omega (0 : Fin 10)).imp
    ((StructuralListTraceSyntax.trace 0 1 2 3 4 5 6).imp ((Source.Formula.mem 7 0).imp ((Source.Formula.mem 8 0).imp
      ((NaturalAdditionSyntax.sum 0 7 8 3).imp ((GraphSyntax.edge 5 8 9).iff (StructuralListProjectionSyntax.iteration false 0 6 7 9))))))).close := rfl

/-- 原迹每个域内索引的反向见证实际存在，不把自然差存在作为额外前提。 -/
example : ObjectStructuralListPositions.reverseExistsSentence = ((OmegaSyntax.omega (0 : Fin 8)).imp
    ((StructuralListTraceSyntax.trace 0 1 2 3 4 5 6).imp ((Source.Formula.mem 7 4).imp (StructuralListPositionSyntax.reverseExists 0 3 5 6 7)))).close := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListPositions.reverseStepSentence)) := ObjectStructuralListPositions.native_reverseStep

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListPositions.advanceSentence true)) := ObjectStructuralListPositions.native_advance true

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListPositions.advanceSentence false)) := ObjectStructuralListPositions.native_advance false

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListPositions.oldIndexSentence)) := ObjectStructuralListPositions.native_oldIndex

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListPositions.swapSentence)) := ObjectStructuralListPositions.native_swap

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListPositions.allPositionsSentence)) := ObjectStructuralListPositions.native_allPositions

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListPositions.atSentence)) := ObjectStructuralListPositions.native_at

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListPositions.iffSentence)) := ObjectStructuralListPositions.native_iff

example : FirstOrder.Derives nativeZF [] (Translation.sentence (ObjectStructuralListPositions.reverseExistsSentence)) := ObjectStructuralListPositions.native_reverseExists

/-- 字段值保留实际tail求值和原head投影的内部见证。 -/
example {m} (w n i y : Fin m) : StructuralListFieldSyntax.field w n i y = .ex
    ((StructuralListProjectionSyntax.iteration false w.castSucc n.castSucc i.castSucc (Fin.last m)).conj
      (StructuralListProjectionSyntax.step true w.castSucc (Fin.last m) y.castSucc)) := rfl

/-- 图成员为精确原Kuratowski索引对像，覆盖所有对象且排除杂项。 -/
example {m} (w n l g : Fin m) : StructuralListFieldPairSyntax.graph w n l g = .all
    ((Source.Formula.mem (Fin.last m) g.castSucc).iff (.ex
      ((Source.Formula.mem (Fin.last (m+1)) l.castSucc.castSucc).conj (.ex
        ((StructuralListFieldSyntax.field w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))).conj
          (PairSyntax.ordered (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)))))))) := rfl

/-- 完整合同同时含原完整有界序列、精确图像及全边双条件。 -/
example {m} (w n l g : Fin m) : StructuralListFieldGraphSyntax.fields w n l g =
    (SequenceSyntax.sequence g l w).conj ((StructuralListFieldPairSyntax.graph w n l g).conj
      (StructuralListFieldGraphSyntax.edgeLaw w n l g)) := rfl

/-- 实际唯一图纤维不把完整函数图或算子总单值性作为额外前提。 -/
example : ObjectStructuralListFields.fiberSentence = ((OmegaSyntax.omega (0 : Fin 3)).imp
    ((Source.Formula.mem 2 0).imp (StructuralListFieldGraphSyntax.fieldsFiber 0 1 2))).close := rfl

/-- 解码实际量化内部长度和完整图，保留原HasLength构造迹。 -/
example {m} (w n : Fin m) : StructuralListFieldGraphSyntax.decoded w n = .ex (.ex
    (((Source.Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj
      (StructuralListLengthSyntax.hasLength w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc)).conj
      (StructuralListFieldGraphSyntax.fields w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))) := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListFields.valueFiberSentence) := ObjectStructuralListFields.native_valueFiber

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListFields.valueRangeSentence) := ObjectStructuralListFields.native_valueRange

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListFields.zeroSentence) := ObjectStructuralListFields.native_zero

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListFields.successorSentence) := ObjectStructuralListFields.native_successor

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListFields.pairFiberSentence) := ObjectStructuralListFields.native_pairFiber

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListFields.rawExistsSentence) := ObjectStructuralListFields.native_rawExists

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListFields.edgeLawSentence) := ObjectStructuralListFields.native_edgeLaw

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListFields.completeSentence) := ObjectStructuralListFields.native_complete

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListFields.graphUniqueSentence) := ObjectStructuralListFields.native_graphUnique

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListFields.fiberSentence) := ObjectStructuralListFields.native_fiber

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListFields.atLengthSentence) := ObjectStructuralListFields.native_atLength

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListFields.decodeSentence) := ObjectStructuralListFields.native_decode

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListFields.decodeIffSentence) := ObjectStructuralListFields.native_decodeIff

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListFields.decodeUniqueSentence) := ObjectStructuralListFields.native_decodeUnique

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListFields.traceHeadSentence) := ObjectStructuralListFields.native_traceHead

/-- 任意原内部完整ω值序列的逆编码实际保留自然码、原构造迹长度及给定源图。 -/
example {m} (w f l : Fin m) : StructuralListEncodeSyntax.existsEncoding w f l = .ex
    (((Source.Formula.mem (Fin.last m) w.castSucc).conj
      (StructuralListLengthSyntax.hasLength w.castSucc (Fin.last m) l.castSucc)).conj
      (StructuralListFieldGraphSyntax.fields w.castSucc (Fin.last m) l.castSucc f.castSucc)) := rfl

/-- 后缀归纳性质量化全部内部偏移，最终编码前提不假定源序列已经有列表码。 -/
example {m} (w f l r : Fin m) : StructuralListSuffixSyntax.property w f l r = .all
    ((Source.Formula.mem (Fin.last m) w.castSucc).imp
      ((NaturalAdditionSyntax.sum w.castSucc r.castSucc (Fin.last m) l.castSucc).imp
        (StructuralListSuffixSyntax.existsCode w.castSucc f.castSucc (Fin.last m) r.castSucc))) := rfl

example : ObjectStructuralListEncode.existsSentence = ((OmegaSyntax.omega (0 : Fin 3)).imp
    ((SequenceSyntax.sequence 1 2 0).imp ((Source.Formula.mem 2 0).imp (StructuralListEncodeSyntax.existsEncoding 0 1 2)))).close := rfl

/-- 读回比较任意实际长度及完整图，没有假定外部标准性或输出图预先相等。 -/
example : ObjectStructuralListEncode.readbackSentence = ((OmegaSyntax.omega (0 : Fin 6)).imp
    ((StructuralListEncodeSyntax.encoding 0 1 2 3).imp ((StructuralListLengthSyntax.hasLength 0 3 4).imp
      ((StructuralListFieldGraphSyntax.fields 0 3 4 5).imp ((Source.Formula.equal 4 2).conj (.equal 5 1)))))).close := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListEncode.nilLengthSentence) := ObjectStructuralListEncode.native_nilLength

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListEncode.consLengthSentence) := ObjectStructuralListEncode.native_consLength

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListEncode.emptyLengthSentence) := ObjectStructuralListEncode.native_emptyLength

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListEncode.offsetSentence) := ObjectStructuralListEncode.native_offset

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListEncode.suffixZeroSentence) := ObjectStructuralListEncode.native_suffixZero

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListEncode.suffixConsSentence) := ObjectStructuralListEncode.native_suffixCons

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListEncode.suffixSentence) := ObjectStructuralListEncode.native_suffix

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListEncode.fullSuffixSentence) := ObjectStructuralListEncode.native_fullSuffix

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListEncode.graphRecoverySentence) := ObjectStructuralListEncode.native_graphRecovery

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListEncode.zeroFieldsSentence) := ObjectStructuralListEncode.native_zeroFields

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListEncode.existsSentence) := ObjectStructuralListEncode.native_exists

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListEncode.validSentence) := ObjectStructuralListEncode.native_valid

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListEncode.readbackSentence) := ObjectStructuralListEncode.native_readback

/-- 同字段比较对每个实际域内索引及任意输出对象给双条件。 -/
example {m} (w r a b : Fin m) : StructuralListCodeSyntax.agree w r a b = .all (.all
    ((Source.Formula.mem (Fin.last m).castSucc r.castSucc.castSucc).imp
      ((StructuralListFieldSyntax.field w.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
        (StructuralListFieldSyntax.field w.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))))) := rfl

/-- 最终单射闭句没有归纳性质或码相等作为前提。 -/
example : ObjectStructuralListRoundTrip.codeUniqueSentence = ((OmegaSyntax.omega (0 : Fin 4)).imp
    ((StructuralListLengthSyntax.hasLength 0 2 1).imp ((StructuralListLengthSyntax.hasLength 0 3 1).imp
      ((StructuralListCodeSyntax.agree 0 1 2 3).imp (Source.Formula.equal 2 3))))).close := rfl

/-- 实际编码唯一纤维比较全部内部候选码。 -/
example {m} (w f r : Fin m) : StructuralListRoundTripSyntax.encodingFiber w f r = .ex
    ((StructuralListEncodeSyntax.encoding w.castSucc f.castSucc r.castSucc (Fin.last m)).conj (.all
      ((StructuralListEncodeSyntax.encoding w.castSucc.castSucc f.castSucc.castSucc r.castSucc.castSucc (Fin.last (m+1))).imp
        (.equal (Fin.last (m+1)) (Fin.last m).castSucc)))) := rfl

/-- 往返实际取得长度、完整原图和重编码值，并证明该值等于原码。 -/
example {m} (w n : Fin m) : StructuralListRoundTripSyntax.roundTrip w n = .ex (.ex (.ex
    ((((StructuralListLengthSyntax.hasLength w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc).conj
      (StructuralListFieldGraphSyntax.fields w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc)).conj
      (StructuralListEncodeSyntax.encoding w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2)))).conj
      (.equal (Fin.last (m+2)) n.castSucc.castSucc.castSucc)))) := rfl

example : ObjectStructuralListRoundTrip.roundTripSentence = ((OmegaSyntax.omega (0 : Fin 2)).imp
    ((StructuralListTraceSyntax.valid 0 1).imp (StructuralListRoundTripSyntax.roundTrip 0 1))).close := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListRoundTrip.predecessorSentence) := ObjectStructuralListRoundTrip.native_predecessor

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListRoundTrip.consViewSentence) := ObjectStructuralListRoundTrip.native_consView

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListRoundTrip.headsSentence) := ObjectStructuralListRoundTrip.native_heads

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListRoundTrip.tailsSentence) := ObjectStructuralListRoundTrip.native_tails

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListRoundTrip.codeUniqueSentence) := ObjectStructuralListRoundTrip.native_codeUnique

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListRoundTrip.sameGraphSentence) := ObjectStructuralListRoundTrip.native_sameGraph

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListRoundTrip.encodedUniqueSentence) := ObjectStructuralListRoundTrip.native_encodedUnique

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListRoundTrip.encodingFiberSentence) := ObjectStructuralListRoundTrip.native_encodingFiber

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListRoundTrip.decodeThenEncodeSentence) := ObjectStructuralListRoundTrip.native_decodeThenEncode

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListRoundTrip.roundTripSentence) := ObjectStructuralListRoundTrip.native_roundTrip

/-- 检查定义的停止条件仅为空集或原Nil构造器。 -/
example {m} (w b : Fin m) : StructuralListCheckSyntax.terminal w b =
    (OmegaSyntax.empty b).disj (StructuralListSyntax.nilCode w b) := rfl

/-- 内部索引的终端事件保留真实tail递归值，没有Valid测试前提。 -/
example {m} (w n r : Fin m) : StructuralListCheckSyntax.occurs w n r = .ex
    ((StructuralListProjectionSyntax.iteration false w.castSucc n.castSucc r.castSucc (Fin.last m)).conj
      (StructuralListCheckSyntax.terminal w.castSucc (Fin.last m))) := rfl

/-- 首次停止排除所有更早内部索引上的终端事件。 -/
example {m} (w n r : Fin m) : StructuralListCheckSyntax.before w n r = .all
    ((Source.Formula.mem (Fin.last m) r.castSucc).imp (StructuralListCheckSyntax.occurs w.castSucc n.castSucc (Fin.last m)).neg) := rfl

example {m} (w n r b : Fin m) : StructuralListCheckSyntax.checkedAt w n r b =
    ((((Source.Formula.mem r w).conj (StructuralListProjectionSyntax.iteration false w n r b)).conj
      ((OmegaSyntax.empty b).disj (StructuralListSyntax.nilCode w b))).conj (StructuralListCheckSyntax.before w n r)) := rfl

example {m} (w n b : Fin m) : StructuralListCheckSyntax.checkValue w n b = .ex
    (StructuralListCheckSyntax.checkedAt w.castSucc n.castSucc (Fin.last m) b.castSucc) := rfl

/-- 唯一纤维实际取得检查值并比较任意对象候选，不预设输出或算法总性。 -/
example {m} (w n : Fin m) : StructuralListCheckSyntax.checkFiber w n = .ex
    ((StructuralListCheckSyntax.checkValue w.castSucc n.castSucc (Fin.last m)).conj (.all
      ((StructuralListCheckSyntax.checkValue w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp
        (.equal (Fin.last (m+1)) (Fin.last m).castSucc)))) := rfl

example {m} (w n : Fin m) : StructuralListCheckSyntax.accepts w n = .ex
    ((StructuralListCheckSyntax.checkValue w.castSucc n.castSucc (Fin.last m)).conj (StructuralListSyntax.nilCode w.castSucc (Fin.last m))) := rfl

example {m} (w n : Fin m) : StructuralListCheckSyntax.rejects w n = .ex
    ((StructuralListCheckSyntax.checkValue w.castSucc n.castSucc (Fin.last m)).conj (OmegaSyntax.empty (Fin.last m))) := rfl

/-- 正确性闭句覆盖每个内部自然码，前件没有终止性、有效性或递归不变量。 -/
example : ObjectStructuralListCheck.acceptsIffSentence = ((OmegaSyntax.omega (0 : Fin 2)).imp
    ((Source.Formula.mem 1 0).imp ((StructuralListTraceSyntax.valid 0 1).iff (StructuralListCheckSyntax.accepts 0 1)))).close := rfl

example : ObjectStructuralListCheck.rejectsIffSentence = ((OmegaSyntax.omega (0 : Fin 2)).imp
    ((Source.Formula.mem 1 0).imp ((StructuralListTraceSyntax.valid 0 1).neg.iff (StructuralListCheckSyntax.rejects 0 1)))).close := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListCheck.terminationSentence) := ObjectStructuralListCheck.native_termination

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListCheck.existsSentence) := ObjectStructuralListCheck.native_exists

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListCheck.fiberSentence) := ObjectStructuralListCheck.native_fiber

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListCheck.indexUniqueSentence) := ObjectStructuralListCheck.native_indexUnique

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListCheck.valueUniqueSentence) := ObjectStructuralListCheck.native_valueUnique

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListCheck.preservesStepSentence) := ObjectStructuralListCheck.native_preservesStep

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListCheck.invariantSentence) := ObjectStructuralListCheck.native_invariant

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListCheck.acceptValueSentence) := ObjectStructuralListCheck.native_acceptValue

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListCheck.rejectValueSentence) := ObjectStructuralListCheck.native_rejectValue

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListCheck.acceptsIffSentence) := ObjectStructuralListCheck.native_acceptsIff

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListCheck.rejectsIffSentence) := ObjectStructuralListCheck.native_rejectsIff

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListCheck.exclusiveSentence) := ObjectStructuralListCheck.native_exclusive

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListCheck.decodeAcceptedSentence) := ObjectStructuralListCheck.native_decodeAccepted

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListCheck.nilAcceptsSentence) := ObjectStructuralListCheck.native_nilAccepts

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListCheck.zeroRejectsSentence) := ObjectStructuralListCheck.native_zeroRejects

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralListCheck.classificationSentence) := ObjectStructuralListCheck.native_classification

/-- 字段严格界性质量化所有原码、域内索引及任意字段输出。 -/
example {m} (w r : Fin m) : StructuralListFieldBoundsSyntax.property w r = .all (.all (.all
    ((StructuralListLengthSyntax.hasLength w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc r.castSucc.castSucc.castSucc).imp
      ((Source.Formula.mem (Fin.last (m+1)).castSucc r.castSucc.castSucc.castSucc).imp
        ((StructuralListFieldSyntax.field w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))).imp
          (.mem (Fin.last (m+2)) (Fin.last m).castSucc.castSucc)))))) := rfl

/-- 最终字段界没有归纳性质或预设子码界前提。 -/
example : ObjectStructuralFieldBounds.fieldBoundSentence = ((OmegaSyntax.omega (0 : Fin 5)).imp
    ((StructuralListLengthSyntax.hasLength 0 1 2).imp ((Source.Formula.mem 3 2).imp
      ((StructuralListFieldSyntax.field 0 1 3 4).imp (.mem 4 1))))).close := rfl

/-- 原节点形状保留实际自然标签、raw载荷、原长度迹和完整精确字段图。 -/
example {m} (w n tag p l f : Fin m) : StructuralTreeOperatorSyntax.shape w n tag p l f =
    ((Source.Formula.mem tag w).conj (StructuralNodeSyntax.raw w tag p n)).conj
      ((StructuralListLengthSyntax.hasLength w p l).conj (StructuralListFieldGraphSyntax.fields w p l f)) := rfl

/-- 历史查询显式限制到严格小于当前码的子字段，覆盖全部边。 -/
example {m} (e n f h : Fin m) : StructuralTreeOperatorSyntax.children e n f h = .all (.all
    ((GraphSyntax.edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
      ((Source.Formula.mem (Fin.last (m+1)) n.castSucc.castSucc).conj
        (GraphSyntax.edge h.castSucc.castSucc (Fin.last (m+1)) e.castSucc.castSucc)))) := rfl

/-- 树局部条件实际量化标签、载荷、长度及字段图四个内部见证。 -/
example {m} (w e n h : Fin m) : StructuralTreeOperatorSyntax.good w e n h = .ex (.ex (.ex (.ex
    ((StructuralTreeOperatorSyntax.shape w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))).conj
      (StructuralTreeOperatorSyntax.children e.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
        (Fin.last (m+3)) h.castSucc.castSucc.castSucc.castSucc))))) := rfl

example {m} (w z e n h y : Fin m) : StructuralTreeOperatorSyntax.step w z e n h y =
    ((StructuralTreeOperatorSyntax.good w e n h).conj (.equal y e)).disj
      ((StructuralTreeOperatorSyntax.good w e n h).neg.conj (.equal y z)) := rfl

/-- 全序数递归图的实际存在唯一句不残留算子总性/单值性假设。 -/
example : ObjectStructuralTreeOperator.recursorsSentence = (StructuralTreeOperatorSyntax.recursors (0 : Fin 3) 1 2).close := rfl

/-- 原Omega实际取得内部零与单位标志，再取得全序数唯一递归图。 -/
example {m} (w : Fin m) : StructuralTreeOperatorSyntax.actualRecursors w = .ex (.ex
    (((OmegaSyntax.empty (Fin.last m).castSucc).conj (OmegaSyntax.successor (Fin.last (m+1)) (Fin.last m).castSucc)).conj
      (OrdinalRecursionExistenceSyntax.allUnique StructuralTreeOperatorSyntax.matrix
        (NaturalAdditionTransport.params3 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))))) := rfl

example : ObjectStructuralTreeOperator.actualUnitsSentence = ((OmegaSyntax.omega (0 : Fin 1)).imp (StructuralTreeOperatorSyntax.actualRecursors 0)).close := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralFieldBounds.fieldBoundSentence) := ObjectStructuralFieldBounds.native_fieldBound

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralFieldBounds.edgeBoundSentence) := ObjectStructuralFieldBounds.native_edgeBound

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralFieldBounds.rawFieldBoundSentence) := ObjectStructuralFieldBounds.native_rawFieldBound

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralFieldBounds.rawEdgeBoundSentence) := ObjectStructuralFieldBounds.native_rawEdgeBound

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeOperator.shapeBoundSentence) := ObjectStructuralTreeOperator.native_shapeBound

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeOperator.childrenIffSentence) := ObjectStructuralTreeOperator.native_childrenIff

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeOperator.leafGoodSentence) := ObjectStructuralTreeOperator.native_leafGood

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeOperator.positiveGoodSentence) := ObjectStructuralTreeOperator.native_positiveGood

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeOperator.rangeSentence) := ObjectStructuralTreeOperator.native_range

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeOperator.zeroSentence) := ObjectStructuralTreeOperator.native_zero

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeOperator.functionalSentence) := ObjectStructuralTreeOperator.native_functional

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeOperator.recursorsSentence) := ObjectStructuralTreeOperator.native_recursors

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeOperator.ordinalFiberSentence) := ObjectStructuralTreeOperator.native_ordinalFiber

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeOperator.actualUnitsSentence) := ObjectStructuralTreeOperator.native_actualUnits

/-- 实际树值保留原后继域、完整递归图及真实边，不用宿主自然数求值。 -/
example {m} (w z e n y : Fin m) : StructuralTreeEvaluationSyntax.evaluation w z e n y = .ex (.ex
    (StructuralTreeEvaluationSyntax.data w.castSucc.castSucc z.castSucc.castSucc e.castSucc.castSucc
      (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc y.castSucc.castSucc)) := rfl

/-- 原自然码守卫与实际零/单位见证均保留；无任意指定真假标记。 -/
example {m} (w n : Fin m) : StructuralTreeValiditySyntax.valid w n =
    (Source.Formula.mem n w).conj (.ex (.ex (StructuralTreeValiditySyntax.validWitness w n))) := rfl

/-- 子字段检查覆盖全部边，不限定外部标准索引。 -/
example {m} (w f : Fin m) : StructuralTreeValiditySyntax.validChildren w f = .all (.all
    ((GraphSyntax.edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
      (StructuralTreeValiditySyntax.valid w.castSucc.castSucc (Fin.last (m+1))))) := rfl

/-- 树解码递归句保留四个实际对象见证及完整字段图。 -/
example {m} (w n : Fin m) : StructuralTreeValiditySyntax.recursive w n =
    .ex (.ex (.ex (.ex (StructuralTreeValiditySyntax.dataBody w n)))) := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeCheck.fiberSentence) := ObjectStructuralTreeCheck.native_fiber

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeCheck.naturalValueSentence) := ObjectStructuralTreeCheck.native_naturalValue

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeCheck.valueUniqueSentence) := ObjectStructuralTreeCheck.native_valueUnique

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeCheck.edgeIffSentence) := ObjectStructuralTreeCheck.native_edgeIff

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeCheck.historySentence) := ObjectStructuralTreeCheck.native_history

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeCheck.rangeSentence) := ObjectStructuralTreeCheck.native_range

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeCheck.goodIffSentence) := ObjectStructuralTreeCheck.native_goodIff

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeCheck.acceptsIffSentence) := ObjectStructuralTreeCheck.native_acceptsIff

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeCheck.rejectsIffSentence) := ObjectStructuralTreeCheck.native_rejectsIff

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeCheck.fixedClassificationSentence) := ObjectStructuralTreeCheck.native_fixedClassification

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeCheck.validAcceptsSentence) := ObjectStructuralTreeCheck.native_validAccepts

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeCheck.invalidRejectsSentence) := ObjectStructuralTreeCheck.native_invalidRejects

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeCheck.markerTransportSentence) := ObjectStructuralTreeCheck.native_markerTransport

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeCheck.classificationSentence) := ObjectStructuralTreeCheck.native_classification

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeCheck.exclusiveSentence) := ObjectStructuralTreeCheck.native_exclusive

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeCheck.invalidIffNotSentence) := ObjectStructuralTreeCheck.native_invalidIffNot

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeCheck.recursiveIffSentence) := ObjectStructuralTreeCheck.native_recursiveIff

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeCheck.decodedFiberSentence) := ObjectStructuralTreeCheck.native_decodedFiber

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeCheck.decodedIffSentence) := ObjectStructuralTreeCheck.native_decodedIff

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeCheck.decodeUniqueSentence) := ObjectStructuralTreeCheck.native_decodeUnique

/-- 树构造保留给定完整字段图、实际长度和标签；只存在量化原payload。 -/
example {m} (w tag l f n : Fin m) : StructuralTreeEncodeSyntax.encoding w tag l f n = .ex
    (StructuralTreeOperatorSyntax.shape w.castSucc n.castSucc tag.castSucc (Fin.last m) l.castSucc f.castSucc) := rfl

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeEncode.existsSentence) := ObjectStructuralTreeEncode.native_exists

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeEncode.fiberSentence) := ObjectStructuralTreeEncode.native_fiber

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeEncode.rangeSentence) := ObjectStructuralTreeEncode.native_range

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeEncode.uniqueSentence) := ObjectStructuralTreeEncode.native_unique

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeEncode.shapeUniqueSentence) := ObjectStructuralTreeEncode.native_shapeUnique

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeEncode.validitySentence) := ObjectStructuralTreeEncode.native_validity

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeEncode.readbackSentence) := ObjectStructuralTreeEncode.native_readback

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectStructuralTreeEncode.codeRecoverySentence) := ObjectStructuralTreeEncode.native_codeRecovery

/-- 内部scalar索引是零字段原节点；保留实际自然标签和原Nil载荷。 -/
example {m} (w i n : Fin m) : SyntaxNodeSyntax.scalar w i n = .ex
    ((Source.Formula.mem i.castSucc w.castSucc).conj
      ((StructuralListSyntax.nilCode w.castSucc (Fin.last m)).conj
        (StructuralNodeSyntax.raw w.castSucc i.castSucc (Fin.last m) n.castSucc))) := rfl

/-- 原变量编码单个字段为scalar，bound/free分别取0/1，不能把索引值直接当子树码。 -/
example {m} (w i n : Fin m) : SyntaxVariableSyntax.code true w i n = .ex
    ((SyntaxNodeSyntax.scalar w.castSucc i.castSucc (Fin.last m)).conj
      (SyntaxNodeSyntax.constructor 1 0 w.castSucc (fun _ => Fin.last m) n.castSucc)) := rfl

example {m} (w i n : Fin m) : SyntaxVariableSyntax.code false w i n = .ex
    ((SyntaxNodeSyntax.scalar w.castSucc i.castSucc (Fin.last m)).conj
      (SyntaxNodeSyntax.constructor 1 1 w.castSucc (fun _ => Fin.last m) n.castSucc)) := rfl

example {m} (k : Nat) (w : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxConstructors.numeralExistsSentence k w)) :=
  ObjectSyntaxConstructors.native_numeralExists k w

example {m} (k : Nat) (x y : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxConstructors.numeralUniqueSentence k x y)) :=
  ObjectSyntaxConstructors.native_numeralUnique k x y

example {m} (k : Nat) (w x : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxConstructors.numeralRangeSentence k w x)) :=
  ObjectSyntaxConstructors.native_numeralRange k w x

example {m} (i j : Nat) (x y : Fin m) (hij : i < j) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxConstructors.numeralLessSentence i j x y)) :=
  ObjectSyntaxConstructors.native_numeralLess i j x y hij

example {m} (i j : Nat) (x y : Fin m) (hij : i ≠ j) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxConstructors.numeralDifferentSentence i j x y)) :=
  ObjectSyntaxConstructors.native_numeralDifferent i j x y hij

example {m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxConstructors.forestExistsSentence k w xs)) :=
  ObjectSyntaxConstructors.native_forestExists k w xs

example {m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (n s : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxConstructors.forestUniqueSentence k w xs n s)) :=
  ObjectSyntaxConstructors.native_forestUnique k w xs n s

example {m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (n : Fin m) (i : Fin k)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxConstructors.forestMemberSentence k w xs n i)) :=
  ObjectSyntaxConstructors.native_forestMember k w xs n i

example {m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (n l : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxConstructors.forestLengthSentence k w xs n l)) :=
  ObjectSyntaxConstructors.native_forestLength k w xs n l

example {m} (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxConstructors.nodeFiberSentence k w tag xs)) :=
  ObjectSyntaxConstructors.native_nodeFiber k w tag xs

example {m} (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m) (n : Fin m) (i : Fin k)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxConstructors.nodeMemberSentence k w tag xs n i)) :=
  ObjectSyntaxConstructors.native_nodeMember k w tag xs n i

example {m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxConstructors.constructorFiberSentence k tag w xs)) :=
  ObjectSyntaxConstructors.native_constructorFiber k tag w xs

example {m} (k l a b : Nat) (w : Fin m) (xs : Fin k → Fin m) (ys : Fin l → Fin m) (n : Fin m) (hab : a ≠ b) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxConstructors.constructorDisjointSentence k l a b w xs ys n)) :=
  ObjectSyntaxConstructors.native_constructorDisjoint k l a b w xs ys n hab

example {m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (n : Fin m) (i : Fin k)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxConstructors.constructorMemberSentence k tag w xs n i)) :=
  ObjectSyntaxConstructors.native_constructorMember k tag w xs n i

example {m} (w i : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxConstructors.scalarFiberSentence w i)) :=
  ObjectSyntaxConstructors.native_scalarFiber w i

example {m} (w i j n : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxConstructors.scalarInjectiveSentence w i j n)) :=
  ObjectSyntaxConstructors.native_scalarInjective w i j n

example {m} (bound : Bool) (w i : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxConstructors.variableFiberSentence bound w i)) :=
  ObjectSyntaxConstructors.native_variableFiber bound w i

example {m} (w i j n : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxConstructors.variableDisjointSentence w i j n)) :=
  ObjectSyntaxConstructors.native_variableDisjoint w i j n

/-! 原生公式构造标签/字段数逐一实例化；这是构造存在唯一，不冒充类型/作用域检查。 -/
example : FirstOrder.Derives nativeZF [] (Translation.sentence
    (ObjectSyntaxConstructors.constructorFiberSentence 0 0 (0 : Fin 1) Fin.elim0)) :=
  ObjectSyntaxConstructors.native_constructorFiber 0 0 0 Fin.elim0

example : FirstOrder.Derives nativeZF [] (Translation.sentence
    (ObjectSyntaxConstructors.constructorFiberSentence 0 1 (0 : Fin 1) Fin.elim0)) :=
  ObjectSyntaxConstructors.native_constructorFiber 0 1 0 Fin.elim0

example : FirstOrder.Derives nativeZF [] (Translation.sentence
    (ObjectSyntaxConstructors.constructorFiberSentence 3 2 (0 : Fin 4) (fun i => i.succ))) :=
  ObjectSyntaxConstructors.native_constructorFiber 3 2 0 (fun i => i.succ)

example : FirstOrder.Derives nativeZF [] (Translation.sentence
    (ObjectSyntaxConstructors.constructorFiberSentence 2 3 (0 : Fin 3) (fun i => i.succ))) :=
  ObjectSyntaxConstructors.native_constructorFiber 2 3 0 (fun i => i.succ)

example : FirstOrder.Derives nativeZF [] (Translation.sentence
    (ObjectSyntaxConstructors.constructorFiberSentence 1 4 (0 : Fin 2) (fun i => i.succ))) :=
  ObjectSyntaxConstructors.native_constructorFiber 1 4 0 (fun i => i.succ)

example : FirstOrder.Derives nativeZF [] (Translation.sentence
    (ObjectSyntaxConstructors.constructorFiberSentence 2 5 (0 : Fin 3) (fun i => i.succ))) :=
  ObjectSyntaxConstructors.native_constructorFiber 2 5 0 (fun i => i.succ)

example : FirstOrder.Derives nativeZF [] (Translation.sentence
    (ObjectSyntaxConstructors.constructorFiberSentence 2 6 (0 : Fin 3) (fun i => i.succ))) :=
  ObjectSyntaxConstructors.native_constructorFiber 2 6 0 (fun i => i.succ)

example : FirstOrder.Derives nativeZF [] (Translation.sentence
    (ObjectSyntaxConstructors.constructorFiberSentence 2 7 (0 : Fin 3) (fun i => i.succ))) :=
  ObjectSyntaxConstructors.native_constructorFiber 2 7 0 (fun i => i.succ)

example : FirstOrder.Derives nativeZF [] (Translation.sentence
    (ObjectSyntaxConstructors.constructorFiberSentence 2 8 (0 : Fin 3) (fun i => i.succ))) :=
  ObjectSyntaxConstructors.native_constructorFiber 2 8 0 (fun i => i.succ)

example : FirstOrder.Derives nativeZF [] (Translation.sentence
    (ObjectSyntaxConstructors.constructorFiberSentence 1 9 (0 : Fin 2) (fun i => i.succ))) :=
  ObjectSyntaxConstructors.native_constructorFiber 1 9 0 (fun i => i.succ)

example : FirstOrder.Derives nativeZF [] (Translation.sentence
    (ObjectSyntaxConstructors.constructorFiberSentence 1 10 (0 : Fin 2) (fun i => i.succ))) :=
  ObjectSyntaxConstructors.native_constructorFiber 1 10 0 (fun i => i.succ)

/-- 纯项同时保留两个内部上下文自然长度，并按对应内部索引域识别原变量。 -/
example {m} (w b f n : Fin m) : SyntaxTermSyntax.term w b f n =
    ((Source.Formula.mem b w).conj (.mem f w)).conj
      ((Source.Formula.ex ((Source.Formula.mem (Fin.last m) b.castSucc).conj
        (SyntaxVariableSyntax.code true w.castSucc (Fin.last m) n.castSucc))).disj
      (.ex ((Source.Formula.mem (Fin.last m) f.castSucc).conj
        (SyntaxVariableSyntax.code false w.castSucc (Fin.last m) n.castSucc)))) := rfl

/-- 解码的唯一索引条件遍历所有内部候选，不限于当前作用域中的候选。 -/
example {m} (bound : Bool) (w n i : Fin m) : SyntaxVariableDecodeSyntax.uniqueIndex bound w n i = .all
    ((SyntaxVariableSyntax.code bound w.castSucc (Fin.last m) n.castSucc).imp (.equal (Fin.last m) i.castSucc)) := rfl

example {m} (k : Nat) (w : Fin m) (xs ys : Fin k → Fin m) (n : Fin m) (i : Fin k)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.forestInputSentence k w xs ys n i)) :=
  ObjectSyntaxTerms.native_forestInput k w xs ys n i

example {m} (k : Nat) (w a b : Fin m) (xs ys : Fin k → Fin m) (n : Fin m) (i : Fin k)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.nodeInputSentence k w a b xs ys n i)) :=
  ObjectSyntaxTerms.native_nodeInput k w a b xs ys n i

example {m} (k a b : Nat) (w : Fin m) (xs ys : Fin k → Fin m) (n : Fin m) (i : Fin k)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.constructorInputSentence k a b w xs ys n i)) :=
  ObjectSyntaxTerms.native_constructorInput k a b w xs ys n i

example {m} (k l : Nat) (w : Fin m) (xs : Fin k → Fin m) (ys : Fin l → Fin m) (n : Fin m) (hkl : k ≠ l) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.forestAritySentence k l w xs ys n)) :=
  ObjectSyntaxTerms.native_forestArity k l w xs ys n hkl

example {m} (k l : Nat) (w a b : Fin m) (xs : Fin k → Fin m) (ys : Fin l → Fin m) (n : Fin m) (hkl : k ≠ l) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.nodeAritySentence k l w a b xs ys n)) :=
  ObjectSyntaxTerms.native_nodeArity k l w a b xs ys n hkl

example {m} (bound : Bool) (w i n : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.indexNaturalSentence bound w i n)) :=
  ObjectSyntaxTerms.native_indexNatural bound w i n

example {m} (bound : Bool) (w i j n : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.indexInjectiveSentence bound w i j n)) :=
  ObjectSyntaxTerms.native_indexInjective bound w i j n

example {m} (bound : Bool) (w n : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.variableDecodeSentence bound w n)) :=
  ObjectSyntaxTerms.native_variableDecode bound w n

example {m} (bound : Bool) (w n i : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.indexFiberSentence bound w n i)) :=
  ObjectSyntaxTerms.native_indexFiber bound w n i

example {m} (bound : Bool) (w l n i : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.branchScopeSentence bound w l n i)) :=
  ObjectSyntaxTerms.native_branchScope bound w l n i

example {m} (bound : Bool) (w l n : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.branchDecodeSentence bound w l n)) :=
  ObjectSyntaxTerms.native_branchDecode bound w l n

example {m} (bound : Bool) (w b f n i : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.scopeSentence bound w b f n i)) :=
  ObjectSyntaxTerms.native_scope bound w b f n i

example {m} (bound : Bool) (w b f i : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.termExistsSentence bound w b f i)) :=
  ObjectSyntaxTerms.native_termExists bound w b f i

example {m} (w b f n : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.termRangeSentence w b f n)) :=
  ObjectSyntaxTerms.native_termRange w b f n

example {m} (w b f n : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.termDecodeSentence w b f n)) :=
  ObjectSyntaxTerms.native_termDecode w b f n

example {m} (w b f n : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.branchExclusiveSentence w b f n)) :=
  ObjectSyntaxTerms.native_branchExclusive w b f n

example {m} (w b f n : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.decodedExclusiveSentence w b f n)) :=
  ObjectSyntaxTerms.native_decodedExclusive w b f n

example {m} (bound : Bool) (w b f n i : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.rejectScopeSentence bound w b f n i)) :=
  ObjectSyntaxTerms.native_rejectScope bound w b f n i

example {m} (w b f n : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.rejectEmptySentence w b f n)) :=
  ObjectSyntaxTerms.native_rejectEmpty w b f n

example {m} (k label : Nat) (w b f n : Fin m) (xs : Fin k → Fin m) (h0 : label ≠ 0) (h1 : label ≠ 1) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.rejectTagSentence k label w b f n xs)) :=
  ObjectSyntaxTerms.native_rejectTag k label w b f n xs h0 h1

example {m} (k : Nat) (w b f n : Fin m) (xs : Fin k → Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.rejectFunctionSentence k w b f n xs)) :=
  ObjectSyntaxTerms.native_rejectFunction k w b f n xs

example {m} (k : Nat) (w a b f n : Fin m) (xs : Fin k → Fin m) (hk : k ≠ 1) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.rejectAritySentence k w a b f n xs)) :=
  ObjectSyntaxTerms.native_rejectArity k w a b f n xs hk

example {m} (w a b f n : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.rejectScalarSentence w a b f n)) :=
  ObjectSyntaxTerms.native_rejectScalar w a b f n

example {m} (bound : Bool) (w l n : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.branchEmptySentence bound w l n)) :=
  ObjectSyntaxTerms.native_branchEmpty bound w l n

example {m} (label : Nat) (w b f t p n : Fin m) (h0 : label ≠ 0) (h1 : label ≠ 1) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.rawRejectTagSentence label w b f t p n)) :=
  ObjectSyntaxTerms.native_rawRejectTag label w b f t p n h0 h1

example {m} (w b f t p n : Fin m)  : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.rawRejectFunctionSentence w b f t p n)) :=
  ObjectSyntaxTerms.native_rawRejectFunction w b f t p n

/-- 函数应用标签2的拒绝量化任意内部自然payload，无外部固定字段数。 -/
example {m} (w b f t p n : Fin m) : ObjectSyntaxTerms.rawRejectFunctionSentence w b f t p n =
    ((OmegaSyntax.omega w).imp ((SyntaxNumeralSyntax.numeral 2 t).imp ((Source.Formula.mem p w).imp
      ((StructuralNodeSyntax.raw w t p n).imp (SyntaxTermSyntax.term w b f n).neg)))).close := rfl

example {m} (w b f n i : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.scopeSentence true w b f n i)) := ObjectSyntaxTerms.native_scope true w b f n i

example {m} (w b f n i : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.scopeSentence false w b f n i)) := ObjectSyntaxTerms.native_scope false w b f n i

/-- 未知标签的拒绝直接量化内部t，不以外部Nat标签模式代替非标准候选。 -/
example {m} (w b f t p n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTerms.rawRejectUnknownTagSentence w b f t p n)) :=
  ObjectSyntaxTerms.native_rawRejectUnknownTag w b f t p n

/-! 四个原子构造的全内部局部类型与实际唯一解码验收。 -/

example {m} (w n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.zeroTwoSentence w n)) := ObjectSyntaxAtoms.native_zeroTwo w n

example {m} (w i s : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.zeroIndexSentence w i s)) := ObjectSyntaxAtoms.native_zeroIndex w i s

example {m} (truth : Bool) (w b f n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.nullaryContextsSentence truth w b f n)) := ObjectSyntaxAtoms.native_nullaryContexts truth w b f n

example {m} (w b f n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.falseTwoSentence w b f n)) := ObjectSyntaxAtoms.native_falseTwo w b f n

example {m} (w b f s x y n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.memberTypesSentence w b f s x y n)) := ObjectSyntaxAtoms.native_memberTypes w b f s x y n

example {m} (w b f x y n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.equalTypesSentence w b f x y n)) := ObjectSyntaxAtoms.native_equalTypes w b f x y n

example {m} (truth : Bool) (w b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.nullaryExistsSentence truth w b f)) := ObjectSyntaxAtoms.native_nullaryExists truth w b f

example {m} (w b f x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.memberExistsSentence w b f x y)) := ObjectSyntaxAtoms.native_memberExists w b f x y

example {m} (w b f x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.equalExistsSentence w b f x y)) := ObjectSyntaxAtoms.native_equalExists w b f x y

example {m} (w s x y t u v n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.memberFieldsSentence w s x y t u v n)) := ObjectSyntaxAtoms.native_memberFields w s x y t u v n

example {m} (w x y u v n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.equalFieldsSentence w x y u v n)) := ObjectSyntaxAtoms.native_equalFields w x y u v n

example {m} (w b f s t x y n r : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.memberValueUniqueSentence w b f s t x y n r)) := ObjectSyntaxAtoms.native_memberValueUnique w b f s t x y n r

example {m} (w b f x y n r : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.equalValueUniqueSentence w b f x y n r)) := ObjectSyntaxAtoms.native_equalValueUnique w b f x y n r

example {m} (w b f n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.memberDecodeSentence w b f n)) := ObjectSyntaxAtoms.native_memberDecode w b f n

example {m} (w n s x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.memberFiberSentence w n s x y)) := ObjectSyntaxAtoms.native_memberFiber w n s x y

example {m} (w b f n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.equalDecodeSentence w b f n)) := ObjectSyntaxAtoms.native_equalDecode w b f n

example {m} (w n x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.equalFiberSentence w n x y)) := ObjectSyntaxAtoms.native_equalFiber w n x y

example {m} (w b f n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.atomicContextsSentence w b f n)) := ObjectSyntaxAtoms.native_atomicContexts w b f n

example {m} (w b f n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.atomicRangeSentence w b f n)) := ObjectSyntaxAtoms.native_atomicRange w b f n

example {m} (truth : Bool) (w b f n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.nullaryAtomicSentence truth w b f n)) := ObjectSyntaxAtoms.native_nullaryAtomic truth w b f n

example {m} (w b f s x y n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.memberAtomicSentence w b f s x y n)) := ObjectSyntaxAtoms.native_memberAtomic w b f s x y n

example {m} (w b f x y n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.equalAtomicSentence w b f x y n)) := ObjectSyntaxAtoms.native_equalAtomic w b f x y n

example {m} (w b f i s x y n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.symbolCheckSentence w b f i s x y n)) := ObjectSyntaxAtoms.native_symbolCheck w b f i s x y n

example {m} (w b f i s x y n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.badSymbolSentence w b f i s x y n)) := ObjectSyntaxAtoms.native_badSymbol w b f i s x y n

example {m} (w b f t p n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.unknownAtomicTagSentence w b f t p n)) := ObjectSyntaxAtoms.native_unknownAtomicTag w b f t p n

example {m} (w s x y n : Fin m) : SyntaxAtomSyntax.memberCode w s x y n =
    SyntaxNodeSyntax.constructor 3 2 w (SyntaxAtomSyntax.three s x y) n := rfl

example {m} (w x y n : Fin m) : SyntaxAtomSyntax.equalCode w x y n =
    SyntaxNodeSyntax.constructor 2 3 w (SyntaxAtomSyntax.two x y) n := rfl

example {m} (w n : Fin m) : SyntaxAtomSyntax.zeroScalar w n =
    SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 n := rfl

example {m} (w b f s x y : Fin m) : SyntaxAtomSyntax.memberTypes w b f s x y =
    (SyntaxAtomSyntax.zeroScalar w s).conj ((SyntaxTermSyntax.term w b f x).conj (SyntaxTermSyntax.term w b f y)) := rfl

/-- 量词绑定的候选字段不设外部标准范围或scope限制。 -/
example {m} (w n s x y : Fin m) : SyntaxAtomDecode.memberUnique w n s x y =
    Source.Formula.all (.all (.all ((SyntaxAtomSyntax.memberCode w.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) n.castSucc.castSucc.castSucc).imp
        ((Source.Formula.equal (Fin.last m).castSucc.castSucc s.castSucc.castSucc.castSucc).conj
          ((Source.Formula.equal (Fin.last (m+1)).castSucc x.castSucc.castSucc.castSucc).conj
            (.equal (Fin.last (m+2)) y.castSucc.castSucc.castSucc)))))) := rfl

example {m} (w b f n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.nullaryAtomicSentence false w b f n)) := ObjectSyntaxAtoms.native_nullaryAtomic false w b f n

example {m} (w b f n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxAtoms.nullaryAtomicSentence true w b f n)) := ObjectSyntaxAtoms.native_nullaryAtomic true w b f n

/-! 七种逻辑局部分支及真实上下文集合值/幂集载体验收。 -/

example {m}  (h d x v b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.readAtValueSentence  h d x v b f)) := ObjectSyntaxLogical.native_readAtValue  h d x v b f

example {m}  (h x b f k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.advancedAtSuccessorSentence  h x b f k)) := ObjectSyntaxLogical.native_advancedAtSuccessor  h x b f k

example {m}  (w b f k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.successorContextSentence  w b f k)) := ObjectSyntaxLogical.native_successorContext  w b f k

example {m} (tag : Nat) (advance : Bool) (w b f h x n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.singleTypesSentence tag advance w b f h x n)) := ObjectSyntaxLogical.native_singleTypes tag advance w b f h x n

example {m}  (w b f h x n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.negationTypesSentence  w b f h x n)) := ObjectSyntaxLogical.native_negationTypes  w b f h x n

example {m} (kind : Fin 4) (w b f h x y n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.binaryTypesSentence kind w b f h x y n)) := ObjectSyntaxLogical.native_binaryTypes kind w b f h x y n

example {m} (universal : Bool) (w b f h x n k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.quantifierTypesSentence universal w b f h x n k)) := ObjectSyntaxLogical.native_quantifierTypes universal w b f h x n k

example {m} (tag : Nat) (advance : Bool) (w b f h x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.singleExistsSentence tag advance w b f h x)) := ObjectSyntaxLogical.native_singleExists tag advance w b f h x

example {m} (kind : Fin 4) (w b f h x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.binaryExistsSentence kind w b f h x y)) := ObjectSyntaxLogical.native_binaryExists kind w b f h x y

example {m} (universal : Bool) (w b f h x k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.quantifierExistsSentence universal w b f h x k)) := ObjectSyntaxLogical.native_quantifierExists universal w b f h x k

example {m} (tag : Nat) (w x y n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.singleFieldsSentence tag w x y n)) := ObjectSyntaxLogical.native_singleFields tag w x y n

example {m} (kind : Fin 4) (w x y u v n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.binaryFieldsSentence kind w x y u v n)) := ObjectSyntaxLogical.native_binaryFields kind w x y u v n

example {m} (tag : Nat) (w x n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.singleBoundSentence tag w x n)) := ObjectSyntaxLogical.native_singleBound tag w x n

example {m} (kind : Fin 4) (w x y n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.binaryBoundsSentence kind w x y n)) := ObjectSyntaxLogical.native_binaryBounds kind w x y n

example {m} (tag : Nat) (w x n r : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.singleUniqueSentence tag w x n r)) := ObjectSyntaxLogical.native_singleUnique tag w x n r

example {m} (kind : Fin 4) (w x y n r : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.binaryUniqueSentence kind w x y n r)) := ObjectSyntaxLogical.native_binaryUnique kind w x y n r

example {m} (tag : Nat) (advance : Bool) (w b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.singleRangeSentence tag advance w b f h n)) := ObjectSyntaxLogical.native_singleRange tag advance w b f h n

example {m} (tag : Nat) (advance : Bool) (w b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.singleDecodeSentence tag advance w b f h n)) := ObjectSyntaxLogical.native_singleDecode tag advance w b f h n

example {m} (kind : Fin 4) (w b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.binaryRangeSentence kind w b f h n)) := ObjectSyntaxLogical.native_binaryRange kind w b f h n

example {m} (kind : Fin 4) (w b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.binaryDecodeSentence kind w b f h n)) := ObjectSyntaxLogical.native_binaryDecode kind w b f h n

example {m} (tag : Nat) (w n x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.singleFiberSentence tag w n x)) := ObjectSyntaxLogical.native_singleFiber tag w n x

example {m} (kind : Fin 4) (w n x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.binaryFiberSentence kind w n x y)) := ObjectSyntaxLogical.native_binaryFiber kind w n x y

example {m} (tag : Nat) (advance : Bool) (w b f h x n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.singleNotCheckSentence tag advance w b f h x n)) := ObjectSyntaxLogical.native_singleNotCheck tag advance w b f h x n

example {m} (kind : Fin 4) (w b f h x y n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.binaryNotReadsSentence kind w b f h x y n)) := ObjectSyntaxLogical.native_binaryNotReads kind w b f h x y n

example {m} (universal : Bool) (w b f h x n k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.quantifierNotReadSentence universal w b f h x n k)) := ObjectSyntaxLogical.native_quantifierNotRead universal w b f h x n k

example {m} (tag : Nat) (advance : Bool) (w b f h t p n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.singleUnknownTagSentence tag advance w b f h t p n)) := ObjectSyntaxLogical.native_singleUnknownTag tag advance w b f h t p n

example {m} (kind : Fin 4) (w b f h t p n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.binaryUnknownTagSentence kind w b f h t p n)) := ObjectSyntaxLogical.native_binaryUnknownTag kind w b f h t p n

example {m}  (p b f w : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxContextCarrier.pairSubsetSentence  p b f w)) := ObjectSyntaxContextCarrier.native_pairSubset  p b f w

example {m}  (w a c b f p : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxContextCarrier.orderedMemberSentence  w a c b f p)) := ObjectSyntaxContextCarrier.native_orderedMember  w a c b f p

example {m}  (w a c b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxContextCarrier.pairExistsSentence  w a c b f)) := ObjectSyntaxContextCarrier.native_pairExists  w a c b f

example {m}  (c u v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxContextCarrier.stateMemberSentence  c u v)) := ObjectSyntaxContextCarrier.native_stateMember  c u v

example {m}  (w : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxContextCarrier.existsSentence  w)) := ObjectSyntaxContextCarrier.native_exists  w

example {m}  (w a c u v d t : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxContextCarrier.uniqueSentence  w a c u v d t)) := ObjectSyntaxContextCarrier.native_unique  w a c u v d t

example : SyntaxLogicalSyntax.binaryTag 0 = 5 := rfl
example : SyntaxLogicalSyntax.binaryTag 1 = 6 := rfl
example : SyntaxLogicalSyntax.binaryTag 2 = 7 := rfl
example : SyntaxLogicalSyntax.binaryTag 3 = 8 := rfl
example : SyntaxLogicalSyntax.quantifierTag true = 9 := rfl
example : SyntaxLogicalSyntax.quantifierTag false = 10 := rfl

/-- 两个量词体读取实际后继bound，不沿用父式bound；free保持原槽位。 -/
example {m} (h x b f : Fin m) : SyntaxContextReadSyntax.advanced h x b f =
    Source.Formula.ex ((OmegaSyntax.successor (Fin.last m) b.castSucc).conj
      (SyntaxContextReadSyntax.read h.castSucc x.castSucc (Fin.last m) f.castSucc)) := rfl

example {m} (w a c u : Fin m) : SyntaxContextCarrierSyntax.tower w a c u =
    (PowerSetSyntax.powerOf a w).conj ((PowerSetSyntax.powerOf c a).conj (PowerSetSyntax.powerOf u c)) := rfl

example {m} (h x b f : Fin m) : SyntaxContextReadSyntax.read h x b f =
    Source.Formula.ex ((GraphSyntax.edge h.castSucc x.castSucc (Fin.last m)).conj
      (GraphSyntax.edge (Fin.last m) b.castSucc f.castSucc)) := rfl

example {m} (w b f h x y n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.binaryTypesSentence 0 w b f h x y n)) := ObjectSyntaxLogical.native_binaryTypes 0 w b f h x y n

example {m} (w b f h x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.binaryExistsSentence 0 w b f h x y)) := ObjectSyntaxLogical.native_binaryExists 0 w b f h x y

example {m} (w b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.binaryDecodeSentence 0 w b f h n)) := ObjectSyntaxLogical.native_binaryDecode 0 w b f h n

example {m} (w b f h x y n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.binaryTypesSentence 1 w b f h x y n)) := ObjectSyntaxLogical.native_binaryTypes 1 w b f h x y n

example {m} (w b f h x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.binaryExistsSentence 1 w b f h x y)) := ObjectSyntaxLogical.native_binaryExists 1 w b f h x y

example {m} (w b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.binaryDecodeSentence 1 w b f h n)) := ObjectSyntaxLogical.native_binaryDecode 1 w b f h n

example {m} (w b f h x y n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.binaryTypesSentence 2 w b f h x y n)) := ObjectSyntaxLogical.native_binaryTypes 2 w b f h x y n

example {m} (w b f h x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.binaryExistsSentence 2 w b f h x y)) := ObjectSyntaxLogical.native_binaryExists 2 w b f h x y

example {m} (w b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.binaryDecodeSentence 2 w b f h n)) := ObjectSyntaxLogical.native_binaryDecode 2 w b f h n

example {m} (w b f h x y n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.binaryTypesSentence 3 w b f h x y n)) := ObjectSyntaxLogical.native_binaryTypes 3 w b f h x y n

example {m} (w b f h x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.binaryExistsSentence 3 w b f h x y)) := ObjectSyntaxLogical.native_binaryExists 3 w b f h x y

example {m} (w b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.binaryDecodeSentence 3 w b f h n)) := ObjectSyntaxLogical.native_binaryDecode 3 w b f h n

example {m} (w b f h x n k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.quantifierTypesSentence true w b f h x n k)) := ObjectSyntaxLogical.native_quantifierTypes true w b f h x n k

example {m} (w b f h x k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.quantifierExistsSentence true w b f h x k)) := ObjectSyntaxLogical.native_quantifierExists true w b f h x k

example {m} (w b f h x n k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.quantifierNotReadSentence true w b f h x n k)) := ObjectSyntaxLogical.native_quantifierNotRead true w b f h x n k

example {m} (w b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.singleDecodeSentence (SyntaxLogicalSyntax.quantifierTag true) true w b f h n)) := ObjectSyntaxLogical.native_singleDecode (SyntaxLogicalSyntax.quantifierTag true) true w b f h n

example {m} (w b f h x n k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.quantifierTypesSentence false w b f h x n k)) := ObjectSyntaxLogical.native_quantifierTypes false w b f h x n k

example {m} (w b f h x k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.quantifierExistsSentence false w b f h x k)) := ObjectSyntaxLogical.native_quantifierExists false w b f h x k

example {m} (w b f h x n k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.quantifierNotReadSentence false w b f h x n k)) := ObjectSyntaxLogical.native_quantifierNotRead false w b f h x n k

example {m} (w b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.singleDecodeSentence (SyntaxLogicalSyntax.quantifierTag false) true w b f h n)) := ObjectSyntaxLogical.native_singleDecode (SyntaxLogicalSyntax.quantifierTag false) true w b f h n

example {m} (w b f h x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.singleExistsSentence 4 false w b f h x)) := ObjectSyntaxLogical.native_singleExists 4 false w b f h x

example {m} (w b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxLogical.singleDecodeSentence 4 false w b f h n)) := ObjectSyntaxLogical.native_singleDecode 4 false w b f h n

/-! 全11局部分支的实际Separation状态、原递归图与全部内部自然码状态值。 -/

example {m}  (w b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.localContextSentence  w b f h n)) := ObjectSyntaxTypeStates.native_localContext  w b f h n

example {m}  (w b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.localRangeSentence  w b f h n)) := ObjectSyntaxTypeStates.native_localRange  w b f h n

example {m}  (w n h p b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.rowAtPairSentence  w n h p b f)) := ObjectSyntaxTypeStates.native_rowAtPair  w n h p b f

example {m}  (w c n h : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.stateExistsSentence  w c n h)) := ObjectSyntaxTypeStates.native_stateExists  w c n h

example {m}  (w c n h : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.stateFiberSentence  w c n h)) := ObjectSyntaxTypeStates.native_stateFiber  w c n h

example {m}  (w c n h v t : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.stateUniqueSentence  w c n h v t)) := ObjectSyntaxTypeStates.native_stateUnique  w c n h v t

example {m}  (w c n h v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.stateSubsetSentence  w c n h v)) := ObjectSyntaxTypeStates.native_stateSubset  w c n h v

example {m}  (w c u n h v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.stateUniverseSentence  w c u n h v)) := ObjectSyntaxTypeStates.native_stateUniverse  w c u n h v

example {m}  (w c n h v p : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.noJunkSentence  w c n h v p)) := ObjectSyntaxTypeStates.native_noJunk  w c n h v p

example {m}  (w a c n h v b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.stateEdgeSentence  w a c n h v b f)) := ObjectSyntaxTypeStates.native_stateEdge  w a c n h v b f

example {m}  (w c n h v b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.badContextSentence  w c n h v b f)) := ObjectSyntaxTypeStates.native_badContext  w c n h v b f

example {m}  (w c n h v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.offNaturalSentence  w c n h v)) := ObjectSyntaxTypeStates.native_offNatural  w c n h v

example {m}  (w c : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.totalSentence  w c)) := ObjectSyntaxTypeStates.native_total  w c

example {m}  (w c : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.deterministicSentence  w c)) := ObjectSyntaxTypeStates.native_deterministic  w c

example {m}  (w c : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.recursorsSentence  w c)) := ObjectSyntaxTypeStates.native_recursors  w c

example {m}  (w c d : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.ordinalFiberSentence  w c d)) := ObjectSyntaxTypeStates.native_ordinalFiber  w c d

example {m}  (w : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.actualCarriersSentence  w)) := ObjectSyntaxTypeStates.native_actualCarriers  w

example {m}  (w c n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.evaluationExistsSentence  w c n)) := ObjectSyntaxTypeStates.native_evaluationExists  w c n

example {m}  (w c n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.naturalEvaluationSentence  w c n)) := ObjectSyntaxTypeStates.native_naturalEvaluation  w c n

example {m}  (w c n v t : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.evaluationUniqueSentence  w c n v t)) := ObjectSyntaxTypeStates.native_evaluationUnique  w c n v t

example {m}  (w c n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.evaluationFiberSentence  w c n)) := ObjectSyntaxTypeStates.native_evaluationFiber  w c n

example {m}  (w c f g d t : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.graphsAgreeSentence  w c f g d t)) := ObjectSyntaxTypeStates.native_graphsAgree  w c f g d t

example {m}  (w c f d n v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.graphValueSentence  w c f d n v)) := ObjectSyntaxTypeStates.native_graphValue  w c f d n v

example {m}  (w c n v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.historySentence  w c n v)) := ObjectSyntaxTypeStates.native_history  w c n v

example {m}  (w c n v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.evaluationSubsetSentence  w c n v)) := ObjectSyntaxTypeStates.native_evaluationSubset  w c n v

example {m}  (w c u n v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.evaluationUniverseSentence  w c u n v)) := ObjectSyntaxTypeStates.native_evaluationUniverse  w c u n v

example {m}  (w c n v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.evaluationOffNaturalSentence  w c n v)) := ObjectSyntaxTypeStates.native_evaluationOffNatural  w c n v

example {m}  (w c n b f v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.typedAtValueSentence  w c n b f v)) := ObjectSyntaxTypeStates.native_typedAtValue  w c n b f v

example {m}  (w c h d x b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.readTypedSentence  w c h d x b f)) := ObjectSyntaxTypeStates.native_readTyped  w c h d x b f

example {m}  (w c n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.typedRejectCodeSentence  w c n b f)) := ObjectSyntaxTypeStates.native_typedRejectCode  w c n b f

example {m}  (w c n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.typedRejectContextSentence  w c n b f)) := ObjectSyntaxTypeStates.native_typedRejectContext  w c n b f

example {m}  (w b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.introduceAtomicSentence  w b f h n)) := ObjectSyntaxTypeStates.native_introduceAtomic  w b f h n

example {m}  (w b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.introduceNegationSentence  w b f h n)) := ObjectSyntaxTypeStates.native_introduceNegation  w b f h n

example {m} (kind : Fin 4) (w b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.introduceBinarySentence kind w b f h n)) := ObjectSyntaxTypeStates.native_introduceBinary kind w b f h n

example {m} (universal : Bool) (w b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.introduceQuantifierSentence universal w b f h n)) := ObjectSyntaxTypeStates.native_introduceQuantifier universal w b f h n

/-- 局部判据精确保留四个原子构造和七个原逻辑构造，没有默认接受分支。 -/
example {m} (w b f h n : Fin m) : SyntaxFormulaLocalSyntax.localType w b f h n =
    (SyntaxAtomSyntax.atomic w b f n).disj ((SyntaxLogicalSyntax.negation w b f h n).disj
      ((SyntaxLogicalSyntax.binary 0 w b f h n).disj ((SyntaxLogicalSyntax.binary 1 w b f h n).disj
        ((SyntaxLogicalSyntax.binary 2 w b f h n).disj ((SyntaxLogicalSyntax.binary 3 w b f h n).disj
          ((SyntaxLogicalSyntax.quantified true w b f h n).disj (SyntaxLogicalSyntax.quantified false w b f h n))))))) := rfl

/-- 类型公式保留自然码和两侧自然上下文守卫；状态值是内部存在量词。 -/
example {m} (w c n b f : Fin m) : SyntaxTypeJudgmentSyntax.typed w c n b f =
    (Source.Formula.mem n w).conj ((SyntaxTermSyntax.contexts w b f).conj (Source.Formula.ex
      ((SyntaxTypeEvaluationSyntax.evaluation w.castSucc c.castSucc n.castSucc (Fin.last m)).conj
        (GraphSyntax.edge (Fin.last m) b.castSucc f.castSucc)))) := rfl

example {m} (ρ : Fin 2 → Fin m) (n h v : Fin m) :
    OrdinalRecursionSyntax.operator SyntaxTypeRecursionSyntax.matrix ρ n h v =
      SyntaxTypeStateSyntax.state (ρ 0) (ρ 1) n h v := SyntaxTypeRecursionSyntax.matrix_operator ρ n h v

/-- 值保留真实后继域、完整原递归图和实际边，不以宿主输出代替。 -/
example {m} (w c d g n v : Fin m) : SyntaxTypeEvaluationSyntax.data w c d g n v =
    (OmegaSyntax.successor d n).conj ((SyntaxTypeRecursionSyntax.graph w c g d).conj (GraphSyntax.edge g n v)) := rfl

example {m} (w b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.introduceBinarySentence 0 w b f h n)) := ObjectSyntaxTypeStates.native_introduceBinary 0 w b f h n

example {m} (w b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.introduceBinarySentence 1 w b f h n)) := ObjectSyntaxTypeStates.native_introduceBinary 1 w b f h n

example {m} (w b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.introduceBinarySentence 2 w b f h n)) := ObjectSyntaxTypeStates.native_introduceBinary 2 w b f h n

example {m} (w b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.introduceBinarySentence 3 w b f h n)) := ObjectSyntaxTypeStates.native_introduceBinary 3 w b f h n

example {m} (w b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.introduceQuantifierSentence true w b f h n)) := ObjectSyntaxTypeStates.native_introduceQuantifier true w b f h n

example {m} (w b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeStates.introduceQuantifierSentence false w b f h n)) := ObjectSyntaxTypeStates.native_introduceQuantifier false w b f h n

/-! 历史无关11构造递归式及无额外存在前提的实际内部类型系统。 -/

example {m}  (w c h n x b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeRecursive.readSentence  w c h n x b f)) := ObjectSyntaxTypeRecursive.native_read  w c h n x b f

example {m}  (w c h n x b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeRecursive.advancedSentence  w c h n x b f)) := ObjectSyntaxTypeRecursive.native_advanced  w c h n x b f

example {m} (advance : Bool) (w c h n x b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeRecursive.checkSentence advance w c h n x b f)) := ObjectSyntaxTypeRecursive.native_check advance w c h n x b f

example {m} (tag : Nat) (advance : Bool) (w c b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeRecursive.singleSentence tag advance w c b f h n)) := ObjectSyntaxTypeRecursive.native_single tag advance w c b f h n

example {m} (kind : Fin 4) (w c b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeRecursive.binarySentence kind w c b f h n)) := ObjectSyntaxTypeRecursive.native_binary kind w c b f h n

example {m}  (w c b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeRecursive.localSentence  w c b f h n)) := ObjectSyntaxTypeRecursive.native_local  w c b f h n

example {m}  (w a c b f h n v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeRecursive.atStateSentence  w a c b f h n v)) := ObjectSyntaxTypeRecursive.native_atState  w a c b f h n v

example {m}  (w a c n v b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeRecursive.atValueSentence  w a c n v b f)) := ObjectSyntaxTypeRecursive.native_atValue  w a c n v b f

example {m}  (w a c n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeRecursive.recursiveSentence  w a c n b f)) := ObjectSyntaxTypeRecursive.native_recursive  w a c n b f

example {m}  (w a c : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeRecursive.universalSentence  w a c)) := ObjectSyntaxTypeRecursive.native_universal  w a c

example {m}  (w : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeRecursive.actualSystemSentence  w)) := ObjectSyntaxTypeRecursive.native_actualSystem  w

example : FirstOrder.Derives nativeZF [] (Translation.sentence ObjectSyntaxTypeRecursive.existenceSentence) := ObjectSyntaxTypeRecursive.native_existence

/-- 两个量词体保留实际后继bound；此处没有历史参数。 -/
example {m} (w c x b f : Fin m) : SyntaxTypeRecursiveSyntax.advancedTyped w c x b f =
    Source.Formula.ex ((OmegaSyntax.successor (Fin.last m) b.castSucc).conj
      (SyntaxTypeJudgmentSyntax.typed w.castSucc c.castSucc x.castSucc (Fin.last m) f.castSucc)) := rfl

/-- 全内部候选n,b,f；不把模式限制为标准码。 -/
example {m} (w c : Fin m) : SyntaxTypeSystemSyntax.universalLaw w c =
    Source.Formula.all (.all (.all
      ((SyntaxTypeJudgmentSyntax.typed w.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc
        (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))).iff
       (SyntaxTypeRecursiveSyntax.criterion w.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc
        (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)))))) := rfl

example : ObjectSyntaxTypeRecursive.existenceSentence = Source.Formula.ex
    ((OmegaSyntax.omega (Fin.last 0)).conj (SyntaxTypeSystemSyntax.system (Fin.last 0))) := rfl

/-- 自然根码守卫在完整历史无关判据中显式保留。 -/
example {m} (w c n b f : Fin m) : SyntaxTypeRecursiveSyntax.criterion w c n b f =
    (Source.Formula.mem n w).conj (SyntaxTypeRecursiveSyntax.allCases w c n b f) := rfl

example {m} (w c b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeRecursive.binarySentence 0 w c b f h n)) := ObjectSyntaxTypeRecursive.native_binary 0 w c b f h n

example {m} (w c b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeRecursive.binarySentence 1 w c b f h n)) := ObjectSyntaxTypeRecursive.native_binary 1 w c b f h n

example {m} (w c b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeRecursive.binarySentence 2 w c b f h n)) := ObjectSyntaxTypeRecursive.native_binary 2 w c b f h n

example {m} (w c b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeRecursive.binarySentence 3 w c b f h n)) := ObjectSyntaxTypeRecursive.native_binary 3 w c b f h n

example {m} (w c b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeRecursive.singleSentence 4 false w c b f h n)) := ObjectSyntaxTypeRecursive.native_single 4 false w c b f h n

example {m} (w c b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeRecursive.singleSentence 9 true w c b f h n)) := ObjectSyntaxTypeRecursive.native_single 9 true w c b f h n

example {m} (w c b f h n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypeRecursive.singleSentence 10 true w c b f h n)) := ObjectSyntaxTypeRecursive.native_single 10 true w c b f h n

/-! 无额外载体FormulaCode；全部原11已知构造、内部ω及任意内部候选。 -/
example {m} (w : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.carrierExistsSentence w)) := ObjectFormulaCode.native_carrierExists w

example {m} (w a c d t : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.carrierUniqueSentence w a c d t)) := ObjectFormulaCode.native_carrierUnique w a c d t

example {m} (w a c n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.atCarrierSentence w a c n b f)) := ObjectFormulaCode.native_atCarrier w a c n b f

example {m} (w n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.guardsSentence w n b f)) := ObjectFormulaCode.native_guards w n b f

example {m} (w n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.rejectCodeSentence w n b f)) := ObjectFormulaCode.native_rejectCode w n b f

example {m} (w n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.rejectContextSentence w n b f)) := ObjectFormulaCode.native_rejectContext w n b f

example {m} (w v n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.omegaIndependentSentence w v n b f)) := ObjectFormulaCode.native_omegaIndependent w v n b f

example {m} (w n b f t : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.rootTransportSentence w n b f t)) := ObjectFormulaCode.native_rootTransport w n b f t

example {m} (w n b f t : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.boundTransportSentence w n b f t)) := ObjectFormulaCode.native_boundTransport w n b f t

example {m} (w n b f t : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.freeTransportSentence w n b f t)) := ObjectFormulaCode.native_freeTransport w n b f t

example {m} (w n b f t : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.omegaTransportSentence w n b f t)) := ObjectFormulaCode.native_omegaTransport w n b f t

example {m} (w a c x b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.advancedTransferSentence w a c x b f)) := ObjectFormulaCode.native_advancedTransfer w a c x b f

example {m} (tag : Nat) (advance : Bool) (w a c b f n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.singleTransferSentence tag advance w a c b f n)) := ObjectFormulaCode.native_singleTransfer tag advance w a c b f n

example {m} (kind : Fin 4) (w a c b f n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.binaryTransferSentence kind w a c b f n)) := ObjectFormulaCode.native_binaryTransfer kind w a c b f n

example {m} (w a c n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.criterionTransferSentence w a c n b f)) := ObjectFormulaCode.native_criterionTransfer w a c n b f

example {m} (w n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.recursiveSentence w n b f)) := ObjectFormulaCode.native_recursive w n b f

example {m} (w : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.universalSentence w)) := ObjectFormulaCode.native_universal w

example {m} (truth : Bool) (w b f n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.nullaryTypesSentence truth w b f n)) := ObjectFormulaCode.native_nullaryTypes truth w b f n

example {m} (w b f s x y n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.memberTypesSentence w b f s x y n)) := ObjectFormulaCode.native_memberTypes w b f s x y n

example {m} (w b f x y n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.equalTypesSentence w b f x y n)) := ObjectFormulaCode.native_equalTypes w b f x y n

example {m} (w b f x n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.negationTypesSentence w b f x n)) := ObjectFormulaCode.native_negationTypes w b f x n

example {m} (w b f x y n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.binary0TypesSentence w b f x y n)) := ObjectFormulaCode.native_binary0Types w b f x y n

example {m} (w b f x y n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.binary1TypesSentence w b f x y n)) := ObjectFormulaCode.native_binary1Types w b f x y n

example {m} (w b f x y n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.binary2TypesSentence w b f x y n)) := ObjectFormulaCode.native_binary2Types w b f x y n

example {m} (w b f x y n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.binary3TypesSentence w b f x y n)) := ObjectFormulaCode.native_binary3Types w b f x y n

example {m} (w b f x n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.forallTypesSentence w b f x n)) := ObjectFormulaCode.native_forallTypes w b f x n

example {m} (w b f x n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.existsTypesSentence w b f x n)) := ObjectFormulaCode.native_existsTypes w b f x n

example {m} (universal : Bool) (w b f x n k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.quantifierTypesSentence universal w b f x n k)) := ObjectFormulaCode.native_quantifierTypes universal w b f x n k

example {m} (w b f t p n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.unknownTagSentence w b f t p n)) := ObjectFormulaCode.native_unknownTag w b f t p n

example {m} (w n b f : Fin m) : FormulaCodeSyntax.formulaCode w n b f =
    Source.Formula.ex (.ex ((FormulaCodeSyntax.carrier w.castSucc.castSucc
        (Fin.last m).castSucc (Fin.last (m+1))).conj
      (SyntaxTypeJudgmentSyntax.typed w.castSucc.castSucc (Fin.last (m+1))
        n.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc))) := rfl

example {m} (w x b f : Fin m) : FormulaCodeRecursiveSyntax.advancedCode w x b f =
    Source.Formula.ex ((OmegaSyntax.successor (Fin.last m) b.castSucc).conj
      (FormulaCodeSyntax.formulaCode w.castSucc x.castSucc (Fin.last m) f.castSucc)) := rfl

example {m} (w : Fin m) : FormulaCodeRecursive.universalLaw w =
    Source.Formula.all (.all (.all
      ((FormulaCodeSyntax.formulaCode w.castSucc.castSucc.castSucc
        (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))).iff
       (FormulaCodeRecursiveSyntax.criterion w.castSucc.castSucc.castSucc
        (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)))))) := rfl

example {m} (w b f n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.nullaryTypesSentence false w b f n)) :=
  ObjectFormulaCode.native_nullaryTypes false w b f n

example {m} (w b f n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.nullaryTypesSentence true w b f n)) :=
  ObjectFormulaCode.native_nullaryTypes true w b f n

example {m} (w b f x n k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.quantifierTypesSentence true w b f x n k)) :=
  ObjectFormulaCode.native_quantifierTypes true w b f x n k

example {m} (w b f x n k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCode.quantifierTypesSentence false w b f x n k)) :=
  ObjectFormulaCode.native_quantifierTypes false w b f x n k

/-! 原实际构造、接受根完整字段及所有内部标签/长度候选的对象核验。 -/
example {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.fiberSentence k tag xs w b f)) :=
  ObjectFormulaCodeConstruction.native_fiber k tag xs w b f

example {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.existsOfFiberSentence k tag xs w b f)) :=
  ObjectFormulaCodeConstruction.native_existsOfFiber k tag xs w b f

example {m} (truth : Bool) (w b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.nullaryLawSentence truth w b f)) :=
  ObjectFormulaCodeConstruction.native_nullaryLaw truth w b f

example {m} (truth : Bool) (w b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.nullaryFiberSentence truth w b f)) :=
  ObjectFormulaCodeConstruction.native_nullaryFiber truth w b f

example {m} (truth : Bool) (w b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.nullaryExistsSentence truth w b f)) :=
  ObjectFormulaCodeConstruction.native_nullaryExists truth w b f

example {m} (w b f s x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.memberLawSentence w b f s x y)) :=
  ObjectFormulaCodeConstruction.native_memberLaw w b f s x y

example {m} (w b f s x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.memberFiberSentence w b f s x y)) :=
  ObjectFormulaCodeConstruction.native_memberFiber w b f s x y

example {m} (w b f s x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.memberExistsSentence w b f s x y)) :=
  ObjectFormulaCodeConstruction.native_memberExists w b f s x y

example {m} (w b f x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.equalLawSentence w b f x y)) :=
  ObjectFormulaCodeConstruction.native_equalLaw w b f x y

example {m} (w b f x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.equalFiberSentence w b f x y)) :=
  ObjectFormulaCodeConstruction.native_equalFiber w b f x y

example {m} (w b f x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.equalExistsSentence w b f x y)) :=
  ObjectFormulaCodeConstruction.native_equalExists w b f x y

example {m} (w b f x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.negationLawSentence w b f x)) :=
  ObjectFormulaCodeConstruction.native_negationLaw w b f x

example {m} (w b f x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.negationFiberSentence w b f x)) :=
  ObjectFormulaCodeConstruction.native_negationFiber w b f x

example {m} (w b f x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.negationExistsSentence w b f x)) :=
  ObjectFormulaCodeConstruction.native_negationExists w b f x

example {m} (w b f x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.forallLawSentence w b f x)) :=
  ObjectFormulaCodeConstruction.native_forallLaw w b f x

example {m} (w b f x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.forallFiberSentence w b f x)) :=
  ObjectFormulaCodeConstruction.native_forallFiber w b f x

example {m} (w b f x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.forallExistsSentence w b f x)) :=
  ObjectFormulaCodeConstruction.native_forallExists w b f x

example {m} (w b f x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.existsLawSentence w b f x)) :=
  ObjectFormulaCodeConstruction.native_existsLaw w b f x

example {m} (w b f x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.existsFiberSentence w b f x)) :=
  ObjectFormulaCodeConstruction.native_existsFiber w b f x

example {m} (w b f x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.existsExistsSentence w b f x)) :=
  ObjectFormulaCodeConstruction.native_existsExists w b f x

example {m} (w b f x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.binary0LawSentence w b f x y)) :=
  ObjectFormulaCodeConstruction.native_binary0Law w b f x y

example {m} (w b f x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.binary0FiberSentence w b f x y)) :=
  ObjectFormulaCodeConstruction.native_binary0Fiber w b f x y

example {m} (w b f x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.binary0ExistsSentence w b f x y)) :=
  ObjectFormulaCodeConstruction.native_binary0Exists w b f x y

example {m} (w b f x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.binary1LawSentence w b f x y)) :=
  ObjectFormulaCodeConstruction.native_binary1Law w b f x y

example {m} (w b f x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.binary1FiberSentence w b f x y)) :=
  ObjectFormulaCodeConstruction.native_binary1Fiber w b f x y

example {m} (w b f x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.binary1ExistsSentence w b f x y)) :=
  ObjectFormulaCodeConstruction.native_binary1Exists w b f x y

example {m} (w b f x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.binary2LawSentence w b f x y)) :=
  ObjectFormulaCodeConstruction.native_binary2Law w b f x y

example {m} (w b f x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.binary2FiberSentence w b f x y)) :=
  ObjectFormulaCodeConstruction.native_binary2Fiber w b f x y

example {m} (w b f x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.binary2ExistsSentence w b f x y)) :=
  ObjectFormulaCodeConstruction.native_binary2Exists w b f x y

example {m} (w b f x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.binary3LawSentence w b f x y)) :=
  ObjectFormulaCodeConstruction.native_binary3Law w b f x y

example {m} (w b f x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.binary3FiberSentence w b f x y)) :=
  ObjectFormulaCodeConstruction.native_binary3Fiber w b f x y

example {m} (w b f x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.binary3ExistsSentence w b f x y)) :=
  ObjectFormulaCodeConstruction.native_binary3Exists w b f x y

example {m} (w b f x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.membershipFiberSentence w b f x y)) :=
  ObjectFormulaCodeConstruction.native_membershipFiber w b f x y

example {m} (k : Nat) (xs : Fin k → Fin m) (w p : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.forestValidSentence k xs w p)) :=
  ObjectFormulaCodeConstruction.native_forestValid k xs w p

example {m} (k : Nat) (xs : Fin k → Fin m) (w t n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.nodeShapeSentence k xs w t n)) :=
  ObjectFormulaCodeConstruction.native_nodeShape k xs w t n

example {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.constructorShapeSentence k tag xs w n)) :=
  ObjectFormulaCodeConstruction.native_constructorShape k tag xs w n

example {m} (w n t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.shapeUniqueSentence w n t p l g)) :=
  ObjectFormulaCodeConstruction.native_shapeUnique w n t p l g

example {m} (w n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.acceptedShapeSentence w n b f)) :=
  ObjectFormulaCodeConstruction.native_acceptedShape w n b f

example {m} (w n b f t p l g r : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.reencodingSentence w n b f t p l g r)) :=
  ObjectFormulaCodeConstruction.native_reencoding w n b f t p l g r

example {m} (w n b f t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.roundTripSentence w n b f t p l g)) :=
  ObjectFormulaCodeConstruction.native_roundTrip w n b f t p l g

example {m} (k : Nat) (xs : Fin k → Fin m) (w p l : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.forestAritySentence k xs w p l)) :=
  ObjectFormulaCodeConstruction.native_forestArity k xs w p l

example {m} (k : Nat) (xs : Fin k → Fin m) (w t n a p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.nodeAritySentence k xs w t n a p l g)) :=
  ObjectFormulaCodeConstruction.native_nodeArity k xs w t n a p l g

example {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n a p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.constructorAritySentence k tag xs w n a p l g)) :=
  ObjectFormulaCodeConstruction.native_constructorArity k tag xs w n a p l g

example {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n a p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.constructorTagSentence k tag xs w n a p l g)) :=
  ObjectFormulaCodeConstruction.native_constructorTag k tag xs w n a p l g

example {m} (w n b f t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.allowedAritySentence w n b f t p l g)) :=
  ObjectFormulaCodeConstruction.native_allowedArity w n b f t p l g

example {m} (w n b f t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.rejectAritySentence w n b f t p l g)) :=
  ObjectFormulaCodeConstruction.native_rejectArity w n b f t p l g

example {m} (w b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.nullaryFiberSentence false w b f)) :=
  ObjectFormulaCodeConstruction.native_nullaryFiber false w b f

example {m} (w b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeConstruction.nullaryFiberSentence true w b f)) :=
  ObjectFormulaCodeConstruction.native_nullaryFiber true w b f

example {m} (w : Fin m) (xs : Fin 1 → Fin m) (b f : Fin m) :
    FormulaCodeConstructSyntax.typedFiber 1 9 w xs b f = Source.Formula.ex
      (((Source.Formula.mem (Fin.last m) w.castSucc).conj
        ((SyntaxNodeSyntax.constructor 1 9 w.castSucc (fun i => (xs i).castSucc) (Fin.last m)).conj
          (FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) b.castSucc f.castSucc))).conj
        (.all ((SyntaxNodeSyntax.constructor 1 9 w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc)
          (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc)))) := rfl

example : FormulaCodeAllowedAritySyntax.expectedArity 0 = 0 := rfl
example : FormulaCodeAllowedAritySyntax.expectedArity 1 = 0 := rfl
example : FormulaCodeAllowedAritySyntax.expectedArity 2 = 3 := rfl
example : FormulaCodeAllowedAritySyntax.expectedArity 3 = 2 := rfl
example : FormulaCodeAllowedAritySyntax.expectedArity 4 = 1 := rfl
example : FormulaCodeAllowedAritySyntax.expectedArity 5 = 2 := rfl
example : FormulaCodeAllowedAritySyntax.expectedArity 6 = 2 := rfl
example : FormulaCodeAllowedAritySyntax.expectedArity 7 = 2 := rfl
example : FormulaCodeAllowedAritySyntax.expectedArity 8 = 2 := rfl
example : FormulaCodeAllowedAritySyntax.expectedArity 9 = 1 := rfl
example : FormulaCodeAllowedAritySyntax.expectedArity 10 = 1 := rfl

/-! 全内部索引字段对应、任意外部纯公式模式及真实量词后继类型。 -/
example {m} (k : Nat) (l i : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.numeralMembersSentence k l i)) :=
  ObjectSyntaxTypedFields.native_numeralMembers k l i

example {m} (k : Nat) (j : Fin k) (l i : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.indexMemberSentence k j l i)) :=
  ObjectSyntaxTypedFields.native_indexMember k j l i

example {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n i y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.forestValueSentence k xs j w n i y)) :=
  ObjectSyntaxTypedFields.native_forestValue k xs j w n i y

example {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n l g i y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.forestEdgeSentence k xs j w n l g i y)) :=
  ObjectSyntaxTypedFields.native_forestEdge k xs j w n l g i y

example {m} (k : Nat) (xs : Fin k → Fin m) (w n l g i y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.forestFullSentence k xs w n l g i y)) :=
  ObjectSyntaxTypedFields.native_forestFull k xs w n l g i y

example {m} (k : Nat) (xs : Fin k → Fin m) (w n l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.forestAllSentence k xs w n l g)) :=
  ObjectSyntaxTypedFields.native_forestAll k xs w n l g

example {m} (k : Nat) (xs : Fin k → Fin m) (w a n t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.nodeAllSentence k xs w a n t p l g)) :=
  ObjectSyntaxTypedFields.native_nodeAll k xs w a n t p l g

example {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w a n t p l g i y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.nodeValueSentence k xs j w a n t p l g i y)) :=
  ObjectSyntaxTypedFields.native_nodeValue k xs j w a n t p l g i y

example {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.constructorAllSentence k tag xs w n t p l g)) :=
  ObjectSyntaxTypedFields.native_constructorAll k tag xs w n t p l g

example {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g i y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.constructorValueSentence k tag xs j w n t p l g i y)) :=
  ObjectSyntaxTypedFields.native_constructorValue k tag xs j w n t p l g i y

example {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.slotSentence k tag xs j w n t p l g y)) :=
  ObjectSyntaxTypedFields.native_slot k tag xs j w n t p l g y

example {m} (q : Nat) (a : Formula (q+1)) (ρ : Fin q → Fin m) (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.checkedSentence q a ρ k tag xs j w n t p l g)) :=
  ObjectSyntaxTypedFields.native_checked q a ρ k tag xs j w n t p l g

example {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.codeFieldSentence k tag xs j w n t p l g b f)) :=
  ObjectSyntaxTypedFields.native_codeField k tag xs j w n t p l g b f

example {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.termFieldSentence k tag xs j w n t p l g b f)) :=
  ObjectSyntaxTypedFields.native_termField k tag xs j w n t p l g b f

example {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.advancedFieldSentence k tag xs j w n t p l g b f)) :=
  ObjectSyntaxTypedFields.native_advancedField k tag xs j w n t p l g b f

example {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.zeroFieldSentence k tag xs j w n t p l g)) :=
  ObjectSyntaxTypedFields.native_zeroField k tag xs j w n t p l g

example {m} (w n b f s x y t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.memberTypingSentence w n b f s x y t p l g)) :=
  ObjectSyntaxTypedFields.native_memberTyping w n b f s x y t p l g

example {m} (w n b f x y t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.equalTypingSentence w n b f x y t p l g)) :=
  ObjectSyntaxTypedFields.native_equalTyping w n b f x y t p l g

example {m} (w n b f x t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.negationTypingSentence w n b f x t p l g)) :=
  ObjectSyntaxTypedFields.native_negationTyping w n b f x t p l g

example {m} (kind : Fin 4) (w n b f x y t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.binaryTypingSentence kind w n b f x y t p l g)) :=
  ObjectSyntaxTypedFields.native_binaryTyping kind w n b f x y t p l g

example {m} (universal : Bool) (w n b f x t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.quantifierTypingSentence universal w n b f x t p l g)) :=
  ObjectSyntaxTypedFields.native_quantifierTyping universal w n b f x t p l g

example {m} (universal : Bool) (w n b f x t p l g u : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.quantifierSuccessorSentence universal w n b f x t p l g u)) :=
  ObjectSyntaxTypedFields.native_quantifierSuccessor universal w n b f x t p l g u

example {m} (k : Nat) (xs : Fin k → Fin m) (g : Fin m) : SyntaxForestFields.graphLaw k xs g =
    Source.Formula.all (.all
      ((GraphSyntax.edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
        (SyntaxPositionSyntax.positions k (fun j => (xs j).castSucc.castSucc)
          (Fin.last m).castSucc (Fin.last (m+1))))) := rfl

example {m} (w x b f : Fin m) : FormulaCodeRecursiveSyntax.advancedCode w x b f =
    Source.Formula.ex ((OmegaSyntax.successor (Fin.last m) b.castSucc).conj
      (FormulaCodeSyntax.formulaCode w.castSucc x.castSucc (Fin.last m) f.castSucc)) := rfl

example {m} (g y : Fin m) (j : Nat) : SyntaxSlotSyntax.slot g j y =
    Source.Formula.ex ((SyntaxNumeralSyntax.numeral j (Fin.last m)).conj
      (GraphSyntax.edge g.castSucc (Fin.last m) y.castSucc)) := rfl

example {m} (w n b f x y t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.binaryTypingSentence 0 w n b f x y t p l g)) :=
  ObjectSyntaxTypedFields.native_binaryTyping 0 w n b f x y t p l g

example {m} (w n b f x y t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.binaryTypingSentence 1 w n b f x y t p l g)) :=
  ObjectSyntaxTypedFields.native_binaryTyping 1 w n b f x y t p l g

example {m} (w n b f x y t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.binaryTypingSentence 2 w n b f x y t p l g)) :=
  ObjectSyntaxTypedFields.native_binaryTyping 2 w n b f x y t p l g

example {m} (w n b f x y t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.binaryTypingSentence 3 w n b f x y t p l g)) :=
  ObjectSyntaxTypedFields.native_binaryTyping 3 w n b f x y t p l g

example {m} (w n b f x t p l g u : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.quantifierSuccessorSentence false w n b f x t p l g u)) :=
  ObjectSyntaxTypedFields.native_quantifierSuccessor false w n b f x t p l g u

example {m} (w n b f x t p l g u : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxTypedFields.quantifierSuccessorSentence true w n b f x t p l g u)) :=
  ObjectSyntaxTypedFields.native_quantifierSuccessor true w n b f x t p l g u

/-! 原树有效性全内部成员归纳及无Constructor前提的实际TypedData正向解码。 -/
example {m} (k : Nat) (xs : Fin k → Fin m) (w g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.graphChildrenSentence k xs w g)) :=
  ObjectFormulaCodeTreeValidity.native_graphChildren k xs w g

example {m} (k : Nat) (xs : Fin k → Fin m) (w a n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.nodeSentence k xs w a n)) :=
  ObjectFormulaCodeTreeValidity.native_node k xs w a n

example {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.constructorSentence k tag xs w n)) :=
  ObjectFormulaCodeTreeValidity.native_constructor k tag xs w n

example {m} (w i n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.scalarSentence w i n)) :=
  ObjectFormulaCodeTreeValidity.native_scalar w i n

example {m} (bound : Bool) (w i n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.variableSentence bound w i n)) :=
  ObjectFormulaCodeTreeValidity.native_variable bound w i n

example {m} (bound : Bool) (w l n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.termBranchSentence bound w l n)) :=
  ObjectFormulaCodeTreeValidity.native_termBranch bound w l n

example {m} (w b f n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.termSentence w b f n)) :=
  ObjectFormulaCodeTreeValidity.native_term w b f n

example {m} (truth : Bool) (w b f n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.nullarySentence truth w b f n)) :=
  ObjectFormulaCodeTreeValidity.native_nullary truth w b f n

example {m} (w b f n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.memberSentence w b f n)) :=
  ObjectFormulaCodeTreeValidity.native_member w b f n

example {m} (w b f n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.equalSentence w b f n)) :=
  ObjectFormulaCodeTreeValidity.native_equal w b f n

example {m} (w b f n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.atomicSentence w b f n)) :=
  ObjectFormulaCodeTreeValidity.native_atomic w b f n

example {m} (w n x b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.advancedChildSentence w n x b f)) :=
  ObjectFormulaCodeTreeValidity.native_advancedChild w n x b f

example {m} (tag : Nat) (advance : Bool) (w n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.singleCaseSentence tag advance w n b f)) :=
  ObjectFormulaCodeTreeValidity.native_singleCase tag advance w n b f

example {m} (kind : Fin 4) (w n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.binaryCaseSentence kind w n b f)) :=
  ObjectFormulaCodeTreeValidity.native_binaryCase kind w n b f

example {m} (w n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.atContextSentence w n b f)) :=
  ObjectFormulaCodeTreeValidity.native_atContext w n b f

example {m} (w n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.propertySentence w n)) :=
  ObjectFormulaCodeTreeValidity.native_property w n

example {m} (w : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.progressiveSentence w)) :=
  ObjectFormulaCodeTreeValidity.native_progressive w

example {m} (w : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.allPropertiesSentence w)) :=
  ObjectFormulaCodeTreeValidity.native_allProperties w

example {m} (w n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.codeSentence w n b f)) :=
  ObjectFormulaCodeTreeValidity.native_code w n b f

example {m} (w n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.rejectNonTreeSentence w n b f)) :=
  ObjectFormulaCodeTreeValidity.native_rejectNonTree w n b f

example {m} (w n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.decodedTreeSentence w n b f)) :=
  ObjectFormulaCodeTreeValidity.native_decodedTree w n b f

example {m} (w n b f t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.treeChildrenSentence w n b f t p l g)) :=
  ObjectFormulaCodeTreeValidity.native_treeChildren w n b f t p l g

example {m} (w n b f t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.typedCasesSentence w n b f t p l g)) :=
  ObjectFormulaCodeTreeValidity.native_typedCases w n b f t p l g

example {m} (w n b f t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.typedDataSentence w n b f t p l g)) :=
  ObjectFormulaCodeTreeValidity.native_typedData w n b f t p l g

example {m} (w n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.typedFiberSentence w n b f)) :=
  ObjectFormulaCodeTreeValidity.native_typedFiber w n b f

example {m} (w n b f t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.rejectCasesSentence w n b f t p l g)) :=
  ObjectFormulaCodeTreeValidity.native_rejectCases w n b f t p l g

example {m} (w n b f t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.rejectDataSentence w n b f t p l g)) :=
  ObjectFormulaCodeTreeValidity.native_rejectData w n b f t p l g

example {m} (w n b f t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.dataTreeValidSentence w n b f t p l g)) :=
  ObjectFormulaCodeTreeValidity.native_dataTreeValid w n b f t p l g

example {m} (w n : Fin m) : FormulaCodeTreeValiditySyntax.property w n =
    Source.Formula.all (.all
      ((FormulaCodeSyntax.formulaCode w.castSucc.castSucc n.castSucc.castSucc
        (Fin.last m).castSucc (Fin.last (m+1))).imp
        (StructuralTreeValiditySyntax.valid w.castSucc.castSucc n.castSucc.castSucc))) := rfl

example {m} (w n b f : Fin m) : ObjectFormulaCodeTreeValidity.codeSentence w n b f =
    ((OmegaSyntax.omega w).imp ((FormulaCodeSyntax.formulaCode w n b f).imp
      (StructuralTreeValiditySyntax.valid w n))).close := rfl

example {m} (w n b f t p l g : Fin m) : FormulaCodeTypedDataSyntax.typedData w n b f t p l g =
    (StructuralTreeValiditySyntax.nodeData w n t p l g).conj
      ((SyntaxTermSyntax.contexts w b f).conj (FormulaCodeTypedDataSyntax.cases 11 w t l g b f)) := rfl

example {m} (w g b f : Fin m) : FormulaCodeTypedDataSyntax.rootCheck 9 w g b f =
    FormulaCodeGraphTyping.singleCheck true w g b f := rfl
example {m} (w g b f : Fin m) : FormulaCodeTypedDataSyntax.rootCheck 10 w g b f =
    FormulaCodeGraphTyping.singleCheck true w g b f := rfl

example {m} (w n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.singleCaseSentence 9 true w n b f)) :=
  ObjectFormulaCodeTreeValidity.native_singleCase 9 true w n b f

example {m} (w n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.singleCaseSentence 10 true w n b f)) :=
  ObjectFormulaCodeTreeValidity.native_singleCase 10 true w n b f

example {m} (w n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.binaryCaseSentence 0 w n b f)) :=
  ObjectFormulaCodeTreeValidity.native_binaryCase 0 w n b f

example {m} (w n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.binaryCaseSentence 1 w n b f)) :=
  ObjectFormulaCodeTreeValidity.native_binaryCase 1 w n b f

example {m} (w n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.binaryCaseSentence 2 w n b f)) :=
  ObjectFormulaCodeTreeValidity.native_binaryCase 2 w n b f

example {m} (w n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTreeValidity.binaryCaseSentence 3 w n b f)) :=
  ObjectFormulaCodeTreeValidity.native_binaryCase 3 w n b f

example {m} (j : Nat) (g y i : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.slotIndexSentence j g y i)) :=
  ObjectFormulaCodeTypedDecode.native_slotIndex j g y i

example {m} (j : Nat) (g w y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.slotNaturalSentence j g w y)) :=
  ObjectFormulaCodeTypedDecode.native_slotNatural j g w y

example {m} (k : Nat) (xs : Fin k → Fin m) (w p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.slotInputsSentence k xs w p l g)) :=
  ObjectFormulaCodeTypedDecode.native_slotInputs k xs w p l g

example {m} (k : Nat) (xs : Fin k → Fin m) (w p l g i y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.slotsFullSentence k xs w p l g i y)) :=
  ObjectFormulaCodeTypedDecode.native_slotsFull k xs w p l g i y

example {m} (k : Nat) (xs : Fin k → Fin m) (w p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.slotsAllSentence k xs w p l g)) :=
  ObjectFormulaCodeTypedDecode.native_slotsAll k xs w p l g

example {m} (k : Nat) (xs : Fin k → Fin m) (g h d e : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.graphEqualitySentence k xs g h d e)) :=
  ObjectFormulaCodeTypedDecode.native_graphEquality k xs g h d e

example {m} (w p l g h : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.fieldsGraphSubstSentence w p l g h)) :=
  ObjectFormulaCodeTypedDecode.native_fieldsGraphSubst w p l g h

example {m} (k : Nat) (xs : Fin k → Fin m) (w p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.forestRecoverSentence k xs w p l g)) :=
  ObjectFormulaCodeTypedDecode.native_forestRecover k xs w p l g

example {m} (k tag : Nat) (xs : Fin k → Fin m) (w n t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.constructorRecoverSentence k tag xs w n t p l g)) :=
  ObjectFormulaCodeTypedDecode.native_constructorRecover k tag xs w n t p l g

example {m} (tag : Nat) (xs : Fin (expectedArity tag) → Fin m) (w n b f t p l g : Fin m) (ht : tag < 11) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.knownTypesSentence tag xs w n b f t p l g)) :=
  ObjectFormulaCodeTypedDecode.native_knownTypes tag xs w n b f t p l g ht

example {m} (tag : Nat) (xs : Fin (expectedArity tag) → Fin m) (w n b f t p l g : Fin m) (ht : tag < 11) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.codeFromSlotsSentence tag xs w n b f t p l g)) :=
  ObjectFormulaCodeTypedDecode.native_codeFromSlots tag xs w n b f t p l g ht

example {m} (k tag : Nat) (j : Fin k) (w g b f : Fin m) (ht : tag < 11) (hk : k = expectedArity tag) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.rootSlotSentence k tag j w g b f)) :=
  ObjectFormulaCodeTypedDecode.native_rootSlot k tag j w g b f ht hk

example {m} (tag : Nat) (w n b f t p l g : Fin m) (ht : tag < 11) (hk : 0 = expectedArity tag) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.arity0Sentence tag w n b f t p l g)) :=
  ObjectFormulaCodeTypedDecode.native_arity0 tag w n b f t p l g ht hk

example {m} (tag : Nat) (w n b f t p l g : Fin m) (ht : tag < 11) (hk : 1 = expectedArity tag) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.arity1Sentence tag w n b f t p l g)) :=
  ObjectFormulaCodeTypedDecode.native_arity1 tag w n b f t p l g ht hk

example {m} (tag : Nat) (w n b f t p l g : Fin m) (ht : tag < 11) (hk : 2 = expectedArity tag) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.arity2Sentence tag w n b f t p l g)) :=
  ObjectFormulaCodeTypedDecode.native_arity2 tag w n b f t p l g ht hk

example {m} (tag : Nat) (w n b f t p l g : Fin m) (ht : tag < 11) (hk : 3 = expectedArity tag) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.arity3Sentence tag w n b f t p l g)) :=
  ObjectFormulaCodeTypedDecode.native_arity3 tag w n b f t p l g ht hk

example {m} (tag : Nat) (w n b f t p l g : Fin m) (ht : tag < 11) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.rootCheckSentence tag w n b f t p l g)) :=
  ObjectFormulaCodeTypedDecode.native_rootCheck tag w n b f t p l g ht

example {m} (w n b f t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.casesCodeSentence w n b f t p l g)) :=
  ObjectFormulaCodeTypedDecode.native_casesCode w n b f t p l g

example {m} (w n b f t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.dataCodeSentence w n b f t p l g)) :=
  ObjectFormulaCodeTypedDecode.native_dataCode w n b f t p l g

example {m} (w n b f t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.dataIffSentence w n b f t p l g)) :=
  ObjectFormulaCodeTypedDecode.native_dataIff w n b f t p l g

example {m} (w n b f t p l g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.casesIffSentence w n b f t p l g)) :=
  ObjectFormulaCodeTypedDecode.native_casesIff w n b f t p l g

example {m} (w n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.fiberCodeSentence w n b f)) :=
  ObjectFormulaCodeTypedDecode.native_fiberCode w n b f

example {m} (w n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.fiberIffSentence w n b f)) :=
  ObjectFormulaCodeTypedDecode.native_fiberIff w n b f

example {m} (w n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.rejectFiberIffSentence w n b f)) :=
  ObjectFormulaCodeTypedDecode.native_rejectFiberIff w n b f

example {m} (w n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectFormulaCodeTypedDecode.classificationSentence w n b f)) :=
  ObjectFormulaCodeTypedDecode.native_classification w n b f

example {m} (w n b f : Fin m) : ObjectFormulaCodeTypedDecode.fiberIffSentence w n b f =
    ((OmegaSyntax.omega w).imp
      ((FormulaCodeSyntax.formulaCode w n b f).iff (FormulaCodeTypedDataSyntax.typedFiber w n b f))).close := rfl

example {m} (w n b f t p l g : Fin m) : ObjectFormulaCodeTypedDecode.dataCodeSentence w n b f t p l g =
    ((OmegaSyntax.omega w).imp ((FormulaCodeTypedDataSyntax.typedData w n b f t p l g).imp
      (FormulaCodeSyntax.formulaCode w n b f))).close := rfl

example {m} (w r s a b c d : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.sourceContextsSentence w r s a b c d)) :=
  ObjectSyntaxRenameTerm.native_sourceContexts w r s a b c d

example {m} (w r s a b c d : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.targetContextsSentence w r s a b c d)) :=
  ObjectSyntaxRenameTerm.native_targetContexts w r s a b c d

example {m} (bound : Bool) (w r s a b c d : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.selectedMapSentence bound w r s a b c d)) :=
  ObjectSyntaxRenameTerm.native_selectedMap bound w r s a b c d

example {m} (w r a c i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.edgeSourceSentence w r a c i j)) :=
  ObjectSyntaxRenameTerm.native_edgeSource w r a c i j

example {m} (w r a c i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.edgeTargetSentence w r a c i j)) :=
  ObjectSyntaxRenameTerm.native_edgeTarget w r a c i j

example {m} (w r a c i : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.valueExistsSentence w r a c i)) :=
  ObjectSyntaxRenameTerm.native_valueExists w r a c i

example {m} (bound : Bool) (w r a n q i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.introBranchSentence bound w r a n q i j)) :=
  ObjectSyntaxRenameTerm.native_introBranch bound w r a n q i j

example {m} (bound : Bool) (w r a n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.sourceBranchSentence bound w r a n q)) :=
  ObjectSyntaxRenameTerm.native_sourceBranch bound w r a n q

example {m} (bound : Bool) (w r a c n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.targetBranchSentence bound w r a c n q)) :=
  ObjectSyntaxRenameTerm.native_targetBranch bound w r a c n q

example {m} (w r s a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.sourceTermSentence w r s a b c d n q)) :=
  ObjectSyntaxRenameTerm.native_sourceTerm w r s a b c d n q

example {m} (w r s a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.targetTermSentence w r s a b c d n q)) :=
  ObjectSyntaxRenameTerm.native_targetTerm w r s a b c d n q

example {m} (w r s a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.outputNaturalSentence w r s a b c d n q)) :=
  ObjectSyntaxRenameTerm.native_outputNatural w r s a b c d n q

example {m} (w r s a b n q v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.oppositeBranchesSentence w r s a b n q v)) :=
  ObjectSyntaxRenameTerm.native_oppositeBranches w r s a b n q v

example {m} (bound : Bool) (w r a n q v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.branchUniqueSentence bound w r a n q v)) :=
  ObjectSyntaxRenameTerm.native_branchUnique bound w r a n q v

example {m} (w r s a b c d n q v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.uniqueSentence w r s a b c d n q v)) :=
  ObjectSyntaxRenameTerm.native_unique w r s a b c d n q v

example {m} (bound : Bool) (w r a c n i : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.existsAtIndexSentence bound w r a c n i)) :=
  ObjectSyntaxRenameTerm.native_existsAtIndex bound w r a c n i

example {m} (bound : Bool) (w r a c n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.existsBranchSentence bound w r a c n)) :=
  ObjectSyntaxRenameTerm.native_existsBranch bound w r a c n

example {m} (w r s a b c d n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.existsTermSentence w r s a b c d n)) :=
  ObjectSyntaxRenameTerm.native_existsTerm w r s a b c d n

example {m} (w r s a b c d n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.fiberSentence w r s a b c d n)) :=
  ObjectSyntaxRenameTerm.native_fiber w r s a b c d n

example {m} (w r s a b c d n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.termOfExistsSentence w r s a b c d n)) :=
  ObjectSyntaxRenameTerm.native_termOfExists w r s a b c d n

example {m} (w r s a b c d n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.termOfFiberSentence w r s a b c d n)) :=
  ObjectSyntaxRenameTerm.native_termOfFiber w r s a b c d n

example {m} (w r s a b c d n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.existsIffSentence w r s a b c d n)) :=
  ObjectSyntaxRenameTerm.native_existsIff w r s a b c d n

example {m} (w r s a b c d n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.fiberIffSentence w r s a b c d n)) :=
  ObjectSyntaxRenameTerm.native_fiberIff w r s a b c d n

example {m} (bound : Bool) (w r a n q i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.knownBranchSentence bound w r a n q i j)) :=
  ObjectSyntaxRenameTerm.native_knownBranch bound w r a n q i j

example {m} (bound : Bool) (w r s a b c d n q i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.knownTermSentence bound w r s a b c d n q i j)) :=
  ObjectSyntaxRenameTerm.native_knownTerm bound w r s a b c d n q i j

example {m} (bound : Bool) (w r s a b c d n q i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.rejectEdgeSentence bound w r s a b c d n q i j)) :=
  ObjectSyntaxRenameTerm.native_rejectEdge bound w r s a b c d n q i j

example {m} (r i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.diagonalAtSentence r i j)) :=
  ObjectSyntaxRenameTerm.native_diagonalAt r i j

example {m} (bound : Bool) (w r a n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.branchIdentitySentence bound w r a n q)) :=
  ObjectSyntaxRenameTerm.native_branchIdentity bound w r a n q

example {m} (w r s a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.identitySentence w r s a b c d n q)) :=
  ObjectSyntaxRenameTerm.native_identity w r s a b c d n q

example {m} (w r s a b c d n q v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.outputSubstSentence w r s a b c d n q v)) :=
  ObjectSyntaxRenameTerm.native_outputSubst w r s a b c d n q v

example {m} (w r s a b c d n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.reflexiveSentence w r s a b c d n)) :=
  ObjectSyntaxRenameTerm.native_reflexive w r s a b c d n

example {m} (w r a c : Fin m) : SyntaxIndexMapSyntax.indexMap w r a c =
    (SyntaxTermSyntax.contexts w a c).conj (SequenceSyntax.sequence r a c) := rfl

example {m} (w r s a b c d n : Fin m) : ObjectSyntaxRenameTerm.fiberIffSentence w r s a b c d n =
    ((OmegaSyntax.omega w).imp ((SyntaxIndexMapSyntax.maps w r s a b c d).imp
      ((SyntaxTermSyntax.term w a b n).iff (SyntaxRenameTermSyntax.fiber w r s a b c d n)))).close := rfl

example {m} (w r s a b c d n q : Fin m) : SyntaxRenameTermSyntax.renamed w r s a b c d n q =
    (SyntaxIndexMapSyntax.maps w r s a b c d).conj
      ((SyntaxRenameTermSyntax.branch true w r a n q).disj (SyntaxRenameTermSyntax.branch false w s b n q)) := rfl

example {m} (w r s a b c d n q i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.knownTermSentence true w r s a b c d n q i j)) :=
  ObjectSyntaxRenameTerm.native_knownTerm true w r s a b c d n q i j
example {m} (w r s a b c d n q i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTerm.knownTermSentence false w r s a b c d n q i j)) :=
  ObjectSyntaxRenameTerm.native_knownTerm false w r s a b c d n q i j

example {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d x y z : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.relationUniqueSentence P ρ d x y z)) :=
  ObjectSyntaxIndexLift.native_relationUnique P ρ d x y z

example {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.pairTotalSentence P ρ d)) :=
  ObjectSyntaxIndexLift.native_pairTotal P ρ d

example {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.pairGraphSentence P ρ d)) :=
  ObjectSyntaxIndexLift.native_pairGraph P ρ d

example {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d g x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.pairEdgeSentence P ρ d g x y)) :=
  ObjectSyntaxIndexLift.native_pairEdge P ρ d g x y

example {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.pairCompleteSentence P ρ d g)) :=
  ObjectSyntaxIndexLift.native_pairComplete P ρ d g

example {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.graphExistsSentence P ρ d)) :=
  ObjectSyntaxIndexLift.native_graphExists P ρ d

example {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.graphFiberSentence P ρ d)) :=
  ObjectSyntaxIndexLift.native_graphFiber P ρ d

example {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d g h : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.graphUniqueSentence P ρ d g h)) :=
  ObjectSyntaxIndexLift.native_graphUnique P ρ d g h

example {n m} (P : Source.Formula (n+2)) (ρ : Fin n → Fin m) (d c g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.graphSequenceSentence P ρ d c g)) :=
  ObjectSyntaxIndexLift.native_graphSequence P ρ d c g

example {m} (w a u z : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.zeroMemberSentence w a u z)) :=
  ObjectSyntaxIndexLift.native_zeroMember w a u z

example {m} (w a b u v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.successorMemberSentence w a b u v)) :=
  ObjectSyntaxIndexLift.native_successorMember w a b u v

example {m} (w a u i k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.predecessorMemberSentence w a u i k)) :=
  ObjectSyntaxIndexLift.native_predecessorMember w a u i k

example {m} (w i k l : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.successorInjectiveSentence w i k l)) :=
  ObjectSyntaxIndexLift.native_successorInjective w i k l

example {m} (r a x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.zeroOutputSentence r a x y)) :=
  ObjectSyntaxIndexLift.native_zeroOutput r a x y

example {m} (w r a x y k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.successorOutputSentence w r a x y k)) :=
  ObjectSyntaxIndexLift.native_successorOutput w r a x y k

example {m} (w r a u x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.sourceMemberSentence w r a u x y)) :=
  ObjectSyntaxIndexLift.native_sourceMember w r a u x y

example {m} (w r a c v x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.targetMemberSentence w r a c v x y)) :=
  ObjectSyntaxIndexLift.native_targetMember w r a c v x y

example {m} (w r a c x y z : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.valueUniqueSentence w r a c x y z)) :=
  ObjectSyntaxIndexLift.native_valueUnique w r a c x y z

example {m} (ρ : Fin 2 → Fin m) (w c u x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.pointExistsSentence ρ w c u x)) :=
  ObjectSyntaxIndexLift.native_pointExists ρ w c u x

example {m} (ρ : Fin 2 → Fin m) (w c u x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.pointFiberSentence ρ w c u x)) :=
  ObjectSyntaxIndexLift.native_pointFiber ρ w c u x

example {m} (ρ : Fin 2 → Fin m) (w c u : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.liftTotalSentence ρ w c u)) :=
  ObjectSyntaxIndexLift.native_liftTotal ρ w c u

example {m} (ρ : Fin 2 → Fin m) (w c u v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.liftOutputsSentence ρ w c u v)) :=
  ObjectSyntaxIndexLift.native_liftOutputs ρ w c u v

example {m} (w r a c u v g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.targetMapSentence w r a c u v g)) :=
  ObjectSyntaxIndexLift.native_targetMap w r a c u v g

example {m} (w r a c u v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.liftExistsSentence w r a c u v)) :=
  ObjectSyntaxIndexLift.native_liftExists w r a c u v

example {m} (w r a c u v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.liftFiberSentence w r a c u v)) :=
  ObjectSyntaxIndexLift.native_liftFiber w r a c u v

example {m} (w r a c u v g h : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.liftUniqueSentence w r a c u v g h)) :=
  ObjectSyntaxIndexLift.native_liftUnique w r a c u v g h

example {m} (w r a c u v g i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.liftEdgeSentence w r a c u v g i j)) :=
  ObjectSyntaxIndexLift.native_liftEdge w r a c u v g i j

example {m} (w r a c u v g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.liftAllSentence w r a c u v g)) :=
  ObjectSyntaxIndexLift.native_liftAll w r a c u v g

example {m} (w r a c u v g z y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.liftZeroSentence w r a c u v g z y)) :=
  ObjectSyntaxIndexLift.native_liftZero w r a c u v g z y

example {m} (w r a c u v g i j k l : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.liftSuccessorSentence w r a c u v g i j k l)) :=
  ObjectSyntaxIndexLift.native_liftSuccessor w r a c u v g i j k l

example {m} (w r s a b c d u v g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.mapsLiftedSentence w r s a b c d u v g)) :=
  ObjectSyntaxIndexLift.native_mapsLifted w r s a b c d u v g

example {m} (w r s a b c d u v g z n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.newBoundFixedSentence w r s a b c d u v g z n)) :=
  ObjectSyntaxIndexLift.native_newBoundFixed w r s a b c d u v g z n

example {m} (w r s a b c d u v g i j k l n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.oldBoundShiftedSentence w r s a b c d u v g i j k l n q)) :=
  ObjectSyntaxIndexLift.native_oldBoundShifted w r s a b c d u v g i j k l n q

example {m} (w r s a b c d u v g i j n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.freePreservedSentence w r s a b c d u v g i j n q)) :=
  ObjectSyntaxIndexLift.native_freePreserved w r s a b c d u v g i j n q

example {m} (w r a c : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxIndexLift.liftSystemSentence w r a c)) :=
  ObjectSyntaxIndexLift.native_liftSystem w r a c

example {m} (w r a c u v g : Fin m) : SyntaxIndexLiftSyntax.lifted w r a c u v g =
    (SyntaxIndexMapSyntax.indexMap w r a c).conj ((OmegaSyntax.successor u a).conj
      ((OmegaSyntax.successor v c).conj ((SyntaxIndexMapSyntax.indexMap w g u v).conj
        (RelationGraphSyntax.edgeLaw SyntaxIndexLiftSyntax.matrix (Source.SetLanguage.args2 r a) u g)))) := rfl

example {m} (r a i j : Fin m) : SyntaxIndexLiftSyntax.value r a i j =
    ((OmegaSyntax.empty i).conj (OmegaSyntax.empty j)).disj (SyntaxIndexLiftSyntax.shifted r a i j) := rfl

example {m} (w r a c : Fin m) : ObjectSyntaxIndexLift.liftSystemSentence w r a c =
    ((OmegaSyntax.omega w).imp ((SyntaxIndexMapSyntax.indexMap w r a c).imp
      (SyntaxIndexLiftSystem.system w r a c))).close := rfl

example {m} (w r a c : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.omegaSequenceSentence w r a c)) :=
  ObjectSyntaxMapCodeState.native_omegaSequence w r a c

example {m} (w r a c k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.codeNaturalSentence w r a c k)) :=
  ObjectSyntaxMapCodeState.native_codeNatural w r a c k

example {m} (w r a c k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.codeValidSentence w r a c k)) :=
  ObjectSyntaxMapCodeState.native_codeValid w r a c k

example {m} (w r a c k l : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.uniqueCodeSentence w r a c k l)) :=
  ObjectSyntaxMapCodeState.native_uniqueCode w r a c k l

example {m} (w r s a c k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.uniqueGraphSentence w r s a c k)) :=
  ObjectSyntaxMapCodeState.native_uniqueGraph w r s a c k

example {m} (w r s a b c d k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.sourceGraphRecoverySentence w r s a b c d k)) :=
  ObjectSyntaxMapCodeState.native_sourceGraphRecovery w r s a b c d k

example {m} (w r a c : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.existsMapCodeSentence w r a c)) :=
  ObjectSyntaxMapCodeState.native_existsMapCode w r a c

example {m} (w r a c : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.codeFiberSentence w r a c)) :=
  ObjectSyntaxMapCodeState.native_codeFiber w r a c

example {m} (w a c k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.mapNaturalSentence w a c k)) :=
  ObjectSyntaxMapCodeState.native_mapNatural w a c k

example {m} (w a c k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.mapContextsSentence w a c k)) :=
  ObjectSyntaxMapCodeState.native_mapContexts w a c k

example {m} (w a c k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.mapValidSentence w a c k)) :=
  ObjectSyntaxMapCodeState.native_mapValid w a c k

example {m} (w a c k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.graphFiberSentence w a c k)) :=
  ObjectSyntaxMapCodeState.native_graphFiber w a c k

example {m} (w a c k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.mapFiberIffSentence w a c k)) :=
  ObjectSyntaxMapCodeState.native_mapFiberIff w a c k

example {m} (w r a c k u v l : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.liftAtSourceSentence w r a c k u v l)) :=
  ObjectSyntaxMapCodeState.native_liftAtSource w r a c k u v l

example {m} (w r a c k u v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.liftExistsAtSourceSentence w r a c k u v)) :=
  ObjectSyntaxMapCodeState.native_liftExistsAtSource w r a c k u v

example {m} (w a c k u v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.liftExistsSentence w a c k u v)) :=
  ObjectSyntaxMapCodeState.native_liftExists w a c k u v

example {m} (w r a c k u v l q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.liftUniqueAtSourceSentence w r a c k u v l q)) :=
  ObjectSyntaxMapCodeState.native_liftUniqueAtSource w r a c k u v l q

example {m} (w a c k u v l : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.liftInputCodeSentence w a c k u v l)) :=
  ObjectSyntaxMapCodeState.native_liftInputCode w a c k u v l

example {m} (w a c k u v l : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.liftOutputCodeSentence w a c k u v l)) :=
  ObjectSyntaxMapCodeState.native_liftOutputCode w a c k u v l

example {m} (w a c k u v l : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.liftOutputNaturalSentence w a c k u v l)) :=
  ObjectSyntaxMapCodeState.native_liftOutputNatural w a c k u v l

example {m} (w a c k u v l q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.liftCodeUniqueSentence w a c k u v l q)) :=
  ObjectSyntaxMapCodeState.native_liftCodeUnique w a c k u v l q

example {m} (w a c k u v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.liftCodeFiberSentence w a c k u v)) :=
  ObjectSyntaxMapCodeState.native_liftCodeFiber w a c k u v

example {m} (w r s a b c d q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.stateInputsSentence w r s a b c d q)) :=
  ObjectSyntaxMapCodeState.native_stateInputs w r s a b c d q

example {m} (w r s a b c d q h : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.cellNaturalSentence w r s a b c d q h)) :=
  ObjectSyntaxMapCodeState.native_cellNatural w r s a b c d q h

example {m} (w r s a b c d q h : Fin m) (j : Fin 7) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.fieldNaturalSentence w r s a b c d q h j)) :=
  ObjectSyntaxMapCodeState.native_fieldNatural w r s a b c d q h j

example {m} (w h r s a b c d q r1 s1 a1 b1 c1 d1 q1 : Fin m) (j : Fin 7) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.sameFieldSentence w h r s a b c d q r1 s1 a1 b1 c1 d1 q1 j)) :=
  ObjectSyntaxMapCodeState.native_sameField w h r s a b c d q r1 s1 a1 b1 c1 d1 q1 j

example {m} (w h r s a b c d q r1 s1 a1 b1 c1 d1 q1 : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.sameFieldsSentence w h r s a b c d q r1 s1 a1 b1 c1 d1 q1)) :=
  ObjectSyntaxMapCodeState.native_sameFields w h r s a b c d q r1 s1 a1 b1 c1 d1 q1

example {m} (w r s a b c d q h t : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.uniqueCellSentence w r s a b c d q h t)) :=
  ObjectSyntaxMapCodeState.native_uniqueCell w r s a b c d q h t

example {m} (w r s a b c d q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.stateFiberSentence w r s a b c d q)) :=
  ObjectSyntaxMapCodeState.native_stateFiber w r s a b c d q

example {m} (w h r s a b c d q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.uniqueParamsSentence w h r s a b c d q)) :=
  ObjectSyntaxMapCodeState.native_uniqueParams w h r s a b c d q

example {m} (w h : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.actualDecodeSentence w h)) :=
  ObjectSyntaxMapCodeState.native_actualDecode w h

example {m} (w h : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.recognizedNaturalSentence w h)) :=
  ObjectSyntaxMapCodeState.native_recognizedNatural w h

example {m} (w h : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.stateDecodeIffSentence w h)) :=
  ObjectSyntaxMapCodeState.native_stateDecodeIff w h

example {m} (w r s a b c d q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.actualStateSystemSentence w r s a b c d q)) :=
  ObjectSyntaxMapCodeState.native_actualStateSystem w r s a b c d q

example {m} (w h r s a b c d q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxMapCodeState.introStateRecognitionSentence w h r s a b c d q)) :=
  ObjectSyntaxMapCodeState.native_introStateRecognition w h r s a b c d q

example {m} (w r a c k : Fin m) : SyntaxMapCodeSyntax.encoded w r a c k =
    (StructuralListEncodeSyntax.encoding w r a k).conj (SyntaxIndexMapSyntax.indexMap w r a c) := rfl

example {m} (w r s a b c d q h : Fin m) : SyntaxRenameStateSyntax.state w r s a b c d q h =
    (SyntaxRenameStateSyntax.cell w r s a b c d q h).conj
      ((SyntaxMapCodeSyntax.mapCode w a c r).conj ((SyntaxMapCodeSyntax.mapCode w b d s).conj
        (FormulaCodeSyntax.formulaCode w q c d))) := rfl

example {m} (w r s a b c d q : Fin m) : ObjectSyntaxMapCodeState.stateFiberSentence w r s a b c d q =
    ((OmegaSyntax.omega w).imp ((SyntaxRenameStateSyntax.legal w r s a b c d q).imp
      (SyntaxRenameStateSyntax.stateFiber w r s a b c d q))).close := rfl

example {m} (w v r s a b c d q t : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.containsAtStateSentence w v r s a b c d q t)) :=
  ObjectSyntaxRenameOperator.native_containsAtState w v r s a b c d q t

example {m} (w h D x v r s a b c d q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.queryAtValueSentence w h D x v r s a b c d q)) :=
  ObjectSyntaxRenameOperator.native_queryAtValue w h D x v r s a b c d q

example {m} (w h D x v r s a b c d q t : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.queryAtStateSentence w h D x v r s a b c d q t)) :=
  ObjectSyntaxRenameOperator.native_queryAtState w h D x v r s a b c d q t

example {m} (w h x r s a b c d q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.advancedFreeMapSentence w h x r s a b c d q)) :=
  ObjectSyntaxRenameOperator.native_advancedFreeMap w h x r s a b c d q

example {m} (w h x r s a b c d q u v l : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.advancedIntroSentence w h x r s a b c d q u v l)) :=
  ObjectSyntaxRenameOperator.native_advancedIntro w h x r s a b c d q u v l

example {m} (truth : Bool) (w R S r s a b c d h n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.nullaryCaseSentence truth w R S r s a b c d h n q)) :=
  ObjectSyntaxRenameOperator.native_nullaryCase truth w R S r s a b c d h n q

example {m} (w R S r s a b c d h n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.membershipCaseSentence w R S r s a b c d h n q)) :=
  ObjectSyntaxRenameOperator.native_membershipCase w R S r s a b c d h n q

example {m} (w R S r s a b c d h n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.equalityCaseSentence w R S r s a b c d h n q)) :=
  ObjectSyntaxRenameOperator.native_equalityCase w R S r s a b c d h n q

example {m} (w R S r s a b c d h n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.negationCaseSentence w R S r s a b c d h n q)) :=
  ObjectSyntaxRenameOperator.native_negationCase w R S r s a b c d h n q

example {m} (kind : Fin 4) (w R S r s a b c d h n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.binaryCaseSentence kind w R S r s a b c d h n q)) :=
  ObjectSyntaxRenameOperator.native_binaryCase kind w R S r s a b c d h n q

example {m} (universal : Bool) (w R S r s a b c d h n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.quantifierCaseSentence universal w R S r s a b c d h n q)) :=
  ObjectSyntaxRenameOperator.native_quantifierCase universal w R S r s a b c d h n q

example {m} (w R S r s a b c d h n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.localGraphsSentence w R S r s a b c d h n q)) :=
  ObjectSyntaxRenameOperator.native_localGraphs w R S r s a b c d h n q

example {m} (w n h p R S a b c d q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.rowIntroSentence w n h p R S a b c d q)) :=
  ObjectSyntaxRenameOperator.native_rowIntro w n h p R S a b c d q

example {m} (w n h p R S a b c d q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.rowAtStateSentence w n h p R S a b c d q)) :=
  ObjectSyntaxRenameOperator.native_rowAtState w n h p R S a b c d q

example {m} (w n h p : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.rowRecognizedSentence w n h p)) :=
  ObjectSyntaxRenameOperator.native_rowRecognized w n h p

example {m} (w n h p : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.rowSourceNaturalSentence w n h p)) :=
  ObjectSyntaxRenameOperator.native_rowSourceNatural w n h p

example {m} (w n h v p : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.valueMemberSentence w n h v p)) :=
  ObjectSyntaxRenameOperator.native_valueMember w n h v p

example {m} (w n h : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.valueExistsSentence w n h)) :=
  ObjectSyntaxRenameOperator.native_valueExists w n h

example {m} (w n h v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.valueSubsetSentence w n h v)) :=
  ObjectSyntaxRenameOperator.native_valueSubset w n h v

example {m} (w u n h v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.valueUniverseSentence w u n h v)) :=
  ObjectSyntaxRenameOperator.native_valueUniverse w u n h v

example {m} (w n h v t : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.valueUniqueSentence w n h v t)) :=
  ObjectSyntaxRenameOperator.native_valueUnique w n h v t

example {m} (w n h : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.valueFiberSentence w n h)) :=
  ObjectSyntaxRenameOperator.native_valueFiber w n h

example {m} (w n h v p : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.memberRecognizedSentence w n h v p)) :=
  ObjectSyntaxRenameOperator.native_memberRecognized w n h v p

example {m} (w n h v p R S a b c d q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.valueAtStateSentence w n h v p R S a b c d q)) :=
  ObjectSyntaxRenameOperator.native_valueAtState w n h v p R S a b c d q

example {m} (w n h v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.offNaturalSentence w n h v)) :=
  ObjectSyntaxRenameOperator.native_offNatural w n h v

example {m} (w : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.operatorTotalSentence w)) :=
  ObjectSyntaxRenameOperator.native_operatorTotal w

example {m} (w : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.operatorDeterministicSentence w)) :=
  ObjectSyntaxRenameOperator.native_operatorDeterministic w

example {m} (w : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.recursorsSentence w)) :=
  ObjectSyntaxRenameOperator.native_recursors w

example {m} (w d : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.graphFiberSentence w d)) :=
  ObjectSyntaxRenameOperator.native_graphFiber w d

example {m} (w : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.carrierRecursorsSentence w)) :=
  ObjectSyntaxRenameOperator.native_carrierRecursors w

example {m} (w n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.evaluationExistsSentence w n)) :=
  ObjectSyntaxRenameOperator.native_evaluationExists w n

example {m} (w n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.naturalEvaluationExistsSentence w n)) :=
  ObjectSyntaxRenameOperator.native_naturalEvaluationExists w n

example {m} (w n y u : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.evaluationUniqueSentence w n y u)) :=
  ObjectSyntaxRenameOperator.native_evaluationUnique w n y u

example {m} (w n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.evaluationFiberSentence w n)) :=
  ObjectSyntaxRenameOperator.native_evaluationFiber w n

example {m} (w n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.naturalEvaluationFiberSentence w n)) :=
  ObjectSyntaxRenameOperator.native_naturalEvaluationFiber w n

example {m} (w f g d t : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.graphAgreementSentence w f g d t)) :=
  ObjectSyntaxRenameOperator.native_graphAgreement w f g d t

example {m} (w f d n y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.graphEdgeValueSentence w f d n y)) :=
  ObjectSyntaxRenameOperator.native_graphEdgeValue w f d n y

example {m} (w n y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.prefixSentence w n y)) :=
  ObjectSyntaxRenameOperator.native_prefix w n y

example {m} (w n y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.evaluationSubsetSentence w n y)) :=
  ObjectSyntaxRenameOperator.native_evaluationSubset w n y

example {m} (w u n y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.evaluationUniverseSentence w u n y)) :=
  ObjectSyntaxRenameOperator.native_evaluationUniverse w u n y

example {m} (w n y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOperator.evaluationOffNaturalSentence w n y)) :=
  ObjectSyntaxRenameOperator.native_evaluationOffNatural w n y

example : FirstOrder.Derives nativeZF []
    (Translation.sentence ObjectSyntaxRenameOperator.existenceSentence) := ObjectSyntaxRenameOperator.native_existence

example {m} (w n h v : Fin m) : SyntaxRenameOperatorSyntax.value w n h v =
    MinimalPredicates.separated SyntaxRenameOperatorSyntax.selectionMatrix (SyntaxAtomSyntax.three w n h) w v := rfl

example {m} (w r s a b c d n q z x y X Y : Fin m) :
    SyntaxRenameAtomSyntax.membershipData w r s a b c d n q z x y X Y =
      (SyntaxAtomSyntax.zeroScalar w z).conj ((SyntaxAtomSyntax.memberCode w z x y n).conj
        ((SyntaxAtomSyntax.memberCode w z X Y q).conj ((SyntaxRenameTermSyntax.renamed w r s a b c d x X).conj
          (SyntaxRenameTermSyntax.renamed w r s a b c d y Y)))) := rfl

example {m} (w h r s a b c d n q x X : Fin m) (universal : Bool) :
    SyntaxRenameLogicalSyntax.singleData (SyntaxLogicalSyntax.quantifierTag universal) true w h r s a b c d n q x X =
      (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n).conj
        ((Formula.mem x n).conj ((SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q).conj
          (SyntaxRenameQuerySyntax.advanced w h x r s a b c d X))) := rfl

example {m} (w r s a b c d n q v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameRecursive.introSentence w r s a b c d n q v)) := ObjectSyntaxRenameRecursive.native_intro w r s a b c d n q v

example {m} (w r s a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameRecursive.rejectCodeSentence w r s a b c d n q)) := ObjectSyntaxRenameRecursive.native_rejectCode w r s a b c d n q

example {m} (w r s a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameRecursive.legalSentence w r s a b c d n q)) := ObjectSyntaxRenameRecursive.native_legal w r s a b c d n q

example {m} (w r s a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameRecursive.targetTypeSentence w r s a b c d n q)) := ObjectSyntaxRenameRecursive.native_targetType w r s a b c d n q

example {m} (w n h v r s a b c d q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameRecursive.containsCriterionSentence w n h v r s a b c d q)) := ObjectSyntaxRenameRecursive.native_containsCriterion w n h v r s a b c d q

example {m} (w r s a b c d n q v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameRecursive.atValueSentence w r s a b c d n q v)) := ObjectSyntaxRenameRecursive.native_atValue w r s a b c d n q v

example {m} (w h D x r s a b c d q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameRecursive.readSentence w h D x r s a b c d q)) := ObjectSyntaxRenameRecursive.native_read w h D x r s a b c d q

example {m} (w h D x r s a b c d q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameRecursive.advancedSentence w h D x r s a b c d q)) := ObjectSyntaxRenameRecursive.native_advanced w h D x r s a b c d q

example {m} (advance : Bool) (w h D x r s a b c d q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameRecursive.checkSentence advance w h D x r s a b c d q)) := ObjectSyntaxRenameRecursive.native_check advance w h D x r s a b c d q

example {m} (tag : Nat) (advance : Bool) (w h r s a b c d n q x X : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameRecursive.singleFieldsSentence tag advance w h r s a b c d n q x X)) := ObjectSyntaxRenameRecursive.native_singleFields tag advance w h r s a b c d n q x X

example {m} (tag : Nat) (advance : Bool) (w h r s a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameRecursive.singleCaseSentence tag advance w h r s a b c d n q)) := ObjectSyntaxRenameRecursive.native_singleCase tag advance w h r s a b c d n q

example {m} (kind : Fin 4) (w h r s a b c d n q x y X Y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameRecursive.binaryFieldsSentence kind w h r s a b c d n q x y X Y)) := ObjectSyntaxRenameRecursive.native_binaryFields kind w h r s a b c d n q x y X Y

example {m} (kind : Fin 4) (w h r s a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameRecursive.binaryCaseSentence kind w h r s a b c d n q)) := ObjectSyntaxRenameRecursive.native_binaryCase kind w h r s a b c d n q

example {m} (w R S r s a b c d h n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameRecursive.allCasesSentence w R S r s a b c d h n q)) := ObjectSyntaxRenameRecursive.native_allCases w R S r s a b c d h n q

example {m} (w R S a b c d h n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameRecursive.localSentence w R S a b c d h n q)) := ObjectSyntaxRenameRecursive.native_local w R S a b c d h n q

example {m} (w r s a b c d n q v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameRecursive.recursiveAtValueSentence w r s a b c d n q v)) := ObjectSyntaxRenameRecursive.native_recursiveAtValue w r s a b c d n q v

example {m} (w r s a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameRecursive.recursiveSentence w r s a b c d n q)) := ObjectSyntaxRenameRecursive.native_recursive w r s a b c d n q

example {m} (w r s a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameRecursive.sourceTypeSentence w r s a b c d n q)) := ObjectSyntaxRenameRecursive.native_sourceType w r s a b c d n q

example {m} (w : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameRecursive.universalSentence w)) := ObjectSyntaxRenameRecursive.native_universal w

example {m} (w : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameRecursive.actualSystemSentence w)) := ObjectSyntaxRenameRecursive.native_actualSystem w

example : FirstOrder.Derives nativeZF []
    (Translation.sentence ObjectSyntaxRenameRecursive.existenceSentence) := ObjectSyntaxRenameRecursive.native_existence

example {m} (w r s a b c d n q : Fin m) : SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q =
    (Formula.mem n w).conj (.ex (SyntaxRenameJudgmentSyntax.body w r s a b c d n q)) := rfl

example {m} (w x r s a b c d q : Fin m) : SyntaxRenameRecursiveSyntax.check false w x r s a b c d q =
    SyntaxRenameJudgmentSyntax.renamed w r s a b c d x q := rfl

example {m} (w r s a b c d n q x y X Y : Fin m) (kind : Fin 4) :
    SyntaxRenameRecursiveSyntax.binaryData kind w r s a b c d n q x y X Y =
      (SyntaxLogicalSyntax.binaryCode kind w x y n).conj ((Formula.mem x n).conj ((Formula.mem y n).conj
        ((SyntaxLogicalSyntax.binaryCode kind w X Y q).conj
          ((SyntaxRenameJudgmentSyntax.renamed w r s a b c d x X).conj (SyntaxRenameJudgmentSyntax.renamed w r s a b c d y Y))))) := rfl

example {m} (w a c k u v l : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOutput.liftSuccessorsSentence w a c k u v l)) := ObjectSyntaxRenameOutput.native_liftSuccessors w a c k u v l

example {m} (w a c k u v l U V L : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOutput.liftParametersSentence w a c k u v l U V L)) := ObjectSyntaxRenameOutput.native_liftParameters w a c k u v l U V L

example {m} (w x r s a b c d q u v l : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOutput.advancedAtLiftSentence w x r s a b c d q u v l)) := ObjectSyntaxRenameOutput.native_advancedAtLift w x r s a b c d q u v l

example {m} (w r s a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOutput.renamedInputSentence w r s a b c d n q)) := ObjectSyntaxRenameOutput.native_renamedInput w r s a b c d n q

example {m} (w r s a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOutput.renamedNaturalSentence w r s a b c d n q)) := ObjectSyntaxRenameOutput.native_renamedNatural w r s a b c d n q

example {m} (w r s a b c d n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOutput.inputNaturalSentence w r s a b c d n)) := ObjectSyntaxRenameOutput.native_inputNatural w r s a b c d n

example {m} (w r s a b c d n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOutput.existsFromFiberSentence w r s a b c d n)) := ObjectSyntaxRenameOutput.native_existsFromFiber w r s a b c d n

example {m} (w r s a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOutput.existsFromRenamedSentence w r s a b c d n q)) := ObjectSyntaxRenameOutput.native_existsFromRenamed w r s a b c d n q

example {m} (w r s a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOutput.fiberIntroSentence w r s a b c d n q)) := ObjectSyntaxRenameOutput.native_fiberIntro w r s a b c d n q

example {m} (w n r s a b c d : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOutput.propertyAtSentence w n r s a b c d)) := ObjectSyntaxRenameOutput.native_propertyAt w n r s a b c d

example {m} (w n x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOutput.earlierAtSentence w n x)) := ObjectSyntaxRenameOutput.native_earlierAt w n x

example {m} (kind : Fin 4) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOutput.atomicFilterSentence kind arity w R S r s a b c d n q xs)) := ObjectSyntaxRenameOutput.native_atomicFilter kind arity w R S r s a b c d n q xs

example {m} (truth : Bool) (w r s a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOutput.nullaryLocalSentence truth w r s a b c d n q)) := ObjectSyntaxRenameOutput.native_nullaryLocal truth w r s a b c d n q

example {m} (truth : Bool) (w r s a b c d n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOutput.nullarySelfSentence truth w r s a b c d n)) := ObjectSyntaxRenameOutput.native_nullarySelf truth w r s a b c d n

example {m} (truth : Bool) (w r s a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOutput.nullaryUniqueSentence truth w r s a b c d n q)) := ObjectSyntaxRenameOutput.native_nullaryUnique truth w r s a b c d n q

example {m} (truth : Bool) (w r s a b c d n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOutput.nullaryFiberSentence truth w r s a b c d n)) := ObjectSyntaxRenameOutput.native_nullaryFiber truth w r s a b c d n

example {m} (truth : Bool) (w n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameOutput.nullaryAllParametersSentence truth w n)) := ObjectSyntaxRenameOutput.native_nullaryAllParameters truth w n

example {m} (w r s a b c d n : Fin m) : SyntaxRenameOutputSyntax.input w r s a b c d n =
    (FormulaCodeSyntax.formulaCode w n a b).conj
      ((SyntaxMapCodeSyntax.mapCode w a c r).conj (SyntaxMapCodeSyntax.mapCode w b d s)) := rfl

example {m} (w r s a b c d n q : Fin m) : SyntaxRenameOutputSyntax.uniqueOutput w r s a b c d n q = .all
    ((SyntaxRenameJudgmentSyntax.renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)).imp
      (.equal (Fin.last m) q.castSucc)) := rfl

example {m} (w r s a b c d n : Fin m) : SyntaxRenameOutputSyntax.fiber w r s a b c d n = .ex
    ((SyntaxRenameJudgmentSyntax.renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)).conj
      (SyntaxRenameOutputSyntax.uniqueOutput w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m))) := rfl

example {m} (w n : Fin m) : SyntaxRenameOutputSyntax.earlier w n = .all
    (((Formula.mem (Fin.last m) w.castSucc).conj (.mem (Fin.last m) n.castSucc)).imp
      (SyntaxRenameOutputSyntax.property w.castSucc (Fin.last m))) := rfl

example {m} (w R S r s a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.graphCasesSentence w R S r s a b c d n q)) := ObjectSyntaxRenameAtomic.native_graphCases w R S r s a b c d n q

example {m} (w R S r s a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.casesFromJudgmentSentence w R S r s a b c d n q)) := ObjectSyntaxRenameAtomic.native_casesFromJudgment w R S r s a b c d n q

example {m} (kind : Fin 4) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.atomicFromJudgmentSentence kind arity w R S r s a b c d n q xs)) := ObjectSyntaxRenameAtomic.native_atomicFromJudgment kind arity w R S r s a b c d n q xs

example {m} (w R S r s a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.introFromCasesSentence w R S r s a b c d n q)) := ObjectSyntaxRenameAtomic.native_introFromCases w R S r s a b c d n q

example {m} (w r s a b c d n q v x y X Y u z U V : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.equalDataUniqueSentence w r s a b c d n q v x y X Y u z U V)) := ObjectSyntaxRenameAtomic.native_equalDataUnique w r s a b c d n q v x y X Y u z U V

example {m} (w r s a b c d n q v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.equalRelationUniqueSentence w r s a b c d n q v)) := ObjectSyntaxRenameAtomic.native_equalRelationUnique w r s a b c d n q v

example {m} (w R S r s a b c d n x y X Y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.equalAtOutputsSentence w R S r s a b c d n x y X Y)) := ObjectSyntaxRenameAtomic.native_equalAtOutputs w R S r s a b c d n x y X Y

example {m} (w R S r s a b c d n x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.equalExistsAtGraphsSentence w R S r s a b c d n x y)) := ObjectSyntaxRenameAtomic.native_equalExistsAtGraphs w R S r s a b c d n x y

example {m} (w R S r s a b c d n q v x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.equalUniqueAtGraphsSentence w R S r s a b c d n q v x y)) := ObjectSyntaxRenameAtomic.native_equalUniqueAtGraphs w R S r s a b c d n q v x y

example {m} (w R S r s a b c d n x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.equalFiberAtGraphsSentence w R S r s a b c d n x y)) := ObjectSyntaxRenameAtomic.native_equalFiberAtGraphs w R S r s a b c d n x y

example {m} (w R S a b c d n x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.equalFiberSentence w R S a b c d n x y)) := ObjectSyntaxRenameAtomic.native_equalFiber w R S a b c d n x y

example {m} (w n x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.equalAllParametersSentence w n x y)) := ObjectSyntaxRenameAtomic.native_equalAllParameters w n x y

example {m} (w a b n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.equalBasePropertySentence w a b n)) := ObjectSyntaxRenameAtomic.native_equalBaseProperty w a b n

example {m} (w r s a b c d n q v z x y X Y j u t U V : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.memberDataUniqueSentence w r s a b c d n q v z x y X Y j u t U V)) := ObjectSyntaxRenameAtomic.native_memberDataUnique w r s a b c d n q v z x y X Y j u t U V

example {m} (w r s a b c d n q v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.memberRelationUniqueSentence w r s a b c d n q v)) := ObjectSyntaxRenameAtomic.native_memberRelationUnique w r s a b c d n q v

example {m} (w R S r s a b c d n z x y X Y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.memberAtOutputsSentence w R S r s a b c d n z x y X Y)) := ObjectSyntaxRenameAtomic.native_memberAtOutputs w R S r s a b c d n z x y X Y

example {m} (w R S r s a b c d n z x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.memberExistsAtGraphsSentence w R S r s a b c d n z x y)) := ObjectSyntaxRenameAtomic.native_memberExistsAtGraphs w R S r s a b c d n z x y

example {m} (w R S r s a b c d n q v z x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.memberUniqueAtGraphsSentence w R S r s a b c d n q v z x y)) := ObjectSyntaxRenameAtomic.native_memberUniqueAtGraphs w R S r s a b c d n q v z x y

example {m} (w R S r s a b c d n z x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.memberFiberAtGraphsSentence w R S r s a b c d n z x y)) := ObjectSyntaxRenameAtomic.native_memberFiberAtGraphs w R S r s a b c d n z x y

example {m} (w R S a b c d n z x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.memberFiberSentence w R S a b c d n z x y)) := ObjectSyntaxRenameAtomic.native_memberFiber w R S a b c d n z x y

example {m} (w n z x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.memberAllParametersSentence w n z x y)) := ObjectSyntaxRenameAtomic.native_memberAllParameters w n z x y

example {m} (w a b n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.memberBasePropertySentence w a b n)) := ObjectSyntaxRenameAtomic.native_memberBaseProperty w a b n

example {m} (w a b n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.atomicPropertySentence w a b n)) := ObjectSyntaxRenameAtomic.native_atomicProperty w a b n

example {m} (w R S a b c d n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.atomicFiberSentence w R S a b c d n)) := ObjectSyntaxRenameAtomic.native_atomicFiber w R S a b c d n

example {m} (w R S a b c d n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameAtomic.atomicExistsSentence w R S a b c d n)) := ObjectSyntaxRenameAtomic.native_atomicExists w R S a b c d n

example {m} (w r s a b c d n q z x y X Y : Fin m) :
    SyntaxRenameAtomSyntax.membershipData w r s a b c d n q z x y X Y =
      (SyntaxAtomSyntax.zeroScalar w z).conj
        ((SyntaxAtomSyntax.memberCode w z x y n).conj
          ((SyntaxAtomSyntax.memberCode w z X Y q).conj
            ((SyntaxRenameTermSyntax.renamed w r s a b c d x X).conj
              (SyntaxRenameTermSyntax.renamed w r s a b c d y Y)))) := rfl

example {m} (w r s a b c d n q x y X Y : Fin m) :
    SyntaxRenameAtomSyntax.equalityData w r s a b c d n q x y X Y =
      (SyntaxAtomSyntax.equalCode w x y n).conj
        ((SyntaxAtomSyntax.equalCode w X Y q).conj
          ((SyntaxRenameTermSyntax.renamed w r s a b c d x X).conj
            (SyntaxRenameTermSyntax.renamed w r s a b c d y Y))) := rfl

example {m} (kind : Fin 11) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.tagFilterSentence kind arity w R S r s a b c d n q xs)) := ObjectSyntaxRenameTotal.native_tagFilter kind arity w R S r s a b c d n q xs

example {m} (kind : Fin 11) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.tagJudgmentSentence kind arity w R S r s a b c d n q xs)) := ObjectSyntaxRenameTotal.native_tagJudgment kind arity w R S r s a b c d n q xs

example {m} (w R S a b c d n q v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.fiberUniqueSentence w R S a b c d n q v)) := ObjectSyntaxRenameTotal.native_fiberUnique w R S a b c d n q v

example {m} (w R S a b c d n q v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.propertyUniqueSentence w R S a b c d n q v)) := ObjectSyntaxRenameTotal.native_propertyUnique w R S a b c d n q v

example {m} (advance : Bool) (w x R S a b c d q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.checkTargetSentence advance w x R S a b c d q)) := ObjectSyntaxRenameTotal.native_checkTarget advance w x R S a b c d q

example {m} (advance : Bool) (w x R S a b c d q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.checkNaturalSentence advance w x R S a b c d q)) := ObjectSyntaxRenameTotal.native_checkNatural advance w x R S a b c d q

example {m} (advance : Bool) (w x R S a b c d q v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.checkUniqueSentence advance w x R S a b c d q v)) := ObjectSyntaxRenameTotal.native_checkUnique advance w x R S a b c d q v

example {m} (advance : Bool) (w x R S a b c d : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.checkExistsSentence advance w x R S a b c d)) := ObjectSyntaxRenameTotal.native_checkExists advance w x R S a b c d

example {m} (tag : Nat) (advance : Bool) (w R S a b c d n q v x X u U : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.singleDataUniqueSentence tag advance w R S a b c d n q v x X u U)) := ObjectSyntaxRenameTotal.native_singleDataUnique tag advance w R S a b c d n q v x X u U

example {m} (tag : Nat) (advance : Bool) (w R S a b c d n q v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.singleRelationUniqueSentence tag advance w R S a b c d n q v)) := ObjectSyntaxRenameTotal.native_singleRelationUnique tag advance w R S a b c d n q v

example {m} (kind : Fin 4) (w R S a b c d n q v x y X Y u t U V : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.binaryDataUniqueSentence kind w R S a b c d n q v x y X Y u t U V)) := ObjectSyntaxRenameTotal.native_binaryDataUnique kind w R S a b c d n q v x y X Y u t U V

example {m} (kind : Fin 4) (w R S a b c d n q v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.binaryRelationUniqueSentence kind w R S a b c d n q v)) := ObjectSyntaxRenameTotal.native_binaryRelationUnique kind w R S a b c d n q v

example {m} (w R S r s a b c d n x X : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.negationAtOutputSentence w R S r s a b c d n x X)) := ObjectSyntaxRenameTotal.native_negationAtOutput w R S r s a b c d n x X

example {m} (w R S r s a b c d n x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.negationExistsAtGraphsSentence w R S r s a b c d n x)) := ObjectSyntaxRenameTotal.native_negationExistsAtGraphs w R S r s a b c d n x

example {m} (w R S a b c d n x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.negationFiberSentence w R S a b c d n x)) := ObjectSyntaxRenameTotal.native_negationFiber w R S a b c d n x

example {m} (w n x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.negationPropertyStepSentence w n x)) := ObjectSyntaxRenameTotal.native_negationPropertyStep w n x

example {m} (w R S r s a b c d n x X : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.forallAtOutputSentence w R S r s a b c d n x X)) := ObjectSyntaxRenameTotal.native_forallAtOutput w R S r s a b c d n x X

example {m} (w R S r s a b c d n x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.forallExistsAtGraphsSentence w R S r s a b c d n x)) := ObjectSyntaxRenameTotal.native_forallExistsAtGraphs w R S r s a b c d n x

example {m} (w R S a b c d n x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.forallFiberSentence w R S a b c d n x)) := ObjectSyntaxRenameTotal.native_forallFiber w R S a b c d n x

example {m} (w n x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.forallPropertyStepSentence w n x)) := ObjectSyntaxRenameTotal.native_forallPropertyStep w n x

example {m} (w R S r s a b c d n x X : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.existsAtOutputSentence w R S r s a b c d n x X)) := ObjectSyntaxRenameTotal.native_existsAtOutput w R S r s a b c d n x X

example {m} (w R S r s a b c d n x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.existsExistsAtGraphsSentence w R S r s a b c d n x)) := ObjectSyntaxRenameTotal.native_existsExistsAtGraphs w R S r s a b c d n x

example {m} (w R S a b c d n x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.existsFiberSentence w R S a b c d n x)) := ObjectSyntaxRenameTotal.native_existsFiber w R S a b c d n x

example {m} (w n x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.existsPropertyStepSentence w n x)) := ObjectSyntaxRenameTotal.native_existsPropertyStep w n x

example {m} (kind : Fin 4) (w R S r s a b c d n x y X Y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.binaryAtOutputsSentence kind w R S r s a b c d n x y X Y)) := ObjectSyntaxRenameTotal.native_binaryAtOutputs kind w R S r s a b c d n x y X Y

example {m} (kind : Fin 4) (w R S r s a b c d n x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.binaryExistsAtGraphsSentence kind w R S r s a b c d n x y)) := ObjectSyntaxRenameTotal.native_binaryExistsAtGraphs kind w R S r s a b c d n x y

example {m} (kind : Fin 4) (w R S a b c d n x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.binaryFiberSentence kind w R S a b c d n x y)) := ObjectSyntaxRenameTotal.native_binaryFiber kind w R S a b c d n x y

example {m} (kind : Fin 4) (w n x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.binaryPropertyStepSentence kind w n x y)) := ObjectSyntaxRenameTotal.native_binaryPropertyStep kind w n x y

example {m} (w n b f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.codePropertyStepSentence w n b f)) := ObjectSyntaxRenameTotal.native_codePropertyStep w n b f

example {m} (w n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.propertyStepSentence w n)) := ObjectSyntaxRenameTotal.native_propertyStep w n

example {m} (w : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.progressiveSentence w)) := ObjectSyntaxRenameTotal.native_progressive w

example {m} (w : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.allPropertiesSentence w)) := ObjectSyntaxRenameTotal.native_allProperties w

example {m} (w n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.naturalPropertySentence w n)) := ObjectSyntaxRenameTotal.native_naturalProperty w n

example {m} (w R S a b c d n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.actualFiberSentence w R S a b c d n)) := ObjectSyntaxRenameTotal.native_actualFiber w R S a b c d n

example {m} (w R S a b c d n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.actualExistsSentence w R S a b c d n)) := ObjectSyntaxRenameTotal.native_actualExists w R S a b c d n

example {m} (w R S a b c d n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.fiberIffInputSentence w R S a b c d n)) := ObjectSyntaxRenameTotal.native_fiberIffInput w R S a b c d n

example {m} (w R S a b c d n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.existsIffInputSentence w R S a b c d n)) := ObjectSyntaxRenameTotal.native_existsIffInput w R S a b c d n

example {m} (w R S a b c d n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.rejectInputSentence w R S a b c d n)) := ObjectSyntaxRenameTotal.native_rejectInput w R S a b c d n

example {m} (w R S a b c d n q v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.uniqueSentence w R S a b c d n q v)) := ObjectSyntaxRenameTotal.native_unique w R S a b c d n q v

example {m} (w R S a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameTotal.uniqueOutputSentence w R S a b c d n q)) := ObjectSyntaxRenameTotal.native_uniqueOutput w R S a b c d n q

example : SyntaxRenameOutputInduction.matrix =
    SyntaxRenameOutputSyntax.property (0 : Fin 1).castSucc (Fin.last 1) := rfl

example {m} (w n : Fin m) : SyntaxRenameOutputInduction.curried w n = .all
    ((Formula.mem (Fin.last m) w.castSucc).imp
      ((Formula.mem (Fin.last m) n.castSucc).imp (SyntaxRenameOutputSyntax.property w.castSucc (Fin.last m)))) := rfl

example {m} (advance : Bool) (w x R S a b c d : Fin m) : SyntaxRenameCheckExistence.existsCheck advance w x R S a b c d =
    .ex (SyntaxRenameRecursiveSyntax.check advance w.castSucc x.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc (Fin.last m)) := rfl

example {m} (kind : Fin 11) (w R S r s a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.introBranchSentence kind w R S r s a b c d n q)) := ObjectSyntaxRenameFields.native_introBranch kind w R S r s a b c d n q

example {m} (kind : Fin 11) (w R S r s a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.branchTargetSentence kind w R S r s a b c d n q)) := ObjectSyntaxRenameFields.native_branchTarget kind w R S r s a b c d n q

example {m} (kind : Fin 11) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.sourceCaseIffSentence kind arity w R S r s a b c d n q xs)) := ObjectSyntaxRenameFields.native_sourceCaseIff kind arity w R S r s a b c d n q xs

example {m} (advance : Bool) (w x R S a b c d q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.checkSourceSentence advance w x R S a b c d q)) := ObjectSyntaxRenameFields.native_checkSource advance w x R S a b c d q

example {m} (w r s a b c d n q x y X Y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.equalityRawIffSentence w r s a b c d n q x y X Y)) := ObjectSyntaxRenameFields.native_equalityRawIff w r s a b c d n q x y X Y

example {m} (w r s a b c d n q z Z x y X Y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.membershipRawIffSentence w r s a b c d n q z Z x y X Y)) := ObjectSyntaxRenameFields.native_membershipRawIff w r s a b c d n q z Z x y X Y

example {m} (tag : Nat) (advance : Bool) (w r s a b c d n q x X : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.singleRawIffSentence tag advance w r s a b c d n q x X)) := ObjectSyntaxRenameFields.native_singleRawIff tag advance w r s a b c d n q x X

example {m} (kind : Fin 4) (w r s a b c d n q x y X Y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.binaryRawIffSentence kind w r s a b c d n q x y X Y)) := ObjectSyntaxRenameFields.native_binaryRawIff kind w r s a b c d n q x y X Y

example {m} (w R S r s a b c d n q x y X Y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.equalityIffSentence w R S r s a b c d n q x y X Y)) := ObjectSyntaxRenameFields.native_equalityIff w R S r s a b c d n q x y X Y

example {m} (w R S r s a b c d n x y X Y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.equalityInputSentence w R S r s a b c d n x y X Y)) := ObjectSyntaxRenameFields.native_equalityInput w R S r s a b c d n x y X Y

example {m} (w R S r s a b c d n q z Z x y X Y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.membershipIffSentence w R S r s a b c d n q z Z x y X Y)) := ObjectSyntaxRenameFields.native_membershipIff w R S r s a b c d n q z Z x y X Y

example {m} (w R S r s a b c d n z Z x y X Y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.membershipInputSentence w R S r s a b c d n z Z x y X Y)) := ObjectSyntaxRenameFields.native_membershipInput w R S r s a b c d n z Z x y X Y

example {m} (w R S r s a b c d n q x X : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.negationIffSentence w R S r s a b c d n q x X)) := ObjectSyntaxRenameFields.native_negationIff w R S r s a b c d n q x X

example {m} (w R S a b c d n q x X : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.negationCodeIffSentence w R S a b c d n q x X)) := ObjectSyntaxRenameFields.native_negationCodeIff w R S a b c d n q x X

example {m} (w R S r s a b c d n x X : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.negationInputSentence w R S r s a b c d n x X)) := ObjectSyntaxRenameFields.native_negationInput w R S r s a b c d n x X

example {m} (w R S r s a b c d n q x X : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.forallIffSentence w R S r s a b c d n q x X)) := ObjectSyntaxRenameFields.native_forallIff w R S r s a b c d n q x X

example {m} (w R S a b c d n q x X : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.forallCodeIffSentence w R S a b c d n q x X)) := ObjectSyntaxRenameFields.native_forallCodeIff w R S a b c d n q x X

example {m} (w R S r s a b c d n x X : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.forallInputSentence w R S r s a b c d n x X)) := ObjectSyntaxRenameFields.native_forallInput w R S r s a b c d n x X

example {m} (w R S r s a b c d n q x X : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.existsIffSentence w R S r s a b c d n q x X)) := ObjectSyntaxRenameFields.native_existsIff w R S r s a b c d n q x X

example {m} (w R S a b c d n q x X : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.existsCodeIffSentence w R S a b c d n q x X)) := ObjectSyntaxRenameFields.native_existsCodeIff w R S a b c d n q x X

example {m} (w R S r s a b c d n x X : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.existsInputSentence w R S r s a b c d n x X)) := ObjectSyntaxRenameFields.native_existsInput w R S r s a b c d n x X

example {m} (kind : Fin 4) (w R S r s a b c d n q x y X Y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.binaryIffSentence kind w R S r s a b c d n q x y X Y)) := ObjectSyntaxRenameFields.native_binaryIff kind w R S r s a b c d n q x y X Y

example {m} (kind : Fin 4) (w R S a b c d n q x y X Y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.binaryCodeIffSentence kind w R S a b c d n q x y X Y)) := ObjectSyntaxRenameFields.native_binaryCodeIff kind w R S a b c d n q x y X Y

example {m} (kind : Fin 4) (w R S r s a b c d n x y X Y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.binaryInputSentence kind w R S r s a b c d n x y X Y)) := ObjectSyntaxRenameFields.native_binaryInput kind w R S r s a b c d n x y X Y

example {m} (truth : Bool) (w R S r s a b c d n q : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.nullaryIffSentence truth w R S r s a b c d n q)) := ObjectSyntaxRenameFields.native_nullaryIff truth w R S r s a b c d n q

example {m} (universal : Bool) (w R S a b c d n q x X u v l : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameFields.quantifiedAtLiftSentence universal w R S a b c d n q x X u v l)) := ObjectSyntaxRenameFields.native_quantifiedAtLift universal w R S a b c d n q x X u v l

example {m} (w r s a b c d x y X Y : Fin m) : SyntaxRenameKnownFieldsSyntax.equalOperands w r s a b c d x y X Y =
    (SyntaxRenameTermSyntax.renamed w r s a b c d x X).conj
      (SyntaxRenameTermSyntax.renamed w r s a b c d y Y) := rfl

example {m} (w r s a b c d z Z x y X Y : Fin m) : SyntaxRenameKnownFieldsSyntax.memberOperands w r s a b c d z Z x y X Y =
    (SyntaxAtomSyntax.zeroScalar w z).conj ((Formula.equal z Z).conj
      (SyntaxRenameKnownFieldsSyntax.equalOperands w r s a b c d x y X Y)) := rfl

-- Actual internal identity graphs/codes and all-code formula identity, in the original native kernel.
example {m} (a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameIdentity.graphExistsSentence a)) := ObjectSyntaxRenameIdentity.native_graphExists a

example {m} (a r i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameIdentity.graphEdgesSentence a r i j)) := ObjectSyntaxRenameIdentity.native_graphEdges a r i j

example {m} (a r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameIdentity.graphUniqueSentence a r s)) := ObjectSyntaxRenameIdentity.native_graphUnique a r s

example {m} (a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameIdentity.graphDiagonalSentence a r)) := ObjectSyntaxRenameIdentity.native_graphDiagonal a r

example {m} (w a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameIdentity.graphIndexMapSentence w a r)) := ObjectSyntaxRenameIdentity.native_graphIndexMap w a r

example {m} (w a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameIdentity.mapExistsSentence w a)) := ObjectSyntaxRenameIdentity.native_mapExists w a

example {m} (w a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameIdentity.codeExistsSentence w a)) := ObjectSyntaxRenameIdentity.native_codeExists w a

example {m} (w a R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameIdentity.codeMapSentence w a R)) := ObjectSyntaxRenameIdentity.native_codeMap w a R

example {m} (w a R r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameIdentity.codeAtGraphSentence w a R r)) := ObjectSyntaxRenameIdentity.native_codeAtGraph w a R r

example {m} (w a R r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameIdentity.codeEncodedIffSentence w a R r)) := ObjectSyntaxRenameIdentity.native_codeEncodedIff w a R r

example {m} (r a i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameIdentity.liftValueDiagonalSentence r a i j)) := ObjectSyntaxRenameIdentity.native_liftValueDiagonal r a i j

example {m} (w r a c u v g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameIdentity.liftGraphDiagonalSentence w r a c u v g)) := ObjectSyntaxRenameIdentity.native_liftGraphDiagonal w r a c u v g

example {m} (w a R u v L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameIdentity.liftCodeSentence w a R u v L)) := ObjectSyntaxRenameIdentity.native_liftCode w a R u v L

example {m} (w R S a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameIdentity.formulaReflexiveSentence w R S a b n)) := ObjectSyntaxRenameIdentity.native_formulaReflexive w R S a b n

example {m} (w R S a b n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameIdentity.formulaIdentitySentence w R S a b n q)) := ObjectSyntaxRenameIdentity.native_formulaIdentity w R S a b n q

example {m} (w R S a b n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxRenameIdentity.formulaIdentityIffSentence w R S a b n q)) := ObjectSyntaxRenameIdentity.native_formulaIdentityIff w R S a b n q

example {m} (w R S a b n : Fin m) : SyntaxRenameIdentitySyntax.input w R S a b n =
    (FormulaCodeSyntax.formulaCode w n a b).conj ((SyntaxIdentityMapSyntax.identityCode w a R).conj (SyntaxIdentityMapSyntax.identityCode w b S)) := rfl

example {m} (w R S a b n : Fin m) : SyntaxRenameIdentitySyntax.self w R S a b n =
    SyntaxRenameJudgmentSyntax.renamed w R S a b a b n n := rfl

-- Complete actual graph/code composition and the exact all-internal term composition law.
example {m} (w r t a c i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.valueSourceSentence w r t a c i j)) := ObjectSyntaxCompose.native_valueSource w r t a c i j

example {m} (w r t c e i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.valueTargetSentence w r t c e i j)) := ObjectSyntaxCompose.native_valueTarget w r t c e i j

example {m} (w r t a c e i j l : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.valueUniqueSentence w r t a c e i j l)) := ObjectSyntaxCompose.native_valueUnique w r t a c e i j l

example {m} (w r t a c e i : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.pointExistsSentence w r t a c e i)) := ObjectSyntaxCompose.native_pointExists w r t a c e i

example {m} (w r t a c e i : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.pointFiberSentence w r t a c e i)) := ObjectSyntaxCompose.native_pointFiber w r t a c e i

example {m} (w r t a c e : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.relationTotalSentence w r t a c e)) := ObjectSyntaxCompose.native_relationTotal w r t a c e

example {m} (w r t a c e : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.graphExistsSentence w r t a c e)) := ObjectSyntaxCompose.native_graphExists w r t a c e

example {m} (w r t a c e : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.graphFiberSentence w r t a c e)) := ObjectSyntaxCompose.native_graphFiber w r t a c e

example {m} (w r t a c e g h : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.graphUniqueSentence w r t a c e g h)) := ObjectSyntaxCompose.native_graphUnique w r t a c e g h

example {m} (w r t a c e g i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.graphEdgesSentence w r t a c e g i j)) := ObjectSyntaxCompose.native_graphEdges w r t a c e g i j

example {m} (w r t a c e g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.graphTargetMapSentence w r t a c e g)) := ObjectSyntaxCompose.native_graphTargetMap w r t a c e g

example {m} (w a c e R T K : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.codeFirstSentence w a c e R T K)) := ObjectSyntaxCompose.native_codeFirst w a c e R T K

example {m} (w a c e R T K : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.codeSecondSentence w a c e R T K)) := ObjectSyntaxCompose.native_codeSecond w a c e R T K

example {m} (w a c e R T K : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.codeOutputSentence w a c e R T K)) := ObjectSyntaxCompose.native_codeOutput w a c e R T K

example {m} (w r t a c e R T K : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.codeReadSourcesSentence w r t a c e R T K)) := ObjectSyntaxCompose.native_codeReadSources w r t a c e R T K

example {m} (w r t a c e R T K g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.codeReadGraphsSentence w r t a c e R T K g)) := ObjectSyntaxCompose.native_codeReadGraphs w r t a c e R T K g

example {m} (w r t a c e R T K g : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.codeEncodedIffSentence w r t a c e R T K g)) := ObjectSyntaxCompose.native_codeEncodedIff w r t a c e R T K g

example {m} (w r t a c e R T K g i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.codeEdgesSentence w r t a c e R T K g i j)) := ObjectSyntaxCompose.native_codeEdges w r t a c e R T K g i j

example {m} (w r t a c e R T : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.codeExistsAtSourcesSentence w r t a c e R T)) := ObjectSyntaxCompose.native_codeExistsAtSources w r t a c e R T

example {m} (w a c e R T : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.codeExistsSentence w a c e R T)) := ObjectSyntaxCompose.native_codeExists w a c e R T

example {m} (w a c e R T K L : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.codeUniqueSentence w a c e R T K L)) := ObjectSyntaxCompose.native_codeUnique w a c e R T K L

example {m} (w a c e R T : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.codeFiberSentence w a c e R T)) := ObjectSyntaxCompose.native_codeFiber w a c e R T

example {m} (w a c e R T : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.codeInputIffSentence w a c e R T)) := ObjectSyntaxCompose.native_codeInputIff w a c e R T

example {m} (bound : Bool) (w r t a c e g n q v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.termBranchSentence bound w r t a c e g n q v)) := ObjectSyntaxCompose.native_termBranch bound w r t a c e g n q v

example {m} (w r s t u g h a b c d e f n q v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.termComposeSentence w r s t u g h a b c d e f n q v)) := ObjectSyntaxCompose.native_termCompose w r s t u g h a b c d e f n q v

example {m} (w r s t u g h a b c d e f n v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.termFactorSentence w r s t u g h a b c d e f n v)) := ObjectSyntaxCompose.native_termFactor w r s t u g h a b c d e f n v

example {m} (w r s t u g h a b c d e f n v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.termCollapseSentence w r s t u g h a b c d e f n v)) := ObjectSyntaxCompose.native_termCollapse w r s t u g h a b c d e f n v

example {m} (w r s t u g h a b c d e f n v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxCompose.termComposeIffSentence w r s t u g h a b c d e f n v)) := ObjectSyntaxCompose.native_termComposeIff w r s t u g h a b c d e f n v

example {m} (r t i j : Fin m) : SyntaxComposeSyntax.value r t i j = Source.Formula.ex
    ((GraphSyntax.edge r.castSucc i.castSucc (Fin.last m)).conj (GraphSyntax.edge t.castSucc (Fin.last m) j.castSucc)) := rfl

example {m} (w a c e R T K : Fin m) : SyntaxComposeCodeSyntax.coded w a c e R T K =
    Source.Formula.ex (.ex (.ex (SyntaxComposeCodeSyntax.body w a c e R T K))) := rfl

-- Actual binder lifting commutes with complete graph/code composition on all internal candidates.
example {m} (w r t a c e A C E ρ τ i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxComposeLift.zeroSentence w r t a c e A C E ρ τ i j)) := ObjectSyntaxComposeLift.native_zero w r t a c e A C E ρ τ i j

example {m} (w r t a c e g A C E ρ τ i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxComposeLift.shiftedSentence w r t a c e g A C E ρ τ i j)) := ObjectSyntaxComposeLift.native_shifted w r t a c e g A C E ρ τ i j

example {m} (w r t a c e g A C E ρ τ i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxComposeLift.valueForwardSentence w r t a c e g A C E ρ τ i j)) := ObjectSyntaxComposeLift.native_valueForward w r t a c e g A C E ρ τ i j

example {m} (w r t a c e g A C E ρ τ γ i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxComposeLift.edgeForwardSentence w r t a c e g A C E ρ τ γ i j)) := ObjectSyntaxComposeLift.native_edgeForward w r t a c e g A C E ρ τ γ i j

example {m} (f g d : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxComposeLift.includedAgreementSentence f g d)) := ObjectSyntaxComposeLift.native_includedAgreement f g d

example {m} (w r t a c e g A C E ρ τ γ k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxComposeLift.includedSentence w r t a c e g A C E ρ τ γ k)) := ObjectSyntaxComposeLift.native_included w r t a c e g A C E ρ τ γ k

example {m} (w r t a c e g A C E ρ τ γ k : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxComposeLift.equalGraphsSentence w r t a c e g A C E ρ τ γ k)) := ObjectSyntaxComposeLift.native_equalGraphs w r t a c e g A C E ρ τ γ k

example {m} (w r t a c e g A C E ρ τ γ : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxComposeLift.graphCompositionSentence w r t a c e g A C E ρ τ γ)) := ObjectSyntaxComposeLift.native_graphComposition w r t a c e g A C E ρ τ γ

example {m} (w r t a c e g A C E ρ τ γ i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxComposeLift.graphEdgesSentence w r t a c e g A C E ρ τ γ i j)) := ObjectSyntaxComposeLift.native_graphEdges w r t a c e g A C E ρ τ γ i j

example {m} (w r t a c e g A C E ρ τ γ i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxComposeLift.graphValuesSentence w r t a c e g A C E ρ τ γ i j)) := ObjectSyntaxComposeLift.native_graphValues w r t a c e g A C E ρ τ γ i j

example {m} (w r t a c e g A C E ρ τ γ : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxComposeLift.liftedIffComposedSentence w r t a c e g A C E ρ τ γ)) := ObjectSyntaxComposeLift.native_liftedIffComposed w r t a c e g A C E ρ τ γ

example {m} (w r t g a c e R T K A C E Lr Lt Lk : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxComposeLift.atSourcesSentence w r t g a c e R T K A C E Lr Lt Lk)) := ObjectSyntaxComposeLift.native_atSources w r t g a c e R T K A C E Lr Lt Lk

example {m} (w a c e R T K A C E Lr Lt Lk : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxComposeLift.codedCompositionSentence w a c e R T K A C E Lr Lt Lk)) := ObjectSyntaxComposeLift.native_codedComposition w a c e R T K A C E Lr Lt Lk

example {m} (w a c e R T K A C E Lr Lt Lk : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxComposeLift.codedIffSentence w a c e R T K A C E Lr Lt Lk)) := ObjectSyntaxComposeLift.native_codedIff w a c e R T K A C E Lr Lt Lk

example {m} (w a c e R T A C D E Lr Lt : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxComposeLift.middleEqualSentence w a c e R T A C D E Lr Lt)) := ObjectSyntaxComposeLift.native_middleEqual w a c e R T A C D E Lr Lt

example {m} (w a c e R T K A C D E Lr Lt Lk : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxComposeLift.mixedMiddleSentence w a c e R T K A C D E Lr Lt Lk)) := ObjectSyntaxComposeLift.native_mixedMiddle w a c e R T K A C D E Lr Lt Lk

example {m} (w a c e R T K A C D E Lr Lt Lk : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxComposeLift.mixedIffSentence w a c e R T K A C D E Lr Lt Lk)) := ObjectSyntaxComposeLift.native_mixedIff w a c e R T K A C D E Lr Lt Lk

-- Full all-internal formula composition, including a closed fourteen-parameter object induction.
example {m} (w R S r s a b c d n q x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.targetNegationSentence w R S r s a b c d n q x)) := ObjectSyntaxFormulaCompose.native_targetNegation w R S r s a b c d n q x

example {m} (w R S r s a b c d n q x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.targetForallSentence w R S r s a b c d n q x)) := ObjectSyntaxFormulaCompose.native_targetForall w R S r s a b c d n q x

example {m} (w R S r s a b c d n q x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.targetExistsSentence w R S r s a b c d n q x)) := ObjectSyntaxFormulaCompose.native_targetExists w R S r s a b c d n q x

example {m} (kind : Fin 4) (w R S r s a b c d n q x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.targetBinarySentence kind w R S r s a b c d n q x y)) := ObjectSyntaxFormulaCompose.native_targetBinary kind w R S r s a b c d n q x y

example {m} (w R S r s a b c d n q x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.targetEqualitySentence w R S r s a b c d n q x y)) := ObjectSyntaxFormulaCompose.native_targetEquality w R S r s a b c d n q x y

example {m} (w R S r s a b c d n q z x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.targetMembershipSentence w R S r s a b c d n q z x y)) := ObjectSyntaxFormulaCompose.native_targetMembership w R S r s a b c d n q z x y

example {m} (w R S T U K L r s t u g h a b c d e f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.boundDiagramCodeSentence w R S T U K L r s t u g h a b c d e f)) := ObjectSyntaxFormulaCompose.native_boundDiagramCode w R S T U K L r s t u g h a b c d e f

example {m} (w R S T U K L r s t u g h a b c d e f : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.freeDiagramCodeSentence w R S T U K L r s t u g h a b c d e f)) := ObjectSyntaxFormulaCompose.native_freeDiagramCode w R S T U K L r s t u g h a b c d e f

example {m} (truth : Bool) (w R S T U K L r s t u g h a b c d e f n q v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.nullarySentence truth w R S T U K L r s t u g h a b c d e f n q v)) := ObjectSyntaxFormulaCompose.native_nullary truth w R S T U K L r s t u g h a b c d e f n q v

example {m} (w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.equalityFieldsSentence w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W)) := ObjectSyntaxFormulaCompose.native_equalityFields w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W

example {m} (w R S T U K L r s t u g h a b c d e f n q v z z1 z2 x y X Y Z W : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.membershipFieldsSentence w R S T U K L r s t u g h a b c d e f n q v z z1 z2 x y X Y Z W)) := ObjectSyntaxFormulaCompose.native_membershipFields w R S T U K L r s t u g h a b c d e f n q v z z1 z2 x y X Y Z W

example {m} (w R S T U K L r s t u g h a b c d e f n q v x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.equalitySentence w R S T U K L r s t u g h a b c d e f n q v x y)) := ObjectSyntaxFormulaCompose.native_equality w R S T U K L r s t u g h a b c d e f n q v x y

example {m} (w R S T U K L r s t u g h a b c d e f n q v z x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.membershipSentence w R S T U K L r s t u g h a b c d e f n q v z x y)) := ObjectSyntaxFormulaCompose.native_membership w R S T U K L r s t u g h a b c d e f n q v z x y

example {m} (w R S T U K L r s t u g h a b c d e f n q v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.atomicSentence w R S T U K L r s t u g h a b c d e f n q v)) := ObjectSyntaxFormulaCompose.native_atomic w R S T U K L r s t u g h a b c d e f n q v

example {m} (w n x R S T U K L a b c d e f X Z : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.advancedComposeSentence w n x R S T U K L a b c d e f X Z)) := ObjectSyntaxFormulaCompose.native_advancedCompose w n x R S T U K L a b c d e f X Z

example {m} (advance : Bool) (w n x R S T U K L a b c d e f X Z : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.checkComposeSentence advance w n x R S T U K L a b c d e f X Z)) := ObjectSyntaxFormulaCompose.native_checkCompose advance w n x R S T U K L a b c d e f X Z

example {m} (w R S T U K L r s t u g h a b c d e f n q v x X Z : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.negationFieldsSentence w R S T U K L r s t u g h a b c d e f n q v x X Z)) := ObjectSyntaxFormulaCompose.native_negationFields w R S T U K L r s t u g h a b c d e f n q v x X Z

example {m} (w R S T U K L r s t u g h a b c d e f n q v x X Z : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.forallFieldsSentence w R S T U K L r s t u g h a b c d e f n q v x X Z)) := ObjectSyntaxFormulaCompose.native_forallFields w R S T U K L r s t u g h a b c d e f n q v x X Z

example {m} (w R S T U K L r s t u g h a b c d e f n q v x X Z : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.existsFieldsSentence w R S T U K L r s t u g h a b c d e f n q v x X Z)) := ObjectSyntaxFormulaCompose.native_existsFields w R S T U K L r s t u g h a b c d e f n q v x X Z

example {m} (kind : Fin 4) (w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.binaryFieldsSentence kind w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W)) := ObjectSyntaxFormulaCompose.native_binaryFields kind w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W

example {m} (w R S T U K L r s t u g h a b c d e f n q v x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.negationSentence w R S T U K L r s t u g h a b c d e f n q v x)) := ObjectSyntaxFormulaCompose.native_negation w R S T U K L r s t u g h a b c d e f n q v x

example {m} (w R S T U K L r s t u g h a b c d e f n q v x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.forallSentence w R S T U K L r s t u g h a b c d e f n q v x)) := ObjectSyntaxFormulaCompose.native_forall w R S T U K L r s t u g h a b c d e f n q v x

example {m} (w R S T U K L r s t u g h a b c d e f n q v x : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.existsSentence w R S T U K L r s t u g h a b c d e f n q v x)) := ObjectSyntaxFormulaCompose.native_exists w R S T U K L r s t u g h a b c d e f n q v x

example {m} (kind : Fin 4) (w R S T U K L r s t u g h a b c d e f n q v x y : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.binarySentence kind w R S T U K L r s t u g h a b c d e f n q v x y)) := ObjectSyntaxFormulaCompose.native_binary kind w R S T U K L r s t u g h a b c d e f n q v x y

example {m} (w R S T U K L r s t u g h a b c d e f n q v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.codeStepSentence w R S T U K L r s t u g h a b c d e f n q v)) := ObjectSyntaxFormulaCompose.native_codeStep w R S T U K L r s t u g h a b c d e f n q v

example {m} (w R S T U K L r s t u g h a b c d e f n q v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.diagramStepSentence w R S T U K L r s t u g h a b c d e f n q v)) := ObjectSyntaxFormulaCompose.native_diagramStep w R S T U K L r s t u g h a b c d e f n q v

example {m} (w n R S T U K L a b c d e f q v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.mapCodeStepSentence w n R S T U K L a b c d e f q v)) := ObjectSyntaxFormulaCompose.native_mapCodeStep w n R S T U K L a b c d e f q v

example {m} (w n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.propertyStepSentence w n)) := ObjectSyntaxFormulaCompose.native_propertyStep w n

example {m} (w : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.progressiveSentence w)) := ObjectSyntaxFormulaCompose.native_progressive w

example {m} (w : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.allPropertiesSentence w)) := ObjectSyntaxFormulaCompose.native_allProperties w

example {m} (w n : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.naturalPropertySentence w n)) := ObjectSyntaxFormulaCompose.native_naturalProperty w n

example {m} (w R S T U K L a b c d e f n q v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.forwardSentence w R S T U K L a b c d e f n q v)) := ObjectSyntaxFormulaCompose.native_forward w R S T U K L a b c d e f n q v

example {m} (w R S T U K L a b c d e f n v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.factorSentence w R S T U K L a b c d e f n v)) := ObjectSyntaxFormulaCompose.native_factor w R S T U K L a b c d e f n v

example {m} (w R S T U K L a b c d e f n v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.collapseSentence w R S T U K L a b c d e f n v)) := ObjectSyntaxFormulaCompose.native_collapse w R S T U K L a b c d e f n v

example {m} (w R S T U K L a b c d e f n v : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFormulaCompose.composeIffSentence w R S T U K L a b c d e f n v)) := ObjectSyntaxFormulaCompose.native_composeIff w R S T U K L a b c d e f n v

example {m} (b : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFreeShift.graphExistsSentence b)) := ObjectSyntaxFreeShift.native_graphExists b

example {m} (b r i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFreeShift.graphEdgesSentence b r i j)) := ObjectSyntaxFreeShift.native_graphEdges b r i j

example {m} (b r s : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFreeShift.graphUniqueSentence b r s)) := ObjectSyntaxFreeShift.native_graphUnique b r s

example {m} (w b B : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFreeShift.mapExistsSentence w b B)) := ObjectSyntaxFreeShift.native_mapExists w b B

example {m} (w b B : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFreeShift.mapFiberSentence w b B)) := ObjectSyntaxFreeShift.native_mapFiber w b B

example {m} (w b B r s : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFreeShift.mapUniqueSentence w b B r s)) := ObjectSyntaxFreeShift.native_mapUnique w b B r s

example {m} (w b B r i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFreeShift.mapEdgesSentence w b B r i j)) := ObjectSyntaxFreeShift.native_mapEdges w b B r i j

example {m} (w b B : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFreeShift.codeExistsSentence w b B)) := ObjectSyntaxFreeShift.native_codeExists w b B

example {m} (w b B S : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFreeShift.codeMapSentence w b B S)) := ObjectSyntaxFreeShift.native_codeMap w b B S

example {m} (w b B S : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFreeShift.codeNaturalSentence w b B S)) := ObjectSyntaxFreeShift.native_codeNatural w b B S

example {m} (w b B S : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFreeShift.codeInputSentence w b B S)) := ObjectSyntaxFreeShift.native_codeInput w b B S

example {m} (w b B S r : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFreeShift.codeAtGraphSentence w b B S r)) := ObjectSyntaxFreeShift.native_codeAtGraph w b B S r

example {m} (w b B S r : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFreeShift.codeEncodedIffSentence w b B S r)) := ObjectSyntaxFreeShift.native_codeEncodedIff w b B S r

example {m} (w b B S T : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFreeShift.codeUniqueSentence w b B S T)) := ObjectSyntaxFreeShift.native_codeUnique w b B S T

example {m} (w b B : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFreeShift.codeFiberSentence w b B)) := ObjectSyntaxFreeShift.native_codeFiber w b B

example {m} (w b B : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFreeShift.codeInputIffSentence w b B)) := ObjectSyntaxFreeShift.native_codeInputIff w b B

example {m} (w b : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFreeShift.actualStateSentence w b)) := ObjectSyntaxFreeShift.native_actualState w b

example {m} (w z : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFreeShift.zeroStateSentence w z)) := ObjectSyntaxFreeShift.native_zeroState w z

example {m} (w b B S r i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFreeShift.codedEdgesSentence w b B S r i j)) := ObjectSyntaxFreeShift.native_codedEdges w b B S r i j

example {m} (w b B r i z : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFreeShift.freshAbsentSentence w b B r i z)) := ObjectSyntaxFreeShift.native_freshAbsent w b B r i z

example {m} (w b B r i j : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFreeShift.emptySourceSentence w b B r i j)) := ObjectSyntaxFreeShift.native_emptySource w b B r i j

example {m} (w b B r : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFreeShift.emptyGraphSentence w b B r)) := ObjectSyntaxFreeShift.native_emptyGraph w b B r

example {m} (w b B C S T : Fin m) : FirstOrder.Derives nativeZF []
    (Translation.sentence (ObjectSyntaxFreeShift.rangeUniqueSentence w b B C S T)) := ObjectSyntaxFreeShift.native_rangeUnique w b B C S T

-- Full internal free-head weakening: generic closed schemas.
example {m} (w a R T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.identityUniqueSentence w a R T)) :=
  Internal.ObjectSyntaxWeakenFree.native_identityUnique w a R T

example {m} (w a R u L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.identityLiftSentence w a R u L)) :=
  Internal.ObjectSyntaxWeakenFree.native_identityLift w a R u L

example {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.inputSentence w a b B n q)) :=
  Internal.ObjectSyntaxWeakenFree.native_input w a b B n q

example {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.sourceTypeSentence w a b B n q)) :=
  Internal.ObjectSyntaxWeakenFree.native_sourceType w a b B n q

example {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.targetTypeSentence w a b B n q)) :=
  Internal.ObjectSyntaxWeakenFree.native_targetType w a b B n q

example {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.outputNaturalSentence w a b B n q)) :=
  Internal.ObjectSyntaxWeakenFree.native_outputNatural w a b B n q

example {m} (w a b B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.existsOutputSentence w a b B n)) :=
  Internal.ObjectSyntaxWeakenFree.native_existsOutput w a b B n

example {m} (w a b B n q R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.atCodesSentence w a b B n q R S)) :=
  Internal.ObjectSyntaxWeakenFree.native_atCodes w a b B n q R S

example {m} (w a b B n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.outputUniqueSentence w a b B n q v)) :=
  Internal.ObjectSyntaxWeakenFree.native_outputUnique w a b B n q v

example {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.uniqueOutputSentence w a b B n q)) :=
  Internal.ObjectSyntaxWeakenFree.native_uniqueOutput w a b B n q

example {m} (w a b B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.actualFiberSentence w a b B n)) :=
  Internal.ObjectSyntaxWeakenFree.native_actualFiber w a b B n

example {m} (w a b B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.existsInputIffSentence w a b B n)) :=
  Internal.ObjectSyntaxWeakenFree.native_existsInputIff w a b B n

example {m} (w a b B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.fiberInputIffSentence w a b B n)) :=
  Internal.ObjectSyntaxWeakenFree.native_fiberInputIff w a b B n

example {m} (w a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.actualStateSentence w a b n)) :=
  Internal.ObjectSyntaxWeakenFree.native_actualState w a b n

example {m} (w a b B n q x X R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.negationSentence w a b B n q x X R S)) :=
  Internal.ObjectSyntaxWeakenFree.native_negation w a b B n q x X R S

example {m} (kind : Fin 4) (w a b B n q x y X Y R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.binarySentence kind w a b B n q x y X Y R S)) :=
  Internal.ObjectSyntaxWeakenFree.native_binary kind w a b B n q x y X Y R S

example {m} (universal : Bool) (w a b B n q x X R S u L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.quantifiedSentence universal w a b B n q x X R S u L)) :=
  Internal.ObjectSyntaxWeakenFree.native_quantified universal w a b B n q x X R S u L

example {m} (w a b B n q x X R S u L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.forallSentence w a b B n q x X R S u L)) :=
  Internal.ObjectSyntaxWeakenFree.native_forall w a b B n q x X R S u L

example {m} (w a b B n q x X R S u L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.existsSentence w a b B n q x X R S u L)) :=
  Internal.ObjectSyntaxWeakenFree.native_exists w a b B n q x X R S u L

example {m} (truth : Bool) (w a b B n q R S r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.nullarySentence truth w a b B n q R S r s)) :=
  Internal.ObjectSyntaxWeakenFree.native_nullary truth w a b B n q R S r s

example {m} (w a b B n q R S r s x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.equalitySentence w a b B n q R S r s x y X Y)) :=
  Internal.ObjectSyntaxWeakenFree.native_equality w a b B n q R S r s x y X Y

example {m} (w a b B n q R S r s z Z x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.membershipSentence w a b B n q R S r s z Z x y X Y)) :=
  Internal.ObjectSyntaxWeakenFree.native_membership w a b B n q R S r s z Z x y X Y

example {m} (w a b B R S r s n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.boundTermSentence w a b B R S r s n q i j)) :=
  Internal.ObjectSyntaxWeakenFree.native_boundTerm w a b B R S r s n q i j

example {m} (w a b B R S r s n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.freeTermSentence w a b B R S r s n q i j)) :=
  Internal.ObjectSyntaxWeakenFree.native_freeTerm w a b B R S r s n q i j

example {m} (w a b B R S r s n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.freshFreeAbsentSentence w a b B R S r s n q i j)) :=
  Internal.ObjectSyntaxWeakenFree.native_freshFreeAbsent w a b B R S r s n q i j

example {m} (w a b B R S r s n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.emptyFreeAbsentSentence w a b B R S r s n q i j)) :=
  Internal.ObjectSyntaxWeakenFree.native_emptyFreeAbsent w a b B R S r s n q i j

example {m} (w a b B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.actualCodesSentence w a b B)) :=
  Internal.ObjectSyntaxWeakenFree.native_actualCodes w a b B

example {m} (w a b B n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.internalNegationSentence w a b B n q x X)) :=
  Internal.ObjectSyntaxWeakenFree.native_internalNegation w a b B n q x X

example {m} (kind : Fin 4) (w a b B n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.internalBinarySentence kind w a b B n q x y X Y)) :=
  Internal.ObjectSyntaxWeakenFree.native_internalBinary kind w a b B n q x y X Y

example {m} (universal : Bool) (w a b B n q x X u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxWeakenFree.internalQuantifiedSentence universal w a b B n q x X u)) :=
  Internal.ObjectSyntaxWeakenFree.native_internalQuantified universal w a b B n q x X u

-- All-internal original term-list / actual index-code conversion.
example {m} (w z c t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.openTermSentence w z c t)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_openTerm w z c t

example {m} (w f a c i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.decodedTargetSentence w f a c i j)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_decodedTarget w f a c i j

example {m} (w r i t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.encodedNaturalSentence w r i t)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_encodedNatural w r i t

example {m} (w r a c i t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.encodedFreeSentence w r a c i t)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_encodedFree w r a c i t

example {m} (w f a i j k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.decodedUniqueSentence w f a i j k)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_decodedUnique w f a i j k

example {m} (w f a i j k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.encodedUniqueSentence w f a i j k)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_encodedUnique w f a i j k

example {m} (w f a c r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.decodedIndexSentence w f a c r)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_decodedIndex w f a c r

example {m} (w r a c f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.encodedTermsSentence w r a c f)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_encodedTerms w r a c f

example {m} (w f a c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.decodeExistsSentence w f a c)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_decodeExists w f a c

example {m} (w r a c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.encodeExistsSentence w r a c)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_encodeExists w r a c

example {m} (w f a r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.decodeGraphUniqueSentence w f a r s)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_decodeGraphUnique w f a r s

example {m} (w r a f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.encodeGraphUniqueSentence w r a f g)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_encodeGraphUnique w r a f g

example {m} (w r a c f i j t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.encodedAtCodeSentence w r a c f i j t)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_encodedAtCode w r a c f i j t

example {m} (w f a c r i j t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.decodedAtCodeSentence w f a c r i j t)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_decodedAtCode w f a c r i j t

example {m} (w r a c f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.encodedToDecodedSentence w r a c f)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_encodedToDecoded w r a c f

example {m} (w r a c f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.decodedToEncodedSentence w r a c f)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_decodedToEncoded w r a c f

example {m} (w f a c r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.indicesUniqueSentence w f a c r s)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_indicesUnique w f a c r s

example {m} (w f g a c r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.termsUniqueSentence w f g a c r)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_termsUnique w f g a c r

example {m} (w a c L S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.listProjectionSentence w a c L S)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_listProjection w a c L S

example {m} (w a c L S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.mapProjectionSentence w a c L S)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_mapProjection w a c L S

example {m} (w a c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.fromListSentence w a c L)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_fromList w a c L

example {m} (w a c S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.fromMapSentence w a c S)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_fromMap w a c S

example {m} (w a c L S T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.mapUniqueSentence w a c L S T)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_mapUnique w a c L S T

example {m} (w a c L M S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.listUniqueSentence w a c L M S)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_listUnique w a c L M S

example {m} (w a c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.mapFiberSentence w a c L)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_mapFiber w a c L

example {m} (w a c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.mapExistsIffSentence w a c L)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_mapExistsIff w a c L

example {m} (w a c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.mapFiberIffSentence w a c L)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_mapFiberIff w a c L

example {m} (w a c S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.listFiberSentence w a c S)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_listFiber w a c S

example {m} (w a c S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.listExistsIffSentence w a c S)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_listExistsIff w a c S

example {m} (w a c S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.listFiberIffSentence w a c S)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_listFiberIff w a c S

example {m} (w a c L S r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.atGraphSentence w a c L S r)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_atGraph w a c L S r

example {m} (w a c L S r i j t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.fieldAtCodeSentence w a c L S r i j t)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_fieldAtCode w a c L S r i j t

example {m} (w a c L i t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSyntaxFreeSubstCodec.fieldIsFreeSentence w a c L i t)) :=
  Internal.ObjectSyntaxFreeSubstCodec.native_fieldIsFree w a c L i t

-- Formula free substitution from the original term-code list.
example {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.inputSentence w b a c L n q)) :=
  Internal.ObjectFormulaFreeSubst.native_input w b a c L n q

example {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.sourceTypeSentence w b a c L n q)) :=
  Internal.ObjectFormulaFreeSubst.native_sourceType w b a c L n q

example {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.targetTypeSentence w b a c L n q)) :=
  Internal.ObjectFormulaFreeSubst.native_targetType w b a c L n q

example {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.outputNaturalSentence w b a c L n q)) :=
  Internal.ObjectFormulaFreeSubst.native_outputNatural w b a c L n q

example {m} (w b a c L n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.existsOutputSentence w b a c L n)) :=
  Internal.ObjectFormulaFreeSubst.native_existsOutput w b a c L n

example {m} (w b a c L n q R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.atCodesSentence w b a c L n q R S)) :=
  Internal.ObjectFormulaFreeSubst.native_atCodes w b a c L n q R S

example {m} (w b a c L n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.outputUniqueSentence w b a c L n q v)) :=
  Internal.ObjectFormulaFreeSubst.native_outputUnique w b a c L n q v

example {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.uniqueOutputSentence w b a c L n q)) :=
  Internal.ObjectFormulaFreeSubst.native_uniqueOutput w b a c L n q

example {m} (w b a c L n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.actualFiberSentence w b a c L n)) :=
  Internal.ObjectFormulaFreeSubst.native_actualFiber w b a c L n

example {m} (w b a c L n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.existsInputIffSentence w b a c L n)) :=
  Internal.ObjectFormulaFreeSubst.native_existsInputIff w b a c L n

example {m} (w b a c L n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.fiberInputIffSentence w b a c L n)) :=
  Internal.ObjectFormulaFreeSubst.native_fiberInputIff w b a c L n

example {m} (w b a c L n q x X R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.negationSentence w b a c L n q x X R S)) :=
  Internal.ObjectFormulaFreeSubst.native_negation w b a c L n q x X R S

example {m} (kind : Fin 4) (w b a c L n q x y X Y R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.binarySentence kind w b a c L n q x y X Y R S)) :=
  Internal.ObjectFormulaFreeSubst.native_binary kind w b a c L n q x y X Y R S

example {m} (universal : Bool) (w b a c L n q x X R S u K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.quantifiedSentence universal w b a c L n q x X R S u K)) :=
  Internal.ObjectFormulaFreeSubst.native_quantified universal w b a c L n q x X R S u K

example {m} (w b a c L n q x X R S u K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.forallSentence w b a c L n q x X R S u K)) :=
  Internal.ObjectFormulaFreeSubst.native_forall w b a c L n q x X R S u K

example {m} (w b a c L n q x X R S u K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.existsSentence w b a c L n q x X R S u K)) :=
  Internal.ObjectFormulaFreeSubst.native_exists w b a c L n q x X R S u K

example {m} (truth : Bool) (w b a c L n q R S r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.nullarySentence truth w b a c L n q R S r s)) :=
  Internal.ObjectFormulaFreeSubst.native_nullary truth w b a c L n q R S r s

example {m} (w b a c L n q R S r s x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.equalitySentence w b a c L n q R S r s x y X Y)) :=
  Internal.ObjectFormulaFreeSubst.native_equality w b a c L n q R S r s x y X Y

example {m} (w b a c L n q R S r s z Z x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.membershipSentence w b a c L n q R S r s z Z x y X Y)) :=
  Internal.ObjectFormulaFreeSubst.native_membership w b a c L n q R S r s z Z x y X Y

example {m} (w b a c R S r s n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.boundTermSentence w b a c R S r s n q i j)) :=
  Internal.ObjectFormulaFreeSubst.native_boundTerm w b a c R S r s n q i j

example {m} (w b a c L R S r s n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.freeTermFieldSentence w b a c L R S r s n q i j)) :=
  Internal.ObjectFormulaFreeSubst.native_freeTermField w b a c L R S r s n q i j

example {m} (w b a c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.actualCodesSentence w b a c L)) :=
  Internal.ObjectFormulaFreeSubst.native_actualCodes w b a c L

example {m} (w b a c L n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.internalNegationSentence w b a c L n q x X)) :=
  Internal.ObjectFormulaFreeSubst.native_internalNegation w b a c L n q x X

example {m} (kind : Fin 4) (w b a c L n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.internalBinarySentence kind w b a c L n q x y X Y)) :=
  Internal.ObjectFormulaFreeSubst.native_internalBinary kind w b a c L n q x y X Y

example {m} (universal : Bool) (w b a c L n q x X u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaFreeSubst.internalQuantifiedSentence universal w b a c L n q x X u)) :=
  Internal.ObjectFormulaFreeSubst.native_internalQuantified universal w b a c L n q x X u

example {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedTerm.inputSentence w r s a b c d n q)) :=
  Internal.ObjectMixedTerm.native_input w r s a b c d n q

example {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedTerm.sourceTypeSentence w r s a b c d n q)) :=
  Internal.ObjectMixedTerm.native_sourceType w r s a b c d n q

example {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedTerm.targetTypeSentence w r s a b c d n q)) :=
  Internal.ObjectMixedTerm.native_targetType w r s a b c d n q

example {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedTerm.outputNaturalSentence w r s a b c d n q)) :=
  Internal.ObjectMixedTerm.native_outputNatural w r s a b c d n q

example {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedTerm.existsOutputSentence w r s a b c d n)) :=
  Internal.ObjectMixedTerm.native_existsOutput w r s a b c d n

example {m} (w r s a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedTerm.outputUniqueSentence w r s a b c d n q v)) :=
  Internal.ObjectMixedTerm.native_outputUnique w r s a b c d n q v

example {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedTerm.uniqueOutputSentence w r s a b c d n q)) :=
  Internal.ObjectMixedTerm.native_uniqueOutput w r s a b c d n q

example {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedTerm.actualFiberSentence w r s a b c d n)) :=
  Internal.ObjectMixedTerm.native_actualFiber w r s a b c d n

example {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedTerm.existsInputIffSentence w r s a b c d n)) :=
  Internal.ObjectMixedTerm.native_existsInputIff w r s a b c d n

example {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedTerm.fiberInputIffSentence w r s a b c d n)) :=
  Internal.ObjectMixedTerm.native_fiberInputIff w r s a b c d n

example {m} (bound : Bool) (w r s a b c d n q i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedTerm.atCodeSentence bound w r s a b c d n q i)) :=
  Internal.ObjectMixedTerm.native_atCode bound w r s a b c d n q i

example {m} {p} (P : Formula (p+2)) (ρ : Fin p → Fin m) (w a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedTerm.imageGraphExistsSentence P ρ w a c d)) :=
  Internal.ObjectMixedTerm.native_imageGraphExists P ρ w a c d

example {m} (w R S c d C D f a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedTerm.pushExistsSentence w R S c d C D f a)) :=
  Internal.ObjectMixedTerm.native_pushExists w R S c d C D f a

example {m} (w R S c d C D f a g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedTerm.pushUniqueSentence w R S c d C D f a g h)) :=
  Internal.ObjectMixedTerm.native_pushUnique w R S c d C D f a g h

example {m} (w R S c d C D f a g i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedTerm.pushGuardedEdgesSentence w R S c d C D f a g i q)) :=
  Internal.ObjectMixedTerm.native_pushGuardedEdges w R S c d C D f a g i q

example {m} (w R S c d C D f a g i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedTerm.pushEdgesSentence w R S c d C D f a g i q)) :=
  Internal.ObjectMixedTerm.native_pushEdges w R S c d C D f a g i q

example {m} (w R S c d C D f a g i t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedTerm.pushAtValueSentence w R S c d C D f a g i t q)) :=
  Internal.ObjectMixedTerm.native_pushAtValue w R S c d C D f a g i t q

example {m} (w R S c d C D r s a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedTerm.bothExistSentence w R S c d C D r s a b)) :=
  Internal.ObjectMixedTerm.native_bothExist w R S c d C D r s a b

example {m} (w R S c d C D r s a b g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedTerm.bothTargetSentence w R S c d C D r s a b g h)) :=
  Internal.ObjectMixedTerm.native_bothTarget w R S c d C D r s a b g h

example {m} (w R S c d C D r s a b g h G H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedTerm.bothUniqueSentence w R S c d C D r s a b g h G H)) :=
  Internal.ObjectMixedTerm.native_bothUnique w R S c d C D r s a b g h G H

example {m} (w r s a b c d C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedTerm.boundShiftExistsSentence w r s a b c d C)) :=
  Internal.ObjectMixedTerm.native_boundShiftExists w r s a b c d C

example {m} (w f a c d z A : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.prefixExistsSentence w f a c d z A)) :=
  Internal.ObjectMixedBinder.native_prefixExists w f a c d z A

example {m} (w f a c d z A g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.prefixUniqueSentence w f a c d z A g h)) :=
  Internal.ObjectMixedBinder.native_prefixUnique w f a c d z A g h

example {m} (w f a c d z A g i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.prefixEdgesSentence w f a c d z A g i q)) :=
  Internal.ObjectMixedBinder.native_prefixEdges w f a c d z A g i q

example {m} (w f a c d z A g i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.prefixZeroSentence w f a c d z A g i q)) :=
  Internal.ObjectMixedBinder.native_prefixZero w f a c d z A g i q

example {m} (w f a c d z A g i q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.prefixSuccessorSentence w f a c d z A g i q k)) :=
  Internal.ObjectMixedBinder.native_prefixSuccessor w f a c d z A g i q k

example {m} (w f a c d z i q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.valueUniqueSentence w f a c d z i q v)) :=
  Internal.ObjectMixedBinder.native_valueUnique w f a c d z i q v

example {m} (f a z i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.valueZeroSentence f a z i q)) :=
  Internal.ObjectMixedBinder.native_valueZero f a z i q

example {m} (w f a z i q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.valueSuccessorSentence w f a z i q k)) :=
  Internal.ObjectMixedBinder.native_valueSuccessor w f a z i q k

example {m} (w f a c d z i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.valueTargetSentence w f a c d z i q)) :=
  Internal.ObjectMixedBinder.native_valueTarget w f a c d z i q

example {m} (w f a z A i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.valueSourceSentence w f a z A i q)) :=
  Internal.ObjectMixedBinder.native_valueSource w f a z A i q

example {m} (w c C d z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.headTermSentence w c C d z n)) :=
  Internal.ObjectMixedBinder.native_headTerm w c C d z n

example {m} (w c C d z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.headCodeSentence w c C d z)) :=
  Internal.ObjectMixedBinder.native_headCode w c C d z

example {m} (w c C d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.headExistsSentence w c C d)) :=
  Internal.ObjectMixedBinder.native_headExists w c C d

example {m} (w C d z n Z N : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.headUniqueSentence w C d z n Z N)) :=
  Internal.ObjectMixedBinder.native_headUnique w C d z n Z N

example {m} (w R S r s a b c d A C n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.preparedExistsSentence w R S r s a b c d A C n)) :=
  Internal.ObjectMixedBinder.native_preparedExists w R S r s a b c d A C n

example {m} (w R S r s a b c d A C n k h K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.preparedUniqueSentence w R S r s a b c d A C n k h K H)) :=
  Internal.ObjectMixedBinder.native_preparedUnique w R S r s a b c d A C n k h K H

example {m} (w R S r s a b c d A C n k h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.preparedTargetSentence w R S r s a b c d A C n k h)) :=
  Internal.ObjectMixedBinder.native_preparedTarget w R S r s a b c d A C n k h

example {m} (w r s a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.actualStateSentence w r s a b c d A C)) :=
  Internal.ObjectMixedBinder.native_actualState w r s a b c d A C

example {m} (w r s a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.binderExistsSentence w r s a b c d A C)) :=
  Internal.ObjectMixedBinder.native_binderExists w r s a b c d A C

example {m} (w r s a b c d A C k h K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.binderUniqueSentence w r s a b c d A C k h K H)) :=
  Internal.ObjectMixedBinder.native_binderUnique w r s a b c d A C k h K H

example {m} (w r s a b c d A C k h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.binderTargetSentence w r s a b c d A C k h)) :=
  Internal.ObjectMixedBinder.native_binderTarget w r s a b c d A C k h

example {m} (w r s a b c d A C k h R S z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.binderAtWitnessesSentence w r s a b c d A C k h R S z n)) :=
  Internal.ObjectMixedBinder.native_binderAtWitnesses w r s a b c d A C k h R S z n

example {m} (w r s a b c d A C k h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.binderInputSentence w r s a b c d A C k h)) :=
  Internal.ObjectMixedBinder.native_binderInput w r s a b c d A C k h

example {m} (w r s a b c d A C k h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.binderUniquePairSentence w r s a b c d A C k h)) :=
  Internal.ObjectMixedBinder.native_binderUniquePair w r s a b c d A C k h

example {m} (w r s a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.binderFiberSentence w r s a b c d A C)) :=
  Internal.ObjectMixedBinder.native_binderFiber w r s a b c d A C

example {m} (w r s a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.binderExistsIffSentence w r s a b c d A C)) :=
  Internal.ObjectMixedBinder.native_binderExistsIff w r s a b c d A C

example {m} (w r s a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.binderFiberIffSentence w r s a b c d A C)) :=
  Internal.ObjectMixedBinder.native_binderFiberIff w r s a b c d A C

example {m} (w r s a b c d A C k h R S z n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.binderZeroSentence w r s a b c d A C k h R S z n q)) :=
  Internal.ObjectMixedBinder.native_binderZero w r s a b c d A C k h R S z n q

example {m} (w r s a b c d A C k h R S z n i j t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.binderBoundSentence w r s a b c d A C k h R S z n i j t q)) :=
  Internal.ObjectMixedBinder.native_binderBound w r s a b c d A C k h R S z n i j t q

example {m} (w r s a b c d A C k h R S z n j t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedBinder.binderFreeSentence w r s a b c d A C k h R S z n j t q)) :=
  Internal.ObjectMixedBinder.native_binderFree w r s a b c d A C k h R S z n j t q

example {m} (w f a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.listTypeSentence w f a c d L)) :=
  Internal.ObjectMixedEnvironment.native_listType w f a c d L

example {m} (w f a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.fromFieldsSentence w f a c d L)) :=
  Internal.ObjectMixedEnvironment.native_fromFields w f a c d L

example {m} (w a c d L i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.fieldTypeSentence w a c d L i q)) :=
  Internal.ObjectMixedEnvironment.native_fieldType w a c d L i q

example {m} (w f a c d L i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.imageEdgesSentence w f a c d L i q)) :=
  Internal.ObjectMixedEnvironment.native_imageEdges w f a c d L i q

example {m} (w f a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.codeExistsSentence w f a c d)) :=
  Internal.ObjectMixedEnvironment.native_codeExists w f a c d

example {m} (w a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.graphExistsSentence w a c d L)) :=
  Internal.ObjectMixedEnvironment.native_graphExists w a c d L

example {m} (w f a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.codeInputIffSentence w f a c d)) :=
  Internal.ObjectMixedEnvironment.native_codeInputIff w f a c d

example {m} (w a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.graphInputIffSentence w a c d L)) :=
  Internal.ObjectMixedEnvironment.native_graphInputIff w a c d L

example {m} (w f a c d L M : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.codeUniqueSentence w f a c d L M)) :=
  Internal.ObjectMixedEnvironment.native_codeUnique w f a c d L M

example {m} (w f g a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.graphUniqueSentence w f g a c d L)) :=
  Internal.ObjectMixedEnvironment.native_graphUnique w f g a c d L

example {m} (w f a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.atEncodingSentence w f a c d L)) :=
  Internal.ObjectMixedEnvironment.native_atEncoding w f a c d L

example {m} (w f a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.codeFiberSentence w f a c d)) :=
  Internal.ObjectMixedEnvironment.native_codeFiber w f a c d

example {m} (w f a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.codeFiberIffSentence w f a c d)) :=
  Internal.ObjectMixedEnvironment.native_codeFiberIff w f a c d

example {m} (w a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.graphFiberSentence w a c d L)) :=
  Internal.ObjectMixedEnvironment.native_graphFiber w a c d L

example {m} (w a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.graphFiberIffSentence w a c d L)) :=
  Internal.ObjectMixedEnvironment.native_graphFiberIff w a c d L

example {m} (w r s a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.pairCodesSentence w r s a b c d)) :=
  Internal.ObjectMixedEnvironment.native_pairCodes w r s a b c d

example {m} (w a b c d R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.pairGraphsSentence w a b c d R S)) :=
  Internal.ObjectMixedEnvironment.native_pairGraphs w a b c d R S

example {m} (w r s a b c d R S u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.pairGraphUniqueSentence w r s a b c d R S u v)) :=
  Internal.ObjectMixedEnvironment.native_pairGraphUnique w r s a b c d R S u v

example {m} (w r s a b c d R S U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.pairCodeUniqueSentence w r s a b c d R S U V)) :=
  Internal.ObjectMixedEnvironment.native_pairCodeUnique w r s a b c d R S U V

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.termInputSentence w R S a b c d n q)) :=
  Internal.ObjectMixedEnvironment.native_termInput w R S a b c d n q

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.termSourceSentence w R S a b c d n q)) :=
  Internal.ObjectMixedEnvironment.native_termSource w R S a b c d n q

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.termTargetSentence w R S a b c d n q)) :=
  Internal.ObjectMixedEnvironment.native_termTarget w R S a b c d n q

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.termNaturalSentence w R S a b c d n q)) :=
  Internal.ObjectMixedEnvironment.native_termNatural w R S a b c d n q

example {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.termExistsSentence w R S a b c d n)) :=
  Internal.ObjectMixedEnvironment.native_termExists w R S a b c d n

example {m} (w R S a b c d n q r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.termAtGraphsSentence w R S a b c d n q r s)) :=
  Internal.ObjectMixedEnvironment.native_termAtGraphs w R S a b c d n q r s

example {m} (w R S a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.termUniqueSentence w R S a b c d n q v)) :=
  Internal.ObjectMixedEnvironment.native_termUnique w R S a b c d n q v

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.termUniqueOutputSentence w R S a b c d n q)) :=
  Internal.ObjectMixedEnvironment.native_termUniqueOutput w R S a b c d n q

example {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.termFiberSentence w R S a b c d n)) :=
  Internal.ObjectMixedEnvironment.native_termFiber w R S a b c d n

example {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.termExistsIffSentence w R S a b c d n)) :=
  Internal.ObjectMixedEnvironment.native_termExistsIff w R S a b c d n

example {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.termFiberIffSentence w R S a b c d n)) :=
  Internal.ObjectMixedEnvironment.native_termFiberIff w R S a b c d n

example {m} (bound : Bool) (w R S a b c d n q i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.termFieldSentence bound w R S a b c d n q i)) :=
  Internal.ObjectMixedEnvironment.native_termField bound w R S a b c d n q i

example {m} (w R S a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.binderExistsSentence w R S a b c d A C)) :=
  Internal.ObjectMixedEnvironment.native_binderExists w R S a b c d A C

example {m} (w R S a b c d A C K H U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.binderUniqueSentence w R S a b c d A C K H U V)) :=
  Internal.ObjectMixedEnvironment.native_binderUnique w R S a b c d A C K H U V

example {m} (w R S a b c d A C K H r s k h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.binderAtGraphsSentence w R S a b c d A C K H r s k h)) :=
  Internal.ObjectMixedEnvironment.native_binderAtGraphs w R S a b c d A C K H r s k h

example {m} (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.binderInputListsSentence w R S a b c d A C K H)) :=
  Internal.ObjectMixedEnvironment.native_binderInputLists w R S a b c d A C K H

example {m} (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.binderOutputListsSentence w R S a b c d A C K H)) :=
  Internal.ObjectMixedEnvironment.native_binderOutputLists w R S a b c d A C K H

example {m} (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.binderInputSentence w R S a b c d A C K H)) :=
  Internal.ObjectMixedEnvironment.native_binderInput w R S a b c d A C K H

example {m} (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.binderNaturalSentence w R S a b c d A C K H)) :=
  Internal.ObjectMixedEnvironment.native_binderNatural w R S a b c d A C K H

example {m} (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.binderUniqueOutputSentence w R S a b c d A C K H)) :=
  Internal.ObjectMixedEnvironment.native_binderUniqueOutput w R S a b c d A C K H

example {m} (w R S a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.binderFiberSentence w R S a b c d A C)) :=
  Internal.ObjectMixedEnvironment.native_binderFiber w R S a b c d A C

example {m} (w R S a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.binderExistsIffSentence w R S a b c d A C)) :=
  Internal.ObjectMixedEnvironment.native_binderExistsIff w R S a b c d A C

example {m} (w R S a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.binderFiberIffSentence w R S a b c d A C)) :=
  Internal.ObjectMixedEnvironment.native_binderFiberIff w R S a b c d A C

example {m} (w R S a b c d A C K H U V z n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.binderZeroSentence w R S a b c d A C K H U V z n q)) :=
  Internal.ObjectMixedEnvironment.native_binderZero w R S a b c d A C K H U V z n q

example {m} (w R S a b c d A C K H U V z n i j t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.binderBoundSentence w R S a b c d A C K H U V z n i j t q)) :=
  Internal.ObjectMixedEnvironment.native_binderBound w R S a b c d A C K H U V z n i j t q

example {m} (w R S a b c d A C K H U V z n j t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedEnvironment.binderFreeSentence w R S a b c d A C K H U V z n j t q)) :=
  Internal.ObjectMixedEnvironment.native_binderFree w R S a b c d A C K H U V z n j t q

example {m} (w r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.stateExistsSentence w r s a b c d q)) :=
  Internal.ObjectMixedFormula.native_stateExists w r s a b c d q

example {m} (w r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.stateInputIffSentence w r s a b c d q)) :=
  Internal.ObjectMixedFormula.native_stateInputIff w r s a b c d q

example {m} (w r s a b c d q t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.stateNaturalSentence w r s a b c d q t)) :=
  Internal.ObjectMixedFormula.native_stateNatural w r s a b c d q t

example {m} (w r s a b c d q t v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.stateUniqueSentence w r s a b c d q t v)) :=
  Internal.ObjectMixedFormula.native_stateUnique w r s a b c d q t v

example {m} (w t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.stateDecodeSentence w t)) :=
  Internal.ObjectMixedFormula.native_stateDecode w t

example {m} (w t r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.stateParamsUniqueSentence w t r s a b c d q)) :=
  Internal.ObjectMixedFormula.native_stateParamsUnique w t r s a b c d q

example {m} (w v r s a b c d q t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.containsAtStateSentence w v r s a b c d q t)) :=
  Internal.ObjectMixedFormula.native_containsAtState w v r s a b c d q t

example {m} (w h D x v r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.readAtValueSentence w h D x v r s a b c d q)) :=
  Internal.ObjectMixedFormula.native_readAtValue w h D x v r s a b c d q

example {m} (w h D x v r s a b c d q t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.readAtStateSentence w h D x v r s a b c d q t)) :=
  Internal.ObjectMixedFormula.native_readAtState w h D x v r s a b c d q t

example {m} (w h x r s a b c d q A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.advancedQuerySentence w h x r s a b c d q A C K H)) :=
  Internal.ObjectMixedFormula.native_advancedQuery w h x r s a b c d q A C K H

example {m} (w n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.operatorExistsSentence w n h)) :=
  Internal.ObjectMixedFormula.native_operatorExists w n h

example {m} (w n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.operatorFiberSentence w n h)) :=
  Internal.ObjectMixedFormula.native_operatorFiber w n h

example {m} (w n h v t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.operatorUniqueSentence w n h v t)) :=
  Internal.ObjectMixedFormula.native_operatorUnique w n h v t

example {m} (w n h v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.operatorSubsetSentence w n h v)) :=
  Internal.ObjectMixedFormula.native_operatorSubset w n h v

example {m} (w n h v p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.operatorRecognizedSentence w n h v p)) :=
  Internal.ObjectMixedFormula.native_operatorRecognized w n h v p

example {m} (w n h v p r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.operatorMembershipSentence w n h v p r s a b c d q)) :=
  Internal.ObjectMixedFormula.native_operatorMembership w n h v p r s a b c d q

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.recursorsSentence w)) :=
  Internal.ObjectMixedFormula.native_recursors w

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.carrierSentence w)) :=
  Internal.ObjectMixedFormula.native_carrier w

example {m} (w D : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.graphExistsSentence w D)) :=
  Internal.ObjectMixedFormula.native_graphExists w D

example {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.evaluationExistsSentence w n)) :=
  Internal.ObjectMixedFormula.native_evaluationExists w n

example {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.evaluationFiberSentence w n)) :=
  Internal.ObjectMixedFormula.native_evaluationFiber w n

example {m} (w n v t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.evaluationUniqueSentence w n v t)) :=
  Internal.ObjectMixedFormula.native_evaluationUnique w n v t

example {m} (w n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.historySentence w n v)) :=
  Internal.ObjectMixedFormula.native_history w n v

example {m} (w h D x r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.judgmentReadSentence w h D x r s a b c d q)) :=
  Internal.ObjectMixedFormula.native_judgmentRead w h D x r s a b c d q

example {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.formulaSourceSentence w r s a b c d n q)) :=
  Internal.ObjectMixedFormula.native_formulaSource w r s a b c d n q

example {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.formulaTargetSentence w r s a b c d n q)) :=
  Internal.ObjectMixedFormula.native_formulaTarget w r s a b c d n q

example {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.formulaLegalSentence w r s a b c d n q)) :=
  Internal.ObjectMixedFormula.native_formulaLegal w r s a b c d n q

example {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.formulaInputSentence w r s a b c d n q)) :=
  Internal.ObjectMixedFormula.native_formulaInput w r s a b c d n q

example {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.formulaNaturalSentence w r s a b c d n q)) :=
  Internal.ObjectMixedFormula.native_formulaNatural w r s a b c d n q

example {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.recursiveIffSentence w r s a b c d n q)) :=
  Internal.ObjectMixedFormula.native_recursiveIff w r s a b c d n q

example {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.formulaFiberSentence w r s a b c d n)) :=
  Internal.ObjectMixedFormula.native_formulaFiber w r s a b c d n

example {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.formulaExistsSentence w r s a b c d n)) :=
  Internal.ObjectMixedFormula.native_formulaExists w r s a b c d n

example {m} (w r s a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.formulaUniqueSentence w r s a b c d n q v)) :=
  Internal.ObjectMixedFormula.native_formulaUnique w r s a b c d n q v

example {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.formulaUniqueOutputSentence w r s a b c d n q)) :=
  Internal.ObjectMixedFormula.native_formulaUniqueOutput w r s a b c d n q

example {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.formulaExistsIffSentence w r s a b c d n)) :=
  Internal.ObjectMixedFormula.native_formulaExistsIff w r s a b c d n

example {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.formulaFiberIffSentence w r s a b c d n)) :=
  Internal.ObjectMixedFormula.native_formulaFiberIff w r s a b c d n

example {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.formulaRejectInvalidSentence w r s a b c d n)) :=
  Internal.ObjectMixedFormula.native_formulaRejectInvalid w r s a b c d n

example {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.nullaryFalseSentence w r s a b c d n q)) :=
  Internal.ObjectMixedFormula.native_nullaryFalse w r s a b c d n q

example {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.nullaryTrueSentence w r s a b c d n q)) :=
  Internal.ObjectMixedFormula.native_nullaryTrue w r s a b c d n q

example {m} (w r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.equalityFieldsSentence w r s a b c d n q x y X Y)) :=
  Internal.ObjectMixedFormula.native_equalityFields w r s a b c d n q x y X Y

example {m} (w r s a b c d n q z Z x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.membershipFieldsSentence w r s a b c d n q z Z x y X Y)) :=
  Internal.ObjectMixedFormula.native_membershipFields w r s a b c d n q z Z x y X Y

example {m} (w r s a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.negationFieldsSentence w r s a b c d n q x X)) :=
  Internal.ObjectMixedFormula.native_negationFields w r s a b c d n q x X

example {m} (w r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.binary0FieldsSentence w r s a b c d n q x y X Y)) :=
  Internal.ObjectMixedFormula.native_binary0Fields w r s a b c d n q x y X Y

example {m} (w r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.binary1FieldsSentence w r s a b c d n q x y X Y)) :=
  Internal.ObjectMixedFormula.native_binary1Fields w r s a b c d n q x y X Y

example {m} (w r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.binary2FieldsSentence w r s a b c d n q x y X Y)) :=
  Internal.ObjectMixedFormula.native_binary2Fields w r s a b c d n q x y X Y

example {m} (w r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.binary3FieldsSentence w r s a b c d n q x y X Y)) :=
  Internal.ObjectMixedFormula.native_binary3Fields w r s a b c d n q x y X Y

example {m} (w r s a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.forallFieldsSentence w r s a b c d n q x X)) :=
  Internal.ObjectMixedFormula.native_forallFields w r s a b c d n q x X

example {m} (w r s a b c d n q x X A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.forallAtLiftSentence w r s a b c d n q x X A C K H)) :=
  Internal.ObjectMixedFormula.native_forallAtLift w r s a b c d n q x X A C K H

example {m} (w r s a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.existsFieldsSentence w r s a b c d n q x X)) :=
  Internal.ObjectMixedFormula.native_existsFields w r s a b c d n q x X

example {m} (w r s a b c d n q x X A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectMixedFormula.existsAtLiftSentence w r s a b c d n q x X A C K H)) :=
  Internal.ObjectMixedFormula.native_existsAtLift w r s a b c d n q x X A C K H

example {m} (bound : Bool) (w r a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.variableImageExistsSentence bound w r a c d)) :=
  Internal.ObjectTopEnvironment.native_variableImageExists bound w r a c d

example {m} (bound : Bool) (w r a c d f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.variableImageUniqueSentence bound w r a c d f g)) :=
  Internal.ObjectTopEnvironment.native_variableImageUnique bound w r a c d f g

example {m} (bound : Bool) (w r a c d f i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.variableImageEdgesSentence bound w r a c d f i q)) :=
  Internal.ObjectTopEnvironment.native_variableImageEdges bound w r a c d f i q

example {m} (bound : Bool) (w r a c d f i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.variableImageAtIndexSentence bound w r a c d f i j q)) :=
  Internal.ObjectTopEnvironment.native_variableImageAtIndex bound w r a c d f i j q

example {m} (bound : Bool) (w c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.identityTableExistsSentence bound w c d)) :=
  Internal.ObjectTopEnvironment.native_identityTableExists bound w c d

example {m} (bound : Bool) (w a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.shiftedTableExistsSentence bound w a c d)) :=
  Internal.ObjectTopEnvironment.native_shiftedTableExists bound w a c d

example {m} (bound : Bool) (w c d f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.identityTableUniqueSentence bound w c d f g)) :=
  Internal.ObjectTopEnvironment.native_identityTableUnique bound w c d f g

example {m} (bound : Bool) (w a c d f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.shiftedTableUniqueSentence bound w a c d f g)) :=
  Internal.ObjectTopEnvironment.native_shiftedTableUnique bound w a c d f g

example {m} (bound : Bool) (w c d f i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.identityTableAtSentence bound w c d f i q)) :=
  Internal.ObjectTopEnvironment.native_identityTableAt bound w c d f i q

example {m} (bound : Bool) (w a c d f i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.shiftedTableAtSentence bound w a c d f i j q)) :=
  Internal.ObjectTopEnvironment.native_shiftedTableAt bound w a c d f i j q

example {m} (w a b A t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.instantiateActualExistsSentence w a b A t)) :=
  Internal.ObjectTopEnvironment.native_instantiateActualExists w a b A t

example {m} (w a b A t f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.instantiateActualInputSentence w a b A t f g)) :=
  Internal.ObjectTopEnvironment.native_instantiateActualInput w a b A t f g

example {m} (w a b A t f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.instantiateActualMapsSentence w a b A t f g)) :=
  Internal.ObjectTopEnvironment.native_instantiateActualMaps w a b A t f g

example {m} (w a b A t f g F G : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.instantiateActualUniqueSentence w a b A t f g F G)) :=
  Internal.ObjectTopEnvironment.native_instantiateActualUnique w a b A t f g F G

example {m} (w a b A t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.instantiateCodeExistsSentence w a b A t)) :=
  Internal.ObjectTopEnvironment.native_instantiateCodeExists w a b A t

example {m} (w a b A t R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.instantiateCodeInputSentence w a b A t R S)) :=
  Internal.ObjectTopEnvironment.native_instantiateCodeInput w a b A t R S

example {m} (w a b A t R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.instantiateCodeListsSentence w a b A t R S)) :=
  Internal.ObjectTopEnvironment.native_instantiateCodeLists w a b A t R S

example {m} (w a b A t R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.instantiateCodeNaturalSentence w a b A t R S)) :=
  Internal.ObjectTopEnvironment.native_instantiateCodeNatural w a b A t R S

example {m} (w a b A t R S U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.instantiateCodeUniqueSentence w a b A t R S U V)) :=
  Internal.ObjectTopEnvironment.native_instantiateCodeUnique w a b A t R S U V

example {m} (w a b A t R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.instantiateCodeUniqueOutputSentence w a b A t R S)) :=
  Internal.ObjectTopEnvironment.native_instantiateCodeUniqueOutput w a b A t R S

example {m} (w a b A t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.instantiateCodeFiberSentence w a b A t)) :=
  Internal.ObjectTopEnvironment.native_instantiateCodeFiber w a b A t

example {m} (w a b A t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.instantiateCodeExistsIffSentence w a b A t)) :=
  Internal.ObjectTopEnvironment.native_instantiateCodeExistsIff w a b A t

example {m} (w a b A t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.instantiateCodeFiberIffSentence w a b A t)) :=
  Internal.ObjectTopEnvironment.native_instantiateCodeFiberIff w a b A t

example {m} (w a b A t R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.instantiateFormulaFiberSentence w a b A t R S n)) :=
  Internal.ObjectTopEnvironment.native_instantiateFormulaFiber w a b A t R S n

example {m} (w a b A t R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.instantiateFormulaExistsSentence w a b A t R S n)) :=
  Internal.ObjectTopEnvironment.native_instantiateFormulaExists w a b A t R S n

example {m} (w a b A t f g i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.instantiateActualZeroSentence w a b A t f g i q)) :=
  Internal.ObjectTopEnvironment.native_instantiateActualZero w a b A t f g i q

example {m} (w a b A t R S i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.instantiateCodeZeroSentence w a b A t R S i q)) :=
  Internal.ObjectTopEnvironment.native_instantiateCodeZero w a b A t R S i q

example {m} (w a b A t f g i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.instantiateActualBoundSentence w a b A t f g i j q)) :=
  Internal.ObjectTopEnvironment.native_instantiateActualBound w a b A t f g i j q

example {m} (w a b A t R S i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.instantiateCodeBoundSentence w a b A t R S i j q)) :=
  Internal.ObjectTopEnvironment.native_instantiateCodeBound w a b A t R S i j q

example {m} (w a b A t f g i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.instantiateActualFreeSentence w a b A t f g i q)) :=
  Internal.ObjectTopEnvironment.native_instantiateActualFree w a b A t f g i q

example {m} (w a b A t R S i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.instantiateCodeFreeSentence w a b A t R S i q)) :=
  Internal.ObjectTopEnvironment.native_instantiateCodeFree w a b A t R S i q

example {m} (w a b A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.abstractActualExistsSentence w a b A B)) :=
  Internal.ObjectTopEnvironment.native_abstractActualExists w a b A B

example {m} (w a b A B f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.abstractActualInputSentence w a b A B f g)) :=
  Internal.ObjectTopEnvironment.native_abstractActualInput w a b A B f g

example {m} (w a b A B f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.abstractActualMapsSentence w a b A B f g)) :=
  Internal.ObjectTopEnvironment.native_abstractActualMaps w a b A B f g

example {m} (w a b A B f g F G : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.abstractActualUniqueSentence w a b A B f g F G)) :=
  Internal.ObjectTopEnvironment.native_abstractActualUnique w a b A B f g F G

example {m} (w a b A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.abstractCodeExistsSentence w a b A B)) :=
  Internal.ObjectTopEnvironment.native_abstractCodeExists w a b A B

example {m} (w a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.abstractCodeInputSentence w a b A B R S)) :=
  Internal.ObjectTopEnvironment.native_abstractCodeInput w a b A B R S

example {m} (w a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.abstractCodeListsSentence w a b A B R S)) :=
  Internal.ObjectTopEnvironment.native_abstractCodeLists w a b A B R S

example {m} (w a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.abstractCodeNaturalSentence w a b A B R S)) :=
  Internal.ObjectTopEnvironment.native_abstractCodeNatural w a b A B R S

example {m} (w a b A B R S U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.abstractCodeUniqueSentence w a b A B R S U V)) :=
  Internal.ObjectTopEnvironment.native_abstractCodeUnique w a b A B R S U V

example {m} (w a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.abstractCodeUniqueOutputSentence w a b A B R S)) :=
  Internal.ObjectTopEnvironment.native_abstractCodeUniqueOutput w a b A B R S

example {m} (w a b A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.abstractCodeFiberSentence w a b A B)) :=
  Internal.ObjectTopEnvironment.native_abstractCodeFiber w a b A B

example {m} (w a b A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.abstractCodeExistsIffSentence w a b A B)) :=
  Internal.ObjectTopEnvironment.native_abstractCodeExistsIff w a b A B

example {m} (w a b A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.abstractCodeFiberIffSentence w a b A B)) :=
  Internal.ObjectTopEnvironment.native_abstractCodeFiberIff w a b A B

example {m} (w a b A B R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.abstractFormulaFiberSentence w a b A B R S n)) :=
  Internal.ObjectTopEnvironment.native_abstractFormulaFiber w a b A B R S n

example {m} (w a b A B R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.abstractFormulaExistsSentence w a b A B R S n)) :=
  Internal.ObjectTopEnvironment.native_abstractFormulaExists w a b A B R S n

example {m} (w a b A B f g i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.abstractActualZeroSentence w a b A B f g i q)) :=
  Internal.ObjectTopEnvironment.native_abstractActualZero w a b A B f g i q

example {m} (w a b A B R S i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.abstractCodeZeroSentence w a b A B R S i q)) :=
  Internal.ObjectTopEnvironment.native_abstractCodeZero w a b A B R S i q

example {m} (w a b A B f g i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.abstractActualBoundSentence w a b A B f g i j q)) :=
  Internal.ObjectTopEnvironment.native_abstractActualBound w a b A B f g i j q

example {m} (w a b A B R S i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.abstractCodeBoundSentence w a b A B R S i j q)) :=
  Internal.ObjectTopEnvironment.native_abstractCodeBound w a b A B R S i j q

example {m} (w a b A B f g i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.abstractActualFreeSentence w a b A B f g i j q)) :=
  Internal.ObjectTopEnvironment.native_abstractActualFree w a b A B f g i j q

example {m} (w a b A B R S i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopEnvironment.abstractCodeFreeSentence w a b A B R S i j q)) :=
  Internal.ObjectTopEnvironment.native_abstractCodeFree w a b A B R S i j q

example {m} (w a b A t n q R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.instantiateAtCodesSentence w a b A t n q R S)) :=
  Internal.ObjectTopFormula.native_instantiateAtCodes w a b A t n q R S

example {m} (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.instantiateEnvironmentSentence w a b A t n q)) :=
  Internal.ObjectTopFormula.native_instantiateEnvironment w a b A t n q

example {m} (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.instantiateSourceTypeSentence w a b A t n q)) :=
  Internal.ObjectTopFormula.native_instantiateSourceType w a b A t n q

example {m} (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.instantiateTargetTypeSentence w a b A t n q)) :=
  Internal.ObjectTopFormula.native_instantiateTargetType w a b A t n q

example {m} (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.instantiateSourceNaturalSentence w a b A t n q)) :=
  Internal.ObjectTopFormula.native_instantiateSourceNatural w a b A t n q

example {m} (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.instantiateInputSentence w a b A t n q)) :=
  Internal.ObjectTopFormula.native_instantiateInput w a b A t n q

example {m} (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.instantiateTargetNaturalSentence w a b A t n q)) :=
  Internal.ObjectTopFormula.native_instantiateTargetNatural w a b A t n q

example {m} (w a b A t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.instantiateExistsSentence w a b A t n)) :=
  Internal.ObjectTopFormula.native_instantiateExists w a b A t n

example {m} (w a b A t n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.instantiateUniqueSentence w a b A t n q v)) :=
  Internal.ObjectTopFormula.native_instantiateUnique w a b A t n q v

example {m} (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.instantiateUniqueOutputSentence w a b A t n q)) :=
  Internal.ObjectTopFormula.native_instantiateUniqueOutput w a b A t n q

example {m} (w a b A t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.instantiateFiberSentence w a b A t n)) :=
  Internal.ObjectTopFormula.native_instantiateFiber w a b A t n

example {m} (w a b A t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.instantiateExistsIffSentence w a b A t n)) :=
  Internal.ObjectTopFormula.native_instantiateExistsIff w a b A t n

example {m} (w a b A t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.instantiateFiberIffSentence w a b A t n)) :=
  Internal.ObjectTopFormula.native_instantiateFiberIff w a b A t n

example {m} (w a b A t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.instantiateRejectInputSentence w a b A t n)) :=
  Internal.ObjectTopFormula.native_instantiateRejectInput w a b A t n

example {m} (truth : Bool) (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.instantiateNullarySentence truth w a b A t n q)) :=
  Internal.ObjectTopFormula.native_instantiateNullary truth w a b A t n q

example {m} (w a b A t n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.instantiateNegationSentence w a b A t n q x X)) :=
  Internal.ObjectTopFormula.native_instantiateNegation w a b A t n q x X

example {m} (kind : Fin 4) (w a b A t n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.instantiateBinarySentence kind w a b A t n q x y X Y)) :=
  Internal.ObjectTopFormula.native_instantiateBinary kind w a b A t n q x y X Y

example {m} (w a b A t n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.instantiateEqualSentence w a b A t n q x y X Y)) :=
  Internal.ObjectTopFormula.native_instantiateEqual w a b A t n q x y X Y

example {m} (w a b A t n q z Z x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.instantiateMemberSentence w a b A t n q z Z x y X Y)) :=
  Internal.ObjectTopFormula.native_instantiateMember w a b A t n q z Z x y X Y

example {m} (universal : Bool) (w a b A t n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.instantiateQuantifiedSentence universal w a b A t n q x X)) :=
  Internal.ObjectTopFormula.native_instantiateQuantified universal w a b A t n q x X

example {m} (w a b A B n q R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.abstractAtCodesSentence w a b A B n q R S)) :=
  Internal.ObjectTopFormula.native_abstractAtCodes w a b A B n q R S

example {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.abstractEnvironmentSentence w a b A B n q)) :=
  Internal.ObjectTopFormula.native_abstractEnvironment w a b A B n q

example {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.abstractSourceTypeSentence w a b A B n q)) :=
  Internal.ObjectTopFormula.native_abstractSourceType w a b A B n q

example {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.abstractTargetTypeSentence w a b A B n q)) :=
  Internal.ObjectTopFormula.native_abstractTargetType w a b A B n q

example {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.abstractSourceNaturalSentence w a b A B n q)) :=
  Internal.ObjectTopFormula.native_abstractSourceNatural w a b A B n q

example {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.abstractInputSentence w a b A B n q)) :=
  Internal.ObjectTopFormula.native_abstractInput w a b A B n q

example {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.abstractTargetNaturalSentence w a b A B n q)) :=
  Internal.ObjectTopFormula.native_abstractTargetNatural w a b A B n q

example {m} (w a b A B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.abstractExistsSentence w a b A B n)) :=
  Internal.ObjectTopFormula.native_abstractExists w a b A B n

example {m} (w a b A B n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.abstractUniqueSentence w a b A B n q v)) :=
  Internal.ObjectTopFormula.native_abstractUnique w a b A B n q v

example {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.abstractUniqueOutputSentence w a b A B n q)) :=
  Internal.ObjectTopFormula.native_abstractUniqueOutput w a b A B n q

example {m} (w a b A B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.abstractFiberSentence w a b A B n)) :=
  Internal.ObjectTopFormula.native_abstractFiber w a b A B n

example {m} (w a b A B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.abstractExistsIffSentence w a b A B n)) :=
  Internal.ObjectTopFormula.native_abstractExistsIff w a b A B n

example {m} (w a b A B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.abstractFiberIffSentence w a b A B n)) :=
  Internal.ObjectTopFormula.native_abstractFiberIff w a b A B n

example {m} (w a b A B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.abstractRejectInputSentence w a b A B n)) :=
  Internal.ObjectTopFormula.native_abstractRejectInput w a b A B n

example {m} (truth : Bool) (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.abstractNullarySentence truth w a b A B n q)) :=
  Internal.ObjectTopFormula.native_abstractNullary truth w a b A B n q

example {m} (w a b A B n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.abstractNegationSentence w a b A B n q x X)) :=
  Internal.ObjectTopFormula.native_abstractNegation w a b A B n q x X

example {m} (kind : Fin 4) (w a b A B n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.abstractBinarySentence kind w a b A B n q x y X Y)) :=
  Internal.ObjectTopFormula.native_abstractBinary kind w a b A B n q x y X Y

example {m} (w a b A B n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.abstractEqualSentence w a b A B n q x y X Y)) :=
  Internal.ObjectTopFormula.native_abstractEqual w a b A B n q x y X Y

example {m} (w a b A B n q z Z x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.abstractMemberSentence w a b A B n q z Z x y X Y)) :=
  Internal.ObjectTopFormula.native_abstractMember w a b A B n q z Z x y X Y

example {m} (universal : Bool) (w a b A B n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTopFormula.abstractQuantifiedSentence universal w a b A B n q x X)) :=
  Internal.ObjectTopFormula.native_abstractQuantified universal w a b A B n q x X

example {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalQuotation.treeExistsSentence input w)) :=
  Internal.ObjectOriginalQuotation.native_treeExists input w

example {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalQuotation.treeRangeSentence input w n)) :=
  Internal.ObjectOriginalQuotation.native_treeRange input w n

example {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalQuotation.treeUniqueSentence input w n v)) :=
  Internal.ObjectOriginalQuotation.native_treeUnique input w n v

example {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalQuotation.treeUniqueOutputSentence input w n)) :=
  Internal.ObjectOriginalQuotation.native_treeUniqueOutput input w n

example {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalQuotation.treeFiberSentence input w)) :=
  Internal.ObjectOriginalQuotation.native_treeFiber input w

example {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalQuotation.forestExistsSentence input w)) :=
  Internal.ObjectOriginalQuotation.native_forestExists input w

example {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalQuotation.forestRangeSentence input w n)) :=
  Internal.ObjectOriginalQuotation.native_forestRange input w n

example {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalQuotation.forestUniqueSentence input w n v)) :=
  Internal.ObjectOriginalQuotation.native_forestUnique input w n v

example {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalQuotation.forestUniqueOutputSentence input w n)) :=
  Internal.ObjectOriginalQuotation.native_forestUniqueOutput input w n

example {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalQuotation.forestFiberSentence input w)) :=
  Internal.ObjectOriginalQuotation.native_forestFiber input w

example {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalQuotation.termExistsSentence input w)) :=
  Internal.ObjectOriginalQuotation.native_termExists input w

example {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalQuotation.termRangeSentence input w n)) :=
  Internal.ObjectOriginalQuotation.native_termRange input w n

example {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalQuotation.termUniqueSentence input w n v)) :=
  Internal.ObjectOriginalQuotation.native_termUnique input w n v

example {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalQuotation.termFiberSentence input w)) :=
  Internal.ObjectOriginalQuotation.native_termFiber input w

example {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalQuotation.formulaExistsSentence input w)) :=
  Internal.ObjectOriginalQuotation.native_formulaExists input w

example {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalQuotation.formulaRangeSentence input w n)) :=
  Internal.ObjectOriginalQuotation.native_formulaRange input w n

example {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalQuotation.formulaUniqueSentence input w n v)) :=
  Internal.ObjectOriginalQuotation.native_formulaUnique input w n v

example {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalQuotation.formulaFiberSentence input w)) :=
  Internal.ObjectOriginalQuotation.native_formulaFiber input w

example {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.fieldNaturalSentence children xs w)) :=
  Internal.ObjectQuotationFields.native_fieldNatural children xs w

example {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (i : Fin children.length) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.fieldAtSentence children xs i w)) :=
  Internal.ObjectQuotationFields.native_fieldAt children xs i w

example {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.forestOfFieldsSentence children xs w p)) :=
  Internal.ObjectQuotationFields.native_forestOfFields children xs w p

example {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.forestToFieldsSentence children xs w p)) :=
  Internal.ObjectQuotationFields.native_forestToFields children xs w p

example {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.forestIffSentence children xs w p)) :=
  Internal.ObjectQuotationFields.native_forestIff children xs w p

example {m} (tag : Nat) (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.treeOfConstructorSentence tag children xs w n)) :=
  Internal.ObjectQuotationFields.native_treeOfConstructor tag children xs w n

example {m} (tag : Nat) (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.treeToConstructorSentence tag children xs w n)) :=
  Internal.ObjectQuotationFields.native_treeToConstructor tag children xs w n

example {m} (tag : Nat) (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.treeIffSentence tag children xs w n)) :=
  Internal.ObjectQuotationFields.native_treeIff tag children xs w n

example {m} (k : Nat) (w i n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.treeOfScalarSentence k w i n)) :=
  Internal.ObjectQuotationFields.native_treeOfScalar k w i n

example {m} (k : Nat) (w i n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.scalarOfTreeSentence k w i n)) :=
  Internal.ObjectQuotationFields.native_scalarOfTree k w i n

example {m} (k : Nat) (w i n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.scalarIffSentence k w i n)) :=
  Internal.ObjectQuotationFields.native_scalarIff k w i n

example {m} (bound : Bool) (k : Nat) (w i n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.treeOfVariableSentence bound k w i n)) :=
  Internal.ObjectQuotationFields.native_treeOfVariable bound k w i n

example {m} (bound : Bool) (k : Nat) (w i n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.variableOfTreeSentence bound k w i n)) :=
  Internal.ObjectQuotationFields.native_variableOfTree bound k w i n

example {m} (bound : Bool) (k : Nat) (w i n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.variableIffSentence bound k w i n)) :=
  Internal.ObjectQuotationFields.native_variableIff bound k w i n

example {m} (bLen fLen : Nat) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.contextsOfLengthsSentence bLen fLen w b f)) :=
  Internal.ObjectQuotationFields.native_contextsOfLengths bLen fLen w b f

example {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.termTypeSentence input w b f n)) :=
  Internal.ObjectQuotationFields.native_termType input w b f n

example {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.termTypedExistsSentence input w b f)) :=
  Internal.ObjectQuotationFields.native_termTypedExists input w b f

example {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.termTypedUniqueSentence input w b f n v)) :=
  Internal.ObjectQuotationFields.native_termTypedUnique input w b f n v

example {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.termTypedUniqueOutputSentence input w b f n)) :=
  Internal.ObjectQuotationFields.native_termTypedUniqueOutput input w b f n

example {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.termTypedFiberSentence input w b f)) :=
  Internal.ObjectQuotationFields.native_termTypedFiber input w b f

example {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.formulaTypeSentence input w b f n)) :=
  Internal.ObjectQuotationFields.native_formulaType input w b f n

example {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.formulaTypedExistsSentence input w b f)) :=
  Internal.ObjectQuotationFields.native_formulaTypedExists input w b f

example {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.formulaTypedUniqueSentence input w b f n v)) :=
  Internal.ObjectQuotationFields.native_formulaTypedUnique input w b f n v

example {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.formulaTypedUniqueOutputSentence input w b f n)) :=
  Internal.ObjectQuotationFields.native_formulaTypedUniqueOutput input w b f n

example {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.formulaTypedFiberSentence input w b f)) :=
  Internal.ObjectQuotationFields.native_formulaTypedFiber input w b f

example {m} (truth : Bool) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.nullaryTypeSentence truth w b f n)) :=
  Internal.ObjectQuotationFields.native_nullaryType truth w b f n

example {m} (left right : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.equalTypeSentence left right w b f n x y)) :=
  Internal.ObjectQuotationFields.native_equalType left right w b f n x y

example {m} (left right : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n s x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.memberTypeSentence left right w b f n s x y)) :=
  Internal.ObjectQuotationFields.native_memberType left right w b f n s x y

example {m} (body : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.negationTypeSentence body w b f n x)) :=
  Internal.ObjectQuotationFields.native_negationType body w b f n x

example {m} (kind : Fin 4) (left right : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.binaryTypeSentence kind left right w b f n x y)) :=
  Internal.ObjectQuotationFields.native_binaryType kind left right w b f n x y

example {m} (universal : Bool) (body : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n x k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectQuotationFields.quantifiedTypeSentence universal body w b f n x k)) :=
  Internal.ObjectQuotationFields.native_quantifiedType universal body w b f n x k

example {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermImageQuotation.quotationAtValueSentence input w n q)) :=
  Internal.ObjectTermImageQuotation.native_quotationAtValue input w n q

example {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (j : Fin children.length) (w n i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermImageQuotation.forestReadSentence children j w n i q)) :=
  Internal.ObjectTermImageQuotation.native_forestRead children j w n i q

example {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w n l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermImageQuotation.forestLengthSentence children w n l)) :=
  Internal.ObjectTermImageQuotation.native_forestLength children w n l

example {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (j : Fin values.length) (w L i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermImageQuotation.imageFieldSentence values j w L i q)) :=
  Internal.ObjectTermImageQuotation.native_imageField values j w L i q

example {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w L a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermImageQuotation.imageLengthSentence values w L a)) :=
  Internal.ObjectTermImageQuotation.native_imageLength values w L a

example {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermImageQuotation.imageRangeSentence values w L)) :=
  Internal.ObjectTermImageQuotation.native_imageRange values w L

example {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w L K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermImageQuotation.imageUniqueSentence values w L K)) :=
  Internal.ObjectTermImageQuotation.native_imageUnique values w L K

example {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermImageQuotation.imageExistsSentence values w)) :=
  Internal.ObjectTermImageQuotation.native_imageExists values w

example {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermImageQuotation.imageTypedFieldsSentence values w a c d L)) :=
  Internal.ObjectTermImageQuotation.native_imageTypedFields values w a c d L

example {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermImageQuotation.imageTermListSentence values w a c d L)) :=
  Internal.ObjectTermImageQuotation.native_imageTermList values w a c d L

example {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermImageQuotation.environmentExistsSentence bs fs w a b c d)) :=
  Internal.ObjectTermImageQuotation.native_environmentExists bs fs w a b c d

example {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermImageQuotation.environmentFiberSentence bs fs w a b c d)) :=
  Internal.ObjectTermImageQuotation.native_environmentFiber bs fs w a b c d

example {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d R S U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermImageQuotation.environmentUniqueSentence bs fs w a b c d R S U V)) :=
  Internal.ObjectTermImageQuotation.native_environmentUnique bs fs w a b c d R S U V

example {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermImageQuotation.environmentUniqueOutputSentence bs fs w a b c d R S)) :=
  Internal.ObjectTermImageQuotation.native_environmentUniqueOutput bs fs w a b c d R S

example {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (isBound : Bool) (j : Fin (TermQuotationSubstitution.selected isBound bs fs).length) (w a b c d R S n i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermImageQuotation.mixedAtIndexSentence bs fs isBound j w a b c d R S n i q)) :=
  Internal.ObjectTermImageQuotation.native_mixedAtIndex bs fs isBound j w a b c d R S n i q

example {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (isBound : Bool) (j : Fin (TermQuotationSubstitution.selected isBound bs fs).length) (w a b c d R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermImageQuotation.mixedTermSentence bs fs isBound j w a b c d R S n q)) :=
  Internal.ObjectTermImageQuotation.native_mixedTerm bs fs isBound j w a b c d R S n q

example {m} (isBound : Bool) (k bLen fLen : Nat) (hlt : k < (if isBound then bLen else fLen)) (w U V c d C n q i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermImageQuotation.shiftAtIndexSentence isBound k bLen fLen hlt w U V c d C n q i)) :=
  Internal.ObjectTermImageQuotation.native_shiftAtIndex isBound k bLen fLen hlt w U V c d C n q i

example {m} (isBound : Bool) (k bLen fLen : Nat) (hlt : k < (if isBound then bLen else fLen)) (w U V c d C n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermImageQuotation.shiftVariableSentence isBound k bLen fLen hlt w U V c d C n q)) :=
  Internal.ObjectTermImageQuotation.native_shiftVariable isBound k bLen fLen hlt w U V c d C n q

example {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w U V c d C n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermImageQuotation.shiftTermSentence input w U V c d C n q)) :=
  Internal.ObjectTermImageQuotation.native_shiftTerm input w U V c d C n q

example {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermLiftQuotation.readingsFromImagesSentence values w L)) :=
  Internal.ObjectTermLiftQuotation.native_readingsFromImages values w L

example {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (j : Fin values.length) (w L i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermLiftQuotation.readingsAtSentence values j w L i q)) :=
  Internal.ObjectTermLiftQuotation.native_readingsAt values j w L i q

example {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w a L V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermLiftQuotation.agreeFromReadingsSentence values w a L V)) :=
  Internal.ObjectTermLiftQuotation.native_agreeFromReadings values w a L V

example {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w a L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermLiftQuotation.imagesFromReadingsSentence values w a L)) :=
  Internal.ObjectTermLiftQuotation.native_imagesFromReadings values w a L

example {m} (w R S a b c d A C K H U V z n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermLiftQuotation.zeroFieldSentence w R S a b c d A C K H U V z n q)) :=
  Internal.ObjectTermLiftQuotation.native_zeroField w R S a b c d A C K H U V z n q

example {m} (w R S a b c d A C K H U V z n i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermLiftQuotation.zeroAtNumeralSentence w R S a b c d A C K H U V z n i q)) :=
  Internal.ObjectTermLiftQuotation.native_zeroAtNumeral w R S a b c d A C K H U V z n i q

example {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin bs.length) (w R S a b c d A C K H U V z n i v t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermLiftQuotation.boundAtCodeSentence bs fs j w R S a b c d A C K H U V z n i v t q)) :=
  Internal.ObjectTermLiftQuotation.native_boundAtCode bs fs j w R S a b c d A C K H U V z n i v t q

example {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin bs.length) (w R S a b c d A C K H U V z n i v q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermLiftQuotation.boundValueSentence bs fs j w R S a b c d A C K H U V z n i v q)) :=
  Internal.ObjectTermLiftQuotation.native_boundValue bs fs j w R S a b c d A C K H U V z n i v q

example {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin bs.length) (w R S a b c d A C K H U V z n i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermLiftQuotation.boundAtNumeralSentence bs fs j w R S a b c d A C K H U V z n i q)) :=
  Internal.ObjectTermLiftQuotation.native_boundAtNumeral bs fs j w R S a b c d A C K H U V z n i q

example {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermLiftQuotation.boundReadingsSentence bs fs w R S a b c d A C K H U V z n)) :=
  Internal.ObjectTermLiftQuotation.native_boundReadings bs fs w R S a b c d A C K H U V z n

example {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin fs.length) (w R S a b c d A C K H U V z n v t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermLiftQuotation.freeAtCodeSentence bs fs j w R S a b c d A C K H U V z n v t q)) :=
  Internal.ObjectTermLiftQuotation.native_freeAtCode bs fs j w R S a b c d A C K H U V z n v t q

example {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin fs.length) (w R S a b c d A C K H U V z n v q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermLiftQuotation.freeValueSentence bs fs j w R S a b c d A C K H U V z n v q)) :=
  Internal.ObjectTermLiftQuotation.native_freeValue bs fs j w R S a b c d A C K H U V z n v q

example {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermLiftQuotation.freeReadingsSentence bs fs w R S a b c d A C K H U V z n)) :=
  Internal.ObjectTermLiftQuotation.native_freeReadings bs fs w R S a b c d A C K H U V z n

example {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermLiftQuotation.environmentAtWitnessesSentence bs fs w R S a b c d A C K H U V z n)) :=
  Internal.ObjectTermLiftQuotation.native_environmentAtWitnesses bs fs w R S a b c d A C K H U V z n

example {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermLiftQuotation.environmentAtMapsSentence bs fs w R S a b c d A C K H U V)) :=
  Internal.ObjectTermLiftQuotation.native_environmentAtMaps bs fs w R S a b c d A C K H U V

example {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermLiftQuotation.environmentAtLiftedSentence bs fs w R S a b c d A C K H)) :=
  Internal.ObjectTermLiftQuotation.native_environmentAtLifted bs fs w R S a b c d A C K H

example {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermLiftQuotation.liftedFromEnvironmentSentence bs fs w R S a b c d A C K H)) :=
  Internal.ObjectTermLiftQuotation.native_liftedFromEnvironment bs fs w R S a b c d A C K H

example {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermLiftQuotation.liftedIffEnvironmentSentence bs fs w R S a b c d A C K H)) :=
  Internal.ObjectTermLiftQuotation.native_liftedIffEnvironment bs fs w R S a b c d A C K H

example {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermLiftQuotation.environmentFiberSentence bs fs w a b c d A C)) :=
  Internal.ObjectTermLiftQuotation.native_environmentFiber bs fs w a b c d A C

example {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermLiftQuotation.jointFiberSentence bs fs w R S a b c d A C)) :=
  Internal.ObjectTermLiftQuotation.native_jointFiber bs fs w R S a b c d A C

example {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (w a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeFormulaQuotation.environmentExistsSentence σ τ w a b c d)) :=
  Internal.ObjectNativeFormulaQuotation.native_environmentExists σ τ w a b c d

example {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (w a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeFormulaQuotation.environmentFiberSentence σ τ w a b c d)) :=
  Internal.ObjectNativeFormulaQuotation.native_environmentFiber σ τ w a b c d

example {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeFormulaQuotation.environmentAtLiftedSentence σ τ w R S a b c d A C K H)) :=
  Internal.ObjectNativeFormulaQuotation.native_environmentAtLifted σ τ w R S a b c d A C K H

example {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm sb sf sort) (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeFormulaQuotation.termIffSentence σ τ input w R S a b c d n q)) :=
  Internal.ObjectNativeFormulaQuotation.native_termIff σ τ input w R S a b c d n q

example {m} (truth : Bool) (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeFormulaQuotation.nullaryStepSentence truth w R S a b c d n q)) :=
  Internal.ObjectNativeFormulaQuotation.native_nullaryStep truth w R S a b c d n q

example {m} (left right targetLeft targetRight : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeFormulaQuotation.equalityStepSentence left right targetLeft targetRight w R S a b c d n q x y X Y)) :=
  Internal.ObjectNativeFormulaQuotation.native_equalityStep left right targetLeft targetRight w R S a b c d n q x y X Y

example {m} (left right targetLeft targetRight : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q s x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeFormulaQuotation.membershipStepSentence left right targetLeft targetRight w R S a b c d n q s x y X Y)) :=
  Internal.ObjectNativeFormulaQuotation.native_membershipStep left right targetLeft targetRight w R S a b c d n q s x y X Y

example {m} (body targetBody : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeFormulaQuotation.negationStepSentence body targetBody w R S a b c d n q x X)) :=
  Internal.ObjectNativeFormulaQuotation.native_negationStep body targetBody w R S a b c d n q x X

example {m} (kind : Fin 4) (left right targetLeft targetRight : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeFormulaQuotation.binaryStepSentence kind left right targetLeft targetRight w R S a b c d n q x y X Y)) :=
  Internal.ObjectNativeFormulaQuotation.native_binaryStep kind left right targetLeft targetRight w R S a b c d n q x y X Y

example {m} (universal : Bool) (body targetBody : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q x X A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeFormulaQuotation.quantifiedStepSentence universal body targetBody w R S a b c d n q x X A C K H)) :=
  Internal.ObjectNativeFormulaQuotation.native_quantifiedStep universal body targetBody w R S a b c d n q x X A C K H

example {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeFormulaQuotation.formulaConstructSentence σ τ input w R S a b c d n q)) :=
  Internal.ObjectNativeFormulaQuotation.native_formulaConstruct σ τ input w R S a b c d n q

example {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeFormulaQuotation.formulaIffSentence σ τ input w R S a b c d n q)) :=
  Internal.ObjectNativeFormulaQuotation.native_formulaIff σ τ input w R S a b c d n q

example {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeFormulaQuotation.formulaAtCandidateSentence σ τ input w R S a b c d n q)) :=
  Internal.ObjectNativeFormulaQuotation.native_formulaAtCandidate σ τ input w R S a b c d n q

example {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeFormulaQuotation.formulaValueUniqueSentence σ τ input w R S a b c d n q v)) :=
  Internal.ObjectNativeFormulaQuotation.native_formulaValueUnique σ τ input w R S a b c d n q v

example {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeFormulaQuotation.formulaUniqueOutputSentence σ τ input w R S a b c d n q)) :=
  Internal.ObjectNativeFormulaQuotation.native_formulaUniqueOutput σ τ input w R S a b c d n q

example {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeFormulaQuotation.formulaFiberSentence σ τ input w R S a b c d n)) :=
  Internal.ObjectNativeFormulaQuotation.native_formulaFiber σ τ input w R S a b c d n

example {m} {bound free : PureSyntaxQuotation.Ctx} (replacement : PureSyntaxQuotation.Tm bound free) (entry : YesMetaZFC.Logic.FirstOrder.Variable (YesMetaZFC.SetTheory.SetSort.set :: bound) YesMetaZFC.SetTheory.SetSort.set) (w a b A t R S i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeTopQuotation.instantiateBoundFieldSentence (bound := bound) (free := free) replacement entry w a b A t R S i q)) :=
  Internal.ObjectNativeTopQuotation.native_instantiateBoundField (bound := bound) (free := free) replacement entry w a b A t R S i q

example {m} {bound free : PureSyntaxQuotation.Ctx} (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeTopQuotation.instantiateBoundReadingsSentence (bound := bound) (free := free) replacement w a b A t R S)) :=
  Internal.ObjectNativeTopQuotation.native_instantiateBoundReadings (bound := bound) (free := free) replacement w a b A t R S

example {m} {bound free : PureSyntaxQuotation.Ctx} (entry : YesMetaZFC.Logic.FirstOrder.Variable free YesMetaZFC.SetTheory.SetSort.set) (w a b A t R S i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeTopQuotation.instantiateFreeFieldSentence (bound := bound) (free := free) entry w a b A t R S i q)) :=
  Internal.ObjectNativeTopQuotation.native_instantiateFreeField (bound := bound) (free := free) entry w a b A t R S i q

example {m} {bound free : PureSyntaxQuotation.Ctx} (w a b A t R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeTopQuotation.instantiateFreeReadingsSentence (bound := bound) (free := free)  w a b A t R S)) :=
  Internal.ObjectNativeTopQuotation.native_instantiateFreeReadings (bound := bound) (free := free)  w a b A t R S

example {m} {bound free : PureSyntaxQuotation.Ctx} (entry : YesMetaZFC.Logic.FirstOrder.Variable bound YesMetaZFC.SetTheory.SetSort.set) (w a b A B R S i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeTopQuotation.abstractBoundFieldSentence (bound := bound) (free := free) entry w a b A B R S i q)) :=
  Internal.ObjectNativeTopQuotation.native_abstractBoundField (bound := bound) (free := free) entry w a b A B R S i q

example {m} {bound free : PureSyntaxQuotation.Ctx} (w a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeTopQuotation.abstractBoundReadingsSentence (bound := bound) (free := free)  w a b A B R S)) :=
  Internal.ObjectNativeTopQuotation.native_abstractBoundReadings (bound := bound) (free := free)  w a b A B R S

example {m} {bound free : PureSyntaxQuotation.Ctx} (entry : YesMetaZFC.Logic.FirstOrder.Variable (YesMetaZFC.SetTheory.SetSort.set :: free) YesMetaZFC.SetTheory.SetSort.set) (w a b A B R S i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeTopQuotation.abstractFreeFieldSentence (bound := bound) (free := free) entry w a b A B R S i q)) :=
  Internal.ObjectNativeTopQuotation.native_abstractFreeField (bound := bound) (free := free) entry w a b A B R S i q

example {m} {bound free : PureSyntaxQuotation.Ctx} (w a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeTopQuotation.abstractFreeReadingsSentence (bound := bound) (free := free)  w a b A B R S)) :=
  Internal.ObjectNativeTopQuotation.native_abstractFreeReadings (bound := bound) (free := free)  w a b A B R S

example {m} {bound free : PureSyntaxQuotation.Ctx} (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeTopQuotation.instantiateEnvironmentSentence (bound := bound) (free := free) replacement w a b A t R S)) :=
  Internal.ObjectNativeTopQuotation.native_instantiateEnvironment (bound := bound) (free := free) replacement w a b A t R S

example {m} {bound free : PureSyntaxQuotation.Ctx} (w a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeTopQuotation.abstractEnvironmentSentence (bound := bound) (free := free)  w a b A B R S)) :=
  Internal.ObjectNativeTopQuotation.native_abstractEnvironment (bound := bound) (free := free)  w a b A B R S

example {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n q R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeTopQuotation.instantiateAtCodesSentence (bound := bound) (free := free) input replacement w a b A t n q R S)) :=
  Internal.ObjectNativeTopQuotation.native_instantiateAtCodes (bound := bound) (free := free) input replacement w a b A t n q R S

example {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeTopQuotation.instantiateIffSentence (bound := bound) (free := free) input replacement w a b A t n q)) :=
  Internal.ObjectNativeTopQuotation.native_instantiateIff (bound := bound) (free := free) input replacement w a b A t n q

example {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeTopQuotation.instantiateOriginalIffSentence (bound := bound) (free := free) input replacement w a b A t n q)) :=
  Internal.ObjectNativeTopQuotation.native_instantiateOriginalIff (bound := bound) (free := free) input replacement w a b A t n q

example {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeTopQuotation.instantiateAtCandidateSentence (bound := bound) (free := free) input replacement w a b A t n q)) :=
  Internal.ObjectNativeTopQuotation.native_instantiateAtCandidate (bound := bound) (free := free) input replacement w a b A t n q

example {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeTopQuotation.instantiateFiberSentence (bound := bound) (free := free) input replacement w a b A t n)) :=
  Internal.ObjectNativeTopQuotation.native_instantiateFiber (bound := bound) (free := free) input replacement w a b A t n

example {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n q R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeTopQuotation.abstractAtCodesSentence (bound := bound) (free := free) input w a b A B n q R S)) :=
  Internal.ObjectNativeTopQuotation.native_abstractAtCodes (bound := bound) (free := free) input w a b A B n q R S

example {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeTopQuotation.abstractIffSentence (bound := bound) (free := free) input w a b A B n q)) :=
  Internal.ObjectNativeTopQuotation.native_abstractIff (bound := bound) (free := free) input w a b A B n q

example {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeTopQuotation.abstractOriginalIffSentence (bound := bound) (free := free) input w a b A B n q)) :=
  Internal.ObjectNativeTopQuotation.native_abstractOriginalIff (bound := bound) (free := free) input w a b A B n q

example {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeTopQuotation.abstractAtCandidateSentence (bound := bound) (free := free) input w a b A B n q)) :=
  Internal.ObjectNativeTopQuotation.native_abstractAtCandidate (bound := bound) (free := free) input w a b A B n q

example {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectNativeTopQuotation.abstractFiberSentence (bound := bound) (free := free) input w a b A B n)) :=
  Internal.ObjectNativeTopQuotation.native_abstractFiber (bound := bound) (free := free) input w a b A B n

example {m} (isBound : Bool) (w R S n q i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermTransformProgram.variableRunSentence isBound w R S n q i)) :=
  Internal.ObjectTermTransformProgram.native_variableRun isBound w R S n q i

example {m} (w R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermTransformProgram.defaultRunSentence w R S n q)) :=
  Internal.ObjectTermTransformProgram.native_defaultRun w R S n q

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermTransformProgram.checkedIffSentence w R S a b c d n q)) :=
  Internal.ObjectTermTransformProgram.native_checkedIff w R S a b c d n q

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermTransformProgram.rejectEnvironmentSentence w R S a b c d n q)) :=
  Internal.ObjectTermTransformProgram.native_rejectEnvironment w R S a b c d n q

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermTransformProgram.rejectSourceSentence w R S a b c d n q)) :=
  Internal.ObjectTermTransformProgram.native_rejectSource w R S a b c d n q

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermTransformProgram.targetTypeSentence w R S a b c d n q)) :=
  Internal.ObjectTermTransformProgram.native_targetType w R S a b c d n q

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermTransformProgram.outputNaturalSentence w R S a b c d n q)) :=
  Internal.ObjectTermTransformProgram.native_outputNatural w R S a b c d n q

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermTransformProgram.rejectTargetSentence w R S a b c d n q)) :=
  Internal.ObjectTermTransformProgram.native_rejectTarget w R S a b c d n q

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermTransformProgram.rejectOutputNaturalSentence w R S a b c d n q)) :=
  Internal.ObjectTermTransformProgram.native_rejectOutputNatural w R S a b c d n q

example {m} (w R S a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermTransformProgram.uniqueSentence w R S a b c d n q v)) :=
  Internal.ObjectTermTransformProgram.native_unique w R S a b c d n q v

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermTransformProgram.uniqueOutputSentence w R S a b c d n q)) :=
  Internal.ObjectTermTransformProgram.native_uniqueOutput w R S a b c d n q

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermTransformProgram.atCandidateSentence w R S a b c d n q)) :=
  Internal.ObjectTermTransformProgram.native_atCandidate w R S a b c d n q

example {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermTransformProgram.actualFiberSentence w R S a b c d n)) :=
  Internal.ObjectTermTransformProgram.native_actualFiber w R S a b c d n

example {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermTransformProgram.fiberIffInputSentence w R S a b c d n)) :=
  Internal.ObjectTermTransformProgram.native_fiberIffInput w R S a b c d n

example {m} (w P R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermTransformProgram.encodedCheckedIffSentence w P R S a b c d n q)) :=
  Internal.ObjectTermTransformProgram.native_encodedCheckedIff w P R S a b c d n q

example {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermTransformProgram.uniformCorrectnessSentence w P)) :=
  Internal.ObjectTermTransformProgram.native_uniformCorrectness w P

example {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermTransformProgram.uniqueCodeSentence w P)) :=
  Internal.ObjectTermTransformProgram.native_uniqueCode w P

example {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermTransformProgram.atCodeSentence w P)) :=
  Internal.ObjectTermTransformProgram.native_atCode w P

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTermTransformProgram.existsCorrectProgramSentence w)) :=
  Internal.ObjectTermTransformProgram.native_existsCorrectProgram w

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.membershipInstructionIffSentence w R S a b c d n q)) :=
  Internal.ObjectFormulaTransformProgram.native_membershipInstructionIff w R S a b c d n q

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.equalityInstructionIffSentence w R S a b c d n q)) :=
  Internal.ObjectFormulaTransformProgram.native_equalityInstructionIff w R S a b c d n q

example {m} (w R S a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.compiledStepIffSentence w R S a b c d h n q)) :=
  Internal.ObjectFormulaTransformProgram.native_compiledStepIff w R S a b c d h n q

example {m} (w n h p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.operatorRowIffSentence w n h p)) :=
  Internal.ObjectFormulaTransformProgram.native_operatorRowIff w n h p

example {m} (w n h v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.operatorValueIffSentence w n h v)) :=
  Internal.ObjectFormulaTransformProgram.native_operatorValueIff w n h v

example {m} (w f d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.graphIffSentence w f d)) :=
  Internal.ObjectFormulaTransformProgram.native_graphIff w f d

example {m} (w n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.evaluationIffSentence w n v)) :=
  Internal.ObjectFormulaTransformProgram.native_evaluationIff w n v

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.executionIffSentence w R S a b c d n q)) :=
  Internal.ObjectFormulaTransformProgram.native_executionIff w R S a b c d n q

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.actualRecursorsSentence w)) :=
  Internal.ObjectFormulaTransformProgram.native_actualRecursors w

example {m} (w d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.graphExistsSentence w d)) :=
  Internal.ObjectFormulaTransformProgram.native_graphExists w d

example {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.evaluationExistsSentence w n)) :=
  Internal.ObjectFormulaTransformProgram.native_evaluationExists w n

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.inputOfExecutionSentence w R S a b c d n q)) :=
  Internal.ObjectFormulaTransformProgram.native_inputOfExecution w R S a b c d n q

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.sourceTypeSentence w R S a b c d n q)) :=
  Internal.ObjectFormulaTransformProgram.native_sourceType w R S a b c d n q

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.targetTypeSentence w R S a b c d n q)) :=
  Internal.ObjectFormulaTransformProgram.native_targetType w R S a b c d n q

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.outputNaturalSentence w R S a b c d n q)) :=
  Internal.ObjectFormulaTransformProgram.native_outputNatural w R S a b c d n q

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.uniqueOutputSentence w R S a b c d n q)) :=
  Internal.ObjectFormulaTransformProgram.native_uniqueOutput w R S a b c d n q

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.atCandidateSentence w R S a b c d n q)) :=
  Internal.ObjectFormulaTransformProgram.native_atCandidate w R S a b c d n q

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.rejectEnvironmentSentence w R S a b c d n q)) :=
  Internal.ObjectFormulaTransformProgram.native_rejectEnvironment w R S a b c d n q

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.rejectSourceSentence w R S a b c d n q)) :=
  Internal.ObjectFormulaTransformProgram.native_rejectSource w R S a b c d n q

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.rejectInputSentence w R S a b c d n q)) :=
  Internal.ObjectFormulaTransformProgram.native_rejectInput w R S a b c d n q

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.rejectTargetSentence w R S a b c d n q)) :=
  Internal.ObjectFormulaTransformProgram.native_rejectTarget w R S a b c d n q

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.rejectOutputNaturalSentence w R S a b c d n q)) :=
  Internal.ObjectFormulaTransformProgram.native_rejectOutputNatural w R S a b c d n q

example {m} (w R S a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.uniqueSentence w R S a b c d n q v)) :=
  Internal.ObjectFormulaTransformProgram.native_unique w R S a b c d n q v

example {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.actualFiberSentence w R S a b c d n)) :=
  Internal.ObjectFormulaTransformProgram.native_actualFiber w R S a b c d n

example {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.fiberIffInputSentence w R S a b c d n)) :=
  Internal.ObjectFormulaTransformProgram.native_fiberIffInput w R S a b c d n

example {m} (w P R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.encodedExecutionIffSentence w P R S a b c d n q)) :=
  Internal.ObjectFormulaTransformProgram.native_encodedExecutionIff w P R S a b c d n q

example {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.uniformCorrectnessSentence w P)) :=
  Internal.ObjectFormulaTransformProgram.native_uniformCorrectness w P

example {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.uniqueCodeSentence w P)) :=
  Internal.ObjectFormulaTransformProgram.native_uniqueCode w P

example {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.atCodeSentence w P)) :=
  Internal.ObjectFormulaTransformProgram.native_atCode w P

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformProgram.existsCorrectProgramSentence w)) :=
  Internal.ObjectFormulaTransformProgram.native_existsCorrectProgram w

example {m} (isBound : Bool) (w I a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectIndexFormulaRename.convertedExistsSentence isBound w I a c d)) :=
  Internal.ObjectIndexFormulaRename.native_convertedExists isBound w I a c d

example {m} (isBound : Bool) (w I a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectIndexFormulaRename.convertedFiberSentence isBound w I a c d)) :=
  Internal.ObjectIndexFormulaRename.native_convertedFiber isBound w I a c d

example {m} (isBound : Bool) (w I a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectIndexFormulaRename.convertedDomainIffSentence isBound w I a c d)) :=
  Internal.ObjectIndexFormulaRename.native_convertedDomainIff isBound w I a c d

example {m} (isBound : Bool) (w I T U a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectIndexFormulaRename.convertedUniqueSentence isBound w I T U a c d)) :=
  Internal.ObjectIndexFormulaRename.native_convertedUnique isBound w I T U a c d

example {m} (w I J a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectIndexFormulaRename.environmentExistsSentence w I J a b c d)) :=
  Internal.ObjectIndexFormulaRename.native_environmentExists w I J a b c d

example {m} (w I J R S U V a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectIndexFormulaRename.environmentUniqueSentence w I J R S U V a b c d)) :=
  Internal.ObjectIndexFormulaRename.native_environmentUnique w I J R S U V a b c d

example {m} (w I J R S a b c d r s n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectIndexFormulaRename.termProgramIffSentence w I J R S a b c d r s n q)) :=
  Internal.ObjectIndexFormulaRename.native_termProgramIff w I J R S a b c d r s n q

example {m} (w I J R S a b c d r s n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectIndexFormulaRename.membershipIffSentence w I J R S a b c d r s n q)) :=
  Internal.ObjectIndexFormulaRename.native_membershipIff w I J R S a b c d r s n q

example {m} (w I J R S a b c d r s n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectIndexFormulaRename.equalityIffSentence w I J R S a b c d r s n q)) :=
  Internal.ObjectIndexFormulaRename.native_equalityIff w I J R S a b c d r s n q

example {m} (w I J R S a b c d A C L K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectIndexFormulaRename.binderEnvironmentSentence w I J R S a b c d A C L K H)) :=
  Internal.ObjectIndexFormulaRename.native_binderEnvironment w I J R S a b c d A C L K H

example {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectIndexFormulaRename.allMetadataAtNaturalSentence w n)) :=
  Internal.ObjectIndexFormulaRename.native_allMetadataAtNatural w n

example {m} (w I J R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectIndexFormulaRename.formulaForwardSentence w I J R S a b c d n q)) :=
  Internal.ObjectIndexFormulaRename.native_formulaForward w I J R S a b c d n q

example {m} (w I J R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectIndexFormulaRename.formulaReverseSentence w I J R S a b c d n q)) :=
  Internal.ObjectIndexFormulaRename.native_formulaReverse w I J R S a b c d n q

example {m} (w I J R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectIndexFormulaRename.formulaRenameIffSentence w I J R S a b c d n q)) :=
  Internal.ObjectIndexFormulaRename.native_formulaRenameIff w I J R S a b c d n q

example {m} (w I J R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectIndexFormulaRename.formulaProgramIffSentence w I J R S a b c d n q)) :=
  Internal.ObjectIndexFormulaRename.native_formulaProgramIff w I J R S a b c d n q

example {m} (w r f a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.freeImageGraphSentence w r f a c d)) :=
  Internal.ObjectFreeVariablePrograms.native_freeImageGraph w r f a c d

example {m} (w a c d L J : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.freeSameListCodeSentence w a c d L J)) :=
  Internal.ObjectFreeVariablePrograms.native_freeSameListCode w a c d L J

example {m} (w a c d L J T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.freeSameListCodeUniqueSentence w a c d L J T)) :=
  Internal.ObjectFreeVariablePrograms.native_freeSameListCodeUnique w a c d L J T

example {m} (w b c I : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.boundIdentityImageExistsSentence w b c I)) :=
  Internal.ObjectFreeVariablePrograms.native_boundIdentityImageExists w b c I

example {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.freeForwardSentence w b a c L n q)) :=
  Internal.ObjectFreeVariablePrograms.native_freeForward w b a c L n q

example {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.freeReverseSentence w b a c L n q)) :=
  Internal.ObjectFreeVariablePrograms.native_freeReverse w b a c L n q

example {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.freeExecutionIffSentence w b a c L n q)) :=
  Internal.ObjectFreeVariablePrograms.native_freeExecutionIff w b a c L n q

example {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.freeInputOfExecutionSentence w b a c L n q)) :=
  Internal.ObjectFreeVariablePrograms.native_freeInputOfExecution w b a c L n q

example {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.freeSourceTypeSentence w b a c L n q)) :=
  Internal.ObjectFreeVariablePrograms.native_freeSourceType w b a c L n q

example {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.freeTargetTypeSentence w b a c L n q)) :=
  Internal.ObjectFreeVariablePrograms.native_freeTargetType w b a c L n q

example {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.freeOutputNaturalSentence w b a c L n q)) :=
  Internal.ObjectFreeVariablePrograms.native_freeOutputNatural w b a c L n q

example {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.freeUniqueOutputSentence w b a c L n q)) :=
  Internal.ObjectFreeVariablePrograms.native_freeUniqueOutput w b a c L n q

example {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.freeAtCandidateSentence w b a c L n q)) :=
  Internal.ObjectFreeVariablePrograms.native_freeAtCandidate w b a c L n q

example {m} (w b a c L n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.freeUniqueSentence w b a c L n q v)) :=
  Internal.ObjectFreeVariablePrograms.native_freeUnique w b a c L n q v

example {m} (w b a c L n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.freeActualFiberSentence w b a c L n)) :=
  Internal.ObjectFreeVariablePrograms.native_freeActualFiber w b a c L n

example {m} (w b a c L n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.freeFiberIffInputSentence w b a c L n)) :=
  Internal.ObjectFreeVariablePrograms.native_freeFiberIffInput w b a c L n

example {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.freeRejectEnvironmentSentence w b a c L n q)) :=
  Internal.ObjectFreeVariablePrograms.native_freeRejectEnvironment w b a c L n q

example {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.freeRejectSourceSentence w b a c L n q)) :=
  Internal.ObjectFreeVariablePrograms.native_freeRejectSource w b a c L n q

example {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.freeRejectInputSentence w b a c L n q)) :=
  Internal.ObjectFreeVariablePrograms.native_freeRejectInput w b a c L n q

example {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.freeRejectTargetSentence w b a c L n q)) :=
  Internal.ObjectFreeVariablePrograms.native_freeRejectTarget w b a c L n q

example {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.freeRejectOutputNaturalSentence w b a c L n q)) :=
  Internal.ObjectFreeVariablePrograms.native_freeRejectOutputNatural w b a c L n q

example {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.weakForwardSentence w a b B n q)) :=
  Internal.ObjectFreeVariablePrograms.native_weakForward w a b B n q

example {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.weakReverseSentence w a b B n q)) :=
  Internal.ObjectFreeVariablePrograms.native_weakReverse w a b B n q

example {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.weakExecutionIffSentence w a b B n q)) :=
  Internal.ObjectFreeVariablePrograms.native_weakExecutionIff w a b B n q

example {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.weakInputOfExecutionSentence w a b B n q)) :=
  Internal.ObjectFreeVariablePrograms.native_weakInputOfExecution w a b B n q

example {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.weakSourceTypeSentence w a b B n q)) :=
  Internal.ObjectFreeVariablePrograms.native_weakSourceType w a b B n q

example {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.weakTargetTypeSentence w a b B n q)) :=
  Internal.ObjectFreeVariablePrograms.native_weakTargetType w a b B n q

example {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.weakOutputNaturalSentence w a b B n q)) :=
  Internal.ObjectFreeVariablePrograms.native_weakOutputNatural w a b B n q

example {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.weakUniqueOutputSentence w a b B n q)) :=
  Internal.ObjectFreeVariablePrograms.native_weakUniqueOutput w a b B n q

example {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.weakAtCandidateSentence w a b B n q)) :=
  Internal.ObjectFreeVariablePrograms.native_weakAtCandidate w a b B n q

example {m} (w a b B n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.weakUniqueSentence w a b B n q v)) :=
  Internal.ObjectFreeVariablePrograms.native_weakUnique w a b B n q v

example {m} (w a b B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.weakActualFiberSentence w a b B n)) :=
  Internal.ObjectFreeVariablePrograms.native_weakActualFiber w a b B n

example {m} (w a b B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.weakFiberIffInputSentence w a b B n)) :=
  Internal.ObjectFreeVariablePrograms.native_weakFiberIffInput w a b B n

example {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.weakRejectEnvironmentSentence w a b B n q)) :=
  Internal.ObjectFreeVariablePrograms.native_weakRejectEnvironment w a b B n q

example {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.weakRejectSourceSentence w a b B n q)) :=
  Internal.ObjectFreeVariablePrograms.native_weakRejectSource w a b B n q

example {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.weakRejectInputSentence w a b B n q)) :=
  Internal.ObjectFreeVariablePrograms.native_weakRejectInput w a b B n q

example {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.weakRejectTargetSentence w a b B n q)) :=
  Internal.ObjectFreeVariablePrograms.native_weakRejectTarget w a b B n q

example {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.weakRejectOutputNaturalSentence w a b B n q)) :=
  Internal.ObjectFreeVariablePrograms.native_weakRejectOutputNatural w a b B n q

example {m} (w a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeVariablePrograms.weakActualSuccessorStateSentence w a b n)) :=
  Internal.ObjectFreeVariablePrograms.native_weakActualSuccessorState w a b n

example {m} (w I J R S a b c d A C M K H L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectStrictLookup.binderFreeCodeStableSentence w I J R S a b c d A C M K H L)) :=
  Internal.ObjectStrictLookup.native_binderFreeCodeStable w I J R S a b c d A C M K H L

example {m} (w b a c L I J R u v M K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectStrictLookup.binderLiftedEnvironmentSentence w b a c L I J R u v M K H)) :=
  Internal.ObjectStrictLookup.native_binderLiftedEnvironment w b a c L I J R u v M K H

example {m} (w b a c L I J R u v M K H x q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectStrictLookup.binderChildExecutionSentence w b a c L I J R u v M K H x q)) :=
  Internal.ObjectStrictLookup.native_binderChildExecution w b a c L I J R u v M K H x q

example {m} (w n z y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectStrictLookup.lookupZeroSelectedSentence w n z y)) :=
  Internal.ObjectStrictLookup.native_lookupZeroSelected w n z y

example {m} (w h t n r s y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectStrictLookup.lookupConsSuccessorSentence w h t n r s y)) :=
  Internal.ObjectStrictLookup.native_lookupConsSuccessor w h t n r s y

example {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectStrictLookup.lookupOuterRejectedSentence w n i)) :=
  Internal.ObjectStrictLookup.native_lookupOuterRejected w n i

example {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectStrictLookup.lookupNilRejectedSentence w n i)) :=
  Internal.ObjectStrictLookup.native_lookupNilRejected w n i

example {m} (w h t n z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectStrictLookup.lookupConsZeroReturnsSentence w h t n z)) :=
  Internal.ObjectStrictLookup.native_lookupConsZeroReturns w h t n z

example {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectStrictLookup.lookupEmptySinkSentence w n i y)) :=
  Internal.ObjectStrictLookup.native_lookupEmptySink w n i y

example {m} (w n r i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectStrictLookup.lookupExactDomainSentence w n r i y)) :=
  Internal.ObjectStrictLookup.native_lookupExactDomain w n r i y

example {m} (w n r i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectStrictLookup.lookupCheckedDomainSentence w n r i y)) :=
  Internal.ObjectStrictLookup.native_lookupCheckedDomain w n r i y

example {m} (w n i y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectStrictLookup.lookupUniqueSentence w n i y z)) :=
  Internal.ObjectStrictLookup.native_lookupUnique w n i y z

example {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectStrictLookup.lookupUniqueOutputSentence w n i y)) :=
  Internal.ObjectStrictLookup.native_lookupUniqueOutput w n i y

example {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectStrictLookup.lookupAtCandidateSentence w n i y)) :=
  Internal.ObjectStrictLookup.native_lookupAtCandidate w n i y

example {m} (w n r i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectStrictLookup.lookupActualFiberSentence w n r i)) :=
  Internal.ObjectStrictLookup.native_lookupActualFiber w n r i

example {m} (w n r i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectStrictLookup.lookupFiberIffRangeSentence w n r i)) :=
  Internal.ObjectStrictLookup.native_lookupFiberIffRange w n r i

example {m} (w n r i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectStrictLookup.lookupHasOutputIffRangeSentence w n r i)) :=
  Internal.ObjectStrictLookup.native_lookupHasOutputIffRange w n r i

example {m} (w n r i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectStrictLookup.lookupRejectedIffNotRangeSentence w n r i)) :=
  Internal.ObjectStrictLookup.native_lookupRejectedIffNotRange w n r i

example {m} (w n r i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectStrictLookup.lookupOutOfBoundsRejectedSentence w n r i)) :=
  Internal.ObjectStrictLookup.native_lookupOutOfBoundsRejected w n r i

example {m} (w n r i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectStrictLookup.lookupInRangeFieldIffSentence w n r i y)) :=
  Internal.ObjectStrictLookup.native_lookupInRangeFieldIff w n r i y

example {m} (w a c L J r i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectStrictLookup.lookupFreeImageAtEdgeSentence w a c L J r i j q)) :=
  Internal.ObjectStrictLookup.native_lookupFreeImageAtEdge w a c L J r i j q

example {m} (w n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTableProgram.operatorActualFiberSentence w n h)) :=
  Internal.ObjectLookupTableProgram.native_operatorActualFiber w n h

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTableProgram.actualCarrierRecursorsSentence w)) :=
  Internal.ObjectLookupTableProgram.native_actualCarrierRecursors w

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTableProgram.allOrdinalRecursorsSentence w)) :=
  Internal.ObjectLookupTableProgram.native_allOrdinalRecursors w

example {m} (w d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTableProgram.actualGraphSentence w d)) :=
  Internal.ObjectLookupTableProgram.native_actualGraph w d

example {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTableProgram.evaluationAtNaturalSentence w n)) :=
  Internal.ObjectLookupTableProgram.native_evaluationAtNatural w n

example {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTableProgram.evaluationUniqueFiberSentence w n)) :=
  Internal.ObjectLookupTableProgram.native_evaluationUniqueFiber w n

example {m} (w n h v i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTableProgram.stateMembershipIffSentence w n h v i y)) :=
  Internal.ObjectLookupTableProgram.native_stateMembershipIff w n h v i y

example {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTableProgram.recursiveCriterionSentence w n i y)) :=
  Internal.ObjectLookupTableProgram.native_recursiveCriterion w n i y

example {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTableProgram.allInternalExecutionIffSentence w n i y)) :=
  Internal.ObjectLookupTableProgram.native_allInternalExecutionIff w n i y

example {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTableProgram.naturalExecutionIffSentence w n i y)) :=
  Internal.ObjectLookupTableProgram.native_naturalExecutionIff w n i y

example {m} (w P n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTableProgram.encodedExecutionIffSentence w P n i y)) :=
  Internal.ObjectLookupTableProgram.native_encodedExecutionIff w P n i y

example {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTableProgram.uniformCorrectnessSentence w P)) :=
  Internal.ObjectLookupTableProgram.native_uniformCorrectness w P

example {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTableProgram.uniqueProgramCodeSentence w P)) :=
  Internal.ObjectLookupTableProgram.native_uniqueProgramCode w P

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTableProgram.existsCorrectProgramSentence w)) :=
  Internal.ObjectLookupTableProgram.native_existsCorrectProgram w

example {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTableProgram.hasOutputIffSentence w n i)) :=
  Internal.ObjectLookupTableProgram.native_hasOutputIff w n i

example {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTableProgram.noOutputIffSentence w n i)) :=
  Internal.ObjectLookupTableProgram.native_noOutputIff w n i

example {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTableProgram.outcomeExhaustiveSentence w n i)) :=
  Internal.ObjectLookupTableProgram.native_outcomeExhaustive w n i

example {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTableProgram.outcomeIncompatibleSentence w n i)) :=
  Internal.ObjectLookupTableProgram.native_outcomeIncompatible w n i

example {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTableProgram.uniqueOutputSentence w n i y)) :=
  Internal.ObjectLookupTableProgram.native_uniqueOutput w n i y

example {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLookupRules.expressionActualValueSentence e env w)) :=
  Internal.ObjectOriginalLookupRules.native_expressionActualValue e env w

example {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLookupRules.expressionNaturalRangeSentence e env w y)) :=
  Internal.ObjectOriginalLookupRules.native_expressionNaturalRange e env w y

example {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLookupRules.expressionActualUniqueFiberSentence e env w)) :=
  Internal.ObjectOriginalLookupRules.native_expressionActualUniqueFiber e env w

example {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLookupRules.expressionUniqueValueSentence e env w y)) :=
  Internal.ObjectOriginalLookupRules.native_expressionUniqueValue e env w y

example {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLookupRules.expressionCandidateIffSentence e env w y z)) :=
  Internal.ObjectOriginalLookupRules.native_expressionCandidateIff e env w y z

example {m} {n} (e f : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w a b y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLookupRules.rawExpressionIffSentence e f env w a b y)) :=
  Internal.ObjectOriginalLookupRules.native_rawExpressionIff e f env w a b y

example {m} {n} (e f : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w a b y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLookupRules.consExpressionIffSentence e f env w a b y)) :=
  Internal.ObjectOriginalLookupRules.native_consExpressionIff e f env w a b y

example {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w trace y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLookupRules.premiseAtValueSentence e env w trace y)) :=
  Internal.ObjectOriginalLookupRules.native_premiseAtValue e env w trace y

example {m} {n} (e f : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLookupRules.guardAtValuesSentence e f env w a b)) :=
  Internal.ObjectOriginalLookupRules.native_guardAtValues e f env w a b

example {m} (env : Fin 2 → Fin m) (w n z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLookupRules.originalLookupHeadExpressionIffSentence env w n z row)) :=
  Internal.ObjectOriginalLookupRules.native_originalLookupHeadExpressionIff env w n z row

example {m} (env : Fin 4 → Fin m) (w n s row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLookupRules.originalLookupTailExpressionIffSentence env w n s row)) :=
  Internal.ObjectOriginalLookupRules.native_originalLookupTailExpressionIff env w n s row

example {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLookupRules.originalLookupPremiseExpressionIffSentence env w row)) :=
  Internal.ObjectOriginalLookupRules.native_originalLookupPremiseExpressionIff env w row

example {m} (env : Fin 2 → Fin m) (w n z row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLookupRules.originalLookupHeadMatrixIffSentence env w n z row trace)) :=
  Internal.ObjectOriginalLookupRules.native_originalLookupHeadMatrixIff env w n z row trace

example {m} (env : Fin 4 → Fin m) (w n s row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLookupRules.originalLookupTailMatrixIffSentence env w n s row trace)) :=
  Internal.ObjectOriginalLookupRules.native_originalLookupTailMatrixIff env w n s row trace

example {m} (env : Fin 4 → Fin m) (w trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLookupRules.originalLookupChildMemberIffSentence env w trace)) :=
  Internal.ObjectOriginalLookupRules.native_originalLookupChildMemberIff env w trace

example {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLookupRules.originalLookupHeadAssignmentBoundSentence env w row)) :=
  Internal.ObjectOriginalLookupRules.native_originalLookupHeadAssignmentBound env w row

example {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLookupRules.originalLookupTailAssignmentBoundSentence env w row)) :=
  Internal.ObjectOriginalLookupRules.native_originalLookupTailAssignmentBound env w row

example {m} {n} (env : Fin n → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectBoundedLookupDispatch.naturalAssignmentFromSearchBoundSentence env w row)) :=
  Internal.ObjectBoundedLookupDispatch.native_naturalAssignmentFromSearchBound env w row

example {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (env : Fin rule.arity → Fin m) (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectBoundedLookupDispatch.boundedRuleApplicationSentence rule env w row trace)) :=
  Internal.ObjectBoundedLookupDispatch.native_boundedRuleApplication rule env w row trace

example {m} (env : Fin 2 → Fin m) (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectBoundedLookupDispatch.originalLookupHeadApplicationSentence env w row trace)) :=
  Internal.ObjectBoundedLookupDispatch.native_originalLookupHeadApplication env w row trace

example {m} (env : Fin 4 → Fin m) (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectBoundedLookupDispatch.originalLookupTailApplicationSentence env w row trace)) :=
  Internal.ObjectBoundedLookupDispatch.native_originalLookupTailApplication env w row trace

example {m} {n} (env : Fin n → Fin m) (row s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectBoundedLookupDispatch.searchBoundMembershipIffSentence env row s)) :=
  Internal.ObjectBoundedLookupDispatch.native_searchBoundMembershipIff env row s

example {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (env : Fin rule.arity → Fin m) (w row trace s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectBoundedLookupDispatch.originalBoundedMatrixIffSentence rule env w row trace s)) :=
  Internal.ObjectBoundedLookupDispatch.native_originalBoundedMatrixIff rule env w row trace s

example {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (w row trace s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectBoundedLookupDispatch.originalQuantifiedApplicationIffSentence rule w row trace s)) :=
  Internal.ObjectBoundedLookupDispatch.native_originalQuantifiedApplicationIff rule w row trace s

example {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w row trace s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectBoundedLookupDispatch.wholeRuleTableBoundedSearchIffSentence rules w row trace s)) :=
  Internal.ObjectBoundedLookupDispatch.native_wholeRuleTableBoundedSearchIff rules w row trace s

example {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectBoundedLookupDispatch.wholeRuleTableActualSearchIffSentence rules w row trace)) :=
  Internal.ObjectBoundedLookupDispatch.native_wholeRuleTableActualSearchIff rules w row trace

example {m} {k} (xs : Fin k → Fin m) (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectBoundedLookupDispatch.originalOtherRulesRejectedSentence xs w row trace)) :=
  Internal.ObjectBoundedLookupDispatch.native_originalOtherRulesRejected xs w row trace

example {m} {k} (xs : Fin k → Fin m) (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectBoundedLookupDispatch.originalWholeTableLookupDispatchIffSentence xs w row trace)) :=
  Internal.ObjectBoundedLookupDispatch.native_originalWholeTableLookupDispatchIff xs w row trace

example {m} {k} (xs : Fin k → Fin m) (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectBoundedLookupDispatch.originalActualSearchLookupDispatchIffSentence xs w row trace)) :=
  Internal.ObjectBoundedLookupDispatch.native_originalActualSearchLookupDispatchIff xs w row trace

example {m} (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectBoundedLookupDispatch.originalLookupIntoWholeTableSentence w row trace)) :=
  Internal.ObjectBoundedLookupDispatch.native_originalLookupIntoWholeTable w row trace

example {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.actualOriginalLookupRowSentence w n i y)) :=
  Internal.ObjectLookupTrace.native_actualOriginalLookupRow w n i y

example {m} (w n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.originalLookupRowNaturalFieldsSentence w n i y r)) :=
  Internal.ObjectLookupTrace.native_originalLookupRowNaturalFields w n i y r

example {m} (w n i y r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.originalHeadApplicationSoundSentence w n i y r R)) :=
  Internal.ObjectLookupTrace.native_originalHeadApplicationSound w n i y r R

example {m} (w R n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.arbitraryClosedInternalTraceSoundSentence w R n i y r)) :=
  Internal.ObjectLookupTrace.native_arbitraryClosedInternalTraceSound w R n i y r

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.canonicalTraceActualSetSentence w)) :=
  Internal.ObjectLookupTrace.native_canonicalTraceActualSet w

example {m} (w R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.canonicalTraceSubsetOmegaSentence w R)) :=
  Internal.ObjectLookupTrace.native_canonicalTraceSubsetOmega w R

example {m} (w R n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.canonicalTraceSuccessfulMemberSentence w R n i y r)) :=
  Internal.ObjectLookupTrace.native_canonicalTraceSuccessfulMember w R n i y r

example {m} (w R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.canonicalTraceClosedSentence w R)) :=
  Internal.ObjectLookupTrace.native_canonicalTraceClosed w R

example {m} (w n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.compiledTraceCompleteSentence w n i y r)) :=
  Internal.ObjectLookupTrace.native_compiledTraceComplete w n i y r

example {m} (w n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.compiledTraceExecutionIffSentence w n i y r)) :=
  Internal.ObjectLookupTrace.native_compiledTraceExecutionIff w n i y r

example {m} (w n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.compiledTraceCandidateRejectionIffSentence w n i y r)) :=
  Internal.ObjectLookupTrace.native_compiledTraceCandidateRejectionIff w n i y r

example {m} (w R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.originalBoundedSearchClosureIffSentence w R)) :=
  Internal.ObjectLookupTrace.native_originalBoundedSearchClosureIff w R

example {m} (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.originalBoundedSearchTraceIffSentence w r)) :=
  Internal.ObjectLookupTrace.native_originalBoundedSearchTraceIff w r

example {m} (w n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.originalBoundedSearchTraceExecutionIffSentence w n i y r)) :=
  Internal.ObjectLookupTrace.native_originalBoundedSearchTraceExecutionIff w n i y r

example {m} (w r P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.actualPowerTraceDomainIffSentence w r P)) :=
  Internal.ObjectLookupTrace.native_actualPowerTraceDomainIff w r P

example {m} (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.actualPowerTraceSearchIffSentence w r)) :=
  Internal.ObjectLookupTrace.native_actualPowerTraceSearchIff w r

example {m} (w n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.actualPowerTraceExecutionIffSentence w n i y r)) :=
  Internal.ObjectLookupTrace.native_actualPowerTraceExecutionIff w n i y r

example {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.allInternalTraceSomeExecutionIffSentence w n i y)) :=
  Internal.ObjectLookupTrace.native_allInternalTraceSomeExecutionIff w n i y

example {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.allInternalTraceSomeCheckedIffSentence w n i y)) :=
  Internal.ObjectLookupTrace.native_allInternalTraceSomeCheckedIff w n i y

example {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.naturalTraceSomeRawLookupIffSentence w n i y)) :=
  Internal.ObjectLookupTrace.native_naturalTraceSomeRawLookupIff w n i y

example {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.allInternalTraceHasOutputIffSentence w n i)) :=
  Internal.ObjectLookupTrace.native_allInternalTraceHasOutputIff w n i

example {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.allInternalTraceNoOutputIffSentence w n i)) :=
  Internal.ObjectLookupTrace.native_allInternalTraceNoOutputIff w n i

example {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.naturalTraceHasOutputStrictIffSentence w n i)) :=
  Internal.ObjectLookupTrace.native_naturalTraceHasOutputStrictIff w n i

example {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.naturalTraceNoOutputStrictIffSentence w n i)) :=
  Internal.ObjectLookupTrace.native_naturalTraceNoOutputStrictIff w n i

example {m} (w n i y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLookupTrace.allInternalTraceOutputUniqueSentence w n i y z)) :=
  Internal.ObjectLookupTrace.native_allInternalTraceOutputUnique w n i y z

example {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (env : Fin rule.arity → Fin m) (w r R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarTrace.ruleMatrixTraceMonotoneSentence rule env w r R S)) :=
  Internal.ObjectScalarTrace.native_ruleMatrixTraceMonotone rule env w r R S

example {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (w r R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarTrace.ruleApplicationTraceMonotoneSentence rule w r R S)) :=
  Internal.ObjectScalarTrace.native_ruleApplicationTraceMonotone rule w r R S

example {m} (w r R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarTrace.originalWholeTableTraceMonotoneSentence w r R S)) :=
  Internal.ObjectScalarTrace.native_originalWholeTableTraceMonotone w r R S

example {m} (R r S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarTrace.insertedTraceIncludesSentence R r S)) :=
  Internal.ObjectScalarTrace.native_insertedTraceIncludes R r S

example {m} (w R r S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarTrace.insertedTraceSubsetOmegaSentence w R r S)) :=
  Internal.ObjectScalarTrace.native_insertedTraceSubsetOmega w R r S

example {m} (w R r S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarTrace.insertedTraceClosedSentence w R r S)) :=
  Internal.ObjectScalarTrace.native_insertedTraceClosed w R r S

example {m} (w R r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarTrace.insertedRootActualTraceSentence w R r)) :=
  Internal.ObjectScalarTrace.native_insertedRootActualTrace w R r

example {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarTrace.boundModeZeroTraceSentence env w r)) :=
  Internal.ObjectScalarTrace.native_boundModeZeroTrace env w r

example {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarTrace.boundModeZeroPowerTraceSentence env w r)) :=
  Internal.ObjectScalarTrace.native_boundModeZeroPowerTrace env w r

example {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarTrace.boundModeThreeTraceSentence env w r)) :=
  Internal.ObjectScalarTrace.native_boundModeThreeTrace env w r

example {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarTrace.boundModeThreePowerTraceSentence env w r)) :=
  Internal.ObjectScalarTrace.native_boundModeThreePowerTrace env w r

example {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarTrace.freeModeZeroTraceSentence env w r)) :=
  Internal.ObjectScalarTrace.native_freeModeZeroTrace env w r

example {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarTrace.freeModeZeroPowerTraceSentence env w r)) :=
  Internal.ObjectScalarTrace.native_freeModeZeroPowerTrace env w r

example {m} (env : Fin 4 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarTrace.freeModeThreeTraceSentence env w r)) :=
  Internal.ObjectScalarTrace.native_freeModeThreeTrace env w r

example {m} (env : Fin 4 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarTrace.freeModeThreePowerTraceSentence env w r)) :=
  Internal.ObjectScalarTrace.native_freeModeThreePowerTrace env w r

example {m} {n} (tag target k : Nat) (hne : tag ≠ target) (p : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (xs : Fin k → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarDispatch.originalDifferentNodeTagsSentence tag target k hne p env xs w r)) :=
  Internal.ObjectScalarDispatch.native_originalDifferentNodeTags tag target k hne p env xs w r

example {m} {n} (tag : Nat) (es : Fin 5 → YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (xs : Fin 5 → Fin m) (i : Fin 5) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarDispatch.originalFiveFieldRecoverySentence tag es env xs i w r)) :=
  Internal.ObjectScalarDispatch.native_originalFiveFieldRecovery tag es env xs i w r

example {m} (three : Bool) (xs : Fin 5 → Fin m) (w r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarDispatch.originalModeWholeTableDispatchIffSentence three xs w r R)) :=
  Internal.ObjectScalarDispatch.native_originalModeWholeTableDispatchIff three xs w r R

example {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarDispatch.originalVariableWholeTableDispatchIffSentence three bound xs w r R idx)) :=
  Internal.ObjectScalarDispatch.native_originalVariableWholeTableDispatchIff three bound xs w r R idx

example {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarDispatch.boundModeZeroDispatchIffSentence xs w r R idx)) :=
  Internal.ObjectScalarDispatch.native_boundModeZeroDispatchIff xs w r R idx

example {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarDispatch.boundModeThreeDispatchIffSentence xs w r R idx)) :=
  Internal.ObjectScalarDispatch.native_boundModeThreeDispatchIff xs w r R idx

example {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarDispatch.freeModeZeroDispatchIffSentence xs w r R idx)) :=
  Internal.ObjectScalarDispatch.native_freeModeZeroDispatchIff xs w r R idx

example {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarDispatch.freeModeThreeDispatchIffSentence xs w r R idx)) :=
  Internal.ObjectScalarDispatch.native_freeModeThreeDispatchIff xs w r R idx

example {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarDispatch.originalVariableActualSearchDispatchIffSentence three bound xs w r R idx)) :=
  Internal.ObjectScalarDispatch.native_originalVariableActualSearchDispatchIff three bound xs w r R idx

example {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarDispatch.originalVariableCandidateRejectionIffSentence three bound xs w r R idx)) :=
  Internal.ObjectScalarDispatch.native_originalVariableCandidateRejectionIff three bound xs w r R idx

example {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarDispatch.arbitraryClosedVariableTraceApplicationSentence three bound xs w r R idx)) :=
  Internal.ObjectScalarDispatch.native_arbitraryClosedVariableTraceApplication three bound xs w r R idx

example {m} {n} (bound : Bool) (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarDispatch.originalVariableExprFromCodeSentence bound e env w idx y)) :=
  Internal.ObjectScalarDispatch.native_originalVariableExprFromCode bound e env w idx y

example {m} (three : Bool) (xs : Fin 5 → Fin m) (w r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarDispatch.originalBoundApplicationIdentitySentence three xs w r R)) :=
  Internal.ObjectScalarDispatch.native_originalBoundApplicationIdentity three xs w r R

example {m} (three : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarDispatch.originalBoundTraceIdentityIffSentence three xs w r idx)) :=
  Internal.ObjectScalarDispatch.native_originalBoundTraceIdentityIff three xs w r idx

example {m} (three : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarDispatch.originalBoundPowerTraceIdentityIffSentence three xs w r idx)) :=
  Internal.ObjectScalarDispatch.native_originalBoundPowerTraceIdentityIff three xs w r idx

example {m} (three : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectScalarDispatch.originalBoundTraceRejectionIffSentence three xs w r idx)) :=
  Internal.ObjectScalarDispatch.native_originalBoundTraceRejectionIff three xs w r idx

example {m} {n} (bound : Bool) (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeReplace.originalVariableExprCodeIffSentence bound e env w idx y)) :=
  Internal.ObjectFreeReplace.native_originalVariableExprCodeIff bound e env w idx y

example {m} (bound : Bool) (w idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeReplace.originalVariableCodeNaturalSentence bound w idx y)) :=
  Internal.ObjectFreeReplace.native_originalVariableCodeNatural bound w idx y

example {m} (env : Fin 4 → Fin m) (w R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeReplace.originalFreeReplaceLookupPremiseSoundSentence env w R)) :=
  Internal.ObjectFreeReplace.native_originalFreeReplaceLookupPremiseSound env w R

example {m} (env : Fin 4 → Fin m) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeReplace.originalFreeReplaceMatrixSoundSentence env xs w r R idx)) :=
  Internal.ObjectFreeReplace.native_originalFreeReplaceMatrixSound env xs w r R idx

example {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeReplace.originalFreeReplaceApplicationSoundSentence xs w r R idx)) :=
  Internal.ObjectFreeReplace.native_originalFreeReplaceApplicationSound xs w r R idx

example {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeReplace.originalFreeReplaceTraceExecutionIffSentence xs w r idx)) :=
  Internal.ObjectFreeReplace.native_originalFreeReplaceTraceExecutionIff xs w r idx

example {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeReplace.originalFreeReplacePowerTraceExecutionIffSentence xs w r idx)) :=
  Internal.ObjectFreeReplace.native_originalFreeReplacePowerTraceExecutionIff xs w r idx

example {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeReplace.originalFreeReplaceTraceCandidateRejectionIffSentence xs w r idx)) :=
  Internal.ObjectFreeReplace.native_originalFreeReplaceTraceCandidateRejectionIff xs w r idx

example {m} (w d p x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeReplace.actualOriginalFreeReplaceRootSentence w d p x y)) :=
  Internal.ObjectFreeReplace.native_actualOriginalFreeReplaceRoot w d p x y

example {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeReplace.allInternalFreeReplaceReturnedIffSentence w d p x idx y)) :=
  Internal.ObjectFreeReplace.native_allInternalFreeReplaceReturnedIff w d p x idx y

example {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeReplace.allInternalFreeReplaceCheckedIffSentence w d p x idx y)) :=
  Internal.ObjectFreeReplace.native_allInternalFreeReplaceCheckedIff w d p x idx y

example {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeReplace.validFreeReplaceReturnedExecutionIffSentence w d p x idx y)) :=
  Internal.ObjectFreeReplace.native_validFreeReplaceReturnedExecutionIff w d p x idx y

example {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeReplace.naturalFreeReplaceReturnedStrictIffSentence w d p x idx y)) :=
  Internal.ObjectFreeReplace.native_naturalFreeReplaceReturnedStrictIff w d p x idx y

example {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeReplace.allInternalFreeReplaceCandidateRejectionIffSentence w d p x idx y)) :=
  Internal.ObjectFreeReplace.native_allInternalFreeReplaceCandidateRejectionIff w d p x idx y

example {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeReplace.allInternalFreeReplaceHasOutputGuardedIffSentence w d p x idx)) :=
  Internal.ObjectFreeReplace.native_allInternalFreeReplaceHasOutputGuardedIff w d p x idx

example {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeReplace.allInternalFreeReplaceNoOutputGuardedIffSentence w d p x idx)) :=
  Internal.ObjectFreeReplace.native_allInternalFreeReplaceNoOutputGuardedIff w d p x idx

example {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeReplace.validFreeReplaceHasOutputIffSentence w d p x idx)) :=
  Internal.ObjectFreeReplace.native_validFreeReplaceHasOutputIff w d p x idx

example {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeReplace.validFreeReplaceNoOutputIffSentence w d p x idx)) :=
  Internal.ObjectFreeReplace.native_validFreeReplaceNoOutputIff w d p x idx

example {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeReplace.naturalFreeReplaceStrictNoOutputIffSentence w d p x idx)) :=
  Internal.ObjectFreeReplace.native_naturalFreeReplaceStrictNoOutputIff w d p x idx

example {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeReplace.invalidFreeReplaceGuardNoOutputSentence w d p x idx)) :=
  Internal.ObjectFreeReplace.native_invalidFreeReplaceGuardNoOutput w d p x idx

example {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeReplace.nonNaturalFreeReplaceOutputRejectedSentence w d p x idx y)) :=
  Internal.ObjectFreeReplace.native_nonNaturalFreeReplaceOutputRejected w d p x idx y

example {m} (w d p x idx y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeReplace.allInternalFreeReplaceOutputUniqueSentence w d p x idx y z)) :=
  Internal.ObjectFreeReplace.native_allInternalFreeReplaceOutputUnique w d p x idx y z

example {m} (w idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.actualSuccessorVariableValueSentence w idx)) :=
  Internal.ObjectFreeWeaken.native_actualSuccessorVariableValue w idx

example {m} (w idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.successorVariableValueExactDomainSentence w idx)) :=
  Internal.ObjectFreeWeaken.native_successorVariableValueExactDomain w idx

example {m} (w idx y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.successorVariableValueAtActualSuccessorSentence w idx y s)) :=
  Internal.ObjectFreeWeaken.native_successorVariableValueAtActualSuccessor w idx y s

example {m} (w idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.successorVariableValueNaturalSentence w idx y)) :=
  Internal.ObjectFreeWeaken.native_successorVariableValueNatural w idx y

example {m} (w idx y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.successorVariableValueUniqueSentence w idx y z)) :=
  Internal.ObjectFreeWeaken.native_successorVariableValueUnique w idx y z

example {m} (env : Fin 3 → Fin m) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.originalFreeWeakenMatrixSoundSentence env xs w r R idx)) :=
  Internal.ObjectFreeWeaken.native_originalFreeWeakenMatrixSound env xs w r R idx

example {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.originalFreeWeakenApplicationSoundSentence xs w r R idx)) :=
  Internal.ObjectFreeWeaken.native_originalFreeWeakenApplicationSound xs w r R idx

example {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.originalFreeWeakenTraceValueIffSentence xs w r idx)) :=
  Internal.ObjectFreeWeaken.native_originalFreeWeakenTraceValueIff xs w r idx

example {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.originalFreeWeakenPowerTraceValueIffSentence xs w r idx)) :=
  Internal.ObjectFreeWeaken.native_originalFreeWeakenPowerTraceValueIff xs w r idx

example {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.originalFreeWeakenTraceCandidateRejectionIffSentence xs w r idx)) :=
  Internal.ObjectFreeWeaken.native_originalFreeWeakenTraceCandidateRejectionIff xs w r idx

example {m} (w d p x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.actualOriginalFreeWeakenRootSentence w d p x y)) :=
  Internal.ObjectFreeWeaken.native_actualOriginalFreeWeakenRoot w d p x y

example {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.allInternalFreeWeakenReturnedIffSentence w d p x idx y)) :=
  Internal.ObjectFreeWeaken.native_allInternalFreeWeakenReturnedIff w d p x idx y

example {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.validFreeWeakenReturnedValueIffSentence w d p x idx y)) :=
  Internal.ObjectFreeWeaken.native_validFreeWeakenReturnedValueIff w d p x idx y

example {m} (w d p x idx y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.validFreeWeakenAtActualSuccessorIffSentence w d p x idx y s)) :=
  Internal.ObjectFreeWeaken.native_validFreeWeakenAtActualSuccessorIff w d p x idx y s

example {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.allInternalFreeWeakenCandidateRejectionIffSentence w d p x idx y)) :=
  Internal.ObjectFreeWeaken.native_allInternalFreeWeakenCandidateRejectionIff w d p x idx y

example {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.allInternalFreeWeakenHasOutputIffSentence w d p x idx)) :=
  Internal.ObjectFreeWeaken.native_allInternalFreeWeakenHasOutputIff w d p x idx

example {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.allInternalFreeWeakenNoOutputIffSentence w d p x idx)) :=
  Internal.ObjectFreeWeaken.native_allInternalFreeWeakenNoOutputIff w d p x idx

example {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.validFreeWeakenActualOutputSentence w d p x idx)) :=
  Internal.ObjectFreeWeaken.native_validFreeWeakenActualOutput w d p x idx

example {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.invalidFreeWeakenGuardNoOutputSentence w d p x idx)) :=
  Internal.ObjectFreeWeaken.native_invalidFreeWeakenGuardNoOutput w d p x idx

example {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.nonNaturalFreeWeakenParameterNoOutputSentence w d p x idx)) :=
  Internal.ObjectFreeWeaken.native_nonNaturalFreeWeakenParameterNoOutput w d p x idx

example {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.nonNaturalFreeWeakenDepthNoOutputSentence w d p x idx)) :=
  Internal.ObjectFreeWeaken.native_nonNaturalFreeWeakenDepthNoOutput w d p x idx

example {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.invalidFreeWeakenInputNoOutputSentence w d p x idx)) :=
  Internal.ObjectFreeWeaken.native_invalidFreeWeakenInputNoOutput w d p x idx

example {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.allInternalFreeWeakenOutputNaturalSentence w d p x idx y)) :=
  Internal.ObjectFreeWeaken.native_allInternalFreeWeakenOutputNatural w d p x idx y

example {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.nonNaturalFreeWeakenOutputRejectedSentence w d p x idx y)) :=
  Internal.ObjectFreeWeaken.native_nonNaturalFreeWeakenOutputRejected w d p x idx y

example {m} (w d p x idx y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.allInternalFreeWeakenOutputUniqueSentence w d p x idx y z)) :=
  Internal.ObjectFreeWeaken.native_allInternalFreeWeakenOutputUnique w d p x idx y z

example {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.allFourOriginalVariableTraceValueIffSentence three bound xs w r idx)) :=
  Internal.ObjectFreeWeaken.native_allFourOriginalVariableTraceValueIff three bound xs w r idx

example {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.allFourOriginalVariablePowerTraceValueIffSentence three bound xs w r idx)) :=
  Internal.ObjectFreeWeaken.native_allFourOriginalVariablePowerTraceValueIff three bound xs w r idx

example {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFreeWeaken.allFourOriginalVariableCandidateRejectionIffSentence three bound xs w r idx)) :=
  Internal.ObjectFreeWeaken.native_allFourOriginalVariableCandidateRejectionIff three bound xs w r idx

example {m} (w depth a b c L I R n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalTermProgram.replace_checked_iffSentence w depth a b c L I R n q)) :=
  Internal.ObjectOriginalTermProgram.native_replace_checked_iff w depth a b c L I R n q

example {m} (w depth a b c L I R n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalTermProgram.replace_coded_iffSentence w depth a b c L I R n q)) :=
  Internal.ObjectOriginalTermProgram.native_replace_coded_iff w depth a b c L I R n q

example {m} (w depth parameter a b B I J R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalTermProgram.weaken_checked_iffSentence w depth parameter a b B I J R S n q)) :=
  Internal.ObjectOriginalTermProgram.native_weaken_checked_iff w depth parameter a b B I J R S n q

example {m} (w depth parameter a b B I J R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalTermProgram.weaken_coded_iffSentence w depth parameter a b B I J R S n q)) :=
  Internal.ObjectOriginalTermProgram.native_weaken_coded_iff w depth parameter a b B I J R S n q

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentsTrace.actualUniversalOriginalTraceSentence w)) :=
  Internal.ObjectOriginalArgumentsTrace.native_actualUniversalOriginalTrace w

example {m} (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentsTrace.universalOriginalTraceMembershipIffSentence w V r)) :=
  Internal.ObjectOriginalArgumentsTrace.native_universalOriginalTraceMembershipIff w V r

example {m} (w V R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentsTrace.everyClosedOriginalTraceIncludedSentence w V R)) :=
  Internal.ObjectOriginalArgumentsTrace.native_everyClosedOriginalTraceIncluded w V R

example {m} (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentsTrace.universalOriginalTraceClosedSentence w V)) :=
  Internal.ObjectOriginalArgumentsTrace.native_universalOriginalTraceClosed w V

example {m} (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentsTrace.originalFullTraceOneStepIffSentence w V r)) :=
  Internal.ObjectOriginalArgumentsTrace.native_originalFullTraceOneStepIff w V r

example {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (_hr : rule ∈ YesMetaZFC.Automation.ObjectSyntaxTransform.rules) (env : Fin rule.arity → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentsTrace.originalWholeTableRuleFromTracesSentence rule _hr env w r)) :=
  Internal.ObjectOriginalArgumentsTrace.native_originalWholeTableRuleFromTraces rule _hr env w r

example {m} (xs : Fin 5 → Fin m) (w r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentsTrace.originalArgumentFullTableDispatchIffSentence xs w r R)) :=
  Internal.ObjectOriginalArgumentsTrace.native_originalArgumentFullTableDispatchIff xs w r R

example {m} (xs : Fin 5 → Fin m) (w r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentsTrace.originalArgumentTraceSelectedIffSentence xs w r V)) :=
  Internal.ObjectOriginalArgumentsTrace.native_originalArgumentTraceSelectedIff xs w r V

example {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentsTrace.originalNilArgumentsTraceSentence env w r)) :=
  Internal.ObjectOriginalArgumentsTrace.native_originalNilArgumentsTrace env w r

example {m} (env : Fin 7 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentsTrace.originalConsArgumentsTraceSentence env w r)) :=
  Internal.ObjectOriginalArgumentsTrace.native_originalConsArgumentsTrace env w r

example {m} (env : Fin 7 → Fin m) (w r first rest : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentsTrace.originalConsArgumentActualChildTracesSentence env w r first rest)) :=
  Internal.ObjectOriginalArgumentsTrace.native_originalConsArgumentActualChildTraces env w r first rest

example {m} (three : Bool) (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentMatrix.nilModeZeroThreeGuardSentence three env w)) :=
  Internal.ObjectOriginalArgumentMatrix.native_nilModeZeroThreeGuard three env w

example {m} (arity : Nat) (env : Fin arity → Fin m) (w y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentMatrix.allCandidateEmptyExprNilIffSentence arity env w y)) :=
  Internal.ObjectOriginalArgumentMatrix.native_allCandidateEmptyExprNilIff arity env w y

example {m} (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentMatrix.nilActualHeadNumericIffSentence env w n q r)) :=
  Internal.ObjectOriginalArgumentMatrix.native_nilActualHeadNumericIff env w n q r

example {m} (env : Fin 7 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentMatrix.consActualHeadNumericIffSentence env w n q r)) :=
  Internal.ObjectOriginalArgumentMatrix.native_consActualHeadNumericIff env w n q r

example {m} (env : Fin 7 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentMatrix.headActualChildTraceNumericIffSentence env w)) :=
  Internal.ObjectOriginalArgumentMatrix.native_headActualChildTraceNumericIff env w

example {m} (env : Fin 7 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentMatrix.tailActualChildTraceNumericIffSentence env w)) :=
  Internal.ObjectOriginalArgumentMatrix.native_tailActualChildTraceNumericIff env w

example {m} (three : Bool) (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentMatrix.nilFullTracedMatrixNumericIffSentence three env w n q r)) :=
  Internal.ObjectOriginalArgumentMatrix.native_nilFullTracedMatrixNumericIff three env w n q r

example {m} (env : Fin 7 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentMatrix.consFullTracedMatrixNumericIffSentence env w n q r)) :=
  Internal.ObjectOriginalArgumentMatrix.native_consFullTracedMatrixNumericIff env w n q r

example {m} (env : Fin 7 → Fin m) (w V n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentMatrix.consOriginalMatrixNumericIffSentence env w V n q r)) :=
  Internal.ObjectOriginalArgumentMatrix.native_consOriginalMatrixNumericIff env w V n q r

example {m} (three : Bool) (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentMatrix.nilAllCandidateRowMatrixIffSentence three env w n q r)) :=
  Internal.ObjectOriginalArgumentMatrix.native_nilAllCandidateRowMatrixIff three env w n q r

example {m} (env : Fin 7 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentMatrix.consAllCandidateRowMatrixIffSentence env w n q r)) :=
  Internal.ObjectOriginalArgumentMatrix.native_consAllCandidateRowMatrixIff env w n q r

example {m} (kind : Nat) (w mode depth parameter input output : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentRun.originalRunInputNaturalSentence kind w mode depth parameter input output)) :=
  Internal.ObjectOriginalArgumentRun.native_originalRunInputNatural kind w mode depth parameter input output

example {m} (kind : Nat) (w mode depth parameter input output : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentRun.originalRunOutputNaturalSentence kind w mode depth parameter input output)) :=
  Internal.ObjectOriginalArgumentRun.native_originalRunOutputNatural kind w mode depth parameter input output

example {m} (w mode depth parameter input output : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentRun.actualOriginalArgumentRootSentence w mode depth parameter input output)) :=
  Internal.ObjectOriginalArgumentRun.native_actualOriginalArgumentRoot w mode depth parameter input output

example {m} (w mode depth parameter input output : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentRun.originalArgumentOutcomesNaturalSentence w mode depth parameter input output)) :=
  Internal.ObjectOriginalArgumentRun.native_originalArgumentOutcomesNatural w mode depth parameter input output

example {m} (three : Bool) (w mode depth parameter input output r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentRun.originalNilApplicationExactIffSentence three w mode depth parameter input output r V)) :=
  Internal.ObjectOriginalArgumentRun.native_originalNilApplicationExactIff three w mode depth parameter input output r V

example {m} (w mode depth parameter input output r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentRun.originalConsApplicationExactIffSentence w mode depth parameter input output r V)) :=
  Internal.ObjectOriginalArgumentRun.native_originalConsApplicationExactIff w mode depth parameter input output r V

example {m} (three : Bool) (w mode depth parameter input output r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentRun.originalArgumentTraceCasesExactIffSentence three w mode depth parameter input output r)) :=
  Internal.ObjectOriginalArgumentRun.native_originalArgumentTraceCasesExactIff three w mode depth parameter input output r

example {m} (three : Bool) (w mode depth parameter input output : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentRun.originalArgumentWholeRunCasesExactIffSentence three w mode depth parameter input output)) :=
  Internal.ObjectOriginalArgumentRun.native_originalArgumentWholeRunCasesExactIff three w mode depth parameter input output

example {m} (three : Bool) (w mode depth parameter input output : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTypedArgumentList.numericTermModeRunIffSentence three w mode depth parameter input output)) :=
  Internal.ObjectTypedArgumentList.native_numericTermModeRunIff three w mode depth parameter input output

example {m} (w mode depth a b c L I R n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTypedArgumentList.numericReplaceOnTypedTermSentence w mode depth a b c L I R n q)) :=
  Internal.ObjectTypedArgumentList.native_numericReplaceOnTypedTerm w mode depth a b c L I R n q

example {m} (w mode depth parameter a b B I J R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTypedArgumentList.numericWeakenOnTypedTermSentence w mode depth parameter a b B I J R S n q)) :=
  Internal.ObjectTypedArgumentList.native_numericWeakenOnTypedTerm w mode depth parameter a b B I J R S n q

example {m} (w z a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTypedArgumentList.typedNilListIntroductionSentence w z a b n)) :=
  Internal.ObjectTypedArgumentList.native_typedNilListIntroduction w z a b n

example {m} (w ell k a b h t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTypedArgumentList.typedConsListIntroductionSentence w ell k a b h t n)) :=
  Internal.ObjectTypedArgumentList.native_typedConsListIntroduction w ell k a b h t n

example {m} (w k a b h t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTypedArgumentList.typedConsActualPredecessorSentence w k a b h t n)) :=
  Internal.ObjectTypedArgumentList.native_typedConsActualPredecessor w k a b h t n

example {m} (w k a b h t n ell : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTypedArgumentList.typedConsHeadSentence w k a b h t n ell)) :=
  Internal.ObjectTypedArgumentList.native_typedConsHead w k a b h t n ell

example {m} (w k a b h t n ell : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTypedArgumentList.typedConsTailSentence w k a b h t n ell)) :=
  Internal.ObjectTypedArgumentList.native_typedConsTail w k a b h t n ell

example {m} (w k a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTypedArgumentList.typedNilListIffSentence w k a b n)) :=
  Internal.ObjectTypedArgumentList.native_typedNilListIff w k a b n

example {m} (w k a b n h t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTypedArgumentList.typedConsListIffSentence w k a b n h t)) :=
  Internal.ObjectTypedArgumentList.native_typedConsListIff w k a b n h t

example {m} (w k a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectTypedArgumentList.typedWholeListCasesIffSentence w k a b n)) :=
  Internal.ObjectTypedArgumentList.native_typedWholeListCasesIff w k a b n

example {m} (w mode depth a b c L I R n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalNumericTermFiber.replaceWholeTermAgreementSentence w mode depth a b c L I R n)) :=
  Internal.ObjectOriginalNumericTermFiber.native_replaceWholeTermAgreement w mode depth a b c L I R n

example {m} (w mode depth a b c L I R n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalNumericTermFiber.replaceActualOriginalTermFiberSentence w mode depth a b c L I R n)) :=
  Internal.ObjectOriginalNumericTermFiber.native_replaceActualOriginalTermFiber w mode depth a b c L I R n

example {m} (w mode depth a b c L I R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalNumericTermFiber.replaceAllInternalTermPromiseSentence w mode depth a b c L I R)) :=
  Internal.ObjectOriginalNumericTermFiber.native_replaceAllInternalTermPromise w mode depth a b c L I R

example {m} (w mode depth parameter a b B I J R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalNumericTermFiber.weakenWholeTermAgreementSentence w mode depth parameter a b B I J R S n)) :=
  Internal.ObjectOriginalNumericTermFiber.native_weakenWholeTermAgreement w mode depth parameter a b B I J R S n

example {m} (w mode depth parameter a b B I J R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalNumericTermFiber.weakenActualOriginalTermFiberSentence w mode depth parameter a b B I J R S n)) :=
  Internal.ObjectOriginalNumericTermFiber.native_weakenActualOriginalTermFiber w mode depth parameter a b B I J R S n

example {m} (w mode depth parameter a b B I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalNumericTermFiber.weakenAllInternalTermPromiseSentence w mode depth parameter a b B I J R S)) :=
  Internal.ObjectOriginalNumericTermFiber.native_weakenAllInternalTermPromise w mode depth parameter a b B I J R S

example {m} (w mode depth parameter R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalNumericTermFiber.originalTermValueTransferSentence w mode depth parameter R S a b c d n q)) :=
  Internal.ObjectOriginalNumericTermFiber.native_originalTermValueTransfer w mode depth parameter R S a b c d n q

example {m} (w mode depth parameter R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalNumericTermFiber.originalTermFiberTransferSentence w mode depth parameter R S a b c d n)) :=
  Internal.ObjectOriginalNumericTermFiber.native_originalTermFiberTransfer w mode depth parameter R S a b c d n

example {m} (w mode depth parameter c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalNumericTermFiber.originalTermValueTargetTypeSentence w mode depth parameter c d n q)) :=
  Internal.ObjectOriginalNumericTermFiber.native_originalTermValueTargetType w mode depth parameter c d n q

example {m} (w mode depth parameter c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalNumericTermFiber.originalTermAllCandidateUniqueSentence w mode depth parameter c d n q v)) :=
  Internal.ObjectOriginalNumericTermFiber.native_originalTermAllCandidateUnique w mode depth parameter c d n q v

example {m} (kind : Nat) (w mode depth parameter input output replacement : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentFiber.originalRunInputSubstitutionSentence kind w mode depth parameter input output replacement)) :=
  Internal.ObjectOriginalArgumentFiber.native_originalRunInputSubstitution kind w mode depth parameter input output replacement

example {m} (kind : Nat) (w mode depth parameter input output replacement : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentFiber.originalRunOutputSubstitutionSentence kind w mode depth parameter input output replacement)) :=
  Internal.ObjectOriginalArgumentFiber.native_originalRunOutputSubstitution kind w mode depth parameter input output replacement

example {m} (w mode depth parameter k c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentFiber.originalListValueTargetTypeSentence w mode depth parameter k c d n q)) :=
  Internal.ObjectOriginalArgumentFiber.native_originalListValueTargetType w mode depth parameter k c d n q

example {m} (w mode depth parameter k c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentFiber.originalListAllCandidateUniqueSentence w mode depth parameter k c d n q v)) :=
  Internal.ObjectOriginalArgumentFiber.native_originalListAllCandidateUnique w mode depth parameter k c d n q v

example {m} (three : Bool) (w mode depth parameter k c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentFiber.originalNilListActualValueSentence three w mode depth parameter k c d n q)) :=
  Internal.ObjectOriginalArgumentFiber.native_originalNilListActualValue three w mode depth parameter k c d n q

example {m} (three : Bool) (w mode depth parameter ell k c d n q h t H T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentFiber.originalConsListActualValueSentence three w mode depth parameter ell k c d n q h t H T)) :=
  Internal.ObjectOriginalArgumentFiber.native_originalConsListActualValue three w mode depth parameter ell k c d n q h t H T

example {m} (three : Bool) (w mode depth parameter a b c d n k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentFiber.originalAllInternalTypedListFiberSentence three w mode depth parameter a b c d n k)) :=
  Internal.ObjectOriginalArgumentFiber.native_originalAllInternalTypedListFiber three w mode depth parameter a b c d n k

example {m} (three : Bool) (w mode depth parameter a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentFiber.originalAllInternalListCodePropertiesSentence three w mode depth parameter a b c d)) :=
  Internal.ObjectOriginalArgumentFiber.native_originalAllInternalListCodeProperties three w mode depth parameter a b c d

example {m} (w mode depth a b c L I R n k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentFiber.replaceAllInternalOriginalListFiberSentence w mode depth a b c L I R n k)) :=
  Internal.ObjectOriginalArgumentFiber.native_replaceAllInternalOriginalListFiber w mode depth a b c L I R n k

example {m} (w mode depth parameter a b B I J R S n k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentFiber.weakenAllInternalOriginalListFiberSentence w mode depth parameter a b B I J R S n k)) :=
  Internal.ObjectOriginalArgumentFiber.native_weakenAllInternalOriginalListFiber w mode depth parameter a b B I J R S n k

example {m} (w mode depth parameter k c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentFields.allCandidateOriginalListValueSentence w mode depth parameter k c d n q)) :=
  Internal.ObjectOriginalArgumentFields.native_allCandidateOriginalListValue w mode depth parameter k c d n q

example {m} (three : Bool) (w mode depth parameter a b n k q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentFields.originalAllInternalArgumentFieldsSentence three w mode depth parameter a b n k q)) :=
  Internal.ObjectOriginalArgumentFields.native_originalAllInternalArgumentFields three w mode depth parameter a b n k q

example {m} (three : Bool) (w mode depth parameter a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentFields.originalAllInternalFieldCodePropertiesSentence three w mode depth parameter a b)) :=
  Internal.ObjectOriginalArgumentFields.native_originalAllInternalFieldCodeProperties three w mode depth parameter a b

example {m} (w mode depth parameter a b c d k n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentFields.allInternalFieldImageOutputUniqueSentence w mode depth parameter a b c d k n q r)) :=
  Internal.ObjectOriginalArgumentFields.native_allInternalFieldImageOutputUnique w mode depth parameter a b c d k n q r

example {m} (three : Bool) (w mode depth parameter a b c d n k q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentFields.originalRunAllFieldImageIffSentence three w mode depth parameter a b c d n k q)) :=
  Internal.ObjectOriginalArgumentFields.native_originalRunAllFieldImageIff three w mode depth parameter a b c d n k q

example {m} (w mode depth a b c L I R n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentFields.replaceAllInternalProgramFieldsIffSentence w mode depth a b c L I R n q k)) :=
  Internal.ObjectOriginalArgumentFields.native_replaceAllInternalProgramFieldsIff w mode depth a b c L I R n q k

example {m} (w mode depth a b c L I R n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentFields.replaceWholeOriginalArgumentProgramIffSentence w mode depth a b c L I R n q k)) :=
  Internal.ObjectOriginalArgumentFields.native_replaceWholeOriginalArgumentProgramIff w mode depth a b c L I R n q k

example {m} (w mode depth parameter a b B I J R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentFields.weakenAllInternalProgramFieldsIffSentence w mode depth parameter a b B I J R S n q k)) :=
  Internal.ObjectOriginalArgumentFields.native_weakenAllInternalProgramFieldsIff w mode depth parameter a b B I J R S n q k

example {m} (w mode depth parameter a b B I J R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentFields.weakenWholeOriginalArgumentProgramIffSentence w mode depth parameter a b B I J R S n q k)) :=
  Internal.ObjectOriginalArgumentFields.native_weakenWholeOriginalArgumentProgramIff w mode depth parameter a b B I J R S n q k

example {m} (w mode depth parameter ell k h t H T n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentFields.originalConsAllInternalFieldsSentence w mode depth parameter ell k h t H T n q)) :=
  Internal.ObjectOriginalArgumentFields.native_originalConsAllInternalFields w mode depth parameter ell k h t H T n q

example {m} (xs : Fin 5 → Fin m) (w r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaMatrix.originalKindThreeWholeTableDispatchSentence xs w r R)) :=
  Internal.ObjectOriginalFormulaMatrix.native_originalKindThreeWholeTableDispatch xs w r R

example {m} (xs : Fin 5 → Fin m) (w r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaMatrix.originalKindThreeTraceSelectedIffSentence xs w r V)) :=
  Internal.ObjectOriginalFormulaMatrix.native_originalKindThreeTraceSelectedIff xs w r V

example {m} (a kind : Nat) (j0 j1 j2 : Fin a) (e f : YesMetaZFC.Automation.ObjectHorn.Expr a) (env : Fin a → Fin m) (w mode depth parameter n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaMatrix.originalFormulaHeadMetadataSentence a kind j0 j1 j2 e f env w mode depth parameter n q r)) :=
  Internal.ObjectOriginalFormulaMatrix.native_originalFormulaHeadMetadata a kind j0 j1 j2 e f env w mode depth parameter n q r

example {m} (a : Nat) (i j : Fin a) (env : Fin a → Fin m) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaMatrix.originalFormulaApplicationNumericIffSentence a i j env w n)) :=
  Internal.ObjectOriginalFormulaMatrix.native_originalFormulaApplicationNumericIff a i j env w n

example {m} (three : Bool) (tag : Nat) (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaMatrix.originalFormulaConstantNumericMatrixSentence three tag env w n q r)) :=
  Internal.ObjectOriginalFormulaMatrix.native_originalFormulaConstantNumericMatrix three tag env w n q r

example {m} (tag kind : Nat) (env : Fin 7 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaMatrix.originalFormulaBinaryNumericMatrixSentence tag kind env w n q r)) :=
  Internal.ObjectOriginalFormulaMatrix.native_originalFormulaBinaryNumericMatrix tag kind env w n q r

example {m} (tag : Nat) (env : Fin 5 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaMatrix.originalFormulaNonbinderNumericMatrixSentence tag env w n q r)) :=
  Internal.ObjectOriginalFormulaMatrix.native_originalFormulaNonbinderNumericMatrix tag env w n q r

example {m} (tag : Nat) (env : Fin 5 → Fin m) (w n q r childDepth : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaMatrix.originalFormulaBinderNumericMatrixSentence tag env w n q r childDepth)) :=
  Internal.ObjectOriginalFormulaMatrix.native_originalFormulaBinderNumericMatrix tag env w n q r childDepth

example {m} (env : Fin 6 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaMatrix.originalFormulaApplicationNumericMatrixSentence env w n q r)) :=
  Internal.ObjectOriginalFormulaMatrix.native_originalFormulaApplicationNumericMatrix env w n q r

example {m} (env : Fin 5 → Fin m) (w childDepth : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaMatrix.originalFormulaBinderActualChildRunSentence env w childDepth)) :=
  Internal.ObjectOriginalFormulaMatrix.native_originalFormulaBinderActualChildRun env w childDepth

example {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (_hr : rule ∈ OriginalFormulaClasses.selected) (env : Fin rule.arity → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaMatrix.originalElevenRuleTraceCompositionSentence rule _hr env w r)) :=
  Internal.ObjectOriginalFormulaMatrix.native_originalElevenRuleTraceComposition rule _hr env w r

example {m} (three : Bool) (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.constant tag) ∈ OriginalFormulaClasses.selected) (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaMatrix.originalFormulaConstantTraceFromDataSentence three tag _hr env w n q r)) :=
  Internal.ObjectOriginalFormulaMatrix.native_originalFormulaConstantTraceFromData three tag _hr env w n q r

example {m} (tag kind : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.binary tag kind) ∈ OriginalFormulaClasses.selected) (env : Fin 7 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaMatrix.originalFormulaBinaryTraceFromDataSentence tag kind _hr env w n q r)) :=
  Internal.ObjectOriginalFormulaMatrix.native_originalFormulaBinaryTraceFromData tag kind _hr env w n q r

example {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag false) ∈ OriginalFormulaClasses.selected) (env : Fin 5 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaMatrix.originalFormulaNonbinderTraceFromDataSentence tag _hr env w n q r)) :=
  Internal.ObjectOriginalFormulaMatrix.native_originalFormulaNonbinderTraceFromData tag _hr env w n q r

example {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag true) ∈ OriginalFormulaClasses.selected) (env : Fin 5 → Fin m) (w n q r childDepth : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaMatrix.originalFormulaBinderTraceFromDataSentence tag _hr env w n q r childDepth)) :=
  Internal.ObjectOriginalFormulaMatrix.native_originalFormulaBinderTraceFromData tag _hr env w n q r childDepth

example {m} (env : Fin 6 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaMatrix.originalFormulaApplicationTraceFromDataSentence env w n q r)) :=
  Internal.ObjectOriginalFormulaMatrix.native_originalFormulaApplicationTraceFromData env w n q r

example {m} (three : Bool) (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.constant tag) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaEquation.originalFormulaConstantAssignmentEliminatedSentence three tag _hr w mode depth parameter n q r V)) :=
  Internal.ObjectOriginalFormulaEquation.native_originalFormulaConstantAssignmentEliminated three tag _hr w mode depth parameter n q r V

example {m} (tag kind : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.binary tag kind) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaEquation.originalFormulaBinaryAssignmentEliminatedSentence tag kind _hr w mode depth parameter n q r V)) :=
  Internal.ObjectOriginalFormulaEquation.native_originalFormulaBinaryAssignmentEliminated tag kind _hr w mode depth parameter n q r V

example {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag false) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaEquation.originalFormulaNonbinderAssignmentEliminatedSentence tag _hr w mode depth parameter n q r V)) :=
  Internal.ObjectOriginalFormulaEquation.native_originalFormulaNonbinderAssignmentEliminated tag _hr w mode depth parameter n q r V

example {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag true) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaEquation.originalFormulaBinderAssignmentEliminatedSentence tag _hr w mode depth parameter n q r V)) :=
  Internal.ObjectOriginalFormulaEquation.native_originalFormulaBinderAssignmentEliminated tag _hr w mode depth parameter n q r V

example {m} (w mode depth parameter n q r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaEquation.originalFormulaApplicationAssignmentEliminatedSentence w mode depth parameter n q r V)) :=
  Internal.ObjectOriginalFormulaEquation.native_originalFormulaApplicationAssignmentEliminated w mode depth parameter n q r V

example {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag true) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V childDepth : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaEquation.originalFormulaBinderAtActualSuccessorSentence tag _hr w mode depth parameter n q r V childDepth)) :=
  Internal.ObjectOriginalFormulaEquation.native_originalFormulaBinderAtActualSuccessor tag _hr w mode depth parameter n q r V childDepth

example {m} (three : Bool) (w mode depth parameter n q r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaEquation.originalFormulaElevenCasesAtTraceValueSentence three w mode depth parameter n q r V)) :=
  Internal.ObjectOriginalFormulaEquation.native_originalFormulaElevenCasesAtTraceValue three w mode depth parameter n q r V

example {m} (three : Bool) (w mode depth parameter n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaEquation.originalFormulaElevenCasesAtRowSentence three w mode depth parameter n q r)) :=
  Internal.ObjectOriginalFormulaEquation.native_originalFormulaElevenCasesAtRow three w mode depth parameter n q r

example {m} (w mode depth parameter n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaEquation.originalFormulaElevenCasesInputOutputNaturalSentence w mode depth parameter n q)) :=
  Internal.ObjectOriginalFormulaEquation.native_originalFormulaElevenCasesInputOutputNatural w mode depth parameter n q

example {m} (three : Bool) (w mode depth parameter n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaEquation.originalFormulaWholeRunElevenCasesSentence three w mode depth parameter n q)) :=
  Internal.ObjectOriginalFormulaEquation.native_originalFormulaWholeRunElevenCases three w mode depth parameter n q

example {m} (k : Nat) (xs : Fin k → Fin m) (w symbol s args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalMemberApplication.originalAppHeadForestConstructorIffSentence k xs w symbol s args n)) :=
  Internal.ObjectOriginalMemberApplication.native_originalAppHeadForestConstructorIff k xs w symbol s args n

example {m} (k : Nat) (xs : Fin k → Fin m) (w symbol s args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalMemberApplication.originalAppHeadForestRecoveredSentence k xs w symbol s args n)) :=
  Internal.ObjectOriginalMemberApplication.native_originalAppHeadForestRecovered k xs w symbol s args n

example {m} (w z s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalMemberApplication.originalMemberScalarAtZeroIndexSentence w z s)) :=
  Internal.ObjectOriginalMemberApplication.native_originalMemberScalarAtZeroIndex w z s

example {m} (w z s x y args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalMemberApplication.originalMemberAtTwoArgumentForestIffSentence w z s x y args n)) :=
  Internal.ObjectOriginalMemberApplication.native_originalMemberAtTwoArgumentForestIff w z s x y args n

example {m} (w symbol s x y args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalMemberApplication.originalMemberAppZeroAndTwoArgumentsRecoveredSentence w symbol s x y args n)) :=
  Internal.ObjectOriginalMemberApplication.native_originalMemberAppZeroAndTwoArgumentsRecovered w symbol s x y args n

example {m} (w symbol s x y args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalMemberApplication.originalMemberAppAtNaturalArgumentsIffSentence w symbol s x y args n)) :=
  Internal.ObjectOriginalMemberApplication.native_originalMemberAppAtNaturalArgumentsIff w symbol s x y args n

example {m} (w symbol s x y args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalMemberApplication.originalMemberCheckedAppIffSentence w symbol s x y args n)) :=
  Internal.ObjectOriginalMemberApplication.native_originalMemberCheckedAppIff w symbol s x y args n

example {m} (w mode depth parameter s x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalMemberApplication.originalMemberApplicationCaseIffSentence w mode depth parameter s x y n q)) :=
  Internal.ObjectOriginalMemberApplication.native_originalMemberApplicationCaseIff w mode depth parameter s x y n q

example {m} (k : Nat) (xs : Fin k → Fin m) (w len a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentPair.finiteForestTypedListIffSentence k xs w len a b n)) :=
  Internal.ObjectOriginalArgumentPair.native_finiteForestTypedListIff k xs w len a b n

example {m} (k : Nat) (xs ys : Fin k → Fin m) (w R S len n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentPair.finiteForestAllIndexProgramFieldsIffSentence k xs ys w R S len n q)) :=
  Internal.ObjectOriginalArgumentPair.native_finiteForestAllIndexProgramFieldsIff k xs ys w R S len n q

example {m} (k : Nat) (xs ys : Fin k → Fin m) (w R S len c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentPair.finiteForestMappedProgramIffSentence k xs ys w R S len c d n q)) :=
  Internal.ObjectOriginalArgumentPair.native_finiteForestMappedProgramIff k xs ys w R S len c d n q

example {m} (k : Nat) (xs ys : Fin k → Fin m) (w mode depth a b c L I R n q len : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentPair.replaceOriginalRunAtFiniteForestsIffSentence k xs ys w mode depth a b c L I R n q len)) :=
  Internal.ObjectOriginalArgumentPair.native_replaceOriginalRunAtFiniteForestsIff k xs ys w mode depth a b c L I R n q len

example {m} (k : Nat) (xs ys : Fin k → Fin m) (w mode depth parameter a b B I J R S n q len : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentPair.weakenOriginalRunAtFiniteForestsIffSentence k xs ys w mode depth parameter a b B I J R S n q len)) :=
  Internal.ObjectOriginalArgumentPair.native_weakenOriginalRunAtFiniteForestsIff k xs ys w mode depth parameter a b B I J R S n q len

example {m} (w len a b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentPair.twoArgumentListActualForestWitnessSentence w len a b q)) :=
  Internal.ObjectOriginalArgumentPair.native_twoArgumentListActualForestWitness w len a b q

example {m} (w R S len c d n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentPair.twoArgumentMappedAllCandidatesIffSentence w R S len c d n q x y)) :=
  Internal.ObjectOriginalArgumentPair.native_twoArgumentMappedAllCandidatesIff w R S len c d n q x y

example {m} (w mode depth a b c L I R n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentPair.replaceOriginalTwoArgumentAllCandidatesIffSentence w mode depth a b c L I R n q x y)) :=
  Internal.ObjectOriginalArgumentPair.native_replaceOriginalTwoArgumentAllCandidatesIff w mode depth a b c L I R n q x y

example {m} (w mode depth parameter a b B I J R S n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentPair.weakenOriginalTwoArgumentAllCandidatesIffSentence w mode depth parameter a b B I J R S n q x y)) :=
  Internal.ObjectOriginalArgumentPair.native_weakenOriginalTwoArgumentAllCandidatesIff w mode depth parameter a b B I J R S n q x y

example {m} (w len z e x y q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalArgumentPair.twoArgumentForestRecoveredFromActualFieldsSentence w len z e x y q)) :=
  Internal.ObjectOriginalArgumentPair.native_twoArgumentForestRecoveredFromActualFields w len z e x y q

example {m} (w mode depth a b c L I R x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalMemberProgram.replaceMemberPairAllInternalAgreementSentence w mode depth a b c L I R x y)) :=
  Internal.ObjectOriginalMemberProgram.native_replaceMemberPairAllInternalAgreement w mode depth a b c L I R x y

example {m} (w mode depth parameter a b B I J R S x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalMemberProgram.weakenMemberPairAllInternalAgreementSentence w mode depth parameter a b B I J R S x y)) :=
  Internal.ObjectOriginalMemberProgram.native_weakenMemberPairAllInternalAgreement w mode depth parameter a b B I J R S x y

example {m} (w mode depth parameter s x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalMemberProgram.originalMemberWholeElevenCaseDispatchIffSentence w mode depth parameter s x y n q)) :=
  Internal.ObjectOriginalMemberProgram.native_originalMemberWholeElevenCaseDispatchIff w mode depth parameter s x y n q

example {m} (three : Bool) (w mode depth parameter s x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalMemberProgram.originalMemberWholeRunApplicationIffSentence three w mode depth parameter s x y n q)) :=
  Internal.ObjectOriginalMemberProgram.native_originalMemberWholeRunApplicationIff three w mode depth parameter s x y n q

example {m} (w mode depth parameter R S c d s x y q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalMemberProgram.originalMembershipCaseProgramIffSentence w mode depth parameter R S c d s x y q)) :=
  Internal.ObjectOriginalMemberProgram.native_originalMembershipCaseProgramIff w mode depth parameter R S c d s x y q

example {m} (w mode depth parameter R S c d s x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalMemberProgram.originalMemberApplicationProgramIffSentence w mode depth parameter R S c d s x y n q)) :=
  Internal.ObjectOriginalMemberProgram.native_originalMemberApplicationProgramIff w mode depth parameter R S c d s x y n q

example {m} (w mode depth a b c L I R n q x y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalMemberProgram.replaceOriginalMemberApplicationProgramIffSentence w mode depth a b c L I R n q x y s)) :=
  Internal.ObjectOriginalMemberProgram.native_replaceOriginalMemberApplicationProgramIff w mode depth a b c L I R n q x y s

example {m} (w mode depth a b c L I R n q x y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalMemberProgram.replaceOriginalMemberWholeRunProgramIffSentence w mode depth a b c L I R n q x y s)) :=
  Internal.ObjectOriginalMemberProgram.native_replaceOriginalMemberWholeRunProgramIff w mode depth a b c L I R n q x y s

example {m} (w mode depth parameter a b B I J R S n q x y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalMemberProgram.weakenOriginalMemberApplicationProgramIffSentence w mode depth parameter a b B I J R S n q x y s)) :=
  Internal.ObjectOriginalMemberProgram.native_weakenOriginalMemberApplicationProgramIff w mode depth parameter a b B I J R S n q x y s

example {m} (w mode depth parameter a b B I J R S n q x y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalMemberProgram.weakenOriginalMemberWholeRunProgramIffSentence w mode depth parameter a b B I J R S n q x y s)) :=
  Internal.ObjectOriginalMemberProgram.native_weakenOriginalMemberWholeRunProgramIff w mode depth parameter a b B I J R S n q x y s

example {m} (w R S a b c d s x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectExistingAtomicInterfaces.memberResultExistingAtomIffSentence w R S a b c d s x y n q)) :=
  Internal.ObjectExistingAtomicInterfaces.native_memberResultExistingAtomIff w R S a b c d s x y n q

example {m} (w mode depth a b c L I R n q x y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectExistingAtomicInterfaces.replaceWholeMemberExistingAtomIffSentence w mode depth a b c L I R n q x y s)) :=
  Internal.ObjectExistingAtomicInterfaces.native_replaceWholeMemberExistingAtomIff w mode depth a b c L I R n q x y s

example {m} (w mode depth parameter a b B I J R S n q x y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectExistingAtomicInterfaces.weakenWholeMemberExistingAtomIffSentence w mode depth parameter a b B I J R S n q x y s)) :=
  Internal.ObjectExistingAtomicInterfaces.native_weakenWholeMemberExistingAtomIff w mode depth parameter a b B I J R S n q x y s

example {m} (w mode depth a b c L I R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectExistingAtomicInterfaces.replaceAllInternalCheckedTermAgreementSentence w mode depth a b c L I R)) :=
  Internal.ObjectExistingAtomicInterfaces.native_replaceAllInternalCheckedTermAgreement w mode depth a b c L I R

example {m} (w mode depth parameter a b B I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectExistingAtomicInterfaces.weakenAllInternalCheckedTermAgreementSentence w mode depth parameter a b B I J R S)) :=
  Internal.ObjectExistingAtomicInterfaces.native_weakenAllInternalCheckedTermAgreement w mode depth parameter a b B I J R S

example {m} (w mode depth parameter R S a b c d x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectExistingAtomicInterfaces.equalityLocalCaseExistingAtomIffSentence w mode depth parameter R S a b c d x y n q)) :=
  Internal.ObjectExistingAtomicInterfaces.native_equalityLocalCaseExistingAtomIff w mode depth parameter R S a b c d x y n q

example {m} (w mode depth a b c L I R n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectExistingAtomicInterfaces.replaceEqualityLocalExistingAtomIffSentence w mode depth a b c L I R n q x y)) :=
  Internal.ObjectExistingAtomicInterfaces.native_replaceEqualityLocalExistingAtomIff w mode depth a b c L I R n q x y

example {m} (w mode depth parameter a b B I J R S n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectExistingAtomicInterfaces.weakenEqualityLocalExistingAtomIffSentence w mode depth parameter a b B I J R S n q x y)) :=
  Internal.ObjectExistingAtomicInterfaces.native_weakenEqualityLocalExistingAtomIff w mode depth parameter a b B I J R S n q x y

example {m} (truth : Bool) (w a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectExistingAtomicInterfaces.constantDataExistingAtomIffSentence truth w a b c d n q)) :=
  Internal.ObjectExistingAtomicInterfaces.native_constantDataExistingAtomIff truth w a b c d n q

example {m} (k tag : Nat) (hne : tag ≠ 2) (xs : Fin k → Fin m) (w symbol args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectWholeAtomicInterfaces.rawApplicationWrongTagRejectedSentence k tag xs w symbol args n)) :=
  Internal.ObjectWholeAtomicInterfaces.native_rawApplicationWrongTagRejected k tag hne xs w symbol args n

example {m} (k tag : Nat) (hne : tag ≠ 2) (xs : Fin k → Fin m) (w mode depth parameter n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectWholeAtomicInterfaces.applicationCaseWrongTagRejectedSentence k tag xs w mode depth parameter n q)) :=
  Internal.ObjectWholeAtomicInterfaces.native_applicationCaseWrongTagRejected k tag hne xs w mode depth parameter n q

example {m} (three : Bool) (w mode depth parameter n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectWholeAtomicInterfaces.wholeFalseDispatchIffSentence three w mode depth parameter n q)) :=
  Internal.ObjectWholeAtomicInterfaces.native_wholeFalseDispatchIff three w mode depth parameter n q

example {m} (three : Bool) (w mode depth parameter n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectWholeAtomicInterfaces.wholeTrueDispatchIffSentence three w mode depth parameter n q)) :=
  Internal.ObjectWholeAtomicInterfaces.native_wholeTrueDispatchIff three w mode depth parameter n q

example {m} (three : Bool) (w mode depth parameter n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectWholeAtomicInterfaces.wholeEqualityDispatchIffSentence three w mode depth parameter n q x y)) :=
  Internal.ObjectWholeAtomicInterfaces.native_wholeEqualityDispatchIff three w mode depth parameter n q x y

example {m} (w mode depth a b c L I R n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectWholeAtomicInterfaces.replaceWholeEqualityExistingAtomIffSentence w mode depth a b c L I R n q x y)) :=
  Internal.ObjectWholeAtomicInterfaces.native_replaceWholeEqualityExistingAtomIff w mode depth a b c L I R n q x y

example {m} (w mode depth parameter a b B I J R S n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectWholeAtomicInterfaces.weakenWholeEqualityExistingAtomIffSentence w mode depth parameter a b B I J R S n q x y)) :=
  Internal.ObjectWholeAtomicInterfaces.native_weakenWholeEqualityExistingAtomIff w mode depth parameter a b B I J R S n q x y

example {m} (three truth : Bool) (w mode depth parameter a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectWholeAtomicInterfaces.wholeConstantExistingAtomIffSentence three truth w mode depth parameter a b c d n q)) :=
  Internal.ObjectWholeAtomicInterfaces.native_wholeConstantExistingAtomIff three truth w mode depth parameter a b c d n q

example {m} (w R S a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectUnifiedAtomicProgram.compiledAtomicProgramSourceSentence w R S a b c d h n q)) :=
  Internal.ObjectUnifiedAtomicProgram.native_compiledAtomicProgramSource w R S a b c d h n q

example {m} (w mode depth a b c L I R n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectUnifiedAtomicProgram.replaceTypedMembershipWholeRunIffSentence w mode depth a b c L I R n q)) :=
  Internal.ObjectUnifiedAtomicProgram.native_replaceTypedMembershipWholeRunIff w mode depth a b c L I R n q

example {m} (w mode depth a b c L I R n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectUnifiedAtomicProgram.replaceTypedEqualityWholeRunIffSentence w mode depth a b c L I R n q)) :=
  Internal.ObjectUnifiedAtomicProgram.native_replaceTypedEqualityWholeRunIff w mode depth a b c L I R n q

example {m} (w mode depth a b c L I R h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectUnifiedAtomicProgram.replaceUnifiedAtomicProgramIffSentence w mode depth a b c L I R h n q)) :=
  Internal.ObjectUnifiedAtomicProgram.native_replaceUnifiedAtomicProgramIff w mode depth a b c L I R h n q

example {m} (w mode depth parameter a b B I J R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectUnifiedAtomicProgram.weakenTypedMembershipWholeRunIffSentence w mode depth parameter a b B I J R S n q)) :=
  Internal.ObjectUnifiedAtomicProgram.native_weakenTypedMembershipWholeRunIff w mode depth parameter a b B I J R S n q

example {m} (w mode depth parameter a b B I J R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectUnifiedAtomicProgram.weakenTypedEqualityWholeRunIffSentence w mode depth parameter a b B I J R S n q)) :=
  Internal.ObjectUnifiedAtomicProgram.native_weakenTypedEqualityWholeRunIff w mode depth parameter a b B I J R S n q

example {m} (w mode depth parameter a b B I J R S h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectUnifiedAtomicProgram.weakenUnifiedAtomicProgramIffSentence w mode depth parameter a b B I J R S h n q)) :=
  Internal.ObjectUnifiedAtomicProgram.native_weakenUnifiedAtomicProgramIff w mode depth parameter a b B I J R S h n q

example {m} (w mode depth parameter h R S a b c d n x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLogicalProgram.logicalHistoryAgreementAtSentence w mode depth parameter h R S a b c d n x X)) :=
  Internal.ObjectOriginalLogicalProgram.native_logicalHistoryAgreementAt w mode depth parameter h R S a b c d n x X

example {m} (w a b n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLogicalProgram.negationChildFormulaCodeSentence w a b n x)) :=
  Internal.ObjectOriginalLogicalProgram.native_negationChildFormulaCode w a b n x

example {m} (kind : Fin 4) (w a b n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLogicalProgram.binaryChildrenFormulaCodeSentence kind w a b n x y)) :=
  Internal.ObjectOriginalLogicalProgram.native_binaryChildrenFormulaCode kind w a b n x y

example {m} (w mode depth parameter h R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLogicalProgram.negationLocalHistoryIffSentence w mode depth parameter h R S a b c d n q)) :=
  Internal.ObjectOriginalLogicalProgram.native_negationLocalHistoryIff w mode depth parameter h R S a b c d n q

example {m} (three : Bool)  (w mode depth parameter n q x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLogicalProgram.negationWholeRunDispatchIffSentence three w mode depth parameter n q x)) :=
  Internal.ObjectOriginalLogicalProgram.native_negationWholeRunDispatchIff three w mode depth parameter n q x

example {m} (three : Bool)  (w mode depth parameter h R S a b c d n q x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLogicalProgram.negationWholeRunHistoryConditionalIffSentence three w mode depth parameter h R S a b c d n q x)) :=
  Internal.ObjectOriginalLogicalProgram.native_negationWholeRunHistoryConditionalIff three w mode depth parameter h R S a b c d n q x

example {m} (kind : Fin 4) (w mode depth parameter h R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLogicalProgram.binaryLocalHistoryIffSentence kind w mode depth parameter h R S a b c d n q)) :=
  Internal.ObjectOriginalLogicalProgram.native_binaryLocalHistoryIff kind w mode depth parameter h R S a b c d n q

example {m} (three : Bool) (kind : Fin 4) (w mode depth parameter n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLogicalProgram.binaryWholeRunDispatchIffSentence three kind w mode depth parameter n q x y)) :=
  Internal.ObjectOriginalLogicalProgram.native_binaryWholeRunDispatchIff three kind w mode depth parameter n q x y

example {m} (three : Bool) (kind : Fin 4) (w mode depth parameter h R S a b c d n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalLogicalProgram.binaryWholeRunHistoryConditionalIffSentence three kind w mode depth parameter h R S a b c d n q x y)) :=
  Internal.ObjectOriginalLogicalProgram.native_binaryWholeRunHistoryConditionalIff three kind w mode depth parameter h R S a b c d n q x y

example {m} (w h D x R S a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectActualFormulaHistory.actualHistoryReadExecutedIffSentence w h D x R S a b c d q)) :=
  Internal.ObjectActualFormulaHistory.native_actualHistoryReadExecutedIff w h D x R S a b c d q

example {m} (w mode depth parameter R S a b c d n x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectActualFormulaHistory.prefixInductionAtSentence w mode depth parameter R S a b c d n x X)) :=
  Internal.ObjectActualFormulaHistory.native_prefixInductionAt w mode depth parameter R S a b c d n x X

example {m} (w mode depth parameter h R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectActualFormulaHistory.actualHistoryAgreementFromInductionSentence w mode depth parameter h R S a b c d n)) :=
  Internal.ObjectActualFormulaHistory.native_actualHistoryAgreementFromInduction w mode depth parameter h R S a b c d n

example {m} (w mode depth parameter R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectActualFormulaHistory.agreedActualHistoryExistsSentence w mode depth parameter R S a b c d n)) :=
  Internal.ObjectActualFormulaHistory.native_agreedActualHistoryExists w mode depth parameter R S a b c d n

example {m} (three : Bool)  (w mode depth parameter h R S a b c d n q x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectActualFormulaHistory.negationActualHistoryFromInductionIffSentence three w mode depth parameter h R S a b c d n q x)) :=
  Internal.ObjectActualFormulaHistory.native_negationActualHistoryFromInductionIff three w mode depth parameter h R S a b c d n q x

example {m} (three : Bool) (kind : Fin 4) (w mode depth parameter h R S a b c d n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectActualFormulaHistory.binaryActualHistoryFromInductionIffSentence three kind w mode depth parameter h R S a b c d n q x y)) :=
  Internal.ObjectActualFormulaHistory.native_binaryActualHistoryFromInductionIff three kind w mode depth parameter h R S a b c d n q x y

example {m} (w J S b a c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectUniformOperationFrames.freeConversionFromActualConvertedSentence w J S b a c)) :=
  Internal.ObjectUniformOperationFrames.native_freeConversionFromActualConverted w J S b a c

example {m} (three : Bool) (w mode depth P a b c I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectUniformOperationFrames.frameEnvironmentSentence three w mode depth P a b c I J R S)) :=
  Internal.ObjectUniformOperationFrames.native_frameEnvironment three w mode depth P a b c I J R S

example {m} (w mode depth P a b c I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectUniformOperationFrames.weakenFrameFromExistingEnvironmentSentence w mode depth P a b c I J R S)) :=
  Internal.ObjectUniformOperationFrames.native_weakenFrameFromExistingEnvironment w mode depth P a b c I J R S

example {m} (w mode depth P a b c I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectUniformOperationFrames.replaceFrameFromFreeConversionSentence w mode depth P a b c I J R S)) :=
  Internal.ObjectUniformOperationFrames.native_replaceFrameFromFreeConversion w mode depth P a b c I J R S

example {m} (three : Bool) (w mode depth P a b c I J R S h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectUniformOperationFrames.frameAtomicWholeProgramIffSentence three w mode depth P a b c I J R S h n q)) :=
  Internal.ObjectUniformOperationFrames.native_frameAtomicWholeProgramIff three w mode depth P a b c I J R S h n q

example {m} (three : Bool) (w mode depth P a b c I J R S A C M K H D : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectUniformOperationFrames.binderEnvironmentAtSentence three w mode depth P a b c I J R S A C M K H D)) :=
  Internal.ObjectUniformOperationFrames.native_binderEnvironmentAt three w mode depth P a b c I J R S A C M K H D

example {m} (three : Bool) (w mode depth P a b c I J R S A C K H D : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectUniformOperationFrames.binderEnvironmentExistsSentence three w mode depth P a b c I J R S A C K H D)) :=
  Internal.ObjectUniformOperationFrames.native_binderEnvironmentExists three w mode depth P a b c I J R S A C K H D

example {m} (three : Bool) (w n mode depth P a b c I J R S q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectUniformOperationFrames.uniformCorrectAtSentence three w n mode depth P a b c I J R S q)) :=
  Internal.ObjectUniformOperationFrames.native_uniformCorrectAt three w n mode depth P a b c I J R S q

example {m} (three : Bool) (w n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectUniformOperationFrames.uniformPrefixAtSentence three w n x)) :=
  Internal.ObjectUniformOperationFrames.native_uniformPrefixAt three w n x

example {m} (three : Bool) (w n mode depth P a b c I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectUniformOperationFrames.uniformPrefixAtFrameSentence three w n mode depth P a b c I J R S)) :=
  Internal.ObjectUniformOperationFrames.native_uniformPrefixAtFrame three w n mode depth P a b c I J R S

example {m} (three : Bool) (w n mode depth P a b c I J R S h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectUniformOperationFrames.actualHistoryAgreementAtUniformFrameSentence three w n mode depth P a b c I J R S h)) :=
  Internal.ObjectUniformOperationFrames.native_actualHistoryAgreementAtUniformFrame three w n mode depth P a b c I J R S h

example {m} (three : Bool) (w n mode depth P a b c I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectUniformOperationFrames.actualHistoryExistsAtUniformFrameSentence three w n mode depth P a b c I J R S)) :=
  Internal.ObjectUniformOperationFrames.native_actualHistoryExistsAtUniformFrame three w n mode depth P a b c I J R S

example {m} (three : Bool) (w n mode depth P a b c I J R S A C K H D : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectUniformOperationFrames.binderPrefixFromUniformInductionSentence three w n mode depth P a b c I J R S A C K H D)) :=
  Internal.ObjectUniformOperationFrames.native_binderPrefixFromUniformInduction three w n mode depth P a b c I J R S A C K H D

example {m} (w x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalBinderProgram.naturalSuccessorWitnessSentence w x)) :=
  Internal.ObjectOriginalBinderProgram.native_naturalSuccessorWitness w x

example {m} (w K S H A b C c x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalBinderProgram.liftedChildExecutionAlignmentIffSentence w K S H A b C c x X)) :=
  Internal.ObjectOriginalBinderProgram.native_liftedChildExecutionAlignmentIff w K S H A b C c x X

example {m} (three universal : Bool) (w n mode depth P a b c I J R S h x X A C K H D : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalBinderProgram.quantifierChildReadAtLiftIffSentence three universal w n mode depth P a b c I J R S h x X A C K H D)) :=
  Internal.ObjectOriginalBinderProgram.native_quantifierChildReadAtLiftIff three universal w n mode depth P a b c I J R S h x X A C K H D

example {m} (three universal : Bool) (w n mode depth P a b c I J R S h x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalBinderProgram.quantifierStepAdvancedIffSentence three universal w n mode depth P a b c I J R S h x X)) :=
  Internal.ObjectOriginalBinderProgram.native_quantifierStepAdvancedIff three universal w n mode depth P a b c I J R S h x X

example {m} (three universal : Bool) (w n mode depth P a b c I J R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalBinderProgram.quantifierLocalCaseIffSentence three universal w n mode depth P a b c I J R S h q)) :=
  Internal.ObjectOriginalBinderProgram.native_quantifierLocalCaseIff three universal w n mode depth P a b c I J R S h q

example {m} (three universal : Bool) (w mode depth parameter n q x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalBinderProgram.quantifierWholeRunDispatchIffSentence three universal w mode depth parameter n q x)) :=
  Internal.ObjectOriginalBinderProgram.native_quantifierWholeRunDispatchIff three universal w mode depth parameter n q x

example {m} (three universal : Bool) (w n mode depth P a b c I J R S h x q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalBinderProgram.quantifierWholeRunFromUniformInductionIffSentence three universal w n mode depth P a b c I J R S h x q)) :=
  Internal.ObjectOriginalBinderProgram.native_quantifierWholeRunFromUniformInductionIff three universal w n mode depth P a b c I J R S h x q

example {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformRootStep.recursiveCasesTargetTypeSentence w R S a b c d n q)) :=
  Internal.ObjectFormulaTransformRootStep.native_recursiveCasesTargetType w R S a b c d n q

example {m} (w R S a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformRootStep.actualProgramTargetTypeSentence w R S a b c d h n q)) :=
  Internal.ObjectFormulaTransformRootStep.native_actualProgramTargetType w R S a b c d h n q

example {m} (w R S a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformRootStep.actualRootGuardedStepIffSentence w R S a b c d h n q)) :=
  Internal.ObjectFormulaTransformRootStep.native_actualRootGuardedStepIff w R S a b c d h n q

example {m} (w R S a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformRootStep.actualRootStepIffSentence w R S a b c d h n q)) :=
  Internal.ObjectFormulaTransformRootStep.native_actualRootStepIff w R S a b c d h n q

example {m} (w R S a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFormulaTransformRootStep.actualRootWholeProgramIffSentence w R S a b c d h n q)) :=
  Internal.ObjectFormulaTransformRootStep.native_actualRootWholeProgramIff w R S a b c d h n q

example {m} (three : Bool) (w n mode depth P a b c I J R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaCorrectness.fullElevenProgramFromUniformIffSentence three w n mode depth P a b c I J R S h q)) :=
  Internal.ObjectOriginalFormulaCorrectness.native_fullElevenProgramFromUniformIff three w n mode depth P a b c I J R S h q

example {m} (three : Bool) (w n mode depth P a b c I J R S q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaCorrectness.wholeRunExecutedFromUniformIffSentence three w n mode depth P a b c I J R S q)) :=
  Internal.ObjectOriginalFormulaCorrectness.native_wholeRunExecutedFromUniformIff three w n mode depth P a b c I J R S q

example {m} (three : Bool) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaCorrectness.allParametersCorrectFromUniformSentence three w n)) :=
  Internal.ObjectOriginalFormulaCorrectness.native_allParametersCorrectFromUniform three w n

example {m} (three : Bool) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaCorrectness.allInternalRootsCorrectSentence three w)) :=
  Internal.ObjectOriginalFormulaCorrectness.native_allInternalRootsCorrect three w

example {m} (three : Bool) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaCorrectness.uniformInductionDischargedSentence three w n)) :=
  Internal.ObjectOriginalFormulaCorrectness.native_uniformInductionDischarged three w n

example {m} (three : Bool) (w n mode depth P a b c I J R S q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaCorrectness.allInternalWholeRunExecutedIffSentence three w n mode depth P a b c I J R S q)) :=
  Internal.ObjectOriginalFormulaCorrectness.native_allInternalWholeRunExecutedIff three w n mode depth P a b c I J R S q

example {m} (three : Bool) (w n mode depth P a b c I J R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaCorrectness.allInternalWholeProgramIffSentence three w n mode depth P a b c I J R S h q)) :=
  Internal.ObjectOriginalFormulaCorrectness.native_allInternalWholeProgramIff three w n mode depth P a b c I J R S h q

example {m} (three : Bool) (w n mode depth P a b c I J R S h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaCorrectness.actualHistoryAgreementDischargedSentence three w n mode depth P a b c I J R S h)) :=
  Internal.ObjectOriginalFormulaCorrectness.native_actualHistoryAgreementDischarged three w n mode depth P a b c I J R S h

example {m} (three : Bool) (w n mode depth P a b c I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFormulaCorrectness.agreedActualHistoryExistsDischargedSentence three w n mode depth P a b c I J R S)) :=
  Internal.ObjectOriginalFormulaCorrectness.native_agreedActualHistoryExistsDischarged three w n mode depth P a b c I J R S

-- 直接展开对象闭句合同：只允许 Ω、frame、源 FormulaCode 三个前提。
example {m} (three : Bool) (w n mode depth P a b c I J R S q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (((OmegaSyntax.omega w).imp
        ((OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S).imp
          ((FormulaCodeSyntax.formulaCode w n a b).imp
            ((OriginalTransformRowSyntax.run 3 w mode depth (OriginalOperationFrameSyntax.parameter three P S) n q).iff
              (FormulaTransformExecutionSyntax.executed w R S a b a c n q))))).close)) :=
  ObjectOriginalFormulaCorrectness.native_allInternalWholeRunExecutedIff three w n mode depth P a b c I J R S q

example {m} (w z c t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFreeSubstFormula.emptyBoundTermFreeSentence w z c t)) :=
  Internal.ObjectOriginalFreeSubstFormula.native_emptyBoundTermFree w z c t

example {m} (w a z c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFreeSubstFormula.emptyBoundListsIffSentence w a z c L)) :=
  Internal.ObjectOriginalFreeSubstFormula.native_emptyBoundListsIff w a z c L

example {m} (w a z c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFreeSubstFormula.emptyBoundConversionExistsSentence w a z c L)) :=
  Internal.ObjectOriginalFreeSubstFormula.native_emptyBoundConversionExists w a z c L

example {m} (w mode depth b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFreeSubstFormula.modeThreeWholeSubstitutionIffSentence w mode depth b a c L n q)) :=
  Internal.ObjectOriginalFreeSubstFormula.native_modeThreeWholeSubstitutionIff w mode depth b a c L n q

example {m} (w mode depth b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFreeSubstFormula.modeThreeWholeProgramIffSentence w mode depth b a c L n q)) :=
  Internal.ObjectOriginalFreeSubstFormula.native_modeThreeWholeProgramIff w mode depth b a c L n q

example {m} (w mode depth b a z c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFreeSubstFormula.modeThreeEmptyBoundArgumentsIffSentence w mode depth b a z c L n q)) :=
  Internal.ObjectOriginalFreeSubstFormula.native_modeThreeEmptyBoundArgumentsIff w mode depth b a z c L n q

example {m} (w mode depth b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFreeSubstFormula.modeThreeOutputTypeSentence w mode depth b a c L n q)) :=
  Internal.ObjectOriginalFreeSubstFormula.native_modeThreeOutputType w mode depth b a c L n q

example {m} (w mode depth b a c L n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFreeSubstFormula.modeThreeOutputUniqueSentence w mode depth b a c L n q v)) :=
  Internal.ObjectOriginalFreeSubstFormula.native_modeThreeOutputUnique w mode depth b a c L n q v

example {m} (w mode depth b a c L n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalFreeSubstFormula.modeThreeActualOutputSentence w mode depth b a c L n)) :=
  Internal.ObjectOriginalFreeSubstFormula.native_modeThreeActualOutput w mode depth b a c L n

-- 直接展开真实空绑定界纯参数合同：不要求预给frame或转换码见证。
example {m} (w mode depth b a z c L n q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (((OmegaSyntax.omega w).imp
        ((SyntaxNumeralSyntax.numeral 3 mode).imp
          ((OriginalTermTraceSyntax.metadata w depth L).imp
            ((FormulaCodeSyntax.formulaCode w n b a).imp
              ((OmegaSyntax.empty z).imp
                ((SyntaxMixedImageCodeSyntax.termList w a z c L).imp
                  ((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff
                    (FreeSubstProgramSyntax.executed w b a c L n q)))))))).close)) :=
  ObjectOriginalFreeSubstFormula.native_modeThreeEmptyBoundArgumentsIff w mode depth b a z c L n q

example {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (hmem : rule ∈ PureSyntaxRules.rules) (hn : rule.premises = []) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxTermChecker.purePremiseFreeTraceExistsSentence rule hmem hn w r)) :=
  Internal.ObjectPureSyntaxTermChecker.native_purePremiseFreeTraceExists rule hmem hn w r

example {m} (bound : Bool) (w n e0 e1 e2 : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxTermChecker.pureVariableExpressionIffSentence bound w n e0 e1 e2)) :=
  Internal.ObjectPureSyntaxTermChecker.native_pureVariableExpressionIff bound w n e0 e1 e2

example {m} (bound : Bool) (w b f n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxTermChecker.pureVariableApplicationSoundSentence bound w b f n r R)) :=
  Internal.ObjectPureSyntaxTermChecker.native_pureVariableApplicationSound bound w b f n r R

example {m} (w b f n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxTermChecker.pureTermClosedTraceSoundSentence w b f n r)) :=
  Internal.ObjectPureSyntaxTermChecker.native_pureTermClosedTraceSound w b f n r

example {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxTermChecker.pureTermCheckSoundSentence w b f n)) :=
  Internal.ObjectPureSyntaxTermChecker.native_pureTermCheckSound w b f n

example {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxTermChecker.pureTermCheckCompleteSentence w b f n)) :=
  Internal.ObjectPureSyntaxTermChecker.native_pureTermCheckComplete w b f n

example {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxTermChecker.pureTermCheckIffSentence w b f n)) :=
  Internal.ObjectPureSyntaxTermChecker.native_pureTermCheckIff w b f n

example {m} (w z f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxTermChecker.pureEmptyBoundTermCheckFreeSentence w z f n)) :=
  Internal.ObjectPureSyntaxTermChecker.native_pureEmptyBoundTermCheckFree w z f n

-- 原纯签名表的全部十五条规则；不加入函数应用或额外关系。
example : PureSyntaxRules.rules =
    [YesMetaZFC.Automation.ObjectTermSyntax.variableRule false,
      YesMetaZFC.Automation.ObjectTermSyntax.variableRule true,
      YesMetaZFC.Automation.ObjectTermSyntax.nilRule,
      YesMetaZFC.Automation.ObjectTermSyntax.consRule,
      YesMetaZFC.Automation.ObjectFormulaSyntax.constantRule 0,
      YesMetaZFC.Automation.ObjectFormulaSyntax.constantRule 1,
      YesMetaZFC.Automation.ObjectFormulaSyntax.relationRule .membership,
      YesMetaZFC.Automation.ObjectFormulaSyntax.equalityRule,
      YesMetaZFC.Automation.ObjectFormulaSyntax.unaryRule 4 false,
      YesMetaZFC.Automation.ObjectFormulaSyntax.binaryRule 5,
      YesMetaZFC.Automation.ObjectFormulaSyntax.binaryRule 6,
      YesMetaZFC.Automation.ObjectFormulaSyntax.binaryRule 7,
      YesMetaZFC.Automation.ObjectFormulaSyntax.binaryRule 8,
      YesMetaZFC.Automation.ObjectFormulaSyntax.unaryRule 9 true,
      YesMetaZFC.Automation.ObjectFormulaSyntax.unaryRule 10 true] := rfl

-- 展开最终项查询对象合同：只有内部Omega前提，所有运行字段仍全称闭合。
example {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp
      ((PureSyntaxTrace.term w b f n).iff (SyntaxTermSyntax.term w b f n))).close)) :=
  ObjectPureSyntaxTermChecker.native_pureTermCheckIff w b f n

example {m} (R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxListSteps.binaryUnionExistsSentence R S)) :=
  Internal.ObjectPureSyntaxListSteps.native_binaryUnionExists R S

example {m} (w R r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxListSteps.pureTraceInsertionConditionSentence w R r)) :=
  Internal.ObjectPureSyntaxListSteps.native_pureTraceInsertionCondition w R r

example {m} (w r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxListSteps.pureTracePairConditionSentence w r s)) :=
  Internal.ObjectPureSyntaxListSteps.native_pureTracePairCondition w r s

example {m} (w n e0 e1 : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxListSteps.pureNilExpressionIffSentence w n e0 e1)) :=
  Internal.ObjectPureSyntaxListSteps.native_pureNilExpressionIff w n e0 e1

example {m} (w b f k n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxListSteps.pureNilApplicationSoundSentence w b f k n r R)) :=
  Internal.ObjectPureSyntaxListSteps.native_pureNilApplicationSound w b f k n r R

example {m} (w b f k n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxListSteps.pureNilApplicationCompleteSentence w b f k n r R)) :=
  Internal.ObjectPureSyntaxListSteps.native_pureNilApplicationComplete w b f k n r R

example {m} (w b f k n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxListSteps.pureNilCheckedSentence w b f k n)) :=
  Internal.ObjectPureSyntaxListSteps.native_pureNilChecked w b f k n

example {m} (w b f k n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxListSteps.pureTypedNilCheckedSentence w b f k n)) :=
  Internal.ObjectPureSyntaxListSteps.native_pureTypedNilChecked w b f k n

example {m} (w k n r R p q b f ell h t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxListSteps.pureConsApplicationCompleteSentence w k n r R p q b f ell h t)) :=
  Internal.ObjectPureSyntaxListSteps.native_pureConsApplicationComplete w k n r R p q b f ell h t

example {m} (w k n r p q b f ell h t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxListSteps.pureConsConditionCompleteSentence w k n r p q b f ell h t)) :=
  Internal.ObjectPureSyntaxListSteps.native_pureConsConditionComplete w k n r p q b f ell h t
-- 展开真实闭轨迹合并，不预给公共轨迹见证。
example {m} (w r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((PureSyntaxTrace.condition w r).imp
      ((PureSyntaxTrace.condition w s).imp (PureSyntaxTraceMerge.pairCondition w r s))).close)) :=
  ObjectPureSyntaxListSteps.native_pureTracePairCondition w r s

-- 展开nil完整查询构造：空长度、内部上下文及真实Nil码。
example {m} (w b f k n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((Source.SetLanguage.empty k).imp
      ((SyntaxTermSyntax.contexts w b f).imp ((StructuralListSyntax.nilCode w n).imp
        (PureSyntaxTrace.arguments w b f k n))))).close)) :=
  ObjectPureSyntaxListSteps.native_pureNilChecked w b f k n

example {m} (w b f ell k h t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxArgumentChecker.pureConsQueryCompleteSentence w b f ell k h t n)) :=
  Internal.ObjectPureSyntaxArgumentChecker.native_pureConsQueryComplete w b f ell k h t n

example {m} (w b f k n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxArgumentChecker.pureConsApplicationFromInductionSoundSentence w b f k n r R)) :=
  Internal.ObjectPureSyntaxArgumentChecker.native_pureConsApplicationFromInductionSound w b f k n r R

example {m} (w b f k n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxArgumentChecker.pureArgumentsFromInductionIffSentence w b f k n)) :=
  Internal.ObjectPureSyntaxArgumentChecker.native_pureArgumentsFromInductionIff w b f k n

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxArgumentChecker.pureAllArgumentsCorrectSentence w)) :=
  Internal.ObjectPureSyntaxArgumentChecker.native_pureAllArgumentsCorrect w

example {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxArgumentChecker.pureArgumentsInductionDischargedSentence w n)) :=
  Internal.ObjectPureSyntaxArgumentChecker.native_pureArgumentsInductionDischarged w n

example {m} (w b f k n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxArgumentChecker.pureArgumentsQueryIffSentence w b f k n)) :=
  Internal.ObjectPureSyntaxArgumentChecker.native_pureArgumentsQueryIff w b f k n

example {m} (w b f k n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxArgumentChecker.pureArgumentsQuerySoundSentence w b f k n)) :=
  Internal.ObjectPureSyntaxArgumentChecker.native_pureArgumentsQuerySound w b f k n

example {m} (w b f k n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxArgumentChecker.pureArgumentsQueryCompleteSentence w b f k n)) :=
  Internal.ObjectPureSyntaxArgumentChecker.native_pureArgumentsQueryComplete w b f k n

example {m} (w a z c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxArgumentChecker.pureEmptyBoundArgumentsQueryIffSentence w a z c L)) :=
  Internal.ObjectPureSyntaxArgumentChecker.native_pureEmptyBoundArgumentsQueryIff w a z c L

example {m} (w mode depth b a z c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxArgumentChecker.pureModeThreeFromArgumentsQueryIffSentence w mode depth b a z c L n q)) :=
  Internal.ObjectPureSyntaxArgumentChecker.native_pureModeThreeFromArgumentsQueryIff w mode depth b a z c L n q
-- 展开完整参数查询双条件：仅Omega前提，全部内部字段全称闭合，无IH。
example {m} (w b f k n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp
      ((PureSyntaxTrace.arguments w b f k n).iff (SyntaxMixedImageCodeSyntax.termList w k b f n))).close)) :=
  ObjectPureSyntaxArgumentChecker.native_pureArgumentsQueryIff w b f k n

-- 展开空绑定界实际查询到自由变量像列表的双条件。
example {m} (w a z c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((Source.SetLanguage.empty z).imp
      ((PureSyntaxTrace.arguments w z c a L).iff (SyntaxFreeSubstSyntax.termList w a c L)))).close)) :=
  ObjectPureSyntaxArgumentChecker.native_pureEmptyBoundArgumentsQueryIff w a z c L

example {m} (truth : Bool) (w n e0 e1 : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxFormulaAtoms.constantInputExpressionIffSentence truth w n e0 e1)) :=
  Internal.ObjectPureSyntaxFormulaAtoms.native_constantInputExpressionIff truth w n e0 e1

example {m} (truth : Bool) (w b f n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxFormulaAtoms.constantApplicationIffNullarySentence truth w b f n r R)) :=
  Internal.ObjectPureSyntaxFormulaAtoms.native_constantApplicationIffNullary truth w b f n r R

example {m} (truth : Bool) (w b f n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxFormulaAtoms.constantApplicationSoundSentence truth w b f n r R)) :=
  Internal.ObjectPureSyntaxFormulaAtoms.native_constantApplicationSound truth w b f n r R

example {m} (truth : Bool) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxFormulaAtoms.constantQueryConstructedSentence truth w b f n)) :=
  Internal.ObjectPureSyntaxFormulaAtoms.native_constantQueryConstructed truth w b f n

example {m} (truth : Bool) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxFormulaAtoms.typedConstantQueryConstructedSentence truth w b f n)) :=
  Internal.ObjectPureSyntaxFormulaAtoms.native_typedConstantQueryConstructed truth w b f n

example {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxFormulaAtoms.equalityInputExpressionIffSentence w b f x y n)) :=
  Internal.ObjectPureSyntaxFormulaAtoms.native_equalityInputExpressionIff w b f x y n

example {m} (w b f n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxFormulaAtoms.equalityApplicationSoundSentence w b f n r R)) :=
  Internal.ObjectPureSyntaxFormulaAtoms.native_equalityApplicationSound w b f n r R

example {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxFormulaAtoms.equalityQueryConstructedSentence w b f x y n)) :=
  Internal.ObjectPureSyntaxFormulaAtoms.native_equalityQueryConstructed w b f x y n

example {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxFormulaAtoms.typedEqualityQueryConstructedSentence w b f x y n)) :=
  Internal.ObjectPureSyntaxFormulaAtoms.native_typedEqualityQueryConstructed w b f x y n

example {m} (w b f x y n r p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxFormulaAtoms.equalityActualChildTracesMergedSentence w b f x y n r p q)) :=
  Internal.ObjectPureSyntaxFormulaAtoms.native_equalityActualChildTracesMerged w b f x y n r p q
-- 展开原常量应用与nullary的局部双条件，不能误读为完整公式查询等价。
example {m} (truth : Bool) (w b f n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((PureSyntaxTrace.formulaRow w b f n r).imp
      ((HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectFormulaSyntax.constantRule (SyntaxAtomSyntax.nullaryTag truth)) w r R).iff
        (SyntaxAtomSyntax.nullary truth w b f n)))).close)) :=
  ObjectPureSyntaxFormulaAtoms.native_constantApplicationIffNullary truth w b f n r R

-- 展开等式完整查询构造；两个合法项及实际等式码，全部行和轨迹见证消去。
example {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((SyntaxTermSyntax.term w b f x).imp
      ((SyntaxTermSyntax.term w b f y).imp ((SyntaxAtomSyntax.equalCode w x y n).imp
        (PureSyntaxTrace.formula w b f n))))).close)) :=
  ObjectPureSyntaxFormulaAtoms.native_equalityQueryConstructed w b f x y n

example {m} (w b f args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxMembership.membershipInputDataIffSentence w b f args n)) :=
  Internal.ObjectPureSyntaxMembership.native_membershipInputDataIff w b f args n

example {m} (w s x y args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxMembership.membershipAtForestIffSentence w s x y args n)) :=
  Internal.ObjectPureSyntaxMembership.native_membershipAtForestIff w s x y args n

example {m} (w b f args n len : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxMembership.membershipTypedListSoundSentence w b f args n len)) :=
  Internal.ObjectPureSyntaxMembership.native_membershipTypedListSound w b f args n len

example {m} (w b f args R len : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxMembership.membershipActualPremiseAtTwoSentence w b f args R len)) :=
  Internal.ObjectPureSyntaxMembership.native_membershipActualPremiseAtTwo w b f args R len

example {m} (w b f n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxMembership.membershipApplicationSoundSentence w b f n r R)) :=
  Internal.ObjectPureSyntaxMembership.native_membershipApplicationSound w b f n r R

example {m} (w b f args n len : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxMembership.membershipQueryFromListSentence w b f args n len)) :=
  Internal.ObjectPureSyntaxMembership.native_membershipQueryFromList w b f args n len

example {m} (w b f s x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxMembership.membershipQueryAtSentence w b f s x y n)) :=
  Internal.ObjectPureSyntaxMembership.native_membershipQueryAt w b f s x y n

example {m} (w b f s x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxMembership.typedMembershipQuerySentence w b f s x y n)) :=
  Internal.ObjectPureSyntaxMembership.native_typedMembershipQuery w b f s x y n

example {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxMembership.fullMembershipQuerySentence w b f n)) :=
  Internal.ObjectPureSyntaxMembership.native_fullMembershipQuery w b f n

example {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxMembership.allFourAtomicQueriesSentence w b f n)) :=
  Internal.ObjectPureSyntaxMembership.native_allFourAtomicQueries w b f n
-- 原membership规则确切字段及长度2参数前提，均由内核rfl核对。
example : (YesMetaZFC.Automation.ObjectFormulaSyntax.relationRule .membership).head =
    PureSyntaxFormulaGraph.head (0 : Fin 3) 1 PureSyntaxMembershipInput.input := rfl
example : (YesMetaZFC.Automation.ObjectFormulaSyntax.relationRule .membership).premises =
    [PureSyntaxMembershipPremise.head] := rfl

-- 展开成员查询构造：全部实际码和轨迹见证已消去。
example {m} (w b f s x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((SyntaxAtomSyntax.zeroScalar w s).imp
      ((SyntaxTermSyntax.term w b f x).imp ((SyntaxTermSyntax.term w b f y).imp
        ((SyntaxAtomSyntax.memberCode w s x y n).imp (PureSyntaxTrace.formula w b f n)))))).close)) :=
  ObjectPureSyntaxMembership.native_membershipQueryAt w b f s x y n

-- 四种完整Source原子分支的统一查询构造；不冒充全kind4双条件。
example {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((SyntaxAtomSyntax.atomic w b f n).imp
      (PureSyntaxTrace.formula w b f n))).close)) :=
  ObjectPureSyntaxMembership.native_allFourAtomicQueries w b f n

example {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxBinary.formulaCorrectInstanceSentence w n b f)) :=
  Internal.ObjectPureSyntaxBinary.native_formulaCorrectInstance w n b f

example {m} (w n x b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxBinary.formulaStrictIHInstanceSentence w n x b f)) :=
  Internal.ObjectPureSyntaxBinary.native_formulaStrictIHInstance w n x b f

example {m} (kind : Fin 4) (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxBinary.binaryInputExpressionIffSentence kind w b f x y n)) :=
  Internal.ObjectPureSyntaxBinary.native_binaryInputExpressionIff kind w b f x y n

example {m} (kind : Fin 4) (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxBinary.binaryKnownTypeIffSentence kind w b f x y n)) :=
  Internal.ObjectPureSyntaxBinary.native_binaryKnownTypeIff kind w b f x y n

example {m} (kind : Fin 4) (w b f n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxBinary.binaryActualApplicationSoundSentence kind w b f n r R)) :=
  Internal.ObjectPureSyntaxBinary.native_binaryActualApplicationSound kind w b f n r R

example {m} (kind : Fin 4) (w b f x y n r p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxBinary.binaryActualChildTracesMergedSentence kind w b f x y n r p q)) :=
  Internal.ObjectPureSyntaxBinary.native_binaryActualChildTracesMerged kind w b f x y n r p q

example {m} (kind : Fin 4) (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxBinary.binaryQueryFromActualChildrenSentence kind w b f x y n)) :=
  Internal.ObjectPureSyntaxBinary.native_binaryQueryFromActualChildren kind w b f x y n

example {m} (kind : Fin 4) (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxBinary.binaryQueryFromStrictInductionSentence kind w b f x y n)) :=
  Internal.ObjectPureSyntaxBinary.native_binaryQueryFromStrictInduction kind w b f x y n
-- 四种二元规则的确切head，外部有限索引不能替代内部运行字段。
example (kind : Fin 4) : (YesMetaZFC.Automation.ObjectFormulaSyntax.binaryRule (SyntaxLogicalSyntax.binaryTag kind)).head =
    PureSyntaxFormulaGraph.head (0 : Fin 4) 1 (PureSyntaxBinaryRule.input kind) := rfl

-- 展开严格对象IH下的二元完整查询构造，IH仍是明确前提。
example {m} (kind : Fin 4) (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((PureSyntaxFormulaInductionSyntax.allIH w n).imp
      ((FormulaCodeSyntax.formulaCode w n b f).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp
        (PureSyntaxTrace.formula w b f n))))).close)) :=
  ObjectPureSyntaxBinary.native_binaryQueryFromStrictInduction kind w b f x y n

example {m} (kind : Fin 3) (w b f x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxUnary.unaryInputExpressionIffSentence kind w b f x n)) :=
  Internal.ObjectPureSyntaxUnary.native_unaryInputExpressionIff kind w b f x n

example {m} (kind : Fin 3) (w b f x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxUnary.unaryKnownTypeIffSentence kind w b f x n)) :=
  Internal.ObjectPureSyntaxUnary.native_unaryKnownTypeIff kind w b f x n

example {m} (kind : Fin 3) (w b f n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxUnary.unaryActualApplicationSoundSentence kind w b f n r R)) :=
  Internal.ObjectPureSyntaxUnary.native_unaryActualApplicationSound kind w b f n r R

example {m} (kind : Fin 3) (w b f x n r p B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxUnary.unaryActualChildTraceExtendedSentence kind w b f x n r p B)) :=
  Internal.ObjectPureSyntaxUnary.native_unaryActualChildTraceExtended kind w b f x n r p B

example {m} (kind : Fin 3) (w b f x n B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxUnary.unaryQueryFromActualChildSentence kind w b f x n B)) :=
  Internal.ObjectPureSyntaxUnary.native_unaryQueryFromActualChild kind w b f x n B

example {m} (kind : Fin 3) (w b f x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxUnary.unaryQueryFromInternalStepSentence kind w b f x n)) :=
  Internal.ObjectPureSyntaxUnary.native_unaryQueryFromInternalStep kind w b f x n

example {m} (kind : Fin 3) (w b f x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxUnary.unaryQueryFromStrictInductionSentence kind w b f x n)) :=
  Internal.ObjectPureSyntaxUnary.native_unaryQueryFromStrictInduction kind w b f x n
-- 原否定和量词head及真实子前提，保持绑定界表达式。
example (kind : Fin 3) : (YesMetaZFC.Automation.ObjectFormulaSyntax.unaryRule (PureSyntaxUnarySyntax.tag kind) (PureSyntaxUnarySyntax.advance kind)).head =
    PureSyntaxFormulaGraph.head (0 : Fin 3) 1 (PureSyntaxUnarySyntax.input kind) := rfl
example (kind : Fin 3) : (YesMetaZFC.Automation.ObjectFormulaSyntax.unaryRule (PureSyntaxUnarySyntax.tag kind) (PureSyntaxUnarySyntax.advance kind)).premises =
    [PureSyntaxFormulaPremise.head (PureSyntaxUnarySyntax.boundExpr (PureSyntaxUnarySyntax.advance kind)) (1 : Fin 3) 2] := rfl
-- 展开原核闭句合同；统一对象IH在本批仍是明确前提。
example {m} (kind : Fin 3) (w b f x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((PureSyntaxFormulaInductionSyntax.allIH w n).imp
      ((FormulaCodeSyntax.formulaCode w n b f).imp ((SyntaxLogicalSyntax.singleCode (PureSyntaxUnarySyntax.tag kind) w x n).imp
        (PureSyntaxTrace.formula w b f n))))).close)) :=
  ObjectPureSyntaxUnary.native_unaryQueryFromStrictInduction kind w b f x n

example {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxFormulaChecker.formulaFromInductionIffSentence w b f n)) :=
  Internal.ObjectPureSyntaxFormulaChecker.native_formulaFromInductionIff w b f n

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxFormulaChecker.formulaAllInternalCorrectSentence w)) :=
  Internal.ObjectPureSyntaxFormulaChecker.native_formulaAllInternalCorrect w

example {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxFormulaChecker.formulaCorrectAtRootSentence w n)) :=
  Internal.ObjectPureSyntaxFormulaChecker.native_formulaCorrectAtRoot w n

example {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxFormulaChecker.formulaInductionDischargedSentence w n)) :=
  Internal.ObjectPureSyntaxFormulaChecker.native_formulaInductionDischarged w n

example {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxFormulaChecker.formulaQueryIffSentence w b f n)) :=
  Internal.ObjectPureSyntaxFormulaChecker.native_formulaQueryIff w b f n

example {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxFormulaChecker.formulaQuerySoundSentence w b f n)) :=
  Internal.ObjectPureSyntaxFormulaChecker.native_formulaQuerySound w b f n

example {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxFormulaChecker.formulaQueryCompleteSentence w b f n)) :=
  Internal.ObjectPureSyntaxFormulaChecker.native_formulaQueryComplete w b f n

example {m} (w b f k n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureSyntaxFormulaChecker.fullSyntaxTypingIffSentence w b f k n)) :=
  Internal.ObjectPureSyntaxFormulaChecker.native_fullSyntaxTypingIff w b f k n
-- 全部内部候选；本最终公式查询合同只有Omega，没有IH或预设合法性。
example {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp
      ((PureSyntaxTrace.formula w b f n).iff (FormulaCodeSyntax.formulaCode w n b f))).close)) :=
  ObjectPureSyntaxFormulaChecker.native_formulaQueryIff w b f n

-- 根码和两个内部上下文均在对象全称量词中，不仅逐外部标准quotation。
example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp
      (.all (PureSyntaxFormulaInductionSyntax.correct w.castSucc (Fin.last m)))).close)) :=
  ObjectPureSyntaxFormulaChecker.native_formulaAllInternalCorrect w

example {m} (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureProofSubstitutionQueries.termExprQueryIffSentence env w)) :=
  Internal.ObjectPureProofSubstitutionQueries.native_termExprQueryIff env w

example {m} (env : Fin 4 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureProofSubstitutionQueries.argumentsExprQueryIffSentence env w)) :=
  Internal.ObjectPureProofSubstitutionQueries.native_argumentsExprQueryIff env w

example {m} (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureProofSubstitutionQueries.formulaExprQueryIffSentence env w)) :=
  Internal.ObjectPureProofSubstitutionQueries.native_formulaExprQueryIff env w

example {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureProofSubstitutionQueries.substitutionFormulaQueryIffSentence env w z)) :=
  Internal.ObjectPureProofSubstitutionQueries.native_substitutionFormulaQueryIff env w z

example {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureProofSubstitutionQueries.substitutionArgumentsQueryIffSentence env w z)) :=
  Internal.ObjectPureProofSubstitutionQueries.native_substitutionArgumentsQueryIff env w z

example {m} (env : Fin 6 → Fin m) (w z mode : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureProofSubstitutionQueries.substitutionTransformAtModeIffSentence env w z mode)) :=
  Internal.ObjectPureProofSubstitutionQueries.native_substitutionTransformAtModeIff env w z mode

example {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureProofSubstitutionQueries.substitutionGuardedTransformIffSentence env w z)) :=
  Internal.ObjectPureProofSubstitutionQueries.native_substitutionGuardedTransformIff env w z

example {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectPureProofSubstitutionQueries.substitutionBundleIffSentence env w z)) :=
  Internal.ObjectPureProofSubstitutionQueries.native_substitutionBundleIff env w z
-- 实际原替换节点查询索引和Kind不由复制表替代。
example : YesMetaZFC.Automation.ObjectProofNode.substitutionShape.queries[0] =
    (.syntax, PureProofSubstitutionQueries.substitutionFormula) := rfl
example : YesMetaZFC.Automation.ObjectProofNode.substitutionShape.queries[1] =
    (.syntax, PureProofSubstitutionQueries.substitutionArguments) := rfl
example : YesMetaZFC.Automation.ObjectProofNode.substitutionShape.queries[4] =
    (.transform, PureProofSubstitutionQueries.substitutionTransform) := rfl

-- 展开局部三查询合取：最终只有Omega、真实自然赋值和空集零值，无FormulaCode/IH前提。
example {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp
      ((OmegaSyntax.empty z).imp
        (((PureSyntaxExprQuery.query PureProofSubstitutionQueries.substitutionFormula w env).conj
          ((PureSyntaxExprQuery.query PureProofSubstitutionQueries.substitutionArguments w env).conj
            (OriginalTransformExprQuery.query PureProofSubstitutionQueries.substitutionTransform w env))).iff
          ((FormulaCodeSyntax.formulaCode w (env 5) z (env 2)).conj
            (FreeSubstProgramSyntax.executed w z (env 2) (env 0) (env 3) (env 5) (env 1))))))).close)) :=
  ObjectPureProofSubstitutionQueries.native_substitutionBundleIff env w z

example {m} (raw head : Bool) (w x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeProjection.pairingComponentExistsSentence raw head w x)) :=
  Internal.ObjectRawCodeProjection.native_pairingComponentExists raw head w x

example {m} (raw head : Bool) (w x y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeProjection.pairingComponentUniqueSentence raw head w x y z)) :=
  Internal.ObjectRawCodeProjection.native_pairingComponentUnique raw head w x y z

example {m} (head : Bool) (w x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeProjection.barePairEveryNaturalDecodesSentence head w x)) :=
  Internal.ObjectRawCodeProjection.native_barePairEveryNaturalDecodes head w x

example {m} (head : Bool) (w x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeProjection.rawEveryPositiveNaturalDecodesSentence head w x)) :=
  Internal.ObjectRawCodeProjection.native_rawEveryPositiveNaturalDecodes head w x

example {m} (head : Bool) (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeProjection.rawZeroComponentSentence head w x y)) :=
  Internal.ObjectRawCodeProjection.native_rawZeroComponent head w x y

example {m} (head : Bool) (w x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeProjection.rawUnselectedNaturalIsZeroSentence head w x)) :=
  Internal.ObjectRawCodeProjection.native_rawUnselectedNaturalIsZero head w x

example {m} (head : Bool) (w x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeProjection.rawHeadTailExistsSentence head w x)) :=
  Internal.ObjectRawCodeProjection.native_rawHeadTailExists head w x

example {m} (head : Bool) (w x y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeProjection.rawHeadTailUniqueSentence head w x y z)) :=
  Internal.ObjectRawCodeProjection.native_rawHeadTailUnique head w x y z

example {m} (head : Bool) (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeProjection.rawHeadTailRangeSentence head w x y)) :=
  Internal.ObjectRawCodeProjection.native_rawHeadTailRange head w x y

example {m} (head : Bool) (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeProjection.rawHeadTailZeroIffSentence head w x y)) :=
  Internal.ObjectRawCodeProjection.native_rawHeadTailZeroIff head w x y

example {m} (head : Bool) (w tag p a b x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeProjection.arbitraryRawTagHeadTailIffSentence head w tag p a b x y)) :=
  Internal.ObjectRawCodeProjection.native_arbitraryRawTagHeadTailIff head w tag p a b x y

example {m} (head : Bool) (w x i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeProjection.rawNaturalIterationFiberSentence head w x i)) :=
  Internal.ObjectRawCodeProjection.native_rawNaturalIterationFiber head w x i

example {m} (w x i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeProjection.rawGetExistsSentence w x i)) :=
  Internal.ObjectRawCodeProjection.native_rawGetExists w x i

example {m} (w x i y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeProjection.rawGetUniqueSentence w x i y z)) :=
  Internal.ObjectRawCodeProjection.native_rawGetUnique w x i y z

example {m} (w x i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeProjection.rawGetFiberSentence w x i)) :=
  Internal.ObjectRawCodeProjection.native_rawGetFiber w x i

example {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeProjection.rawGetRangeSentence w x i y)) :=
  Internal.ObjectRawCodeProjection.native_rawGetRange w x i y

example {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeProjection.rawGetZeroEquationSentence w x i y)) :=
  Internal.ObjectRawCodeProjection.native_rawGetZeroEquation w x i y

example {m} (w x t r s y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeProjection.rawGetSuccessorEquationSentence w x t r s y)) :=
  Internal.ObjectRawCodeProjection.native_rawGetSuccessorEquation w x t r s y
-- 任意原始标签，未假定tag=1或规范Cons；整个候选输出双条件返回原核。
example {m} (head : Bool) (w tag p a b x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((Source.Formula.mem tag w).imp
      ((Source.Formula.mem p w).imp ((Source.Formula.mem a w).imp ((Source.Formula.mem b w).imp
        ((StructuralNodeSyntax.raw w tag p x).imp ((GodelPairSyntax.code w a b p).imp
          ((RawCodeProjectionSyntax.step head w x y).iff (Source.Formula.equal y (if head then a else b)))))))))).close)) :=
  ObjectRawCodeProjection.native_arbitraryRawTagHeadTailIff head w tag p a b x y

-- 全内部索引的后继递归方程；实际tail关系明确，不使用宿主自然递归。
example {m} (w x t r s y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((Source.Formula.mem r w).imp
      ((OmegaSyntax.successor s r).imp ((RawCodeProjectionSyntax.step false w x t).imp
        ((RawCodeGetSyntax.get w x s y).iff (RawCodeGetSyntax.get w t r y)))))).close)) :=
  ObjectRawCodeProjection.native_rawGetSuccessorEquation w x t r s y

example {m} (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeField.rawGetZeroAllInternalIndicesSentence w z)) :=
  Internal.ObjectRawCodeField.native_rawGetZeroAllInternalIndices w z

example {m} (w z i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeField.rawGetZeroInputIffSentence w z i y)) :=
  Internal.ObjectRawCodeField.native_rawGetZeroInputIff w z i y

example {m} (w x i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeField.rawFieldExistsSentence w x i)) :=
  Internal.ObjectRawCodeField.native_rawFieldExists w x i

example {m} (w x i y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeField.rawFieldUniqueSentence w x i y z)) :=
  Internal.ObjectRawCodeField.native_rawFieldUnique w x i y z

example {m} (w x i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeField.rawFieldFiberSentence w x i)) :=
  Internal.ObjectRawCodeField.native_rawFieldFiber w x i

example {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeField.rawFieldRangeSentence w x i y)) :=
  Internal.ObjectRawCodeField.native_rawFieldRange w x i y

example {m} (w x p i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeField.rawFieldAtActualPayloadIffSentence w x p i y)) :=
  Internal.ObjectRawCodeField.native_rawFieldAtActualPayloadIff w x p i y

example {m} (w tag p x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeField.rawFieldAtArbitraryRawTagIffSentence w tag p x i y)) :=
  Internal.ObjectRawCodeField.native_rawFieldAtArbitraryRawTagIff w tag p x i y

example {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeField.rawFieldZeroInputIffSentence w x i y)) :=
  Internal.ObjectRawCodeField.native_rawFieldZeroInputIff w x i y

example {m} (head : Bool) (w h t n y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeField.rawHeadTailOnActualConsIffSentence head w h t n y)) :=
  Internal.ObjectRawCodeField.native_rawHeadTailOnActualConsIff head w h t n y

example {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeField.rawGetAtFiniteForestIffSentence k xs j w n i y)) :=
  Internal.ObjectRawCodeField.native_rawGetAtFiniteForestIff k xs j w n i y

example {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w tag n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeField.rawFieldAtFiniteNodeIffSentence k xs j w tag n i y)) :=
  Internal.ObjectRawCodeField.native_rawFieldAtFiniteNodeIff k xs j w tag n i y

example {m} (k tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectRawCodeField.rawFieldAtFiniteConstructorIffSentence k tag xs j w n i y)) :=
  Internal.ObjectRawCodeField.native_rawFieldAtFiniteConstructorIff k tag xs j w n i y
-- 输入零码的全部内部自然索引，不仅索引为零；候选输出不预给自然性。
example {m} (w z i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Source.Formula.mem i w).imp ((RawCodeGetSyntax.get w z i y).iff (OmegaSyntax.empty y))))).close)) :=
  ObjectRawCodeField.native_rawGetZeroInputIff w z i y

-- 原field的实际唯一纤维只有Omega和内部索引自然性，无输入规范性前提。
example {m} (w x i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((Source.Formula.mem i w).imp
      (RawCodeFieldSyntax.fiber w x i))).close)) :=
  ObjectRawCodeField.native_rawFieldFiber w x i

-- 固定合法槽位是外部模式；实际候选原构造器及原字段值均为对象量词。
example {m} (k tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((SyntaxNodeSyntax.constructor k tag w xs n).imp
      ((SyntaxNumeralSyntax.numeral j.val i).imp
        ((RawCodeFieldSyntax.field w n i y).iff (Source.Formula.equal y (xs j)))))).close)) :=
  ObjectRawCodeField.native_rawFieldAtFiniteConstructorIff k tag xs j w n i y

example {m} (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTrace.projectionTraceNaturalSentence w r)) :=
  Internal.ObjectProjectionTrace.native_projectionTraceNatural w r

example {m} (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTrace.projectionTraceOriginalStepSentence w r)) :=
  Internal.ObjectProjectionTrace.native_projectionTraceOriginalStep w r

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTrace.projectionTraceSetExistsSentence w)) :=
  Internal.ObjectProjectionTrace.native_projectionTraceSetExists w

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTrace.projectionTraceAllRootsUnfoldSentence w)) :=
  Internal.ObjectProjectionTrace.native_projectionTraceAllRootsUnfold w

example {m} (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTrace.projectionTraceAtActualSetIffSentence w V r)) :=
  Internal.ObjectProjectionTrace.native_projectionTraceAtActualSetIff w V r

example {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (hr : rule ∈ YesMetaZFC.Automation.ObjectProjection.rules) (env : Fin rule.arity → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTrace.projectionActualHeadBoundSentence rule env w r)) :=
  Internal.ObjectProjectionTrace.native_projectionActualHeadBound rule hr env w r

example {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (hr : rule ∈ YesMetaZFC.Automation.ObjectProjection.rules) (env : Fin rule.arity → Fin m) (w r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTrace.projectionActualRuleApplicationSentence rule env w r R)) :=
  Internal.ObjectProjectionTrace.native_projectionActualRuleApplication rule hr env w r R

example {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (hr : rule ∈ YesMetaZFC.Automation.ObjectProjection.rules) (env : Fin rule.arity → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTrace.projectionActualRuleConditionSentence rule env w r)) :=
  Internal.ObjectProjectionTrace.native_projectionActualRuleCondition rule hr env w r

example {m} (env : Fin 0 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTrace.projectionTagZeroRuleSentence env w)) :=
  Internal.ObjectProjectionTrace.native_projectionTagZeroRule env w

example {m} (env : Fin 2 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTrace.projectionTagPositiveRuleSentence env w)) :=
  Internal.ObjectProjectionTrace.native_projectionTagPositiveRule env w

example {m} (env : Fin 1 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTrace.projectionGetZeroRuleSentence env w)) :=
  Internal.ObjectProjectionTrace.native_projectionGetZeroRule env w

example {m} (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTrace.projectionGetHeadRuleSentence env w)) :=
  Internal.ObjectProjectionTrace.native_projectionGetHeadRule env w

example {m} (env : Fin 5 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTrace.projectionGetTailRuleSentence env w)) :=
  Internal.ObjectProjectionTrace.native_projectionGetTailRule env w

example {m} (env : Fin 1 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTrace.projectionFieldZeroRuleSentence env w)) :=
  Internal.ObjectProjectionTrace.native_projectionFieldZeroRule env w

example {m} (env : Fin 4 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTrace.projectionFieldPositiveRuleSentence env w)) :=
  Internal.ObjectProjectionTrace.native_projectionFieldPositiveRule env w
-- 独立原七规则表，不得将纯十五规则或变换二十八规则当作投影规则。
example : YesMetaZFC.Automation.ObjectProjection.rules =
    [YesMetaZFC.Automation.ObjectProjection.tagZero, YesMetaZFC.Automation.ObjectProjection.tagPositive,
     YesMetaZFC.Automation.ObjectProjection.getZero, YesMetaZFC.Automation.ObjectProjection.getHead,
     YesMetaZFC.Automation.ObjectProjection.getTail, YesMetaZFC.Automation.ObjectProjection.fieldZero,
     YesMetaZFC.Automation.ObjectProjection.fieldPositive] := rfl

-- 实际存在一个内部根集合，统一展开全部内部候选，无外部有限轨迹前提。
example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence ((Source.Formula.ex
      ((ProjectionTraceSetSyntax.value w.castSucc (Fin.last m)).conj
        (Source.Formula.all ((Source.Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).imp
          ((ProjectionTraceSyntax.condition w.castSucc.castSucc (Fin.last (m+1))).iff
            (HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w.castSucc.castSucc
              (Fin.last (m+1)) (Fin.last m).castSucc)))))).close)) :=
  ObjectProjectionTrace.native_projectionTraceAllRootsUnfold w

example {m} (k tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTag.projectionConstructorFieldNaturalSentence k tag xs j w row)) :=
  Internal.ObjectProjectionTag.native_projectionConstructorFieldNatural k tag xs j w row

example {m} (j : Fin 2) (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTag.projectionTagQueryNaturalSentence j w x y)) :=
  Internal.ObjectProjectionTag.native_projectionTagQueryNatural j w x y

example {m} (j : Fin 3) (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTag.projectionGetQueryNaturalSentence j w x i y)) :=
  Internal.ObjectProjectionTag.native_projectionGetQueryNatural j w x i y

example {m} (j : Fin 3) (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTag.projectionFieldQueryNaturalSentence j w x i y)) :=
  Internal.ObjectProjectionTag.native_projectionFieldQueryNatural j w x i y

example {m} (k : Nat) (xs : Fin k → Fin m) (w row R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTag.projectionTagRuleDispatchSentence k xs w row R)) :=
  Internal.ObjectProjectionTag.native_projectionTagRuleDispatch k xs w row R

example {m} (k : Nat) (xs : Fin k → Fin m) (w row R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTag.projectionGetRuleDispatchSentence k xs w row R)) :=
  Internal.ObjectProjectionTag.native_projectionGetRuleDispatch k xs w row R

example {m} (k : Nat) (xs : Fin k → Fin m) (w row R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTag.projectionFieldRuleDispatchSentence k xs w row R)) :=
  Internal.ObjectProjectionTag.native_projectionFieldRuleDispatch k xs w row R

example {m} (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTag.projectionTagZeroConstructedSentence w x y)) :=
  Internal.ObjectProjectionTag.native_projectionTagZeroConstructed w x y

example {m} (w x y b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTag.projectionTagRawConstructedSentence w x y b)) :=
  Internal.ObjectProjectionTag.native_projectionTagRawConstructed w x y b

example {m} (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTag.projectionTagSoundSentence w x y)) :=
  Internal.ObjectProjectionTag.native_projectionTagSound w x y

example {m} (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTag.projectionTagCompleteSentence w x y)) :=
  Internal.ObjectProjectionTag.native_projectionTagComplete w x y

example {m} (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTag.projectionTagQueryIffSentence w x y)) :=
  Internal.ObjectProjectionTag.native_projectionTagQueryIff w x y

example {m} (w x y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTag.projectionTagQueryUniqueSentence w x y z)) :=
  Internal.ObjectProjectionTag.native_projectionTagQueryUnique w x y z

example {m} (w x y row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionTag.projectionTagAtActualRowSoundSentence w x y row)) :=
  Internal.ObjectProjectionTag.native_projectionTagAtActualRowSound w x y row
-- tag双条件只有Omega前提，输入自然域保留在对象结论，不预给候选输出自然性。
example {m} (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp
      ((ProjectionTraceSyntax.tag w x y).iff
        ((Source.Formula.mem x w).conj (PairingProjectionSyntax.step true true w x y)))).close)) :=
  ObjectProjectionTag.native_projectionTagQueryIff w x y

-- 实际get查询本身推出任一字段自然性，包括索引和候选输出。
example {m} (j : Fin 3) (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((ProjectionTraceSyntax.get w x i y).imp
      (Source.Formula.mem (SyntaxAtomSyntax.three x i y j) w))).close)) :=
  ObjectProjectionTag.native_projectionGetQueryNatural j w x i y

example : ProjectionRuleDispatch.tagRules = [YesMetaZFC.Automation.ObjectProjection.tagZero,
    YesMetaZFC.Automation.ObjectProjection.tagPositive] := rfl
example : ProjectionRuleDispatch.getRules = [YesMetaZFC.Automation.ObjectProjection.getZero,
    YesMetaZFC.Automation.ObjectProjection.getHead, YesMetaZFC.Automation.ObjectProjection.getTail] := rfl
example : ProjectionRuleDispatch.fieldRules = [YesMetaZFC.Automation.ObjectProjection.fieldZero,
    YesMetaZFC.Automation.ObjectProjection.fieldPositive] := rfl

example {m} (a : Nat) (e : YesMetaZFC.Automation.ObjectHorn.Expr a) (env : Fin a → Fin m) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.projectionActualPremiseQueryIffSentence a e env w V)) :=
  Internal.ObjectProjectionGetField.native_projectionActualPremiseQueryIff a e env w V

example {m} (a : Nat) (es : List (YesMetaZFC.Automation.ObjectHorn.Expr a)) (env : Fin a → Fin m) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.projectionActualPremisesQueriesIffSentence a es env w V)) :=
  Internal.ObjectProjectionGetField.native_projectionActualPremisesQueriesIff a es env w V

example {m} (a : Nat) (jx ji jy : Fin a) (env : Fin a → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.projectionGetVariablesQueryIffSentence a jx ji jy env w)) :=
  Internal.ObjectProjectionGetField.native_projectionGetVariablesQueryIff a jx ji jy env w

example {m} (head : Bool) (a : Nat) (tag first rest : Fin a) (env : Fin a → Fin m) (w x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.projectionArbitraryRawPairHeadTailSentence head a tag first rest env w x)) :=
  Internal.ObjectProjectionGetField.native_projectionArbitraryRawPairHeadTail head a tag first rest env w x

example {m} (a : Nat) (j : Fin a) (env : Fin a → Fin m) (w s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.projectionSuccessorVariableIffSentence a j env w s)) :=
  Internal.ObjectProjectionGetField.native_projectionSuccessorVariableIff a j env w s

example {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.projectionGetZeroConstructedSentence w x i y)) :=
  Internal.ObjectProjectionGetField.native_projectionGetZeroConstructed w x i y

example {m} (w tag first rest p x z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.projectionGetHeadConstructedSentence w tag first rest p x z)) :=
  Internal.ObjectProjectionGetField.native_projectionGetHeadConstructed w tag first rest p x z

example {m} (w tag first rest p x i s y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.projectionGetTailConstructedSentence w tag first rest p x i s y)) :=
  Internal.ObjectProjectionGetField.native_projectionGetTailConstructed w tag first rest p x i s y

example {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.projectionGetZeroIndexIffSentence w x i y)) :=
  Internal.ObjectProjectionGetField.native_projectionGetZeroIndexIff w x i y

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.projectionGetAllInternalCorrectSentence w)) :=
  Internal.ObjectProjectionGetField.native_projectionGetAllInternalCorrect w

example {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.projectionGetAtInternalIndexIffSentence w x i y)) :=
  Internal.ObjectProjectionGetField.native_projectionGetAtInternalIndexIff w x i y

example {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.projectionGetAllCandidatesIffSentence w x i y)) :=
  Internal.ObjectProjectionGetField.native_projectionGetAllCandidatesIff w x i y

example {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.projectionGetSoundSentence w x i y)) :=
  Internal.ObjectProjectionGetField.native_projectionGetSound w x i y

example {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.projectionGetCompleteSentence w x i y)) :=
  Internal.ObjectProjectionGetField.native_projectionGetComplete w x i y

example {m} (w x i y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.projectionGetUniqueSentence w x i y z)) :=
  Internal.ObjectProjectionGetField.native_projectionGetUnique w x i y z

example {m} (w i s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.projectionGetObjectSuccessorStepSentence w i s)) :=
  Internal.ObjectProjectionGetField.native_projectionGetObjectSuccessorStep w i s

example {m} (env : Fin 5 → Fin m) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.projectionGetTailActualSubquerySentence env w V)) :=
  Internal.ObjectProjectionGetField.native_projectionGetTailActualSubquery env w V

example {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.projectionFieldZeroConstructedSentence w x i y)) :=
  Internal.ObjectProjectionGetField.native_projectionFieldZeroConstructed w x i y

example {m} (w tag p x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.projectionFieldRawConstructedSentence w tag p x i y)) :=
  Internal.ObjectProjectionGetField.native_projectionFieldRawConstructed w tag p x i y

example {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.projectionFieldAllCandidatesIffSentence w x i y)) :=
  Internal.ObjectProjectionGetField.native_projectionFieldAllCandidatesIff w x i y

example {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.projectionFieldSoundSentence w x i y)) :=
  Internal.ObjectProjectionGetField.native_projectionFieldSound w x i y

example {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.projectionFieldCompleteSentence w x i y)) :=
  Internal.ObjectProjectionGetField.native_projectionFieldComplete w x i y

example {m} (w x i y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.projectionFieldUniqueSentence w x i y z)) :=
  Internal.ObjectProjectionGetField.native_projectionFieldUnique w x i y z

example {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectionGetField.originalSevenProjectionNumericIffsSentence w x i y)) :=
  Internal.ObjectProjectionGetField.native_originalSevenProjectionNumericIffs w x i y
-- get最终前提只有Omega；全部内部索引／输入／候选输出由对象量词覆盖。
example {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp
      ((ProjectionTraceSyntax.get w x i y).iff ((Source.Formula.mem x w).conj
        ((Source.Formula.mem i w).conj (RawCodeGetSyntax.get w x i y))))).close)) :=
  ObjectProjectionGetField.native_projectionGetAllCandidatesIff w x i y

-- field最终无get正确性假设，也无外部给定轨迹／解码见证。
example {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp
      ((ProjectionTraceSyntax.field w x i y).iff ((Source.Formula.mem x w).conj
        ((Source.Formula.mem i w).conj (RawCodeFieldSyntax.field w x i y))))).close)) :=
  ObjectProjectionGetField.native_projectionFieldAllCandidatesIff w x i y

-- 内部ALL索引的统一正确性，由原Separation和原omega归纳实际消去IH。
example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp (Source.Formula.all
      ((Source.Formula.mem (Fin.last m) w.castSucc).imp
        (ProjectionGetInductionSyntax.correct w.castSucc (Fin.last m))))).close)) :=
  ObjectProjectionGetField.native_projectionGetAllInternalCorrect w

example {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofSubstitutionNode.substitutionFreeProjectionIffSentence env w z)) :=
  Internal.ObjectProofSubstitutionNode.native_substitutionFreeProjectionIff env w z

example {m} (env : Fin 6 → Fin m) (w one : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofSubstitutionNode.substitutionFormulaProjectionAtOneIffSentence env w one)) :=
  Internal.ObjectProofSubstitutionNode.native_substitutionFormulaProjectionAtOneIff env w one

example {m} (env : Fin 6 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofSubstitutionNode.substitutionFormulaProjectionIffSentence env w)) :=
  Internal.ObjectProofSubstitutionNode.native_substitutionFormulaProjectionIff env w

example {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofSubstitutionNode.substitutionBothProjectionsIffSentence env w z)) :=
  Internal.ObjectProofSubstitutionNode.native_substitutionBothProjectionsIff env w z

example {m} (k tag : Nat) (xs : Fin (k+2) → Fin m) (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofSubstitutionNode.substitutionFreeProjectionAtConstructorSentence k tag xs env w z)) :=
  Internal.ObjectProofSubstitutionNode.native_substitutionFreeProjectionAtConstructor k tag xs env w z

example {m} (k tag : Nat) (xs : Fin (k+2) → Fin m) (env : Fin 6 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofSubstitutionNode.substitutionFormulaProjectionAtConstructorSentence k tag xs env w)) :=
  Internal.ObjectProofSubstitutionNode.native_substitutionFormulaProjectionAtConstructor k tag xs env w

example {m} (k tag : Nat) (xs : Fin (k+2) → Fin m) (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofSubstitutionNode.substitutionProjectionsAtConstructorSentence k tag xs env w z)) :=
  Internal.ObjectProofSubstitutionNode.native_substitutionProjectionsAtConstructor k tag xs env w z

example {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofSubstitutionNode.substitutionAllFiveQueriesIffSentence env w z)) :=
  Internal.ObjectProofSubstitutionNode.native_substitutionAllFiveQueriesIff env w z

example {m} (raw head : Bool) (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofSubstitutionNode.pairingProjectionNumericBoundSentence raw head w x y)) :=
  Internal.ObjectProofSubstitutionNode.native_pairingProjectionNumericBound raw head w x y

example {m} (head : Bool) (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofSubstitutionNode.rawHeadTailNumericBoundSentence head w x y)) :=
  Internal.ObjectProofSubstitutionNode.native_rawHeadTailNumericBound head w x y

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofSubstitutionNode.rawGetAllInternalBoundsSentence w)) :=
  Internal.ObjectProofSubstitutionNode.native_rawGetAllInternalBounds w

example {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofSubstitutionNode.rawGetNumericBoundSentence w x i y)) :=
  Internal.ObjectProofSubstitutionNode.native_rawGetNumericBound w x i y

example {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofSubstitutionNode.rawFieldNumericBoundSentence w x i y)) :=
  Internal.ObjectProofSubstitutionNode.native_rawFieldNumericBound w x i y

example {m} (w p y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofSubstitutionNode.substitutionAtOneBoundSentence w p y)) :=
  Internal.ObjectProofSubstitutionNode.native_substitutionAtOneBound w p y

example {m} (env : Fin 6 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofSubstitutionNode.substitutionFormulaProjectionBoundSentence env w)) :=
  Internal.ObjectProofSubstitutionNode.native_substitutionFormulaProjectionBound env w

example {m} (env : Fin 6 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofSubstitutionNode.substitutionAllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectProofSubstitutionNode.native_substitutionAllAssignmentBounds env w row

example {m} (env : Fin 6 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofSubstitutionNode.substitutionActualFiveFieldHeadIffSentence env w row)) :=
  Internal.ObjectProofSubstitutionNode.native_substitutionActualFiveFieldHeadIff env w row

example {m} (env : Fin 6 → Fin m) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofSubstitutionNode.substitutionBoundedMatrixIffSentence env w z row)) :=
  Internal.ObjectProofSubstitutionNode.native_substitutionBoundedMatrixIff env w z row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofSubstitutionNode.substitutionFullPureRelationalNodeIffSentence w z row)) :=
  Internal.ObjectProofSubstitutionNode.native_substitutionFullPureRelationalNodeIff w z row
-- 确切引用原查询位置／种类，不能用数值规格重定义查询。
example : YesMetaZFC.Automation.ObjectProofNode.substitutionShape.queries[2] =
    YesMetaZFC.Automation.ObjectProofNode.projection (.var 4) 0 (.var 2) := rfl
example : YesMetaZFC.Automation.ObjectProofNode.substitutionShape.queries[3] =
    YesMetaZFC.Automation.ObjectProofNode.projection (.var 4) 1 (.var 5) := rfl
example : YesMetaZFC.Automation.ObjectProofNode.substitutionShape.arity = 6 := rfl
example : YesMetaZFC.Automation.ObjectProofNode.substitutionShape.head =
    YesMetaZFC.Automation.ObjectProofNode.node 5 [.var 0, .var 1, .var 2, .var 3, .var 4] := rfl

-- 原field在所有内部自然输入／索引上的值界，不要求合法前驱证明或规范外壳。
example {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((Source.Formula.mem x w).imp
      ((Source.Formula.mem i w).imp ((RawCodeFieldSyntax.field w x i y).imp
        (NaturalAdditionBounds.below y x))))).close)) :=
  ObjectProofSubstitutionNode.native_rawFieldNumericBound w x i y

-- 全部六赋值、实际原头、全部五查询和搜索界均在node的对象存在块内。
-- 最终没有预给envNat／bounds／query／合法前驱假设；共享扩展条件的Bool对应另行证明。
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((HornBinderSyntax.existsMany 6 (ProofSubstitutionNodeSyntax.body w row)).iff
        (HornBinderSyntax.existsMany 6 (ProofSubstitutionNodeSyntax.specificationBody w z row))))).close)) :=
  ObjectProofSubstitutionNode.native_substitutionFullPureRelationalNodeIff w z row

example {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofMPNode.mpConclusionQueryIffSentence env w z)) :=
  Internal.ObjectProofMPNode.native_mpConclusionQueryIff env w z

example {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofMPNode.mpAntecedentQueryIffSentence env w z)) :=
  Internal.ObjectProofMPNode.native_mpAntecedentQueryIff env w z

example {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofMPNode.mpLeftFreeProjectionIffSentence env w z)) :=
  Internal.ObjectProofMPNode.native_mpLeftFreeProjectionIff env w z

example {m} (env : Fin 5 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofMPNode.mpLeftFormulaProjectionIffSentence env w)) :=
  Internal.ObjectProofMPNode.native_mpLeftFormulaProjectionIff env w

example {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofMPNode.mpRightFreeProjectionIffSentence env w z)) :=
  Internal.ObjectProofMPNode.native_mpRightFreeProjectionIff env w z

example {m} (env : Fin 5 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofMPNode.mpRightImplicationProjectionIffSentence env w)) :=
  Internal.ObjectProofMPNode.native_mpRightImplicationProjectionIff env w

example {m} (env : Fin 5 → Fin m) (w q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofMPNode.mpImplicationGraphIffSentence env w q)) :=
  Internal.ObjectProofMPNode.native_mpImplicationGraphIff env w q

example {m} (env : Fin 5 → Fin m) (w q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofMPNode.mpRightImplicationAtConstructorIffSentence env w q)) :=
  Internal.ObjectProofMPNode.native_mpRightImplicationAtConstructorIff env w q

example {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofMPNode.mpAllFourProjectionsIffSentence env w z)) :=
  Internal.ObjectProofMPNode.native_mpAllFourProjectionsIff env w z

example {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofMPNode.mpBothFormulaQueriesIffSentence env w z)) :=
  Internal.ObjectProofMPNode.native_mpBothFormulaQueriesIff env w z

example {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofMPNode.mpAllSixQueriesIffSentence env w z)) :=
  Internal.ObjectProofMPNode.native_mpAllSixQueriesIff env w z

example {m} (env : Fin 5 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofMPNode.mpAntecedentProjectionBoundSentence env w)) :=
  Internal.ObjectProofMPNode.native_mpAntecedentProjectionBound env w

example {m} (env : Fin 5 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofMPNode.mpAllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectProofMPNode.native_mpAllAssignmentBounds env w row

example {m} (env : Fin 5 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofMPNode.mpActualFourFieldHeadIffSentence env w row)) :=
  Internal.ObjectProofMPNode.native_mpActualFourFieldHeadIff env w row

example {m} (env : Fin 5 → Fin m) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofMPNode.mpBoundedMatrixIffSentence env w z row)) :=
  Internal.ObjectProofMPNode.native_mpBoundedMatrixIff env w z row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofMPNode.mpFullPureRelationalNodeIffSentence w z row)) :=
  Internal.ObjectProofMPNode.native_mpFullPureRelationalNodeIff w z row

-- 原MP五赋值／四字段头／六查询；复合输出来自原表。
example : YesMetaZFC.Automation.ObjectProofNode.mpShape.arity = 5 := rfl
example : YesMetaZFC.Automation.ObjectProofNode.mpShape.queries.length = 6 := rfl
example : YesMetaZFC.Automation.ObjectProofNode.mpShape.head =
    YesMetaZFC.Automation.ObjectProofNode.node 2 [.var 0, .var 1, .var 2, .var 3] := rfl
example : YesMetaZFC.Automation.ObjectProofNode.mpShape.queries[5] =
    YesMetaZFC.Automation.ObjectProofNode.projection (.var 3) 1
      (YesMetaZFC.Automation.ObjectProofNode.node 7 [.var 4, .var 1]) := rfl

-- 最终只有Ω和空集零值前提，全部五赋值与界在对象存在块中消去。
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((HornBinderSyntax.existsMany 5 (ProofMPNodeSyntax.body w row)).iff
       (HornBinderSyntax.existsMany 5 (ProofMPNodeSyntax.specificationBody w z row))))).close)) :=
  ObjectProofMPNode.native_mpFullPureRelationalNodeIff w z row

example {m} (w mode depth P a b B n q I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofStrengtheningNode.modeZeroFormulaAtCodesIffSentence w mode depth P a b B n q I J R S)) :=
  Internal.ObjectProofStrengtheningNode.native_modeZeroFormulaAtCodesIff w mode depth P a b B n q I J R S

example {m} (w mode depth P a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofStrengtheningNode.modeZeroFullFormulaWeakenIffSentence w mode depth P a b B n q)) :=
  Internal.ObjectProofStrengtheningNode.native_modeZeroFullFormulaWeakenIff w mode depth P a b B n q

example {m} (w mode depth P a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofStrengtheningNode.modeZeroFullFormulaProgramIffSentence w mode depth P a b B n q)) :=
  Internal.ObjectProofStrengtheningNode.native_modeZeroFullFormulaProgramIff w mode depth P a b B n q

example {m} (w mode depth P a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofStrengtheningNode.modeZeroFullFormulaOutputTypeSentence w mode depth P a b B n q)) :=
  Internal.ObjectProofStrengtheningNode.native_modeZeroFullFormulaOutputType w mode depth P a b B n q

example {m} (env : Fin 4 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofStrengtheningNode.strengtheningFormulaQueryIffSentence env w z)) :=
  Internal.ObjectProofStrengtheningNode.native_strengtheningFormulaQueryIff env w z

example {m} (env : Fin 4 → Fin m) (w z B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofStrengtheningNode.strengtheningFreeProjectionAtSuccessorIffSentence env w z B)) :=
  Internal.ObjectProofStrengtheningNode.native_strengtheningFreeProjectionAtSuccessorIff env w z B

example {m} (env : Fin 4 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofStrengtheningNode.strengtheningPredecessorFormulaIffSentence env w)) :=
  Internal.ObjectProofStrengtheningNode.native_strengtheningPredecessorFormulaIff env w

example {m} (env : Fin 4 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofStrengtheningNode.strengtheningActualModeZeroQueryIffSentence env w z)) :=
  Internal.ObjectProofStrengtheningNode.native_strengtheningActualModeZeroQueryIff env w z

example {m} (env : Fin 4 → Fin m) (w z B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofStrengtheningNode.strengtheningGuardedModeZeroProgramIffSentence env w z B)) :=
  Internal.ObjectProofStrengtheningNode.native_strengtheningGuardedModeZeroProgramIff env w z B

example {m} (env : Fin 4 → Fin m) (w z B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofStrengtheningNode.strengtheningAllFourQueriesAtSuccessorIffSentence env w z B)) :=
  Internal.ObjectProofStrengtheningNode.native_strengtheningAllFourQueriesAtSuccessorIff env w z B

example {m} (env : Fin 4 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofStrengtheningNode.strengtheningAllFourQueriesIffSentence env w z)) :=
  Internal.ObjectProofStrengtheningNode.native_strengtheningAllFourQueriesIff env w z

example {m} (env : Fin 4 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofStrengtheningNode.strengtheningPredecessorFormulaBoundSentence env w)) :=
  Internal.ObjectProofStrengtheningNode.native_strengtheningPredecessorFormulaBound env w

example {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofStrengtheningNode.strengtheningAllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectProofStrengtheningNode.native_strengtheningAllAssignmentBounds env w row

example {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofStrengtheningNode.strengtheningActualThreeFieldHeadIffSentence env w row)) :=
  Internal.ObjectProofStrengtheningNode.native_strengtheningActualThreeFieldHeadIff env w row

example {m} (env : Fin 4 → Fin m) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofStrengtheningNode.strengtheningBoundedMatrixIffSentence env w z row)) :=
  Internal.ObjectProofStrengtheningNode.native_strengtheningBoundedMatrixIff env w z row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofStrengtheningNode.strengtheningFullPureRelationalNodeIffSentence w z row)) :=
  Internal.ObjectProofStrengtheningNode.native_strengtheningFullPureRelationalNodeIff w z row

example : YesMetaZFC.Automation.ObjectProofNode.strengtheningShape.arity = 4 := rfl
example : YesMetaZFC.Automation.ObjectProofNode.strengtheningShape.queries.length = 4 := rfl
example : YesMetaZFC.Automation.ObjectProofNode.strengtheningShape.head =
    YesMetaZFC.Automation.ObjectProofNode.node 4 [.var 0, .var 1, .var 2] := rfl
example : YesMetaZFC.Automation.ObjectProofNode.strengtheningShape.queries[1] =
    YesMetaZFC.Automation.ObjectProofNode.projection (.var 2) 0 (.succ (.var 0)) := rfl
example : YesMetaZFC.Automation.ObjectProofNode.strengtheningShape.queries[3] =
    YesMetaZFC.Automation.ObjectProofNode.transform 0 (.literal 0) (.var 1) (.var 3) := rfl

-- 原四赋值EX全部内部绑定；最终仅Ω／空集零值，不预给后继界／码表／合法前驱。
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((HornBinderSyntax.existsMany 4 (ProofStrengtheningNodeSyntax.body w row)).iff
       (HornBinderSyntax.existsMany 4 (ProofStrengtheningNodeSyntax.specificationBody w z row))))).close)) :=
  ObjectProofStrengtheningNode.native_strengtheningFullPureRelationalNodeIff w z row

example {m} (xs : Fin 5 → Fin m) (w r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalAbstract.modeOneFiveRuleStepIffSentence xs w r R)) :=
  Internal.ObjectOriginalAbstract.native_modeOneFiveRuleStepIff xs w r R

example {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalAbstract.modeOneVariableTwoRuleStepIffSentence bound xs w r R idx)) :=
  Internal.ObjectOriginalAbstract.native_modeOneVariableTwoRuleStepIff bound xs w r R idx

example {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalAbstract.modeOneVariableWholeTraceIffSentence bound xs w r idx)) :=
  Internal.ObjectOriginalAbstract.native_modeOneVariableWholeTraceIff bound xs w r idx

example {m} (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalAbstract.modeOneBoundIdentityGuardIffSentence env w)) :=
  Internal.ObjectOriginalAbstract.native_modeOneBoundIdentityGuardIff env w

example {m} (env : Fin 3 → Fin m) (w s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalAbstract.modeOneBoundAbstractGuardIffSentence env w s)) :=
  Internal.ObjectOriginalAbstract.native_modeOneBoundAbstractGuardIff env w s

example {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalAbstract.modeOneBoundPreservedTraceSentence env w r)) :=
  Internal.ObjectOriginalAbstract.native_modeOneBoundPreservedTrace env w r

example {m} (env : Fin 3 → Fin m) (w r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalAbstract.modeOneBoundShiftedTraceSentence env w r s)) :=
  Internal.ObjectOriginalAbstract.native_modeOneBoundShiftedTrace env w r s

example {m} (env : Fin 2 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalAbstract.modeOneFreeHeadTraceSentence env w r)) :=
  Internal.ObjectOriginalAbstract.native_modeOneFreeHeadTrace env w r

example {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectOriginalAbstract.modeOneFreeTailTraceSentence env w r)) :=
  Internal.ObjectOriginalAbstract.native_modeOneFreeTailTrace env w r

example : OriginalAbstractClasses.selected =
    [YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity 1 true,
     YesMetaZFC.Automation.ObjectSyntaxTransform.boundAbstract,
     YesMetaZFC.Automation.ObjectSyntaxTransform.freeAbstractHead,
     YesMetaZFC.Automation.ObjectSyntaxTransform.freeAbstractTail,
     YesMetaZFC.Automation.ObjectSyntaxTransform.application 1] := rfl
example : OriginalAbstractClasses.variableSelected true =
    [YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity 1 true,
     YesMetaZFC.Automation.ObjectSyntaxTransform.boundAbstract] := rfl
example : OriginalAbstractClasses.variableSelected false =
    [YesMetaZFC.Automation.ObjectSyntaxTransform.freeAbstractHead,
     YesMetaZFC.Automation.ObjectSyntaxTransform.freeAbstractTail] := rfl
-- 全根集合已在对象EX中取得并消去；最终没有给定V、闭轨迹或规则应用前提。
example {m} (bound : Bool) (w r idx : Fin m) (xs : Fin 5 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (((OmegaSyntax.omega w).imp
        ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 1 (xs 0)).imp
          ((SyntaxVariableSyntax.code bound w idx (xs 3)).imp
            ((HornLookupConditionSyntax.condition w r).iff
              (HornStepSyntax.step (OriginalAbstractClasses.variableSelected bound) w r w)))))).close)) :=
  ObjectOriginalAbstract.native_modeOneVariableWholeTraceIff bound xs w r idx

example {m} (n : Nat) (bound : Bool) (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w idx x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractVariable.originalVariableIndexGraphSentence n bound e env w idx x)) :=
  Internal.ObjectAbstractVariable.native_originalVariableIndexGraph n bound e env w idx x

example {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractVariable.modeOneBoundVariableNumericIffSentence xs w r idx)) :=
  Internal.ObjectAbstractVariable.native_modeOneBoundVariableNumericIff xs w r idx

example {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractVariable.modeOneBoundVariableNumericSoundSentence xs w r idx)) :=
  Internal.ObjectAbstractVariable.native_modeOneBoundVariableNumericSound xs w r idx

example {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractVariable.modeOneBoundVariableNumericCompleteSentence xs w r idx)) :=
  Internal.ObjectAbstractVariable.native_modeOneBoundVariableNumericComplete xs w r idx

example {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractVariable.modeOneFreeVariableNumericIffSentence xs w r idx)) :=
  Internal.ObjectAbstractVariable.native_modeOneFreeVariableNumericIff xs w r idx

example {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractVariable.modeOneFreeVariableNumericSoundSentence xs w r idx)) :=
  Internal.ObjectAbstractVariable.native_modeOneFreeVariableNumericSound xs w r idx

example {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractVariable.modeOneFreeVariableNumericCompleteSentence xs w r idx)) :=
  Internal.ObjectAbstractVariable.native_modeOneFreeVariableNumericComplete xs w r idx

example {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractVariable.modeOneAllVariableNumericTraceIffSentence bound xs w r idx)) :=
  Internal.ObjectAbstractVariable.native_modeOneAllVariableNumericTraceIff bound xs w r idx

example {m} (bound : Bool) (w mode depth P x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractVariable.modeOneAllVariableNumericRunIffSentence bound w mode depth P x idx y)) :=
  Internal.ObjectAbstractVariable.native_modeOneAllVariableNumericRunIff bound w mode depth P x idx y

example {m} (bound : Bool) (w d i x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractVariable.modeOneVariableNumericOutputNaturalSentence bound w d i x y)) :=
  Internal.ObjectAbstractVariable.native_modeOneVariableNumericOutputNatural bound w d i x y

example {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractVariable.modeOnePreservedValueConstructsTraceSentence xs w r idx)) :=
  Internal.ObjectAbstractVariable.native_modeOnePreservedValueConstructsTrace xs w r idx

example {m} (xs : Fin 5 → Fin m) (w r idx s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractVariable.modeOneShiftedValueConstructsTraceSentence xs w r idx s)) :=
  Internal.ObjectAbstractVariable.native_modeOneShiftedValueConstructsTrace xs w r idx s

example {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractVariable.modeOneFreeHeadValueConstructsTraceSentence xs w r idx)) :=
  Internal.ObjectAbstractVariable.native_modeOneFreeHeadValueConstructsTrace xs w r idx

example {m} (xs : Fin 5 → Fin m) (w r idx k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractVariable.modeOneFreeTailValueConstructsTraceSentence xs w r idx k)) :=
  Internal.ObjectAbstractVariable.native_modeOneFreeTailValueConstructsTrace xs w r idx k

-- 数值关系独立于原查询／规则／类型程序；运行时索引和深度均为内部变量。
example {m} (w d i x y : Fin m) : AbstractVariableValueSyntax.boundValue w d i x y =
    ((Source.Formula.mem i d).conj (.equal y x)).disj (AbstractVariableValueSyntax.boundShifted w d i y) := rfl
example {m} (w d i y : Fin m) : AbstractVariableValueSyntax.freeValue w d i y =
    ((OmegaSyntax.empty i).conj (SyntaxVariableSyntax.code true w d y)).disj (AbstractVariableValueSyntax.freeTail w i y) := rfl
-- 整条原kind1运行：没有给定行码、输出自然性、赋值、全根集合或轨迹见证。
example {m} (bound : Bool) (w mode depth P x idx y : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (((OmegaSyntax.omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp
        ((OriginalTermTraceSyntax.metadata w depth P).imp ((SyntaxVariableSyntax.code bound w idx x).imp
          ((OriginalTransformRowSyntax.run 1 w mode depth P x y).iff
            (AbstractVariableValueSyntax.valueSpec bound w depth idx x y)))))).close)) :=
  ObjectAbstractVariable.native_modeOneAllVariableNumericRunIff bound w mode depth P x idx y

example {m} (k : Fin 4) (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSmallModeArguments.smallModeOriginalNilGuardSentence k env w)) :=
  Internal.ObjectSmallModeArguments.native_smallModeOriginalNilGuard k env w

example {m} (k : Fin 4) (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSmallModeArguments.smallModeOriginalNilMatrixIffSentence k env w n q r)) :=
  Internal.ObjectSmallModeArguments.native_smallModeOriginalNilMatrixIff k env w n q r

example {m} (k : Fin 4) (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSmallModeArguments.smallModeOriginalNilAtRowIffSentence k env w n q r)) :=
  Internal.ObjectSmallModeArguments.native_smallModeOriginalNilAtRowIff k env w n q r

example {m} (k : Fin 4) (w mode depth parameter input output r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSmallModeArguments.smallModeOriginalNilApplicationIffSentence k w mode depth parameter input output r V)) :=
  Internal.ObjectSmallModeArguments.native_smallModeOriginalNilApplicationIff k w mode depth parameter input output r V

example {m} (k : Fin 4) (w mode depth parameter input output r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSmallModeArguments.smallModeArgumentTraceAtActualValueIffSentence k w mode depth parameter input output r V)) :=
  Internal.ObjectSmallModeArguments.native_smallModeArgumentTraceAtActualValueIff k w mode depth parameter input output r V

example {m} (k : Fin 4) (w mode depth parameter input output r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSmallModeArguments.smallModeArgumentTraceIffSentence k w mode depth parameter input output r)) :=
  Internal.ObjectSmallModeArguments.native_smallModeArgumentTraceIff k w mode depth parameter input output r

example {m} (k : Fin 4) (w mode depth parameter input output : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSmallModeArguments.smallModeArgumentWholeRunIffSentence k w mode depth parameter input output)) :=
  Internal.ObjectSmallModeArguments.native_smallModeArgumentWholeRunIff k w mode depth parameter input output

example {m} (w mode depth P a b n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSmallModeArguments.modeOnePureTermGuardedNumericIffSentence w mode depth P a b n q)) :=
  Internal.ObjectSmallModeArguments.native_modeOnePureTermGuardedNumericIff w mode depth P a b n q

example {m} (w mode depth P a b n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSmallModeArguments.modeOnePureTermTypedNumericIffSentence w mode depth P a b n q)) :=
  Internal.ObjectSmallModeArguments.native_modeOnePureTermTypedNumericIff w mode depth P a b n q

example {m} (bound : Bool) (w mode depth P limit n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSmallModeArguments.modeOneTermScopeBranchNumericSentence bound w mode depth P limit n q)) :=
  Internal.ObjectSmallModeArguments.native_modeOneTermScopeBranchNumeric bound w mode depth P limit n q

example {m} (bound : Bool) (w mode depth P limit n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSmallModeArguments.modeOneTermNumericBranchRunSentence bound w mode depth P limit n q)) :=
  Internal.ObjectSmallModeArguments.native_modeOneTermNumericBranchRun bound w mode depth P limit n q

-- 明确检查mode1与mode2，不能以旧Boolthree=false(mode0)接口替代。
example {m} (w mode depth parameter input output : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp
      ((Source.Formula.mem depth w).imp ((Source.Formula.mem parameter w).imp
        ((OriginalTransformRowSyntax.run 2 w mode depth parameter input output).iff
          (OriginalArgumentCaseSyntax.outcomes w mode depth parameter input output)))))).close)) :=
  ObjectSmallModeArguments.native_smallModeArgumentWholeRunIff (1 : Fin 4) w mode depth parameter input output
example {m} (w mode depth parameter input output : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((SyntaxNumeralSyntax.numeral 2 mode).imp
      ((Source.Formula.mem depth w).imp ((Source.Formula.mem parameter w).imp
        ((OriginalTransformRowSyntax.run 2 w mode depth parameter input output).iff
          (OriginalArgumentCaseSyntax.outcomes w mode depth parameter input output)))))).close)) :=
  ObjectSmallModeArguments.native_smallModeArgumentWholeRunIff (2 : Fin 4) w mode depth parameter input output
-- 纯成员语言有效项只有两个变量分支；类型守卫保留在结论内部。
example {m} (w mode depth P a b n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp
      ((OriginalTermTraceSyntax.metadata w depth P).imp
        (((SyntaxTermSyntax.term w a b n).conj (OriginalTransformRowSyntax.run 1 w mode depth P n q)).iff
          (AbstractTermValueSyntax.value w a b depth n q))))).close)) :=
  ObjectSmallModeArguments.native_modeOnePureTermGuardedNumericIff w mode depth P a b n q

example {m} (w z i j x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopTerm.modeOneBoundAtZeroDepthIffSentence w z i j x y)) :=
  Internal.ObjectAbstractTopTerm.native_modeOneBoundAtZeroDepthIff w z i j x y

example {m} (w d i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopTerm.modeOneFreeAtZeroIndexIffSentence w d i y)) :=
  Internal.ObjectAbstractTopTerm.native_modeOneFreeAtZeroIndexIff w d i y

example {m} (w d i k y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopTerm.modeOneFreeAtSuccessorIndexIffSentence w d i k y)) :=
  Internal.ObjectAbstractTopTerm.native_modeOneFreeAtSuccessorIndexIff w d i k y

example {m} (w d i x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopTerm.modeOneBoundBelowDepthIffSentence w d i x y)) :=
  Internal.ObjectAbstractTopTerm.native_modeOneBoundBelowDepthIff w d i x y

example {m} (w z a b A B R S i j x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopTerm.modeOneActualBoundTableAtSuccessorIffSentence w z a b A B R S i j x y)) :=
  Internal.ObjectAbstractTopTerm.native_modeOneActualBoundTableAtSuccessorIff w z a b A B R S i j x y

example {m} (w z a b A B R S i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopTerm.modeOneActualFreeTableAtZeroIffSentence w z a b A B R S i y)) :=
  Internal.ObjectAbstractTopTerm.native_modeOneActualFreeTableAtZeroIff w z a b A B R S i y

example {m} (w z a b A B R S i j y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopTerm.modeOneActualFreeTableAtSuccessorIffSentence w z a b A B R S i j y)) :=
  Internal.ObjectAbstractTopTerm.native_modeOneActualFreeTableAtSuccessorIff w z a b A B R S i j y

example {m} (bound : Bool) (w z a b A B R S i n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopTerm.modeOneZeroDepthActualVariableTableIffSentence bound w z a b A B R S i n q)) :=
  Internal.ObjectAbstractTopTerm.native_modeOneZeroDepthActualVariableTableIff bound w z a b A B R S i n q

example {m} (bound : Bool) (w mode z P a b A B R S n q i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopTerm.modeOneZeroDepthActualVariableProgramIffSentence bound w mode z P a b A B R S n q i)) :=
  Internal.ObjectAbstractTopTerm.native_modeOneZeroDepthActualVariableProgramIff bound w mode z P a b A B R S n q i

example {m} (w mode z P a b A B R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopTerm.modeOneZeroDepthActualPureTermProgramIffSentence w mode z P a b A B R S n q)) :=
  Internal.ObjectAbstractTopTerm.native_modeOneZeroDepthActualPureTermProgramIff w mode z P a b A B R S n q

example {m} (w mode z P a b A B R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopTerm.modeOneZeroDepthActualCodedPureTermIffSentence w mode z P a b A B R S n q)) :=
  Internal.ObjectAbstractTopTerm.native_modeOneZeroDepthActualCodedPureTermIff w mode z P a b A B R S n q

example {m} (w mode z P a b A B R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopTerm.modeOneZeroDepthPureTermAtActualCodesIffSentence w mode z P a b A B R S n q)) :=
  Internal.ObjectAbstractTopTerm.native_modeOneZeroDepthPureTermAtActualCodesIff w mode z P a b A B R S n q

example {m} (w mode z P a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopTerm.modeOneZeroDepthPureTermActualOperationIffSentence w mode z P a b A B n q)) :=
  Internal.ObjectAbstractTopTerm.native_modeOneZeroDepthPureTermActualOperationIff w mode z P a b A B n q

example {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopTerm.actualAbstractPureTermSourceTypeSentence w a b A B n q)) :=
  Internal.ObjectAbstractTopTerm.native_actualAbstractPureTermSourceType w a b A B n q

example {m} (w mode z P a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopTerm.modeOneZeroDepthGuardedPureTermActualOperationIffSentence w mode z P a b A B n q)) :=
  Internal.ObjectAbstractTopTerm.native_modeOneZeroDepthGuardedPureTermActualOperationIff w mode z P a b A B n q

-- 实际首槽纯项操作的两个码表均对象EX绑定；定义不调用原Run作为预言机。
example {m} (w a b A B n q : Fin m) : AbstractTopTermSyntax.abstracted w a b A B n q =
    Source.Formula.ex (.ex (AbstractTopTermSyntax.body w a b A B n q)) := rfl
-- 最终类型守卫在结论内部，没有给定R/S码表、解码图、后继索引或比较程序一致性前提。
example {m} (w mode z P a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp
      ((OriginalTermTraceSyntax.metadata w z P).imp ((OmegaSyntax.empty z).imp
        ((SyntaxTopEnvironmentSyntax.abstractInput w a b A B).imp
          (((SyntaxTermSyntax.term w a B n).conj (OriginalTransformRowSyntax.run 1 w mode z P n q)).iff
            (AbstractTopTermSyntax.abstracted w a b A B n q))))))).close)) :=
  ObjectAbstractTopTerm.native_modeOneZeroDepthGuardedPureTermActualOperationIff w mode z P a b A B n q

example {m} (modeIndex : Fin 4) (w mode depth parameter a b c d n k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopArguments.smallModeArgumentActualFiberSentence modeIndex w mode depth parameter a b c d n k)) :=
  Internal.ObjectAbstractTopArguments.native_smallModeArgumentActualFiber modeIndex w mode depth parameter a b c d n k

example {m} (modeIndex : Fin 4) (w mode depth parameter a b n k q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopArguments.smallModeArgumentActualFieldsSentence modeIndex w mode depth parameter a b n k q)) :=
  Internal.ObjectAbstractTopArguments.native_smallModeArgumentActualFields modeIndex w mode depth parameter a b n k q

example {m} (modeIndex : Fin 4) (w mode depth parameter a b c d n k q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopArguments.smallModeArgumentCompleteFieldMapIffSentence modeIndex w mode depth parameter a b c d n k q)) :=
  Internal.ObjectAbstractTopArguments.native_smallModeArgumentCompleteFieldMapIff modeIndex w mode depth parameter a b c d n k q

example {m} (w mode z P a b A B R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopArguments.modeOneActualTermAllOutputsAgreementSentence w mode z P a b A B R S n)) :=
  Internal.ObjectAbstractTopArguments.native_modeOneActualTermAllOutputsAgreement w mode z P a b A B R S n

example {m} (w mode z P a b A B R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopArguments.modeOneActualTermUniqueTypedFiberSentence w mode z P a b A B R S n)) :=
  Internal.ObjectAbstractTopArguments.native_modeOneActualTermUniqueTypedFiber w mode z P a b A B R S n

example {m} (w mode z P a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopArguments.modeOneActualTermPromiseDischargedSentence w mode z P a b A B R S)) :=
  Internal.ObjectAbstractTopArguments.native_modeOneActualTermPromiseDischarged w mode z P a b A B R S

example {m} (w mode z P a b A B R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopArguments.modeOneZeroDepthActualArgumentFieldsIffSentence w mode z P a b A B R S n q k)) :=
  Internal.ObjectAbstractTopArguments.native_modeOneZeroDepthActualArgumentFieldsIff w mode z P a b A B R S n q k

example {m} (w mode z P a b A B R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopArguments.modeOneZeroDepthActualArgumentProgramIffSentence w mode z P a b A B R S n q k)) :=
  Internal.ObjectAbstractTopArguments.native_modeOneZeroDepthActualArgumentProgramIff w mode z P a b A B R S n q k

example {m} (w mode z P a b A B R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopArguments.modeOneZeroDepthArgumentsAtActualCodesIffSentence w mode z P a b A B R S n q k)) :=
  Internal.ObjectAbstractTopArguments.native_modeOneZeroDepthArgumentsAtActualCodesIff w mode z P a b A B R S n q k

example {m} (w mode z P a b A B n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopArguments.modeOneZeroDepthArgumentsActualOperationIffSentence w mode z P a b A B n q k)) :=
  Internal.ObjectAbstractTopArguments.native_modeOneZeroDepthArgumentsActualOperationIff w mode z P a b A B n q k

example {m} (w mode z P a b A B n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractTopArguments.modeOneZeroDepthGuardedArgumentsActualOperationIffSentence w mode z P a b A B n q k)) :=
  Internal.ObjectAbstractTopArguments.native_modeOneZeroDepthGuardedArgumentsActualOperationIff w mode z P a b A B n q k

-- Expanded native contract: source list guard in the conclusion, no code tables, Promise or IH premises.
example {m} (w mode z P a b A B n q k : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (((OmegaSyntax.omega w).imp
        ((Internal.SyntaxNumeralSyntax.numeral 1 mode).imp
          ((Internal.OriginalTermTraceSyntax.metadata w z P).imp
            ((OmegaSyntax.empty z).imp
              ((Internal.SyntaxTopEnvironmentSyntax.abstractInput w a b A B).imp
                (((Internal.SyntaxMixedImageCodeSyntax.termList w k a B n).conj
                  (Internal.OriginalTransformRowSyntax.run 2 w mode z P n q)).iff
                    (Internal.AbstractTopArgumentSyntax.abstracted w a b A B n q k))))))).close)) :=
  Internal.ObjectAbstractTopArguments.native_modeOneZeroDepthGuardedArgumentsActualOperationIff w mode z P a b A B n q k

example {m} (w d i j x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractOperationFrame.arbitraryDepthBoundShiftedIffSentence w d i j x y)) :=
  Internal.ObjectAbstractOperationFrame.native_arbitraryDepthBoundShiftedIff w d i j x y

example {m} (w d i D I : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractOperationFrame.internalSuccessorThresholdIffSentence w d i D I)) :=
  Internal.ObjectAbstractOperationFrame.native_internalSuccessorThresholdIff w d i D I

example {m} (bound : Bool) (w r t a b c e n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractOperationFrame.knownActualIndexVariableRenameIffSentence bound w r t a b c e n q i j)) :=
  Internal.ObjectAbstractOperationFrame.native_knownActualIndexVariableRenameIff bound w r t a b c e n q i j

example {m} (w U V c e C t q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractOperationFrame.actualBinderBoundRenameIffSentence w U V c e C t q i j)) :=
  Internal.ObjectAbstractOperationFrame.native_actualBinderBoundRenameIff w U V c e C t q i j

example {m} (w U V c e C t q i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractOperationFrame.actualBinderFreeRenameIffSentence w U V c e C t q i)) :=
  Internal.ObjectAbstractOperationFrame.native_actualBinderFreeRenameIff w U V c e C t q i

example {m} (w d i D I U V c e C x X t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractOperationFrame.arbitraryDepthBoundBinderCovarianceIffSentence w d i D I U V c e C x X t q)) :=
  Internal.ObjectAbstractOperationFrame.native_arbitraryDepthBoundBinderCovarianceIff w d i D I U V c e C x X t q

example {m} (w d i D U V c e C t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractOperationFrame.arbitraryDepthFreeBinderCovarianceIffSentence w d i D U V c e C t q)) :=
  Internal.ObjectAbstractOperationFrame.native_arbitraryDepthFreeBinderCovarianceIff w d i D U V c e C t q

example {m} (w mode z P a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractOperationFrame.actualAbstractRootCompatibleFrameSentence w mode z P a b A B R S)) :=
  Internal.ObjectAbstractOperationFrame.native_actualAbstractRootCompatibleFrame w mode z P a b A B R S

example {m} (w mode depth P D R S a b c e A C K H U V z n i j X q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractOperationFrame.actualLiftedBoundFieldsIffSentence w mode depth P D R S a b c e A C K H U V z n i j X q)) :=
  Internal.ObjectAbstractOperationFrame.native_actualLiftedBoundFieldsIff w mode depth P D R S a b c e A C K H U V z n i j X q

example {m} (w mode depth P D R S a b c e A C K H U V z n i X q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractOperationFrame.actualLiftedFreeFieldsIffSentence w mode depth P D R S a b c e A C K H U V z n i X q)) :=
  Internal.ObjectAbstractOperationFrame.native_actualLiftedFreeFieldsIff w mode depth P D R S a b c e A C K H U V z n i X q

example {m} (w mode depth P D R S a b c e A C K H U V z n i X q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractOperationFrame.allInternalLiftedBoundFieldsIffSentence w mode depth P D R S a b c e A C K H U V z n i X q)) :=
  Internal.ObjectAbstractOperationFrame.native_allInternalLiftedBoundFieldsIff w mode depth P D R S a b c e A C K H U V z n i X q

example {m} (bound : Bool) (w mode depth P D R S a b c e A C K H U V z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractOperationFrame.allInternalLiftedFrameCompatibilitySentence bound w mode depth P D R S a b c e A C K H U V z n)) :=
  Internal.ObjectAbstractOperationFrame.native_allInternalLiftedFrameCompatibility bound w mode depth P D R S a b c e A C K H U V z n

example {m} (w mode depth P D R S a b c e A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractOperationFrame.actualBinderCompatibleFrameWitnessesDischargedSentence w mode depth P D R S a b c e A C K H)) :=
  Internal.ObjectAbstractOperationFrame.native_actualBinderCompatibleFrameWitnessesDischarged w mode depth P D R S a b c e A C K H

-- Expanded actual binder closure: four premises, no lifting graph/head/old-field witnesses.
example {m} (w mode depth P D R S a b c e A C K H : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (((OmegaSyntax.omega w).imp
        ((Internal.AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp
          ((OmegaSyntax.successor D depth).imp
            ((Internal.SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H).imp
              (Internal.AbstractOperationFrameSyntax.frame w mode D P A b C e K H))))).close)) :=
  Internal.ObjectAbstractOperationFrame.native_actualBinderCompatibleFrameWitnessesDischarged w mode depth P D R S a b c e A C K H

example {m} (bound : Bool) (w mode depth P a b c e R S n q i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractFramePrograms.arbitraryDepthFrameVariableProgramIffSentence bound w mode depth P a b c e R S n q i)) :=
  Internal.ObjectAbstractFramePrograms.native_arbitraryDepthFrameVariableProgramIff bound w mode depth P a b c e R S n q i

example {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractFramePrograms.arbitraryDepthFrameTermProgramIffSentence w mode depth P a b c e R S n q)) :=
  Internal.ObjectAbstractFramePrograms.native_arbitraryDepthFrameTermProgramIff w mode depth P a b c e R S n q

example {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractFramePrograms.arbitraryDepthFrameTermCodedIffSentence w mode depth P a b c e R S n q)) :=
  Internal.ObjectAbstractFramePrograms.native_arbitraryDepthFrameTermCodedIff w mode depth P a b c e R S n q

example {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractFramePrograms.arbitraryDepthFrameTermGuardedCodedIffSentence w mode depth P a b c e R S n q)) :=
  Internal.ObjectAbstractFramePrograms.native_arbitraryDepthFrameTermGuardedCodedIff w mode depth P a b c e R S n q

example {m} (w mode depth P a b c e R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractFramePrograms.arbitraryDepthFrameTermAllOutputsAgreementSentence w mode depth P a b c e R S n)) :=
  Internal.ObjectAbstractFramePrograms.native_arbitraryDepthFrameTermAllOutputsAgreement w mode depth P a b c e R S n

example {m} (w mode depth P a b c e R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractFramePrograms.arbitraryDepthFrameTypedTermUniqueFiberSentence w mode depth P a b c e R S n)) :=
  Internal.ObjectAbstractFramePrograms.native_arbitraryDepthFrameTypedTermUniqueFiber w mode depth P a b c e R S n

example {m} (w mode depth P a b c e R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractFramePrograms.arbitraryDepthFrameTermPromiseDischargedSentence w mode depth P a b c e R S)) :=
  Internal.ObjectAbstractFramePrograms.native_arbitraryDepthFrameTermPromiseDischarged w mode depth P a b c e R S

example {m} (w mode depth P a b c e R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractFramePrograms.arbitraryDepthFrameArgumentFieldsIffSentence w mode depth P a b c e R S n q k)) :=
  Internal.ObjectAbstractFramePrograms.native_arbitraryDepthFrameArgumentFieldsIff w mode depth P a b c e R S n q k

example {m} (w mode depth P a b c e R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractFramePrograms.arbitraryDepthFrameArgumentProgramIffSentence w mode depth P a b c e R S n q k)) :=
  Internal.ObjectAbstractFramePrograms.native_arbitraryDepthFrameArgumentProgramIff w mode depth P a b c e R S n q k

example {m} (w mode depth P a b c e R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractFramePrograms.arbitraryDepthFrameGuardedArgumentProgramIffSentence w mode depth P a b c e R S n q k)) :=
  Internal.ObjectAbstractFramePrograms.native_arbitraryDepthFrameGuardedArgumentProgramIff w mode depth P a b c e R S n q k

-- Expanded arbitrary-depth list contract: source guard inside conclusion; no Promise or IH premises.
example {m} (w mode depth P a b c e R S n q k : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (((OmegaSyntax.omega w).imp
        ((Internal.AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp
          (((Internal.SyntaxMixedImageCodeSyntax.termList w k a b n).conj
            (Internal.OriginalTransformRowSyntax.run 2 w mode depth P n q)).iff
              ((Internal.SyntaxMixedImageCodeSyntax.termList w k a b n).conj
                (Internal.ArgumentProgramFieldSyntax.mapped w R S k c e n q))))).close)) :=
  Internal.ObjectAbstractFramePrograms.native_arbitraryDepthFrameGuardedArgumentProgramIff w mode depth P a b c e R S n q k

example {m} (modeIndex : Fin 4) (tag : Nat) (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractAtomicFormula.smallModeFormulaConstantGuardSentence modeIndex tag env w)) :=
  Internal.ObjectAbstractAtomicFormula.native_smallModeFormulaConstantGuard modeIndex tag env w

example {m} (modeIndex : Fin 4) (tag : Nat) (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractAtomicFormula.smallModeFormulaConstantMatrixIffSentence modeIndex tag env w n q r)) :=
  Internal.ObjectAbstractAtomicFormula.native_smallModeFormulaConstantMatrixIff modeIndex tag env w n q r

example {m} (modeIndex : Fin 4) (truth : Bool) (w mode depth P n q r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractAtomicFormula.smallModeFormulaConstantApplicationIffSentence modeIndex truth w mode depth P n q r V)) :=
  Internal.ObjectAbstractAtomicFormula.native_smallModeFormulaConstantApplicationIff modeIndex truth w mode depth P n q r V

example {m} (modeIndex : Fin 4) (w mode depth P n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractAtomicFormula.smallModeCompleteFormulaTraceIffSentence modeIndex w mode depth P n q r)) :=
  Internal.ObjectAbstractAtomicFormula.native_smallModeCompleteFormulaTraceIff modeIndex w mode depth P n q r

example {m} (modeIndex : Fin 4) (w mode depth P n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractAtomicFormula.smallModeCompleteFormulaWholeRunIffSentence modeIndex w mode depth P n q)) :=
  Internal.ObjectAbstractAtomicFormula.native_smallModeCompleteFormulaWholeRunIff modeIndex w mode depth P n q

example {m} (modeIndex : Fin 4) (w mode depth P n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractAtomicFormula.smallModeWholeFalseDispatchIffSentence modeIndex w mode depth P n q)) :=
  Internal.ObjectAbstractAtomicFormula.native_smallModeWholeFalseDispatchIff modeIndex w mode depth P n q

example {m} (modeIndex : Fin 4) (w mode depth P n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractAtomicFormula.smallModeWholeTrueDispatchIffSentence modeIndex w mode depth P n q)) :=
  Internal.ObjectAbstractAtomicFormula.native_smallModeWholeTrueDispatchIff modeIndex w mode depth P n q

example {m} (modeIndex : Fin 4) (w mode depth P n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractAtomicFormula.smallModeWholeEqualityDispatchIffSentence modeIndex w mode depth P n q x y)) :=
  Internal.ObjectAbstractAtomicFormula.native_smallModeWholeEqualityDispatchIff modeIndex w mode depth P n q x y

example {m} (modeIndex : Fin 4) (w mode depth P s x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractAtomicFormula.smallModeWholeMemberDispatchIffSentence modeIndex w mode depth P s x y n q)) :=
  Internal.ObjectAbstractAtomicFormula.native_smallModeWholeMemberDispatchIff modeIndex w mode depth P s x y n q

example {m} (w mode depth P a b c e R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractAtomicFormula.modeOneFrameAtomicTermAgreementSentence w mode depth P a b c e R S)) :=
  Internal.ObjectAbstractAtomicFormula.native_modeOneFrameAtomicTermAgreement w mode depth P a b c e R S

example {m} (w mode depth P a b c e R S n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractAtomicFormula.modeOneFrameActualPairProgramIffSentence w mode depth P a b c e R S n q x y)) :=
  Internal.ObjectAbstractAtomicFormula.native_modeOneFrameActualPairProgramIff w mode depth P a b c e R S n q x y

example {m} (w mode depth P a b c e R S x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractAtomicFormula.modeOneFrameActualPairAgreementSentence w mode depth P a b c e R S x y)) :=
  Internal.ObjectAbstractAtomicFormula.native_modeOneFrameActualPairAgreement w mode depth P a b c e R S x y

example {m} (truth : Bool) (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractAtomicFormula.modeOneFrameWholeConstantIffSentence truth w mode depth P a b c e R S n q)) :=
  Internal.ObjectAbstractAtomicFormula.native_modeOneFrameWholeConstantIff truth w mode depth P a b c e R S n q

example {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractAtomicFormula.modeOneFrameWholeMembershipIffSentence w mode depth P a b c e R S n q)) :=
  Internal.ObjectAbstractAtomicFormula.native_modeOneFrameWholeMembershipIff w mode depth P a b c e R S n q

example {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractAtomicFormula.modeOneFrameWholeEqualityIffSentence w mode depth P a b c e R S n q)) :=
  Internal.ObjectAbstractAtomicFormula.native_modeOneFrameWholeEqualityIff w mode depth P a b c e R S n q

example {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractAtomicFormula.modeOneFrameAllAtomicWholeRunIffSentence w mode depth P a b c e R S n q)) :=
  Internal.ObjectAbstractAtomicFormula.native_modeOneFrameAllAtomicWholeRunIff w mode depth P a b c e R S n q

example {m} (w mode depth P a b c e R S h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractAtomicFormula.modeOneFrameAllAtomicProgramIffSentence w mode depth P a b c e R S h n q)) :=
  Internal.ObjectAbstractAtomicFormula.native_modeOneFrameAllAtomicProgramIff w mode depth P a b c e R S h n q

-- Explicit actual mode1, not the old Boolean mode0.
example {m} (w mode depth P n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractAtomicFormula.smallModeCompleteFormulaWholeRunIffSentence (1 : Fin 4) w mode depth P n q)) :=
  Internal.ObjectAbstractAtomicFormula.native_smallModeCompleteFormulaWholeRunIff (1 : Fin 4) w mode depth P n q

-- Expanded complete mode1 atomic program contract, with no agreement or source-field witness premise.
example {m} (w mode depth P a b c e R S h n q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (((OmegaSyntax.omega w).imp
        ((Internal.AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp
          ((Internal.SyntaxAtomSyntax.atomic w a b n).imp
            ((Internal.OriginalTransformRowSyntax.run 3 w mode depth P n q).iff
              (Internal.FormulaTransformProgramSyntax.run Internal.FormulaAtomicProgramSyntax.program w R S a b c e h n q))))).close)) :=
  Internal.ObjectAbstractAtomicFormula.native_modeOneFrameAllAtomicProgramIff w mode depth P a b c e R S h n q

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractFormulaCorrectness.modeOneAllFormulaCorrectSentence w)) :=
  Internal.ObjectAbstractFormulaCorrectness.native_modeOneAllFormulaCorrect w

example {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractFormulaCorrectness.modeOneFormulaCorrectAtSentence w n)) :=
  Internal.ObjectAbstractFormulaCorrectness.native_modeOneFormulaCorrectAt w n

example {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractFormulaCorrectness.modeOneAllFramesIHSentence w n)) :=
  Internal.ObjectAbstractFormulaCorrectness.native_modeOneAllFramesIH w n

example {m} (w n mode depth P a b c e R S q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractFormulaCorrectness.modeOneFullFormulaRunExecutionIffSentence w n mode depth P a b c e R S q)) :=
  Internal.ObjectAbstractFormulaCorrectness.native_modeOneFullFormulaRunExecutionIff w n mode depth P a b c e R S q

example {m} (w n mode depth P a b c e R S h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractFormulaCorrectness.modeOneActualHistoryAgreementSentence w n mode depth P a b c e R S h)) :=
  Internal.ObjectAbstractFormulaCorrectness.native_modeOneActualHistoryAgreement w n mode depth P a b c e R S h

example {m} (w n mode depth P a b c e R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractFormulaCorrectness.modeOneFullFormulaRunProgramIffSentence w n mode depth P a b c e R S h q)) :=
  Internal.ObjectAbstractFormulaCorrectness.native_modeOneFullFormulaRunProgramIff w n mode depth P a b c e R S h q

example {m} (w n mode depth P a b c e R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractFormulaCorrectness.modeOneAgreedHistoryExistsSentence w n mode depth P a b c e R S)) :=
  Internal.ObjectAbstractFormulaCorrectness.native_modeOneAgreedHistoryExists w n mode depth P a b c e R S

example {m} (w n mode z P a b A B R S q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractFormulaCorrectness.modeOneActualTopFullFormulaExecutionIffSentence w n mode z P a b A B R S q)) :=
  Internal.ObjectAbstractFormulaCorrectness.native_modeOneActualTopFullFormulaExecutionIff w n mode z P a b A B R S q

example {m} (w n mode z P a b A B R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectAbstractFormulaCorrectness.modeOneActualTopFullFormulaProgramIffSentence w n mode z P a b A B R S h q)) :=
  Internal.ObjectAbstractFormulaCorrectness.native_modeOneActualTopFullFormulaProgramIff w n mode z P a b A B R S h q

-- Expanded final contract: the only premises are Omega, actual frame, typed source formula.
example {m} (w n mode depth P a b c e R S q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (((OmegaSyntax.omega w).imp
        ((Internal.AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp
          ((Internal.FormulaCodeSyntax.formulaCode w n a b).imp
            ((Internal.OriginalTransformRowSyntax.run 3 w mode depth P n q).iff
              (Internal.FormulaTransformExecutionSyntax.executed w R S a b c e n q))))).close)) :=
  Internal.ObjectAbstractFormulaCorrectness.native_modeOneFullFormulaRunExecutionIff w n mode depth P a b c e R S q

example {m} (w mode z P a b A B R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallNode.modeOneActualTopFormulaAtCodesIffSentence w mode z P a b A B R S n q)) :=
  Internal.ObjectForallNode.native_modeOneActualTopFormulaAtCodesIff w mode z P a b A B R S n q

example {m} (w mode z P a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallNode.modeOneActualTopFormulaIffSentence w mode z P a b A B n q)) :=
  Internal.ObjectForallNode.native_modeOneActualTopFormulaIff w mode z P a b A B n q

example {m} (w mode z P a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallNode.modeOneActualTopGuardedFormulaIffSentence w mode z P a b A B n q)) :=
  Internal.ObjectForallNode.native_modeOneActualTopGuardedFormulaIff w mode z P a b A B n q

example {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallNode.modeOneActualTopFormulaSourceSentence w a b A B n q)) :=
  Internal.ObjectForallNode.native_modeOneActualTopFormulaSource w a b A B n q

example {m} (env : Fin 4 → Fin m) (w z B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallNode.forallFormulaQueryIffSentence env w z B)) :=
  Internal.ObjectForallNode.native_forallFormulaQueryIff env w z B

example {m} (env : Fin 4 → Fin m) (w z B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallNode.forallFreeProjectionQueryIffSentence env w z B)) :=
  Internal.ObjectForallNode.native_forallFreeProjectionQueryIff env w z B

example {m} (env : Fin 4 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallNode.forallPredecessorFormulaQueryIffSentence env w)) :=
  Internal.ObjectForallNode.native_forallPredecessorFormulaQueryIff env w

example {m} (env : Fin 4 → Fin m) (w z A : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallNode.forallModeOneTransformNumericIffSentence env w z A)) :=
  Internal.ObjectForallNode.native_forallModeOneTransformNumericIff env w z A

example {m} (env : Fin 4 → Fin m) (w z A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallNode.forallActualTopTransformIffSentence env w z A B)) :=
  Internal.ObjectForallNode.native_forallActualTopTransformIff env w z A B

example {m} (env : Fin 4 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallNode.forallAllFourQueriesIffSentence env w z)) :=
  Internal.ObjectForallNode.native_forallAllFourQueriesIff env w z

example {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallNode.forallAllFourAssignmentBoundsSentence env w row)) :=
  Internal.ObjectForallNode.native_forallAllFourAssignmentBounds env w row

example {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallNode.forallActualNestedHeadIffSentence env w row)) :=
  Internal.ObjectForallNode.native_forallActualNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallNode.forallFullPureRelationalNodeIffSentence w z row)) :=
  Internal.ObjectForallNode.native_forallFullPureRelationalNodeIff w z row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallNode.forallFullNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectForallNode.native_forallFullNormalizedNodeIff w z row

-- Expanded actual top formula operation, with input type guard inside the conclusion.
example {m} (w mode z P a b A B n q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (((OmegaSyntax.omega w).imp
        ((Internal.SyntaxNumeralSyntax.numeral 1 mode).imp
          ((Internal.OriginalTermTraceSyntax.metadata w z P).imp
            ((OmegaSyntax.empty z).imp
              ((Internal.SyntaxTopEnvironmentSyntax.abstractInput w a b A B).imp
                (((Internal.FormulaCodeSyntax.formulaCode w n a B).conj
                  (Internal.OriginalTransformRowSyntax.run 3 w mode z P n q)).iff
                    (Internal.SyntaxTopFormulaSyntax.abstracted w a b A B n q))))))).close)) :=
  Internal.ObjectForallNode.native_modeOneActualTopGuardedFormulaIff w mode z P a b A B n q

-- Expanded complete node, including the four original bounded assignment witnesses.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.ProofForallNodeSyntax.node w row).iff (Internal.ProofForallNode.normalized w z row)))).close)) :=
  Internal.ObjectForallNode.native_forallFullNormalizedNodeIff w z row

example {m} (bound : Bool) (w mode depth P x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateVariable.modeTwoWholeVariableValueIffSentence bound w mode depth P x idx y)) :=
  Internal.ObjectInstantiateVariable.native_modeTwoWholeVariableValueIff bound w mode depth P x idx y

example {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateVariable.modeTwoVariableTraceValueIffSentence bound xs w r idx)) :=
  Internal.ObjectInstantiateVariable.native_modeTwoVariableTraceValueIff bound xs w r idx

example {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateVariable.modeTwoBoundCandidateIffSentence xs w r idx)) :=
  Internal.ObjectInstantiateVariable.native_modeTwoBoundCandidateIff xs w r idx

example {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateVariable.modeTwoFreeCandidateIffSentence xs w r idx)) :=
  Internal.ObjectInstantiateVariable.native_modeTwoFreeCandidateIff xs w r idx

example {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateVariable.modeTwoOriginalVariableTraceStepIffSentence bound xs w r idx)) :=
  Internal.ObjectInstantiateVariable.native_modeTwoOriginalVariableTraceStepIff bound xs w r idx

example {m} (xs : Fin 5 → Fin m) (w r T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateVariable.modeTwoFiveRuleTermDispatchIffSentence xs w r T)) :=
  Internal.ObjectInstantiateVariable.native_modeTwoFiveRuleTermDispatchIff xs w r T

example {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateVariable.modeTwoBoundPreservedPositiveTraceSentence env w r)) :=
  Internal.ObjectInstantiateVariable.native_modeTwoBoundPreservedPositiveTrace env w r

example {m} (env : Fin 2 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateVariable.modeTwoBoundPointPositiveTraceSentence env w r)) :=
  Internal.ObjectInstantiateVariable.native_modeTwoBoundPointPositiveTrace env w r

example {m} (env : Fin 3 → Fin m) (w r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateVariable.modeTwoBoundPredecessorPositiveTraceSentence env w r s)) :=
  Internal.ObjectInstantiateVariable.native_modeTwoBoundPredecessorPositiveTrace env w r s

example {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateVariable.modeTwoFreeIdentityPositiveTraceSentence env w r)) :=
  Internal.ObjectInstantiateVariable.native_modeTwoFreeIdentityPositiveTrace env w r

example {m} (w e P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateVariable.modeTwoClosedParameterFreeBranchSentence w e P)) :=
  Internal.ObjectInstantiateVariable.native_modeTwoClosedParameterFreeBranch w e P

example {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateVariable.modeTwoFrameTermProgramIffSentence w mode depth P a b c e R S n q)) :=
  Internal.ObjectInstantiateVariable.native_modeTwoFrameTermProgramIff w mode depth P a b c e R S n q

example {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateVariable.modeTwoFrameTermCodedIffSentence w mode depth P a b c e R S n q)) :=
  Internal.ObjectInstantiateVariable.native_modeTwoFrameTermCodedIff w mode depth P a b c e R S n q

example {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateVariable.modeTwoFrameGuardedTermCodedIffSentence w mode depth P a b c e R S n q)) :=
  Internal.ObjectInstantiateVariable.native_modeTwoFrameGuardedTermCodedIff w mode depth P a b c e R S n q

-- Expanded genuine mode2 whole-variable contract: no root row or output-naturality premise.
example {m} (bound : Bool) (w mode depth P x idx y : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (((OmegaSyntax.omega w).imp
        ((Internal.SyntaxNumeralSyntax.numeral 2 mode).imp
          ((Internal.OriginalTermTraceSyntax.metadata w depth P).imp
            ((Internal.SyntaxVariableSyntax.code bound w idx x).imp
              ((Internal.OriginalTransformRowSyntax.run 1 w mode depth P x y).iff
                (Internal.InstantiateVariableValueSyntax.valueSpec bound w depth P idx x y)))))).close)) :=
  Internal.ObjectInstantiateVariable.native_modeTwoWholeVariableValueIff bound w mode depth P x idx y

-- Expanded conditional frame term contract, with source type inside the conclusion.
example {m} (w mode depth P a b c e R S n q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (((OmegaSyntax.omega w).imp
        ((Internal.InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S).imp
          (((Internal.SyntaxTermSyntax.term w a b n).conj (Internal.OriginalTransformRowSyntax.run 1 w mode depth P n q)).iff
            (Internal.SyntaxCodedMixedTermSyntax.substituted w R S a b c e n q)))).close)) :=
  Internal.ObjectInstantiateVariable.native_modeTwoFrameGuardedTermCodedIff w mode depth P a b c e R S n q

example {m} (w U V c e C P q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateRoot.modeTwoClosedParameterBinderRenameIffSentence w U V c e C P q)) :=
  Internal.ObjectInstantiateRoot.native_modeTwoClosedParameterBinderRenameIff w U V c e C P q

example {m} (w d P i x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateRoot.modeTwoVariableAtPointIffSentence w d P i x y)) :=
  Internal.ObjectInstantiateRoot.native_modeTwoVariableAtPointIff w d P i x y

example {m} (w d P i x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateRoot.modeTwoVariableBelowIffSentence w d P i x y)) :=
  Internal.ObjectInstantiateRoot.native_modeTwoVariableBelowIff w d P i x y

example {m} (bound : Bool) (w z b A P R S i n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateRoot.modeTwoActualRootVariableFieldIffSentence bound w z b A P R S i n q)) :=
  Internal.ObjectInstantiateRoot.native_modeTwoActualRootVariableFieldIff bound w z b A P R S i n q

example {m} (bound : Bool) (w z b A P R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateRoot.modeTwoActualRootVariableCompatibilitySentence bound w z b A P R S)) :=
  Internal.ObjectInstantiateRoot.native_modeTwoActualRootVariableCompatibility bound w z b A P R S

example {m} (w mode z P b A R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateRoot.modeTwoActualRootFrameSentence w mode z P b A R S)) :=
  Internal.ObjectInstantiateRoot.native_modeTwoActualRootFrame w mode z P b A R S

example {m} (w mode z P b A R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateRoot.modeTwoActualRootTermProgramIffSentence w mode z P b A R S n q)) :=
  Internal.ObjectInstantiateRoot.native_modeTwoActualRootTermProgramIff w mode z P b A R S n q

example {m} (w mode z P b A R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateRoot.modeTwoActualRootTermCodedIffSentence w mode z P b A R S n q)) :=
  Internal.ObjectInstantiateRoot.native_modeTwoActualRootTermCodedIff w mode z P b A R S n q

example {m} (w mode z P b A R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateRoot.modeTwoActualRootGuardedTermCodedIffSentence w mode z P b A R S n q)) :=
  Internal.ObjectInstantiateRoot.native_modeTwoActualRootGuardedTermCodedIff w mode z P b A R S n q
-- Expanded actual mode2 root contract: metadata and compatibility are derived, source type is inside the conclusion.
example {m} (w mode z P b A R S n q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (((OmegaSyntax.omega w).imp
        ((Internal.SyntaxNumeralSyntax.numeral 2 mode).imp
          ((OmegaSyntax.empty z).imp
            ((Internal.SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S).imp
              (((Internal.SyntaxTermSyntax.term w A b n).conj (Internal.OriginalTransformRowSyntax.run 1 w mode z P n q)).iff
                (Internal.SyntaxCodedMixedTermSyntax.substituted w R S A b z b n q)))))).close)) :=
  Internal.ObjectInstantiateRoot.native_modeTwoActualRootGuardedTermCodedIff w mode z P b A R S n q

example {m} (d i D I : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateBinder.modeTwoBinderSuccessorPointSentence d i D I)) :=
  Internal.ObjectInstantiateBinder.native_modeTwoBinderSuccessorPoint d i D I

example {m} (d a b c e D A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateBinder.modeTwoBinderContextGeometrySentence d a b c e D A C)) :=
  Internal.ObjectInstantiateBinder.native_modeTwoBinderContextGeometry d a b c e D A C

example {m} (w d P i D I U V c e C X t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateBinder.modeTwoBinderBelowCaseIffSentence w d P i D I U V c e C X t q)) :=
  Internal.ObjectInstantiateBinder.native_modeTwoBinderBelowCaseIff w d P i D I U V c e C X t q

example {m} (w d P i D I U V c e C X t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateBinder.modeTwoBinderPointCaseIffSentence w d P i D I U V c e C X t q)) :=
  Internal.ObjectInstantiateBinder.native_modeTwoBinderPointCaseIff w d P i D I U V c e C X t q

example {m} (w d P a i D I U V c e C x X t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateBinder.modeTwoBinderBoundCovarianceIffSentence w d P a i D I U V c e C x X t q)) :=
  Internal.ObjectInstantiateBinder.native_modeTwoBinderBoundCovarianceIff w d P a i D I U V c e C x X t q

example {m} (w i U V c e C X t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateBinder.modeTwoBinderFreeCovarianceIffSentence w i U V c e C X t q)) :=
  Internal.ObjectInstantiateBinder.native_modeTwoBinderFreeCovarianceIff w i U V c e C X t q

example {m} (w depth P D R S a b c e A C K H U V z n i X q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateBinder.modeTwoBinderFreshZeroFieldIffSentence w depth P D R S a b c e A C K H U V z n i X q)) :=
  Internal.ObjectInstantiateBinder.native_modeTwoBinderFreshZeroFieldIff w depth P D R S a b c e A C K H U V z n i X q

example {m} (w mode depth P D R S a b c e A C K H U V z n i j X q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateBinder.modeTwoBinderBoundSuccessorFieldIffSentence w mode depth P D R S a b c e A C K H U V z n i j X q)) :=
  Internal.ObjectInstantiateBinder.native_modeTwoBinderBoundSuccessorFieldIff w mode depth P D R S a b c e A C K H U V z n i j X q

example {m} (w mode depth P D R S a b c e A C K H U V z n i X q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateBinder.modeTwoBinderFreeFieldIffSentence w mode depth P D R S a b c e A C K H U V z n i X q)) :=
  Internal.ObjectInstantiateBinder.native_modeTwoBinderFreeFieldIff w mode depth P D R S a b c e A C K H U V z n i X q

example {m} (boundTag : Bool) (w mode depth P D R S a b c e A C K H U V z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateBinder.modeTwoBinderVariableCompatibilitySentence boundTag w mode depth P D R S a b c e A C K H U V z n)) :=
  Internal.ObjectInstantiateBinder.native_modeTwoBinderVariableCompatibility boundTag w mode depth P D R S a b c e A C K H U V z n

example {m} (w mode depth P D R S a b c e A C K H U V z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateBinder.modeTwoBinderFrameAtWitnessesSentence w mode depth P D R S a b c e A C K H U V z n)) :=
  Internal.ObjectInstantiateBinder.native_modeTwoBinderFrameAtWitnesses w mode depth P D R S a b c e A C K H U V z n

example {m} (w mode depth P D R S a b c e A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateBinder.modeTwoActualBinderFrameSentence w mode depth P D R S a b c e A C K H)) :=
  Internal.ObjectInstantiateBinder.native_modeTwoActualBinderFrame w mode depth P D R S a b c e A C K H
-- Expanded actual mode2 binder endpoint: independent source/target successor witnesses are eliminated internally.
example {m} (w mode depth P D R S a b c e A C K H : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (((OmegaSyntax.omega w).imp
        ((Internal.InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S).imp
          ((OmegaSyntax.successor D depth).imp
            ((Internal.SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H).imp
              (Internal.InstantiateOperationFrameSyntax.frame w mode D P A b C e K H))))).close)) :=
  Internal.ObjectInstantiateBinder.native_modeTwoActualBinderFrame w mode depth P D R S a b c e A C K H

example {m} (w mode depth P a b c e R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateFormula.modeTwoAllTypedTermAgreementSentence w mode depth P a b c e R S n)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoAllTypedTermAgreement w mode depth P a b c e R S n

example {m} (w mode depth P a b c e R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateFormula.modeTwoAllTypedTermUniqueFiberSentence w mode depth P a b c e R S n)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoAllTypedTermUniqueFiber w mode depth P a b c e R S n

example {m} (w mode depth P a b c e R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateFormula.modeTwoTermPromiseDerivedSentence w mode depth P a b c e R S)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoTermPromiseDerived w mode depth P a b c e R S

example {m} (w mode depth P a b c e R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateFormula.modeTwoArgumentFieldsProgramIffSentence w mode depth P a b c e R S n q k)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoArgumentFieldsProgramIff w mode depth P a b c e R S n q k

example {m} (w mode depth P a b c e R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateFormula.modeTwoWholeArgumentProgramIffSentence w mode depth P a b c e R S n q k)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoWholeArgumentProgramIff w mode depth P a b c e R S n q k

example {m} (w mode depth P a b c e R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateFormula.modeTwoGuardedArgumentProgramIffSentence w mode depth P a b c e R S n q k)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoGuardedArgumentProgramIff w mode depth P a b c e R S n q k

example {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateFormula.modeTwoFourAtomicRunIffSentence w mode depth P a b c e R S n q)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoFourAtomicRunIff w mode depth P a b c e R S n q

example {m} (w mode depth P a b c e R S h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateFormula.modeTwoFourAtomicProgramIffSentence w mode depth P a b c e R S h n q)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoFourAtomicProgramIff w mode depth P a b c e R S h n q

example {m} (w n mode depth P a b c e R S A C K H D : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateFormula.modeTwoActualBinderPrefixFromInductionSentence w n mode depth P a b c e R S A C K H D)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoActualBinderPrefixFromInduction w n mode depth P a b c e R S A C K H D

example {m} (w n mode depth P a b c e R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateFormula.modeTwoAllElevenProgramFromInductionIffSentence w n mode depth P a b c e R S h q)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoAllElevenProgramFromInductionIff w n mode depth P a b c e R S h q

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateFormula.modeTwoUniformCorrectnessProgressiveSentence w)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoUniformCorrectnessProgressive w

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateFormula.modeTwoAllInternalFormulaCorrectSentence w)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoAllInternalFormulaCorrect w

example {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateFormula.modeTwoAllInternalRootsCorrectSentence w n)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoAllInternalRootsCorrect w n

example {m} (w n mode depth P a b c e R S q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateFormula.modeTwoAllInternalWholeFormulaExecutionIffSentence w n mode depth P a b c e R S q)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoAllInternalWholeFormulaExecutionIff w n mode depth P a b c e R S q

example {m} (w n mode depth P a b c e R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateFormula.modeTwoAllInternalWholeFormulaProgramIffSentence w n mode depth P a b c e R S h q)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoAllInternalWholeFormulaProgramIff w n mode depth P a b c e R S h q

example {m} (w n mode depth P a b c e R S h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateFormula.modeTwoActualHistoryAgreementDischargedSentence w n mode depth P a b c e R S h)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoActualHistoryAgreementDischarged w n mode depth P a b c e R S h

example {m} (w n mode depth P a b c e R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateFormula.modeTwoAgreedActualHistoryExistsDischargedSentence w n mode depth P a b c e R S)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoAgreedActualHistoryExistsDischarged w n mode depth P a b c e R S

example {m} (w n mode z P b A R S q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateFormula.modeTwoActualRootWholeFormulaExecutionIffSentence w n mode z P b A R S q)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoActualRootWholeFormulaExecutionIff w n mode z P b A R S q

example {m} (w n mode z P b A R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateFormula.modeTwoActualRootWholeFormulaProgramIffSentence w n mode z P b A R S h q)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoActualRootWholeFormulaProgramIff w n mode z P b A R S h q

example {m} (w mode z P b A R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateFormula.modeTwoActualInstantiateTopAtCodesIffSentence w mode z P b A R S n q)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoActualInstantiateTopAtCodesIff w mode z P b A R S n q

example {m} (w mode z P b A n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateFormula.modeTwoActualInstantiateTopIffSentence w mode z P b A n q)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoActualInstantiateTopIff w mode z P b A n q

example {m} (w z P b A n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateFormula.modeTwoActualInstantiateTopSourceTypeSentence w z P b A n q)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoActualInstantiateTopSourceType w z P b A n q

example {m} (w mode z P b A n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectInstantiateFormula.modeTwoActualInstantiateTopGuardedIffSentence w mode z P b A n q)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoActualInstantiateTopGuardedIff w mode z P b A n q
-- Expanded genuine mode2 whole formula endpoint: original ZF discharges every internal formula IH.
example {m} (w n mode depth P a b c e R S q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (((OmegaSyntax.omega w).imp
        ((Internal.InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S).imp
          ((Internal.FormulaCodeSyntax.formulaCode w n a b).imp
            ((Internal.OriginalTransformRowSyntax.run 3 w mode depth P n q).iff
              (Internal.FormulaTransformExecutionSyntax.executed w R S a b c e n q))))).close)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoAllInternalWholeFormulaExecutionIff w n mode depth P a b c e R S q

-- Expanded actual InstantiateTop endpoint: no metadata/frame/history/table-code/IH premises; source type is inside.
example {m} (w mode z P b A n q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (((OmegaSyntax.omega w).imp
        ((Internal.SyntaxNumeralSyntax.numeral 2 mode).imp
          ((OmegaSyntax.empty z).imp
            ((Internal.SyntaxTopEnvironmentSyntax.instantiateInput w z b A P).imp
              (((Internal.FormulaCodeSyntax.formulaCode w n A b).conj (Internal.OriginalTransformRowSyntax.run 3 w mode z P n q)).iff
                (Internal.SyntaxTopFormulaSyntax.instantiated w z b A P n q)))))).close)) :=
  Internal.ObjectInstantiateFormula.native_modeTwoActualInstantiateTopGuardedIff w mode z P b A n q

example {m} (env : Fin 4 → Fin m) (w z A : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalInstantiate.logicalTwentyTwentyThreeAtBoundQueriesIffSentence env w z A)) :=
  Internal.ObjectLogicalInstantiate.native_logicalTwentyTwentyThreeAtBoundQueriesIff env w z A

example {m} (env : Fin 4 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalInstantiate.logicalTwentyTwentyThreeAllQueriesIffSentence env w z)) :=
  Internal.ObjectLogicalInstantiate.native_logicalTwentyTwentyThreeAllQueriesIff env w z

example {m} (universal : Bool) (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalInstantiate.logicalTwentyTwentyThreeAllAssignmentBoundsSentence universal env w row)) :=
  Internal.ObjectLogicalInstantiate.native_logicalTwentyTwentyThreeAllAssignmentBounds universal env w row

example {m} (universal : Bool) (env : Fin 4 → Fin m) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalInstantiate.logicalTwentyTwentyThreeBoundedMatrixIffSentence universal env w z row)) :=
  Internal.ObjectLogicalInstantiate.native_logicalTwentyTwentyThreeBoundedMatrixIff universal env w z row

example {m} (universal : Bool) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalInstantiate.logicalTwentyTwentyThreeWholeNodeIffSentence universal w z row)) :=
  Internal.ObjectLogicalInstantiate.native_logicalTwentyTwentyThreeWholeNodeIff universal w z row

example {m} (universal : Bool) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalInstantiate.logicalTwentyTwentyThreeWholeNormalizedNodeIffSentence universal w z row)) :=
  Internal.ObjectLogicalInstantiate.native_logicalTwentyTwentyThreeWholeNormalizedNodeIff universal w z row

example {m} (env : Fin 6 → Fin m) (w z A : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalInstantiate.logicalTwentyFiveAtBoundQueriesIffSentence env w z A)) :=
  Internal.ObjectLogicalInstantiate.native_logicalTwentyFiveAtBoundQueriesIff env w z A

example {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalInstantiate.logicalTwentyFiveAllQueriesIffSentence env w z)) :=
  Internal.ObjectLogicalInstantiate.native_logicalTwentyFiveAllQueriesIff env w z

example {m} (env : Fin 6 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalInstantiate.logicalTwentyFiveAllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalInstantiate.native_logicalTwentyFiveAllAssignmentBounds env w row

example {m} (env : Fin 6 → Fin m) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalInstantiate.logicalTwentyFiveBoundedMatrixIffSentence env w z row)) :=
  Internal.ObjectLogicalInstantiate.native_logicalTwentyFiveBoundedMatrixIff env w z row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalInstantiate.logicalTwentyFiveWholeNodeIffSentence w z row)) :=
  Internal.ObjectLogicalInstantiate.native_logicalTwentyFiveWholeNodeIff w z row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalInstantiate.logicalTwentyFiveWholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalInstantiate.native_logicalTwentyFiveWholeNormalizedNodeIff w z row

example {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalInstantiate.logicalRule20NestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalInstantiate.native_logicalRule20NestedHeadIff env w row

example {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalInstantiate.logicalRule23NestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalInstantiate.native_logicalRule23NestedHeadIff env w row

example {m} (env : Fin 6 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalInstantiate.logicalRule25NestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalInstantiate.native_logicalRule25NestedHeadIff env w row

-- Expanded complete logical node: only Omega and empty; every assignment and head witness is object-quantified.
example {m} (universal : Bool) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalInstantiateNodeSyntax.node4 universal w row).iff
        (Internal.LogicalInstantiateNodeSyntax.normalized4 universal w z row)))).close)) :=
  Internal.ObjectLogicalInstantiate.native_logicalTwentyTwentyThreeWholeNormalizedNodeIff universal w z row

-- Expanded complete logical node: only Omega and empty; every assignment and head witness is object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalInstantiateNodeSyntax.node6 w row).iff
        (Internal.LogicalInstantiateNodeSyntax.normalized6 w z row)))).close)) :=
  Internal.ObjectLogicalInstantiate.native_logicalTwentyFiveWholeNormalizedNodeIff w z row

example {m} (n : Nat) (isTerm : Bool) (env : Fin (n+1) → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalAllQueriesIffSentence n isTerm env w z)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalAllQueriesIff n isTerm env w z

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule0WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule0WholeNormalizedNodeIff w z row

example {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule0AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule0AllAssignmentBounds env w row

example {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule0NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule0NumericNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule1WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule1WholeNormalizedNodeIff w z row

example {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule1AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule1AllAssignmentBounds env w row

example {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule1NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule1NumericNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule2WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule2WholeNormalizedNodeIff w z row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule2AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule2AllAssignmentBounds env w row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule2NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule2NumericNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule3WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule3WholeNormalizedNodeIff w z row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule3AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule3AllAssignmentBounds env w row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule3NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule3NumericNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule4WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule4WholeNormalizedNodeIff w z row

example {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule4AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule4AllAssignmentBounds env w row

example {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule4NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule4NumericNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule5WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule5WholeNormalizedNodeIff w z row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule5AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule5AllAssignmentBounds env w row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule5NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule5NumericNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule6WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule6WholeNormalizedNodeIff w z row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule6AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule6AllAssignmentBounds env w row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule6NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule6NumericNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule7WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule7WholeNormalizedNodeIff w z row

example {m} (env : Fin 1 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule7AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule7AllAssignmentBounds env w row

example {m} (env : Fin 1 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule7NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule7NumericNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule8WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule8WholeNormalizedNodeIff w z row

example {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule8AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule8AllAssignmentBounds env w row

example {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule8NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule8NumericNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule9WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule9WholeNormalizedNodeIff w z row

example {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule9AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule9AllAssignmentBounds env w row

example {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule9NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule9NumericNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule10WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule10WholeNormalizedNodeIff w z row

example {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule10AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule10AllAssignmentBounds env w row

example {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule10NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule10NumericNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule11WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule11WholeNormalizedNodeIff w z row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule11AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule11AllAssignmentBounds env w row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule11NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule11NumericNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule12WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule12WholeNormalizedNodeIff w z row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule12AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule12AllAssignmentBounds env w row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule12NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule12NumericNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule13WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule13WholeNormalizedNodeIff w z row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule13AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule13AllAssignmentBounds env w row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule13NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule13NumericNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule14WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule14WholeNormalizedNodeIff w z row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule14AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule14AllAssignmentBounds env w row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule14NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule14NumericNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule15WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule15WholeNormalizedNodeIff w z row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule15AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule15AllAssignmentBounds env w row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule15NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule15NumericNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule16WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule16WholeNormalizedNodeIff w z row

example {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule16AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule16AllAssignmentBounds env w row

example {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule16NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule16NumericNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule17WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule17WholeNormalizedNodeIff w z row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule17AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule17AllAssignmentBounds env w row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule17NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule17NumericNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule18WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule18WholeNormalizedNodeIff w z row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule18AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule18AllAssignmentBounds env w row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule18NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule18NumericNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule19WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule19WholeNormalizedNodeIff w z row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule19AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule19AllAssignmentBounds env w row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule19NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule19NumericNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule22WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule22WholeNormalizedNodeIff w z row

example {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule22AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule22AllAssignmentBounds env w row

example {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule22NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule22NumericNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule26WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule26WholeNormalizedNodeIff w z row

example {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule26AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule26AllAssignmentBounds env w row

example {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalStatic.staticLogicalRule26NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule26NumericNestedHeadIff env w row

-- Expanded actual rule0: all assignment and numeric head witnesses are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalStaticNodeSyntax.node 3 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule0.head) w row).iff
        (Internal.LogicalStaticNodeSyntax.normalized 3 false (@Internal.LogicalRule0Head.normalized) w z row)))).close)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule0WholeNormalizedNodeIff w z row

-- Expanded actual rule1: all assignment and numeric head witnesses are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalStaticNodeSyntax.node 1 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule1.head) w row).iff
        (Internal.LogicalStaticNodeSyntax.normalized 1 false (@Internal.LogicalRule1Head.normalized) w z row)))).close)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule1WholeNormalizedNodeIff w z row

-- Expanded actual rule2: all assignment and numeric head witnesses are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule2.head) w row).iff
        (Internal.LogicalStaticNodeSyntax.normalized 2 false (@Internal.LogicalRule2Head.normalized) w z row)))).close)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule2WholeNormalizedNodeIff w z row

-- Expanded actual rule3: all assignment and numeric head witnesses are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule3.head) w row).iff
        (Internal.LogicalStaticNodeSyntax.normalized 2 false (@Internal.LogicalRule3Head.normalized) w z row)))).close)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule3WholeNormalizedNodeIff w z row

-- Expanded actual rule4: all assignment and numeric head witnesses are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalStaticNodeSyntax.node 1 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule4.head) w row).iff
        (Internal.LogicalStaticNodeSyntax.normalized 1 false (@Internal.LogicalRule4Head.normalized) w z row)))).close)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule4WholeNormalizedNodeIff w z row

-- Expanded actual rule5: all assignment and numeric head witnesses are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule5.head) w row).iff
        (Internal.LogicalStaticNodeSyntax.normalized 2 false (@Internal.LogicalRule5Head.normalized) w z row)))).close)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule5WholeNormalizedNodeIff w z row

-- Expanded actual rule6: all assignment and numeric head witnesses are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule6.head) w row).iff
        (Internal.LogicalStaticNodeSyntax.normalized 2 false (@Internal.LogicalRule6Head.normalized) w z row)))).close)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule6WholeNormalizedNodeIff w z row

-- Expanded actual rule7: all assignment and numeric head witnesses are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalStaticNodeSyntax.node 0 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule7.head) w row).iff
        (Internal.LogicalStaticNodeSyntax.normalized 0 false (@Internal.LogicalRule7Head.normalized) w z row)))).close)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule7WholeNormalizedNodeIff w z row

-- Expanded actual rule8: all assignment and numeric head witnesses are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalStaticNodeSyntax.node 1 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule8.head) w row).iff
        (Internal.LogicalStaticNodeSyntax.normalized 1 false (@Internal.LogicalRule8Head.normalized) w z row)))).close)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule8WholeNormalizedNodeIff w z row

-- Expanded actual rule9: all assignment and numeric head witnesses are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalStaticNodeSyntax.node 1 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule9.head) w row).iff
        (Internal.LogicalStaticNodeSyntax.normalized 1 false (@Internal.LogicalRule9Head.normalized) w z row)))).close)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule9WholeNormalizedNodeIff w z row

-- Expanded actual rule10: all assignment and numeric head witnesses are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalStaticNodeSyntax.node 1 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule10.head) w row).iff
        (Internal.LogicalStaticNodeSyntax.normalized 1 false (@Internal.LogicalRule10Head.normalized) w z row)))).close)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule10WholeNormalizedNodeIff w z row

-- Expanded actual rule11: all assignment and numeric head witnesses are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule11.head) w row).iff
        (Internal.LogicalStaticNodeSyntax.normalized 2 false (@Internal.LogicalRule11Head.normalized) w z row)))).close)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule11WholeNormalizedNodeIff w z row

-- Expanded actual rule12: all assignment and numeric head witnesses are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule12.head) w row).iff
        (Internal.LogicalStaticNodeSyntax.normalized 2 false (@Internal.LogicalRule12Head.normalized) w z row)))).close)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule12WholeNormalizedNodeIff w z row

-- Expanded actual rule13: all assignment and numeric head witnesses are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule13.head) w row).iff
        (Internal.LogicalStaticNodeSyntax.normalized 2 false (@Internal.LogicalRule13Head.normalized) w z row)))).close)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule13WholeNormalizedNodeIff w z row

-- Expanded actual rule14: all assignment and numeric head witnesses are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule14.head) w row).iff
        (Internal.LogicalStaticNodeSyntax.normalized 2 false (@Internal.LogicalRule14Head.normalized) w z row)))).close)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule14WholeNormalizedNodeIff w z row

-- Expanded actual rule15: all assignment and numeric head witnesses are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule15.head) w row).iff
        (Internal.LogicalStaticNodeSyntax.normalized 2 false (@Internal.LogicalRule15Head.normalized) w z row)))).close)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule15WholeNormalizedNodeIff w z row

-- Expanded actual rule16: all assignment and numeric head witnesses are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalStaticNodeSyntax.node 3 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule16.head) w row).iff
        (Internal.LogicalStaticNodeSyntax.normalized 3 false (@Internal.LogicalRule16Head.normalized) w z row)))).close)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule16WholeNormalizedNodeIff w z row

-- Expanded actual rule17: all assignment and numeric head witnesses are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule17.head) w row).iff
        (Internal.LogicalStaticNodeSyntax.normalized 2 false (@Internal.LogicalRule17Head.normalized) w z row)))).close)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule17WholeNormalizedNodeIff w z row

-- Expanded actual rule18: all assignment and numeric head witnesses are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule18.head) w row).iff
        (Internal.LogicalStaticNodeSyntax.normalized 2 false (@Internal.LogicalRule18Head.normalized) w z row)))).close)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule18WholeNormalizedNodeIff w z row

-- Expanded actual rule19: all assignment and numeric head witnesses are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule19.head) w row).iff
        (Internal.LogicalStaticNodeSyntax.normalized 2 false (@Internal.LogicalRule19Head.normalized) w z row)))).close)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule19WholeNormalizedNodeIff w z row

-- Expanded actual rule22: all assignment and numeric head witnesses are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalStaticNodeSyntax.node 1 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule22.head) w row).iff
        (Internal.LogicalStaticNodeSyntax.normalized 1 false (@Internal.LogicalRule22Head.normalized) w z row)))).close)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule22WholeNormalizedNodeIff w z row

-- Expanded actual rule26: all assignment and numeric head witnesses are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalStaticNodeSyntax.node 1 true (YesMetaZFC.Automation.ObjectLogicalAxiom.rule26.head) w row).iff
        (Internal.LogicalStaticNodeSyntax.normalized 1 true (@Internal.LogicalRule26Head.normalized) w z row)))).close)) :=
  Internal.ObjectLogicalStatic.native_staticLogicalRule26WholeNormalizedNodeIff w z row

example {m} (env : Fin 5 → Fin m) (w z A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalAbstract.logicalRule21AtSuccessorsQueriesIffSentence env w z A B)) :=
  Internal.ObjectLogicalAbstract.native_logicalRule21AtSuccessorsQueriesIff env w z A B

example {m} (env : Fin 5 → Fin m) (w z A : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalAbstract.logicalRule21AtOneQueriesIffSentence env w z A)) :=
  Internal.ObjectLogicalAbstract.native_logicalRule21AtOneQueriesIff env w z A

example {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalAbstract.logicalRule21AllQueriesIffSentence env w z)) :=
  Internal.ObjectLogicalAbstract.native_logicalRule21AllQueriesIff env w z

example {m} (env : Fin 5 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalAbstract.logicalRule21AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalAbstract.native_logicalRule21AllAssignmentBounds env w row

example {m} (env : Fin 5 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalAbstract.logicalRule21NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalAbstract.native_logicalRule21NumericNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalAbstract.logicalRule21WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalAbstract.native_logicalRule21WholeNormalizedNodeIff w z row

example {m} (env : Fin 4 → Fin m) (w z A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalAbstract.logicalRule24AtSuccessorsQueriesIffSentence env w z A B)) :=
  Internal.ObjectLogicalAbstract.native_logicalRule24AtSuccessorsQueriesIff env w z A B

example {m} (env : Fin 4 → Fin m) (w z A : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalAbstract.logicalRule24AtOneQueriesIffSentence env w z A)) :=
  Internal.ObjectLogicalAbstract.native_logicalRule24AtOneQueriesIff env w z A

example {m} (env : Fin 4 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalAbstract.logicalRule24AllQueriesIffSentence env w z)) :=
  Internal.ObjectLogicalAbstract.native_logicalRule24AllQueriesIff env w z

example {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalAbstract.logicalRule24AllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectLogicalAbstract.native_logicalRule24AllAssignmentBounds env w row

example {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalAbstract.logicalRule24NumericNestedHeadIffSentence env w row)) :=
  Internal.ObjectLogicalAbstract.native_logicalRule24NumericNestedHeadIff env w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalAbstract.logicalRule24WholeNormalizedNodeIffSentence w z row)) :=
  Internal.ObjectLogicalAbstract.native_logicalRule24WholeNormalizedNodeIff w z row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalAbstract.logicalAllTwentySevenWholeNodesIffSentence w z row)) :=
  Internal.ObjectLogicalAbstract.native_logicalAllTwentySevenWholeNodesIff w z row

example {m} (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalAbstract.logicalAllTwentySevenActualShapeTableIffSentence w row)) :=
  Internal.ObjectLogicalAbstract.native_logicalAllTwentySevenActualShapeTableIff w row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectLogicalAbstract.logicalAllTwentySevenActualTableSpecificationIffSentence w z row)) :=
  Internal.ObjectLogicalAbstract.native_logicalAllTwentySevenActualTableSpecificationIff w z row

-- Expanded rule21: both successor witnesses and complete assignments are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalAbstractNodeSyntax.node21 w row).iff (Internal.LogicalAbstractNodeSyntax.normalized21 w z row)))).close)) :=
  Internal.ObjectLogicalAbstract.native_logicalRule21WholeNormalizedNodeIff w z row

-- Expanded rule24: both successor witnesses and complete assignments are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalAbstractNodeSyntax.node24 w row).iff (Internal.LogicalAbstractNodeSyntax.normalized24 w z row)))).close)) :=
  Internal.ObjectLogicalAbstract.native_logicalRule24WholeNormalizedNodeIff w z row

-- Exact original 27-Shape table, with actual ordered Bool query lists and all assignment blocks.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.LogicalOriginalNodeSyntax.table w row).iff (Internal.LogicalAllPatterns.specification w z row)))).close)) :=
  Internal.ObjectLogicalAbstract.native_logicalAllTwentySevenActualTableSpecificationIff w z row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofBaseNodes.proofLogicalNumericHeadIffSentence env w row)) :=
  Internal.ObjectProofBaseNodes.native_proofLogicalNumericHeadIff env w row

example {m} (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofBaseNodes.proofLogicalQueryConstructorIffSentence env w)) :=
  Internal.ObjectProofBaseNodes.native_proofLogicalQueryConstructorIff env w

example {m} (env : Fin 3 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofBaseNodes.proofLogicalQueryNormalizedIffSentence env w z)) :=
  Internal.ObjectProofBaseNodes.native_proofLogicalQueryNormalizedIff env w z

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofBaseNodes.proofLogicalAllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectProofBaseNodes.native_proofLogicalAllAssignmentBounds env w row

example {m} (env : Fin 3 → Fin m) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofBaseNodes.proofLogicalBoundedMatrixIffSentence env w z row)) :=
  Internal.ObjectProofBaseNodes.native_proofLogicalBoundedMatrixIff env w z row

example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofBaseNodes.proofLogicalWholeNodeIffSentence w z row)) :=
  Internal.ObjectProofBaseNodes.native_proofLogicalWholeNodeIff w z row

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofBaseNodes.proofTheoryNumericHeadIffSentence env w row)) :=
  Internal.ObjectProofBaseNodes.native_proofTheoryNumericHeadIff env w row

example {m} (env : Fin 3 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofBaseNodes.proofTheoryFormulaQueryIffSentence env w z)) :=
  Internal.ObjectProofBaseNodes.native_proofTheoryFormulaQueryIff env w z

example {m} (test : Source.Formula 1) (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofBaseNodes.proofTheoryParameterizedAxiomQueryIffSentence test env w)) :=
  Internal.ObjectProofBaseNodes.native_proofTheoryParameterizedAxiomQueryIff test env w

example {m} (test : Source.Formula 1) (env : Fin 3 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofBaseNodes.proofTheoryParameterizedAllQueriesIffSentence test env w z)) :=
  Internal.ObjectProofBaseNodes.native_proofTheoryParameterizedAllQueriesIff test env w z

example {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofBaseNodes.proofTheoryAllAssignmentBoundsSentence env w row)) :=
  Internal.ObjectProofBaseNodes.native_proofTheoryAllAssignmentBounds env w row

example {m} (test : Source.Formula 1) (env : Fin 3 → Fin m) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofBaseNodes.proofTheoryParameterizedBoundedMatrixIffSentence test env w z row)) :=
  Internal.ObjectProofBaseNodes.native_proofTheoryParameterizedBoundedMatrixIff test env w z row

example {m} (test : Source.Formula 1) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofBaseNodes.proofTheoryParameterizedWholeNodeIffSentence test w z row)) :=
  Internal.ObjectProofBaseNodes.native_proofTheoryParameterizedWholeNodeIff test w z row

example {m} (test : Source.Formula 1) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofBaseNodes.proofSixRulesParameterizedActualShapeTableIffSentence test w row)) :=
  Internal.ObjectProofBaseNodes.native_proofSixRulesParameterizedActualShapeTableIff test w row

example {m} (test : Source.Formula 1) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofBaseNodes.proofSixRulesParameterizedSelectedNodesIffSentence test w z row)) :=
  Internal.ObjectProofBaseNodes.native_proofSixRulesParameterizedSelectedNodesIff test w z row

example {m} (test : Source.Formula 1) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofBaseNodes.proofSixRulesParameterizedActualTableSpecificationIffSentence test w z row)) :=
  Internal.ObjectProofBaseNodes.native_proofSixRulesParameterizedActualTableSpecificationIff test w z row

-- Expanded logical node: query row and all three assignments are object-quantified.
example {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.ProofLogicalNodeSyntax.node w row).iff (Internal.ProofLogicalNodeSyntax.normalized w z row)))).close)) :=
  Internal.ObjectProofBaseNodes.native_proofLogicalWholeNodeIff w z row

-- Theory test is an explicit object formula schema index; it is not a ZF/U test implementation.
example {m} (test : Source.Formula 1) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.ProofTheoryNodeSyntax.node test w row).iff (Internal.ProofTheoryNodeSyntax.normalized test w z row)))).close)) :=
  Internal.ObjectProofBaseNodes.native_proofTheoryParameterizedWholeNodeIff test w z row

-- Exact six-Shape local table, with all five Kind dispatches and a visible object axiom-test parameter.
example {m} (test : Source.Formula 1) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((OmegaSyntax.omega w).imp ((OmegaSyntax.empty z).imp
      ((Internal.ProofAllNodeSyntax.table test w row).iff (Internal.ProofAllNodeSyntax.specification test w z row)))).close)) :=
  Internal.ObjectProofBaseNodes.native_proofSixRulesParameterizedActualTableSpecificationIff test w z row

example {m} (test : Source.Formula 1) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeTrace.proofTreeAllTraceRootsExistSentence test w)) :=
  Internal.ObjectProofTreeTrace.native_proofTreeAllTraceRootsExist test w

example {m} (test : Source.Formula 1) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeTrace.proofTreeTraceRangeSentence test w r)) :=
  Internal.ObjectProofTreeTrace.native_proofTreeTraceRange test w r

example {m} (test : Source.Formula 1) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeTrace.proofTreeAllRootsMembershipIffSentence test w V r)) :=
  Internal.ObjectProofTreeTrace.native_proofTreeAllRootsMembershipIff test w V r

example {m} (test : Source.Formula 1) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeTrace.proofTreeAllRootsClosedSentence test w V)) :=
  Internal.ObjectProofTreeTrace.native_proofTreeAllRootsClosed test w V

example {m} (test : Source.Formula 1) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeTrace.proofTreeTwelveRuleTracedStepIffSentence test w V r)) :=
  Internal.ObjectProofTreeTrace.native_proofTreeTwelveRuleTracedStepIff test w V r

example {m} (test : Source.Formula 1) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeTrace.proofTreeFullRecursiveTraceIffSentence test w r)) :=
  Internal.ObjectProofTreeTrace.native_proofTreeFullRecursiveTraceIff test w r

example {m} (test : Source.Formula 1) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeTrace.proofTreeNodeEntryRecursiveIffSentence test w code)) :=
  Internal.ObjectProofTreeTrace.native_proofTreeNodeEntryRecursiveIff test w code

example {m} (test : Source.Formula 1) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeTrace.proofTreeRootEntryRecursiveIffSentence test w code conclusion)) :=
  Internal.ObjectProofTreeTrace.native_proofTreeRootEntryRecursiveIff test w code conclusion

example {m} (kind : Fin 6) (isRoot : Bool) (env : Fin ((ProofTreeBranchConstruction.shape kind).extra+2) → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeTrace.proofTreeTwelveBranchAllAssignmentBoundsSentence kind isRoot env w r)) :=
  Internal.ObjectProofTreeTrace.native_proofTreeTwelveBranchAllAssignmentBounds kind isRoot env w r

example {m} (test : Source.Formula 1) (kind : Fin 6) (isRoot : Bool) (env : Fin ((ProofTreeBranchConstruction.shape kind).extra+2) → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeTrace.proofTreeTwelveBranchTraceCompositionSentence test kind isRoot env w r)) :=
  Internal.ObjectProofTreeTrace.native_proofTreeTwelveBranchTraceComposition test kind isRoot env w r

-- Full internal closed-trace equation: no assumed trace set, IH, model or external finite proof.
example {m} (test : Source.Formula 1) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((Internal.ProofTreeTraceSyntax.condition test w r).iff
      (Internal.ProofTreeTraceEquation.equation test w r)).close)) :=
  Internal.ObjectProofTreeTrace.native_proofTreeFullRecursiveTraceIff test w r

-- Actual root row links code and candidate conclusion; rank correctness and root closedness remain separate goals.
example {m} (test : Source.Formula 1) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((Internal.ProofTreeEntrySyntax.root test w code conclusion).iff
      (Internal.ProofTreeEntrySyntax.rootEquation test w code conclusion)).close)) :=
  Internal.ObjectProofTreeTrace.native_proofTreeRootEntryRecursiveIff test w code conclusion

example {m} (x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeRoot.proofRootOneNonemptySentence x)) :=
  Internal.ObjectProofTreeRoot.native_proofRootOneNonempty x

example {m} (u x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeRoot.proofRootOneMembershipSentence u x)) :=
  Internal.ObjectProofTreeRoot.native_proofRootOneMembership u x

example {m} {a} (i : Fin a) (env : Fin a → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeRoot.proofRootZeroGuardIffSentence i env w)) :=
  Internal.ObjectProofTreeRoot.native_proofRootZeroGuardIff i env w

example {m} (s : YesMetaZFC.Automation.ObjectProofTree.Shape) (env : Fin (s.extra+2) → Fin m) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeRoot.proofRootPayloadConstructorIffSentence s env w code)) :=
  Internal.ObjectProofTreeRoot.native_proofRootPayloadConstructorIff s env w code

example {m} (test : Source.Formula 1) (w code conclusion r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeRoot.proofRootActualLocalConditionSentence test w code conclusion r)) :=
  Internal.ObjectProofTreeRoot.native_proofRootActualLocalCondition test w code conclusion r

example {m} (test : Source.Formula 1) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeRoot.proofRootClosedFieldsForwardSentence test w code conclusion)) :=
  Internal.ObjectProofTreeRoot.native_proofRootClosedFieldsForward test w code conclusion

example {m} (test : Source.Formula 1) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeRoot.proofRootClosedFieldsBackwardSentence test w code conclusion)) :=
  Internal.ObjectProofTreeRoot.native_proofRootClosedFieldsBackward test w code conclusion

example {m} (test : Source.Formula 1) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeRoot.proofRootExactClosedFieldsIffSentence test w code conclusion)) :=
  Internal.ObjectProofTreeRoot.native_proofRootExactClosedFieldsIff test w code conclusion

-- Full internal root contract: the only object premise is Omega.
example {m} (test : Source.Formula 1) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((omega w).imp ((Internal.ProofTreeEntrySyntax.root test w code conclusion).iff
      ((Internal.ProofTreeEntrySyntax.node test w code).conj (Internal.ProofTreeRootSyntax.closedPayload w code conclusion)))).close)) :=
  Internal.ObjectProofTreeRoot.native_proofRootExactClosedFieldsIff test w code conclusion

example {m} (test : Source.Formula 1) (w row code z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeNode.proofNodeFieldLocalIffSentence test w row code z)) :=
  Internal.ObjectProofTreeNode.native_proofNodeFieldLocalIff test w row code z

example {m} (test : Source.Formula 1) (w row code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeNode.proofNodeActualTagLocalIffSentence test w row code)) :=
  Internal.ObjectProofTreeNode.native_proofNodeActualTagLocalIff test w row code

example {m} (test : Source.Formula 1) {a} (i : Fin a) (env : Fin a → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeNode.proofNodeVariableChildIffSentence test i env w)) :=
  Internal.ObjectProofTreeNode.native_proofNodeVariableChildIff test i env w

example {m} (test : Source.Formula 1) {a} (is : List (Fin a)) (env : Fin a → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeNode.proofNodeAllChildrenIffSentence test is env w)) :=
  Internal.ObjectProofTreeNode.native_proofNodeAllChildrenIff test is env w

example {m} (kind : Fin 6) (env : Fin ((ProofTreeBranchConstruction.shape kind).extra+2) → Fin m) (i : Fin ((ProofTreeBranchConstruction.shape kind).extra+2)) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeNode.proofNodePayloadFieldBelowSentence kind env i w code)) :=
  Internal.ObjectProofTreeNode.native_proofNodePayloadFieldBelow kind env i w code

example {m} (test : Source.Formula 1) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeNode.proofNodeSixCasesForwardSentence test w code)) :=
  Internal.ObjectProofTreeNode.native_proofNodeSixCasesForward test w code

example {m} (test : Source.Formula 1) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeNode.proofNodeSixCasesBackwardSentence test w code)) :=
  Internal.ObjectProofTreeNode.native_proofNodeSixCasesBackward test w code

example {m} (test : Source.Formula 1) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeNode.proofNodeExactSixCasesIffSentence test w code)) :=
  Internal.ObjectProofTreeNode.native_proofNodeExactSixCasesIff test w code

example {m} (test : Source.Formula 1) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeNode.proofRootExactNodeSixCasesIffSentence test w code conclusion)) :=
  Internal.ObjectProofTreeNode.native_proofRootExactNodeSixCasesIff test w code conclusion

-- All actual node branches, with local table and original children; only Omega is assumed.
example {m} (test : Source.Formula 1) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((omega w).imp ((Internal.ProofTreeEntrySyntax.node test w code).iff
      ((Internal.ProofAllNodeSyntax.table test w code).conj (Internal.ProofTreeNodeSyntax.payloadCases test w code)))).close)) :=
  Internal.ObjectProofTreeNode.native_proofNodeExactSixCasesIff test w code

example {m} (test : Source.Formula 1) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((omega w).imp ((Internal.ProofTreeEntrySyntax.root test w code conclusion).iff
      (((Internal.ProofAllNodeSyntax.table test w code).conj (Internal.ProofTreeNodeSyntax.payloadCases test w code)).conj
        (Internal.ProofTreeRootSyntax.closedPayload w code conclusion)))).close)) :=
  Internal.ObjectProofTreeNode.native_proofRootExactNodeSixCasesIff test w code conclusion

example {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeInduction.proofTreePropertyStepWithMemberIHSentence test P w code)) :=
  Internal.ObjectProofTreeInduction.native_proofTreePropertyStepWithMemberIH test P w code

example {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeInduction.proofTreePropertyProgressiveSentence test P w)) :=
  Internal.ObjectProofTreeInduction.native_proofTreePropertyProgressive test P w

example {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeInduction.proofTreeInternalInductionSentence test P w)) :=
  Internal.ObjectProofTreeInduction.native_proofTreeInternalInduction test P w

example {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeInduction.proofTreePointInductionSentence test P w code)) :=
  Internal.ObjectProofTreeInduction.native_proofTreePointInduction test P w code

example {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeInduction.proofTreeRootPropertySentence test P w code conclusion)) :=
  Internal.ObjectProofTreeInduction.native_proofTreeRootProperty test P w code conclusion

example {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeInduction.proofTreeRejectNodeFromPropertySentence test P w code)) :=
  Internal.ObjectProofTreeInduction.native_proofTreeRejectNodeFromProperty test P w code

example {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeInduction.proofTreeRejectRootFromPropertySentence test P w code conclusion)) :=
  Internal.ObjectProofTreeInduction.native_proofTreeRejectRootFromProperty test P w code conclusion

-- Foundation removes the internal member IH; the object local-closure hypothesis stays explicit.
example {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((omega w).imp ((Internal.ProofTreeInductionSyntax.closure test P w).imp
      (Source.Formula.all ((Internal.ProofTreeEntrySyntax.node test w.castSucc (Fin.last m)).imp
        (Internal.ProofTreeInductionSyntax.property P w.castSucc (Fin.last m)))))).close)) :=
  Internal.ObjectProofTreeInduction.native_proofTreeInternalInduction test P w

example {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((omega w).imp ((Internal.ProofTreeInductionSyntax.closure test P w).imp
      ((Internal.ProofTreeEntrySyntax.node test w code).imp (Internal.ProofTreeInductionSyntax.property P w code)))).close)) :=
  Internal.ObjectProofTreeInduction.native_proofTreePointInduction test P w code

example {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeEquation.proofTreeEquationImpliesLocalClosureSentence test P w)) :=
  Internal.ObjectProofTreeEquation.native_proofTreeEquationImpliesLocalClosure test P w

example {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeEquation.proofTreeEquationReverseProgressiveSentence test P w)) :=
  Internal.ObjectProofTreeEquation.native_proofTreeEquationReverseProgressive test P w

example {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeEquation.proofTreeEquationAllCodeUniqueSentence test P w)) :=
  Internal.ObjectProofTreeEquation.native_proofTreeEquationAllCodeUnique test P w

example {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeEquation.proofTreeEquationPointUniqueSentence test P w code)) :=
  Internal.ObjectProofTreeEquation.native_proofTreeEquationPointUnique test P w code

example {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeEquation.proofTreeEquationRootUniqueSentence test P w code conclusion)) :=
  Internal.ObjectProofTreeEquation.native_proofTreeEquationRootUnique test P w code conclusion

example {m} (test : Source.Formula 1) (P Q : Source.Formula 2) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeEquation.proofTreeEquationTwoSolutionsSentence test P Q w code)) :=
  Internal.ObjectProofTreeEquation.native_proofTreeEquationTwoSolutions test P Q w code

example {m} (test : Source.Formula 1) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeEquation.proofTreeEquationNodeNaturalSentence test w code)) :=
  Internal.ObjectProofTreeEquation.native_proofTreeEquationNodeNatural test w code

example {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeEquation.proofTreeEquationSolutionNaturalSentence test P w code)) :=
  Internal.ObjectProofTreeEquation.native_proofTreeEquationSolutionNatural test P w code

example {m} (test : Source.Formula 1) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProofTreeEquation.proofTreeCanonicalNodeEquationSentence test w)) :=
  Internal.ObjectProofTreeEquation.native_proofTreeCanonicalNodeEquation test w

-- Uniqueness over all object codes, with the candidate equation explicitly inside the sentence.
example {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((omega w).imp ((Internal.ProofTreeEquationSyntax.equation test P w).imp
      (Source.Formula.all ((Internal.ProofTreeEntrySyntax.node test w.castSucc (Fin.last m)).iff
        (Internal.ProofTreeInductionSyntax.property P w.castSucc (Fin.last m)))))).close)) :=
  Internal.ObjectProofTreeEquation.native_proofTreeEquationAllCodeUnique test P w

-- The original Node template satisfies the actual six-case equation; no equation is assumed here.
example {m} (test : Source.Formula 1) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((omega w).imp (Source.Formula.all
      ((Internal.ProofTreeInductionSyntax.property (Internal.ProofTreeEquationCanonical.nodeTemplate test) w.castSucc (Fin.last m)).iff
        (Internal.ProofTreeInductionSyntax.normalized test (Internal.ProofTreeEquationCanonical.nodeTemplate test) w.castSucc (Fin.last m))))).close)) :=
  Internal.ObjectProofTreeEquation.native_proofTreeCanonicalNodeEquation test w

example {m} (tag : Nat) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFixedAxiomTest.fixedPacketExistsSentence tag w)) :=
  Internal.ObjectFixedAxiomTest.native_fixedPacketExists tag w

example {m} (tag : Nat) (w p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFixedAxiomTest.fixedPacketNaturalSentence tag w p)) :=
  Internal.ObjectFixedAxiomTest.native_fixedPacketNatural tag w p

example {m} (tag : Nat) (w p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFixedAxiomTest.fixedPacketUniqueSentence tag w p q)) :=
  Internal.ObjectFixedAxiomTest.native_fixedPacketUnique tag w p q

example {m} (k l : Nat) (hkl : k ≠ l) (w p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFixedAxiomTest.fixedPacketTagsDisjointSentence k l hkl w p)) :=
  Internal.ObjectFixedAxiomTest.native_fixedPacketTagsDisjoint k l hkl w p

example {m} (tag : Nat) (w p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFixedAxiomTest.fixedPacketAtValueSentence tag w p q)) :=
  Internal.ObjectFixedAxiomTest.native_fixedPacketAtValue tag w p q

example {m} (target : Bool) (kind : Fin 10) (hk : kind ∈ FixedAxiomTableSyntax.kinds target) (w c f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFixedAxiomTest.fixedAxiomTableAtPacketSentence target kind hk w c f)) :=
  Internal.ObjectFixedAxiomTest.native_fixedAxiomTableAtPacket target kind hk w c f

example {m} (target : Bool) (w row c f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFixedAxiomTest.fixedAxiomRowAtConstructorSentence target w row c f)) :=
  Internal.ObjectFixedAxiomTest.native_fixedAxiomRowAtConstructor target w row c f

example {m} (target : Bool) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFixedAxiomTest.fixedAxiomTestAtOmegaSentence target w row)) :=
  Internal.ObjectFixedAxiomTest.native_fixedAxiomTestAtOmega target w row

example {m} (target : Bool) (kind : Fin 10) (hk : kind ∈ FixedAxiomTableSyntax.kinds target) (w row c f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFixedAxiomTest.fixedAxiomTestAtPacketRowSentence target kind hk w row c f)) :=
  Internal.ObjectFixedAxiomTest.native_fixedAxiomTestAtPacketRow target kind hk w row c f

example {m} (target : Bool) (w row c f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFixedAxiomTest.fixedAxiomChoicePacketRejectedSentence target w row c f)) :=
  Internal.ObjectFixedAxiomTest.native_fixedAxiomChoicePacketRejected target w row c f

example {m} (target : Bool) (kind : Fin 10) (hk : kind ∈ FixedAxiomTableSyntax.kinds target) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectFixedAxiomTest.fixedAxiomAcceptedWitnessExistsSentence target kind hk w)) :=
  Internal.ObjectFixedAxiomTest.native_fixedAxiomAcceptedWitnessExists target kind hk w

-- Expanded fixed-test contract, with the actual row and packet premises retained.
example {m} (target : Bool) (kind : Fin 10) (hk : kind ∈ Internal.FixedAxiomTableSyntax.kinds target)
    (w row c f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((omega w).imp
      ((Internal.SyntaxNodeSyntax.constructor 2 0 w (Source.SetLanguage.args2 c f) row).imp
        ((Internal.FixedAxiomPacketSyntax.leaf (Internal.NativeAxiomCertificateData.fixedTag kind) w c).imp
          ((Internal.AxiomTestSyntax.holds (Internal.FixedAxiomTableSyntax.test target) row).iff
            (Internal.PureQuotationSyntax.formula (Internal.NativeAxiomCertificateData.fixedFormula kind) w f))))).close)) :=
  Internal.ObjectFixedAxiomTest.native_fixedAxiomTestAtPacketRow target kind hk w row c f

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((omega w).imp (Internal.FixedAxiomTableExistence.existsTest true w)).close)) :=
  Internal.ObjectFixedAxiomTest.native_fixedAxiomAcceptedWitnessExists true 0 (by decide) w

example {m} (tag : Nat) (w a n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallClosure.unaryIterationExistsUniqueSentence tag w a n)) :=
  Internal.ObjectForallClosure.native_unaryIterationExistsUnique tag w a n

example {m} (tag : Nat) (w a n y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallClosure.unaryIterationNaturalRangeSentence tag w a n y)) :=
  Internal.ObjectForallClosure.native_unaryIterationNaturalRange tag w a n y

example {m} (tag : Nat) (w a n y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallClosure.unaryIterationUniqueSentence tag w a n y z)) :=
  Internal.ObjectForallClosure.native_unaryIterationUnique tag w a n y z

example {m} (tag : Nat) (w a z y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallClosure.unaryIterationZeroIffSentence tag w a z y)) :=
  Internal.ObjectForallClosure.native_unaryIterationZeroIff tag w a z y

example {m} (tag : Nat) (w a n s y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallClosure.unaryIterationSuccessorIffSentence tag w a n s y z)) :=
  Internal.ObjectForallClosure.native_unaryIterationSuccessorIff tag w a n s y z

example {m} (tag : Nat) (w a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallClosure.unaryIterationAllInternalCountsSentence tag w a)) :=
  Internal.ObjectForallClosure.native_unaryIterationAllInternalCounts tag w a

example {m} (w a source f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallClosure.forallClosureUniformTypingSentence w a source f)) :=
  Internal.ObjectForallClosure.native_forallClosureUniformTyping w a source f

example {m} (w a source f n b y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallClosure.forallClosureTypingIffSentence w a source f n b y)) :=
  Internal.ObjectForallClosure.native_forallClosureTypingIff w a source f n b y

example {m} (w a n z y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallClosure.forallClosureClosedIffSentence w a n z y)) :=
  Internal.ObjectForallClosure.native_forallClosureClosedIff w a n z y

example {m} (w a n z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallClosure.forallClosureClosedExistsUniqueSentence w a n z)) :=
  Internal.ObjectForallClosure.native_forallClosureClosedExistsUnique w a n z

example {m} (w a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectForallClosure.forallClosureAllInternalCountsSentence w a)) :=
  Internal.ObjectForallClosure.native_forallClosureAllInternalCounts w a

-- The iteration count is an object-quantified omega element.
example {m} (w a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((omega w).imp ((Source.Formula.mem a w).imp (Source.Formula.all ((Source.Formula.mem (Fin.last m) w.castSucc).imp (Internal.SyntaxUnaryIterationSyntax.fiber 9 w.castSucc a.castSucc (Fin.last m)))))).close)) :=
  Internal.ObjectForallClosure.native_forallClosureAllInternalCounts w a

-- Input typing supplies count/input naturality; all closed-output witnesses are internal.
example {m} (w a n z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((omega w).imp ((empty z).imp
      ((Internal.FormulaCodeSyntax.formulaCode w a n z).imp (Internal.SyntaxForallClosureOutput.fiber w a n z)))).close)) :=
  Internal.ObjectForallClosure.native_forallClosureClosedExistsUnique w a n z

example {m} (w n b c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSchemaIndex.doubleShiftExistsSentence w n b c)) :=
  Internal.ObjectSchemaIndex.native_doubleShiftExists w n b c

example {m} (w n b c g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSchemaIndex.doubleShiftMapSentence w n b c g)) :=
  Internal.ObjectSchemaIndex.native_doubleShiftMap w n b c g

example {m} (w n b c g i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSchemaIndex.doubleShiftEdgesIffSentence w n b c g i j)) :=
  Internal.ObjectSchemaIndex.native_doubleShiftEdgesIff w n b c g i j

example {m} (w n b c g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSchemaIndex.doubleShiftUniqueSentence w n b c g h)) :=
  Internal.ObjectSchemaIndex.native_doubleShiftUnique w n b c g h

example {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSchemaIndex.schemaIndexGraphExistsSentence site scopes w n)) :=
  Internal.ObjectSchemaIndex.native_schemaIndexGraphExists site scopes w n

example {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w n g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSchemaIndex.schemaIndexMapSentence site scopes w n g)) :=
  Internal.ObjectSchemaIndex.native_schemaIndexMap site scopes w n g

example {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w n g z y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSchemaIndex.schemaIndexZeroIffSentence site scopes w n g z y)) :=
  Internal.ObjectSchemaIndex.native_schemaIndexZeroIff site scopes w n g z y

example {m} (image : Bool) (scopes : Fin 4 → Fin m) (w n g p y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSchemaIndex.schemaCollectionOneIffSentence image scopes w n g p y)) :=
  Internal.ObjectSchemaIndex.native_schemaCollectionOneIff image scopes w n g p y

example {m} (scopes : Fin 4 → Fin m) (w n g i I j J : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSchemaIndex.schemaSeparationTailIffSentence scopes w n g i I j J)) :=
  Internal.ObjectSchemaIndex.native_schemaSeparationTailIff scopes w n g i I j J

example {m} (image : Bool) (scopes : Fin 4 → Fin m) (w n g i u I j v J : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSchemaIndex.schemaCollectionTailIffSentence image scopes w n g i u I j v J)) :=
  Internal.ObjectSchemaIndex.native_schemaCollectionTailIff image scopes w n g i u I j v J

example {m} (site : Fin 3) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSchemaIndex.schemaIndexStateExistsSentence site w n)) :=
  Internal.ObjectSchemaIndex.native_schemaIndexStateExists site w n

example {m} (site : Fin 3) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSchemaIndex.schemaIndexCodeExistsSentence site w n)) :=
  Internal.ObjectSchemaIndex.native_schemaIndexCodeExists site w n

example {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w g R S z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSchemaIndex.schemaIndexRenameLawSentence site scopes w g R S z)) :=
  Internal.ObjectSchemaIndex.native_schemaIndexRenameLaw site scopes w g R S z

example {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w R S z a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSchemaIndex.schemaIndexRenameAtSentence site scopes w R S z a)) :=
  Internal.ObjectSchemaIndex.native_schemaIndexRenameAt site scopes w R S z a

example {m} (site : Fin 3) (w n z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectSchemaIndex.schemaIndexSystemExistsSentence site w n z)) :=
  Internal.ObjectSchemaIndex.native_schemaIndexSystemExists site w n z
-- Only object omega/count/zero premises; all scopes and code tables are existential.
example {m} (site : Fin 3) (w n z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((omega w).imp ((Source.Formula.mem n w).imp ((empty z).imp
      (Internal.SchemaIndexRenameSystem.existsSystem site w n z)))).close)) :=
  Internal.ObjectSchemaIndex.native_schemaIndexSystemExists site w n z

example {m} (w x y q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectAtomic.projectBoundShiftUniqueSentence w x y q)) :=
  Internal.ObjectProjectAtomic.native_projectBoundShiftUnique w x y q

example {m} (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectAtomic.projectBoundShiftRangeSentence w x y)) :=
  Internal.ObjectProjectAtomic.native_projectBoundShiftRange w x y

example {m} (w b B f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectAtomic.projectBoundShiftTargetTypeSentence w b B f x y)) :=
  Internal.ObjectProjectAtomic.native_projectBoundShiftTargetType w b B f x y

example {m} (w b x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectAtomic.projectBoundShiftExistsSentence w b x)) :=
  Internal.ObjectProjectAtomic.native_projectBoundShiftExists w b x

example {m} (w b x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectAtomic.projectBoundShiftExistsUniqueSentence w b x)) :=
  Internal.ObjectProjectAtomic.native_projectBoundShiftExistsUnique w b x

example {m} (w b z x y q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectAtomic.projectSubsetUniqueSentence w b z x y q r)) :=
  Internal.ObjectProjectAtomic.native_projectSubsetUnique w b z x y q r

example {m} (w b z x y q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectAtomic.projectSubsetTargetTypeSentence w b z x y q)) :=
  Internal.ObjectProjectAtomic.native_projectSubsetTargetType w b z x y q

example {m} (w b z x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectAtomic.projectSubsetExistsSentence w b z x y)) :=
  Internal.ObjectProjectAtomic.native_projectSubsetExists w b z x y

example {m} (w b z x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectAtomic.projectSubsetTypedUniqueSentence w b z x y)) :=
  Internal.ObjectProjectAtomic.native_projectSubsetTypedUnique w b z x y

example {m} (kind : Fin 3) (w b z x y q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectAtomic.projectAtomicResultUniqueSentence kind w b z x y q r)) :=
  Internal.ObjectProjectAtomic.native_projectAtomicResultUnique kind w b z x y q r

example {m} (kind : Fin 3) (w b z x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectAtomic.projectAtomicCompiledTypeSentence kind w b z x y n q)) :=
  Internal.ObjectProjectAtomic.native_projectAtomicCompiledType kind w b z x y n q

example {m} (kind : Fin 3) (w b z x y n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectAtomic.projectAtomicCompiledUniqueSentence kind w b z x y n q r)) :=
  Internal.ObjectProjectAtomic.native_projectAtomicCompiledUnique kind w b z x y n q r

example {m} (w b z x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectAtomic.projectEqualitySameCodeSentence w b z x y n q)) :=
  Internal.ObjectProjectAtomic.native_projectEqualitySameCode w b z x y n q

example {m} (kind : Fin 3) (w b z x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectAtomic.projectAtomicTypedUniqueSentence kind w b z x y n)) :=
  Internal.ObjectProjectAtomic.native_projectAtomicTypedUnique kind w b z x y n

example {m} (kind : Fin 3) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectAtomic.projectAtomicAllInternalInputsSentence kind w z)) :=
  Internal.ObjectProjectAtomic.native_projectAtomicAllInternalInputs kind w z
-- Bound/scope/term/input-code variables all vary under object ALL4.
example {m} (kind : Fin 3) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((omega w).imp ((empty z).imp
      (Internal.ProjectAtomicExistence.allInputs kind w z))).close)) :=
  Internal.ObjectProjectAtomic.native_projectAtomicAllInternalInputs kind w z

example {m} (w c n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectSourceCode.projectSourceStateExistsSentence w c n h)) :=
  Internal.ObjectProjectSourceCode.native_projectSourceStateExists w c n h

example {m} (w c n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectSourceCode.projectSourceStateUniqueFiberSentence w c n h)) :=
  Internal.ObjectProjectSourceCode.native_projectSourceStateUniqueFiber w c n h

example {m} (w a c n h v b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectSourceCode.projectSourceStateEdgesIffSentence w a c n h v b f)) :=
  Internal.ObjectProjectSourceCode.native_projectSourceStateEdgesIff w a c n h v b f

example {m} (w c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectSourceCode.projectSourceRecursorsSentence w c)) :=
  Internal.ObjectProjectSourceCode.native_projectSourceRecursors w c

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectSourceCode.projectSourceActualCarrierRecursorsSentence w)) :=
  Internal.ObjectProjectSourceCode.native_projectSourceActualCarrierRecursors w

example {m} (w c n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectSourceCode.projectSourceNaturalEvaluationExistsSentence w c n)) :=
  Internal.ObjectProjectSourceCode.native_projectSourceNaturalEvaluationExists w c n

example {m} (w c n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectSourceCode.projectSourceEvaluationUniqueFiberSentence w c n)) :=
  Internal.ObjectProjectSourceCode.native_projectSourceEvaluationUniqueFiber w c n

example {m} (w a c n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectSourceCode.projectSourceTypedRecursiveIffSentence w a c n b f)) :=
  Internal.ObjectProjectSourceCode.native_projectSourceTypedRecursiveIff w a c n b f

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectSourceCode.projectSourceCodeCarrierExistsSentence w)) :=
  Internal.ObjectProjectSourceCode.native_projectSourceCodeCarrierExists w

example {m} (w a c n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectSourceCode.projectSourceCodeAtCarrierIffSentence w a c n b f)) :=
  Internal.ObjectProjectSourceCode.native_projectSourceCodeAtCarrierIff w a c n b f

example {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectSourceCode.projectSourceCodeGuardsSentence w n b f)) :=
  Internal.ObjectProjectSourceCode.native_projectSourceCodeGuards w n b f

example {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectSourceCode.projectSourceNonNaturalCodeRejectedSentence w n b f)) :=
  Internal.ObjectProjectSourceCode.native_projectSourceNonNaturalCodeRejected w n b f

example {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectSourceCode.projectSourceInvalidContextRejectedSentence w n b f)) :=
  Internal.ObjectProjectSourceCode.native_projectSourceInvalidContextRejected w n b f

example {m} (w v n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectSourceCode.projectSourceCodeOmegaIndependentSentence w v n b f)) :=
  Internal.ObjectProjectSourceCode.native_projectSourceCodeOmegaIndependent w v n b f

example {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectSourceCode.projectSourceCodeRecursiveIffSentence w n b f)) :=
  Internal.ObjectProjectSourceCode.native_projectSourceCodeRecursiveIff w n b f

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectSourceCode.projectSourceAllInternalRecursiveLawSentence w)) :=
  Internal.ObjectProjectSourceCode.native_projectSourceAllInternalRecursiveLaw w
-- An object ALL3 law; no external AST/standardness or carrier premise remains.
example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((omega w).imp (Source.Formula.all (Source.Formula.all (Source.Formula.all
      ((Internal.ProjectSourceCodeSyntax.sourceCode w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc
        (Fin.last (m+1)).castSucc (Fin.last (m+2))).iff
        (Internal.ProjectSourceCodeRecursiveSyntax.criterion w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc
        (Fin.last (m+1)).castSucc (Fin.last (m+2)))))))).close)) :=
  Internal.ObjectProjectSourceCode.native_projectSourceAllInternalRecursiveLaw w

example {m} (w c n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompiler.compilerStateExistsSentence w c n h)) :=
  Internal.ObjectProjectCompiler.native_compilerStateExists w c n h

example {m} (w c n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompiler.compilerStateUniqueFiberSentence w c n h)) :=
  Internal.ObjectProjectCompiler.native_compilerStateUniqueFiber w c n h

example {m} (w a c n h v b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompiler.compilerStateEdgesIffSentence w a c n h v b q)) :=
  Internal.ObjectProjectCompiler.native_compilerStateEdgesIff w a c n h v b q

example {m} (w c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompiler.compilerAllRecursorsSentence w c)) :=
  Internal.ObjectProjectCompiler.native_compilerAllRecursors w c

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompiler.compilerActualCarrierRecursorsSentence w)) :=
  Internal.ObjectProjectCompiler.native_compilerActualCarrierRecursors w

example {m} (w c n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompiler.compilerNaturalEvaluationExistsSentence w c n)) :=
  Internal.ObjectProjectCompiler.native_compilerNaturalEvaluationExists w c n

example {m} (w c n y u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompiler.compilerEvaluationStateUniqueSentence w c n y u)) :=
  Internal.ObjectProjectCompiler.native_compilerEvaluationStateUnique w c n y u

example {m} (w n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompiler.compilerProducedOutputRootCertificateSentence w n b q)) :=
  Internal.ObjectProjectCompiler.native_compilerProducedOutputRootCertificate w n b q

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompiler.compilerCarrierExistsSentence w)) :=
  Internal.ObjectProjectCompiler.native_compilerCarrierExists w

example {m} (w a c n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompiler.compilerAtActualCarrierIffSentence w a c n b q)) :=
  Internal.ObjectProjectCompiler.native_compilerAtActualCarrierIff w a c n b q

example {m} (w n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompiler.compilerNaturalGuardsSentence w n b q)) :=
  Internal.ObjectProjectCompiler.native_compilerNaturalGuards w n b q

example {m} (w n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompiler.compilerNonNaturalInputRejectedSentence w n b q)) :=
  Internal.ObjectProjectCompiler.native_compilerNonNaturalInputRejected w n b q

example {m} (w n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompiler.compilerInvalidCoordinatesRejectedSentence w n b q)) :=
  Internal.ObjectProjectCompiler.native_compilerInvalidCoordinatesRejected w n b q

example {m} (w v n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompiler.compilerOmegaIndependentSentence w v n b q)) :=
  Internal.ObjectProjectCompiler.native_compilerOmegaIndependent w v n b q

example {m} (truth : Bool) (w n b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompiler.compilerConstantsActuallyProducedSentence truth w n b)) :=
  Internal.ObjectProjectCompiler.native_compilerConstantsActuallyProduced truth w n b

example {m} (kind : Fin 3) (w b z x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompiler.compilerThreeAtomsActuallyProducedSentence kind w b z x y n q)) :=
  Internal.ObjectProjectCompiler.native_compilerThreeAtomsActuallyProduced kind w b z x y n q

example {m} (kind : Fin 3) (w b z x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompiler.compilerThreeAtomsTypedOutputExistsSentence kind w b z x y n)) :=
  Internal.ObjectProjectCompiler.native_compilerThreeAtomsTypedOutputExists kind w b z x y n

example {m} (w n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompiler.compilerHistoryIndependentActualOutputSentence w n b q)) :=
  Internal.ObjectProjectCompiler.native_compilerHistoryIndependentActualOutput w n b q

example {m} (w c n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompiler.compilerEvaluationStateUniqueFiberSentence w c n)) :=
  Internal.ObjectProjectCompiler.native_compilerEvaluationStateUniqueFiber w c n

example {m} (w c n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompiler.compilerActualHistoryFromValueSentence w c n v)) :=
  Internal.ObjectProjectCompiler.native_compilerActualHistoryFromValue w c n v
-- Atomic witnesses belong to the actual recursive compiler and have target FormulaCode.
example {m} (kind : Fin 3) (w b z x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (((omega w).imp ((empty z).imp
      ((Internal.ProjectAtomicSyntax.sourceAt kind w b x y n).imp
        (Internal.ProjectCompilerBase.existsTyped w n b z)))).close)) :=
  Internal.ObjectProjectCompiler.native_compilerThreeAtomsTypedOutputExists kind w b z x y n

example {m} (w a c h n x b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerRecursive.compilerActualChildReadIffSentence w a c h n x b q)) :=
  Internal.ObjectProjectCompilerRecursive.native_compilerActualChildReadIff w a c h n x b q

example {m} (w a c h n x b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerRecursive.compilerGuardedChildQueryIffSentence w a c h n x b q)) :=
  Internal.ObjectProjectCompilerRecursive.native_compilerGuardedChildQueryIff w a c h n x b q

example {m} (w a c h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerRecursive.compilerAllInternalChildQueriesSentence w a c h n)) :=
  Internal.ObjectProjectCompilerRecursive.native_compilerAllInternalChildQueries w a c h n

example {m} (w a c h n x b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerRecursive.compilerSuccessorQueryIffSentence w a c h n x b q)) :=
  Internal.ObjectProjectCompilerRecursive.native_compilerSuccessorQueryIff w a c h n x b q

example {m} (advance : Bool) (w a c h n x b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerRecursive.compilerScopedChildQueryIffSentence advance w a c h n x b q)) :=
  Internal.ObjectProjectCompilerRecursive.native_compilerScopedChildQueryIff advance w a c h n x b q

example {m} (w a c h n b z q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerRecursive.compilerAllTwelveCasesIffSentence w a c h n b z q)) :=
  Internal.ObjectProjectCompilerRecursive.native_compilerAllTwelveCasesIff w a c h n b z q

example {m} (w a c h n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerRecursive.compilerActualLocalRecursiveIffSentence w a c h n b q)) :=
  Internal.ObjectProjectCompilerRecursive.native_compilerActualLocalRecursiveIff w a c h n b q

example {m} (w a c n h v b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerRecursive.compilerActualStateRecursiveIffSentence w a c n h v b q)) :=
  Internal.ObjectProjectCompilerRecursive.native_compilerActualStateRecursiveIff w a c n h v b q

example {m} (w a c n v b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerRecursive.compilerAtEvaluationRecursiveIffSentence w a c n v b q)) :=
  Internal.ObjectProjectCompilerRecursive.native_compilerAtEvaluationRecursiveIff w a c n v b q

example {m} (w a c n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerRecursive.compilerAtCarrierRecursiveIffSentence w a c n b q)) :=
  Internal.ObjectProjectCompilerRecursive.native_compilerAtCarrierRecursiveIff w a c n b q

example {m} (w n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerRecursive.compilerAllCandidatesRecursiveIffSentence w n b q)) :=
  Internal.ObjectProjectCompilerRecursive.native_compilerAllCandidatesRecursiveIff w n b q

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerRecursive.compilerAllInternalRecursiveLawSentence w)) :=
  Internal.ObjectProjectCompilerRecursive.native_compilerAllInternalRecursiveLaw w
example {m} (w n z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerTyping.compilerChildTypingFromMemberIHSentence w n z)) :=
  Internal.ObjectProjectCompilerTyping.native_compilerChildTypingFromMemberIH w n z

example {m} (w b z n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerTyping.compilerTwelveCasesTargetTypedSentence w b z n q)) :=
  Internal.ObjectProjectCompilerTyping.native_compilerTwelveCasesTargetTyped w b z n q

example {m} (w n b q z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerTyping.compilerOutputTypedFromMemberIHSentence w n b q z)) :=
  Internal.ObjectProjectCompilerTyping.native_compilerOutputTypedFromMemberIH w n b q z

example {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerTyping.compilerTypingPropertyStepSentence w n)) :=
  Internal.ObjectProjectCompilerTyping.native_compilerTypingPropertyStep w n

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerTyping.compilerTypingProgressiveSentence w)) :=
  Internal.ObjectProjectCompilerTyping.native_compilerTypingProgressive w

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerTyping.compilerAllInternalOutputsTargetTypedSentence w)) :=
  Internal.ObjectProjectCompilerTyping.native_compilerAllInternalOutputsTargetTyped w

example {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerTyping.compilerInputTypingPropertySentence w n)) :=
  Internal.ObjectProjectCompilerTyping.native_compilerInputTypingProperty w n

example {m} (w n b q z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerTyping.compilerActualOutputTargetTypedSentence w n b q z)) :=
  Internal.ObjectProjectCompilerTyping.native_compilerActualOutputTargetTyped w n b q z

example {m} (w n b q z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerTyping.compilerUntypedOutputRejectedSentence w n b q z)) :=
  Internal.ObjectProjectCompilerTyping.native_compilerUntypedOutputRejected w n b q z
example {m} (w n b f z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerComplete.compilerSourceAtomsActualOutputSentence w n b f z)) :=
  Internal.ObjectProjectCompilerComplete.native_compilerSourceAtomsActualOutput w n b f z

example {m} (w n x b f z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerComplete.compilerSourceChildOutputFromMemberIHSentence w n x b f z)) :=
  Internal.ObjectProjectCompilerComplete.native_compilerSourceChildOutputFromMemberIH w n x b f z

example {m} (w n b f z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerComplete.compilerSourceOutputFromMemberIHSentence w n b f z)) :=
  Internal.ObjectProjectCompilerComplete.native_compilerSourceOutputFromMemberIH w n b f z

example {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerComplete.compilerCompletenessPropertyStepSentence w n)) :=
  Internal.ObjectProjectCompilerComplete.native_compilerCompletenessPropertyStep w n

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerComplete.compilerCompletenessProgressiveSentence w)) :=
  Internal.ObjectProjectCompilerComplete.native_compilerCompletenessProgressive w

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerComplete.compilerAllInternalCompletenessPropertySentence w)) :=
  Internal.ObjectProjectCompilerComplete.native_compilerAllInternalCompletenessProperty w

example {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerComplete.compilerSourceInputActualOutputExistsSentence w n b f)) :=
  Internal.ObjectProjectCompilerComplete.native_compilerSourceInputActualOutputExists w n b f

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerComplete.compilerAllInternalSourceOutputsExistSentence w)) :=
  Internal.ObjectProjectCompilerComplete.native_compilerAllInternalSourceOutputsExist w

example {m} (w n b f z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerComplete.compilerSourceInputActualTypedOutputExistsSentence w n b f z)) :=
  Internal.ObjectProjectCompilerComplete.native_compilerSourceInputActualTypedOutputExists w n b f z
example {m} (w n x b q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerUnique.compilerGuardedChildScalarUniqueSentence w n x b q r)) :=
  Internal.ObjectProjectCompilerUnique.native_compilerGuardedChildScalarUnique w n x b q r

example {m} (w n x b q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerUnique.compilerSuccessorChildScalarUniqueSentence w n x b q r)) :=
  Internal.ObjectProjectCompilerUnique.native_compilerSuccessorChildScalarUnique w n x b q r

example {m} (w b z n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerUnique.compilerAllCasesScalarUniqueSentence w b z n q r)) :=
  Internal.ObjectProjectCompilerUnique.native_compilerAllCasesScalarUnique w b z n q r

example {m} (w n b q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerUnique.compilerOutputsUniqueFromMemberIHSentence w n b q r)) :=
  Internal.ObjectProjectCompilerUnique.native_compilerOutputsUniqueFromMemberIH w n b q r

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerUnique.compilerScalarFunctionalityProgressiveSentence w)) :=
  Internal.ObjectProjectCompilerUnique.native_compilerScalarFunctionalityProgressive w

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerUnique.compilerAllInternalOutputsScalarUniqueSentence w)) :=
  Internal.ObjectProjectCompilerUnique.native_compilerAllInternalOutputsScalarUnique w

example {m} (w n b q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerUnique.compilerActualOutputsScalarUniqueSentence w n b q r)) :=
  Internal.ObjectProjectCompilerUnique.native_compilerActualOutputsScalarUnique w n b q r

example {m} (w n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerUnique.compilerActualUniqueOutputFiberSentence w n b q)) :=
  Internal.ObjectProjectCompilerUnique.native_compilerActualUniqueOutputFiber w n b q

example {m} (w n b f z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerUnique.compilerSourceActualTypedUniqueOutputExistsSentence w n b f z)) :=
  Internal.ObjectProjectCompilerUnique.native_compilerSourceActualTypedUniqueOutputExists w n b f z

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerUnique.compilerAllInternalSourceTypedUniqueOutputExistsSentence w)) :=
  Internal.ObjectProjectCompilerUnique.native_compilerAllInternalSourceTypedUniqueOutputExists w
example {m} (w n f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerSourceValid.compilerSourceChildValidityFromMemberIHSentence w n f)) :=
  Internal.ObjectProjectCompilerSourceValid.native_compilerSourceChildValidityFromMemberIH w n f

example {m} (w b z n q f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerSourceValid.compilerActualCasesRecoverSourceGrammarSentence w b z n q f)) :=
  Internal.ObjectProjectCompilerSourceValid.native_compilerActualCasesRecoverSourceGrammar w b z n q f

example {m} (w n b q f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerSourceValid.compilerInputValidFromMemberIHSentence w n b q f)) :=
  Internal.ObjectProjectCompilerSourceValid.native_compilerInputValidFromMemberIH w n b q f

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerSourceValid.compilerSourceValidityProgressiveSentence w)) :=
  Internal.ObjectProjectCompilerSourceValid.native_compilerSourceValidityProgressive w

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerSourceValid.compilerAllInternalActualInputsValidSentence w)) :=
  Internal.ObjectProjectCompilerSourceValid.native_compilerAllInternalActualInputsValid w

example {m} (w n b q f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerSourceValid.compilerActualInputValidSentence w n b q f)) :=
  Internal.ObjectProjectCompilerSourceValid.native_compilerActualInputValid w n b q f

example {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerSourceValid.compilerSourceAcceptanceIffSentence w n b f)) :=
  Internal.ObjectProjectCompilerSourceValid.native_compilerSourceAcceptanceIff w n b f

example {m} (w n b f z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerSourceValid.compilerSourceTypedUniqueAcceptanceIffSentence w n b f z)) :=
  Internal.ObjectProjectCompilerSourceValid.native_compilerSourceTypedUniqueAcceptanceIff w n b f z

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerSourceValid.compilerAllInternalSourceAcceptanceIffSentence w)) :=
  Internal.ObjectProjectCompilerSourceValid.native_compilerAllInternalSourceAcceptanceIff w

example {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerSourceValid.compilerAllInternalSourceTypedUniqueAcceptanceIffSentence w)) :=
  Internal.ObjectProjectCompilerSourceValid.native_compilerAllInternalSourceTypedUniqueAcceptanceIff w

example {m} (w n b z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerSourceValid.compilerClosedSourceTypedUniqueAcceptanceIffSentence w n b z)) :=
  Internal.ObjectProjectCompilerSourceValid.native_compilerClosedSourceTypedUniqueAcceptanceIff w n b z

example {m} (w n b q f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Internal.ObjectProjectCompilerSourceValid.compilerInvalidSourceRejectedSentence w n b q f)) :=
  Internal.ObjectProjectCompilerSourceValid.native_compilerInvalidSourceRejected w n b q f

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionMergerFiniteWeightsSyntax.constructionSentence) :=
  ConstructionMergerFiniteWeightsSyntax.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionMergerWeightEstimatesSyntax.constructionSentence) :=
  ConstructionMergerWeightEstimatesSyntax.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionMergerHeightComparisonSyntax.constructionSentence) :=
  ConstructionMergerHeightComparisonSyntax.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionMergerHeightUpperSyntax.constructionSentence) :=
  ConstructionMergerHeightUpperSyntax.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionMergerAverageGapSyntax.constructionSentence) :=
  ConstructionMergerAverageGapSyntax.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionMergerCoordinateMarginSyntax.constructionSentence) :=
  ConstructionMergerCoordinateMarginSyntax.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionMergerUniformMarginSyntax.constructionSentence) :=
  ConstructionMergerUniformMarginSyntax.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionMergerHeightCostSyntax.constructionSentence) :=
  ConstructionMergerHeightCostSyntax.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionMergerWordWeightsSyntax.constructionSentence) :=
  ConstructionMergerWordWeightsSyntax.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionMergerWordHeightCostSyntax.constructionSentence) :=
  ConstructionMergerWordHeightCostSyntax.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionMergerCardinality.boundSentence) :=
  ConstructionMergerCardinality.bound_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionMergerParentSyntax.constructionSentence) :=
  ConstructionMergerParentSyntax.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionDirectedLimitCarrierSyntax.constructionSentence) :=
  ConstructionDirectedLimitCarrierSyntax.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionDirectedMonoidSyntax.constructionSentence) :=
  ConstructionDirectedMonoidSyntax.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionDirectedConservativeSyntax.constructionSentence) :=
  ConstructionDirectedConservativeSyntax.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionDirectedProfilesSyntax.constructionSentence) :=
  ConstructionDirectedProfilesSyntax.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionDirectedHeightCostSyntax.constructionSentence) :=
  ConstructionDirectedHeightCostSyntax.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionDirectedCardinality.boundSentence) :=
  ConstructionDirectedCardinality.bound_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionDirectedObjectSyntax.constructionSentence) :=
  ConstructionDirectedObjectSyntax.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionDirectedLiftSyntax.universalSentence) :=
  ConstructionDirectedLiftSyntax.universal_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionDirectedColimitSyntax.constructionSentence) :=
  ConstructionDirectedColimitSyntax.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionMergerPrescriptionMapSyntax.constructionSentence) :=
  ConstructionMergerPrescriptionMapSyntax.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionRequestMapsSyntax.mapsSentence) :=
  ConstructionRequestMapsSyntax.maps_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionRoundStepSyntax.stepSentence) :=
  ConstructionRoundStepSyntax.step_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionRequestScheduleSyntax.scheduleSentence) :=
  ConstructionRequestScheduleSyntax.schedule_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionCompleteScheduleSyntax.constructionSentence) :=
  ConstructionCompleteScheduleSyntax.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionScheduleOrderSyntax.constructionSentence) :=
  ConstructionScheduleOrderSyntax.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionOrdinalScheduleSyntax.fullSentence) :=
  ConstructionOrdinalScheduleSyntax.full_kernel_certificate

-- Arbitrary native ZF/ZFC schema indices; SAME original derivation kernel.
example {p : SetTheory.Definitional.Project.Sentence} (hp : SetTheory.ZF p) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative p)) :=
  ConstructibleGround.zf_axiom_kernel hp

example {p : SetTheory.Definitional.Project.Sentence} (hp : SetTheory.ZFC p) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative p)) :=
  ConstructibleGround.zfc_axiom_kernel hp

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative SetTheory.InnerModel.js_universe_s)) :=
  ConstructibleGround.global_order_kernel

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructibleGround.nonemptySentence) :=
  ConstructibleGround.nonempty_kernel

-- SAME completed L domain discharges the existing source interpreted theory.
example {p : Source.Sentence} (hp : Source.SetLanguage.ZF p) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (Relativization.formula ConstructibleSource.domain p)) :=
  ConstructibleSource.zf_axiom_kernel hp

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (Relativization.formula ConstructibleSource.domain Source.SetLanguage.AC)) :=
  ConstructibleSource.choice_kernel

example {n : Nat} (p : Source.Formula (n+2)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (Relativization.formula ConstructibleSource.domain (CollectionSyntax.collection p))) :=
  ConstructibleSource.collection_kernel p

example {p : YesMetaZFC.Logic.FirstOrder.Sentence SetTheory.PureSetLanguage}
    (h : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] p) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (Relativization.formula ConstructibleSource.domain (Reverse.sentence p))) :=
  ConstructibleSource.native_sentence h

example {p : Source.Sentence}
    (h : YesMetaZFC.Logic.FirstOrder.Derives (SetTheory.Definitional.Project.fo_theory SetTheory.ZFC) [] (Translation.sentence p)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (Relativization.formula ConstructibleSource.domain p)) :=
  ConstructibleSource.source_zfc_sentence h

-- Actual complete successor selector, SAME L; no supplied successor tuple.
example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionRoundSelection.totalSentence)) :=
  ConstructionRoundSelection.total_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionRoundSelection.stepSentence)) :=
  ConstructionRoundSelection.step_kernel_certificate

-- SAME selected round successor; ALL old varying carriers and actual leg family.
example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionTowerSuccessor.successorSentence)) :=
  ConstructionTowerSuccessor.successor_kernel_certificate

-- ALL internal ordinal lengths: append new carrier and OWN actual identity leg.
example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionTowerSuccessor.appendSentence) :=
  ConstructionTowerSuccessor.append_kernel_certificate

-- Actual complete UNDER-base limit, all old stages, unique base map/all triangles.
example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionTowerLimit.constructionSentence) :=
  ConstructionTowerLimit.construction_kernel_certificate

-- Actual typed transition profiles imply source hP, including mapped-function typing.
example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionTowerLimit.typedProfileSentence) :=
  ConstructionTowerLimit.typedProfile_kernel_certificate

-- SAME normalized codec/full incoming+self family in ALL three actual cases.
example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionTowerInitial.initialSentence) :=
  ConstructionTowerInitial.initial_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionTowerCanonicalLimit.constructionSentence) :=
  ConstructionTowerCanonicalLimit.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionTowerCanonicalSuccessor.constructionSentence)) :=
  ConstructionTowerCanonicalSuccessor.construction_kernel_certificate

-- Actual native graph construction from ALL internally indexed record histories.
example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionTowerHistory.extractionSentence) :=
  ConstructionTowerHistory.extraction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionTowerTransitions.constructionSentence) :=
  ConstructionTowerTransitions.construction_kernel_certificate

-- Full native history contracts: no given diagram in the actual constructor endpoints.
example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionTowerDiagram.extractionSentence) :=
  ConstructionTowerDiagram.extraction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionTowerHistoryLimit.constructionSentence) :=
  ConstructionTowerHistoryLimit.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionTowerHistoryInitial.constructionSentence) :=
  ConstructionTowerHistoryInitial.construction_kernel_certificate

-- Full source-parent constructor plus actual append validity, same normalized records.
example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative ConstructionTowerHistorySuccessor.constructionSentence)) :=
  ConstructionTowerHistorySuccessor.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionTowerHistoryClosure.limitSentence) :=
  ConstructionTowerHistoryClosure.limit_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionTowerHistoryClosure.successorSentence) :=
  ConstructionTowerHistoryClosure.successor_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative ConstructionTowerHistoryClosure.successorConstructionSentence)) :=
  ConstructionTowerHistoryClosure.successorConstruction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionTowerHistoryClosure.limitConstructionSentence) :=
  ConstructionTowerHistoryClosure.limitConstruction_kernel_certificate

-- Concrete operator/recursion/full-valid tower; SAME L/order producer discharges needed order.
example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative ConstructionTowerIteration.totalSentence)) :=
  ConstructionTowerIteration.total_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionTowerIteration.stepSentence) :=
  ConstructionTowerIteration.step_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative ConstructionTowerIteration.recursionSentence)) :=
  ConstructionTowerIteration.recursion_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative ConstructionTowerIterationValidity.constructionSentence)) :=
  ConstructionTowerIterationValidity.construction_kernel_certificate

-- SAME actual global successor map, complete Step and original request witnesses.
example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionTowerMapSucc.mapSuccSentence) :=
  ConstructionTowerMapSucc.mapSucc_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative ConstructionTowerMapSucc.constructionSentence)) :=
  ConstructionTowerMapSucc.construction_kernel_certificate

-- Native ZF Request bound and actual small Request set; no object Choice premise.
example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionRequestCardinality.boundSentence) :=
  ConstructionRequestCardinality.bound_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionRequestCardinality.constructionSentence) :=
  ConstructionRequestCardinality.construction_kernel_certificate

-- Existing actual carriers/collapse and source successor/limit bounds; no rebuilt foundations.
example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionScheduleCardinality.boundSentence) :=
  ConstructionScheduleCardinality.bound_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionScheduleCardinality.constructionSentence) :=
  ConstructionScheduleCardinality.construction_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionTowerCardinality.boundSentence) :=
  ConstructionTowerCardinality.bound_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative ConstructionTowerCardinality.constructionSentence)) :=
  ConstructionTowerCardinality.construction_kernel_certificate


-- Exact all-internal-word common exit cone; consume the SAME actual request source.
example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionProbeIndependent.independentSentence) :=
  ConstructionProbeIndependent.independent_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionProbeIndependent.realizedSentence) :=
  ConstructionProbeIndependent.realized_kernel_certificate

-- Full source RootSystem on SAME normal forms and SAME actual mapped request.
example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionMergerRootSystem.rootSystemSentence) :=
  ConstructionMergerRootSystem.rootSystem_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionMergerRootSystem.realizedSentence) :=
  ConstructionMergerRootSystem.realized_kernel_certificate

-- Actual image/composite construction, then SAME recursive tower later-cut consumer.
example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionConeTransport.probeAfterSentence) :=
  ConstructionConeTransport.probeAfter_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionConeTransport.mergerAfterSentence) :=
  ConstructionConeTransport.mergerAfter_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionTowerRequestCones.cutSentence) :=
  ConstructionTowerRequestCones.cut_kernel_certificate

-- SAME existing internal L selector; actual execution/root graph construction.
example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative ConstructionTowerExecution.executionSentence)) :=
  ConstructionTowerExecution.execution_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionTowerProbeFamily.familySentence) :=
  ConstructionTowerProbeFamily.family_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionTowerProbeFamily.transitionSentence) :=
  ConstructionTowerProbeFamily.transition_kernel_certificate

-- Actual family construction, retaining graph/profile and proving pairwise source conclusions.
example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionTowerProbeIndependence.constructionSentence) :=
  ConstructionTowerProbeIndependence.construction_kernel_certificate

-- Full original-parent construction, using existing SAME L Choice/order.
example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative ConstructionCompleteRound.constructionSentence)) :=
  ConstructionCompleteRound.construction_kernel_certificate

-- Actual outer successor, preserving SAME complete-round construction trace.
example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative ConstructionSaturationStep.stepSentence)) :=
  ConstructionSaturationStep.step_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative ConstructionSaturationSuccessor.constructionSentence)) :=
  ConstructionSaturationSuccessor.construction_kernel_certificate

-- ALL internal set histories, then the actual full bounded outer recursive tower.
example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative ConstructionSaturationIteration.totalSentence)) :=
  ConstructionSaturationIteration.total_kernel_certificate

example : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative ConstructionSaturationIterationValidity.constructionSentence)) :=
  ConstructionSaturationIterationValidity.construction_kernel_certificate

-- Concrete internal omega1+1, retaining omega1 <= mu and the original cardinal parents.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative ConstructionSaturationIndex.indexSentence)) :=
  ConstructionSaturationIndex.index_kernel_certificate

example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative ConstructionSaturationIndex.constructionSentence)) :=
  ConstructionSaturationIndex.construction_kernel_certificate

-- Any internally countable domain and any actual internal function; range is constructed.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionSaturationBoundedness.subsetSentence) :=
  ConstructionSaturationBoundedness.subset_kernel_certificate

example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionSaturationBoundedness.countableSentence) :=
  ConstructionSaturationBoundedness.countable_kernel_certificate

-- Original source parents produce the actual tower AND countable-stage factorization
-- for its SAME recursive history and SAME actual transition matrix.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionSaturationCover.constructionSentence)) :=
  ConstructionSaturationCover.construction_kernel_certificate

-- SAME actual constructed tower, with all final Probe requests and K-indexed
-- injection/full final divisor profiles/exact pairwise intersections.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionSaturationProbes.constructionSentence)) :=
  ConstructionSaturationProbes.construction_kernel_certificate

-- SAME actual constructed tower; all internal finite prescriptions, including
-- n=0, have the SAME root graph with full RootSystem AND equality iff GIVEN CopyRel.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionSaturationMergers.constructionSentence)) :=
  ConstructionSaturationMergers.construction_kernel_certificate

-- SAME actual MergerTower, strengthened by an internal K-injection
-- whose EVERY output lies outside the distinguished mark's full cone.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionSaturationComplement.constructionSentence)) :=
  ConstructionSaturationComplement.construction_kernel_certificate

-- SAME actual final tower; original K=mu gives MODEL-INTERNAL bijections
-- from both the full final carrier and full mark-cone complement to mu.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionSaturationCardinals.constructionSentence)) :=
  ConstructionSaturationCardinals.construction_kernel_certificate

-- Arbitrary internal cone ideals; unit-first internally cofinal path.
-- SAME final Probe family, ALL final divisors and exact full intersections.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionIdealProbes.constructionSentence)) :=
  ConstructionIdealProbes.construction_kernel_certificate

-- Actual FULL internal P(omega), its cardinal continuum, successor mu,
-- mu^omega=mu/regularity/omega1 bound, and K=mu consumed by SAME IdealTower.
-- The source Base geometric/countable-carrier contract remains explicit.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionConcreteCardinals.constructionSentence)) :=
  ConstructionConcreteCardinals.construction_kernel_certificate
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionConcreteTower.constructionSentence)) :=
  ConstructionConcreteTower.construction_kernel_certificate

-- No supplied Base geometry, monoid, height/cost graph, mu/K or tower.
-- SAME actual final row explicitly carries full ObjectFields, all probes,
-- exact finite mergers, arbitrary ideals, complement and cardinal endpoints.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionConcreteBase.constructionSentence)) :=
  ConstructionConcreteBase.construction_kernel_certificate

-- Source PlacementExtensions: all internal indices/sets, ground Choice discharged in SAME L.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionPlacementFreshness.constructionSentence)) :=
  ConstructionPlacementFreshness.construction_kernel_certificate

-- Source PlacementExtensions: all internal indices/sets, ground Choice discharged in SAME L.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionPlacementFreshness.familySentence)) :=
  ConstructionPlacementFreshness.family_kernel_certificate

-- Pinned exact extend_permutation_off and original actual coordinate-set consumer.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative ConstructionPlacementExtensions.constructionSentence)) :=
  ConstructionPlacementExtensions.construction_kernel_certificate

-- Pinned exact extend_permutation_off and original actual coordinate-set consumer.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionPlacementExtensions.labelsSentence) :=
  ConstructionPlacementExtensions.labels_kernel_certificate

-- Pinned exact extend_permutation_off and original actual coordinate-set consumer.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative ConstructionPlacementExtensions.actualLabelsSentence)) :=
  ConstructionPlacementExtensions.actualLabels_kernel_certificate

-- Fixed-source exact root intersections and simultaneous fresh placements.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionPlacementPasting.pasteSentence) :=
  ConstructionPlacementPasting.paste_kernel_certificate

-- Fixed-source exact root intersections and simultaneous fresh placements.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative ConstructionPlacementPasting.constructionSentence)) :=
  ConstructionPlacementPasting.construction_kernel_certificate

-- Fixed-source exact root intersections and simultaneous fresh placements.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative ConstructionPlacementTriple.constructionSentence)) :=
  ConstructionPlacementTriple.construction_kernel_certificate

-- Exact actual Diagram contracts required by overlap-prescription and descent consumers.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionDiagramPlacements.rangeSentence) :=
  ConstructionDiagramPlacements.range_kernel_certificate

-- Exact actual Diagram contracts required by overlap-prescription and descent consumers.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionDiagramPlacements.commonSentence) :=
  ConstructionDiagramPlacements.common_kernel_certificate

-- Exact actual Diagram contracts required by overlap-prescription and descent consumers.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionDiagramPlacements.overlapSentence) :=
  ConstructionDiagramPlacements.overlap_kernel_certificate

-- Exact actual Diagram contracts required by overlap-prescription and descent consumers.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionDiagramPlacements.agreeSentence) :=
  ConstructionDiagramPlacements.agree_kernel_certificate

-- Exact actual Diagram contracts required by overlap-prescription and descent consumers.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative ConstructionDiagramPlacements.rootSentence)) :=
  ConstructionDiagramPlacements.root_kernel_certificate

-- Original literal optional table: all internal indices, SAME P and SAME actual final row.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionDiagramPrescription.constructionSentence)) :=
  ConstructionDiagramPrescription.construction_kernel_certificate

-- Original literal optional table: all internal indices, SAME P and SAME actual final row.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionDiagramPrescription.realizationSentence)) :=
  ConstructionDiagramPrescription.realization_kernel_certificate

-- No supplied whole embedding or amalgamating diagram; actual canonical source labels.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionDiagramAmalgamation.constructionSentence)) :=
  ConstructionDiagramAmalgamation.construction_kernel_certificate

-- Pinned common_extension_three: internal ordinal-three family, existing finite amalgamation.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionDiagramThree.constructionSentence)) :=
  ConstructionDiagramThree.construction_kernel_certificate

-- Actual Cohen graphs; separate s0 restriction range and s1 overlap range; no Choice.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionCohenCompatibility.supportSentence) :=
  ConstructionCohenCompatibility.support_kernel_certificate

example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionCohenCompatibility.movementSentence) :=
  ConstructionCohenCompatibility.movement_kernel_certificate

example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionCohenCompatibility.agreementSentence) :=
  ConstructionCohenCompatibility.agreement_kernel_certificate

example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionCohenCompatibility.comparisonSentence) :=
  ConstructionCohenCompatibility.comparison_kernel_certificate

-- Full pinned descent_comparison_placement, arbitrary counterexample c,t, same L.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionDescentPlacement.constructionSentence)) :=
  ConstructionDescentPlacement.construction_kernel_certificate

-- Pinned binary hull / actual countable conservative submonoid, same internal L.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionCountableHull.constructionSentence)) :=
  ConstructionCountableHull.construction_kernel_certificate

-- Pinned binary hull / actual countable conservative submonoid, same internal L.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionCountableConservativeHull.constructionSentence)) :=
  ConstructionCountableConservativeHull.construction_kernel_certificate


-- Pinned actual vertex geometry and entire carrier, ordinary native ZF.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionComponentVertices.geometrySentence) :=
  ConstructionComponentVertices.geometry_kernel_certificate

example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence ConstructionComponentCarrier.constructionSentence) :=
  ConstructionComponentCarrier.construction_kernel_certificate

-- Full internal omega chain cofinal in the ENTIRE Common component, same L.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionComponentCofinal.constructionSentence)) :=
  ConstructionComponentCofinal.construction_kernel_certificate


-- Pinned equivariant mixture: exact raw entries, all internal names and conditions.
example {n : Nat} (R : Source.Formula (n+2)) (P J f a : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ForcingMixName.existenceSentence R P J f a)) :=
  ForcingMixName.existence_kernel_certificate R P J f a

example {n : Nat} (R : Source.Formula (n+2)) (P J f a name nu p : Fin n) :
    FirstOrder.Derives nativeZF []
      (Translation.sentence (ForcingMixLaws.membershipSentence R P J f a name nu p)) :=
  ForcingMixLaws.membership_kernel_certificate R P J f a name nu p

example {n : Nat} (R : Source.Formula (n+2)) (P J f a name i sigma t : Fin n) :
    FirstOrder.Derives nativeZF []
      (Translation.sentence (ForcingMixLaws.equalitySentence R P J f a name i sigma t)) :=
  ForcingMixLaws.equality_kernel_certificate R P J f a name i sigma t

-- Literal Product action: family permutation is an input; fixedness/HS of the mix are derived.
example {n : Nat} (rho : Fin 7 → Fin n) (mul I K B w G F H J f a : Fin n) :
    FirstOrder.Derives nativeZF []
      (Translation.sentence (ForcingEquivariantMix.sentence rho mul I K B w G F H J f a)) :=
  ForcingEquivariantMix.kernel_certificate rho mul I K B w G F H J f a


-- Pinned OrbitNames: literal equality, all internal names; ordinary nativeZF.
example {n : Nat} (v : Fin 7 → Fin n) (I K B w G p J H sigma pi rho q A Bact x y : Fin n) :
    FirstOrder.Derives nativeZF []
      (Translation.sentence (ForcingSupportedNames.sentence v I K B w G p J H sigma pi rho q A Bact x y)) :=
  ForcingSupportedNames.kernel_certificate v I K B w G p J H sigma pi rho q A Bact x y

-- Pinned ProductForcing: actual fixed-root permutation and common Product lower bound.
example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative ConstructionCompatiblePlacement.constructionSentence)) :=
  ConstructionCompatiblePlacement.construction_kernel_certificate


-- Pinned supporting-root implication and restriction iff, SAME internal L, all-rank HS.
example {k n : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s d A fixing dR z zR : Fin k) (v : Fin n → Fin k) (phi : Source.Formula n) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative (ForcingSupportingRoot.constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s d A fixing dR z zR v phi))) :=
  ForcingSupportingRoot.construction_kernel_certificate rho w mu history kappa e mark H C incoming base I K B G F mul p s d A fixing dR z zR v phi

-- Pinned LocalQuotients:18, independent active copies; original overlap retained.
example {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v alpha beta sa sb d A0 A1 fixing0 fixing1 delta da db za zb z r sigma0 sigma1 actA actB x y : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative
        (ForcingActiveIndependent.constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v alpha beta sa sb d A0 A1 fixing0 fixing1 delta da db za zb z r sigma0 sigma1 actA actB x y))) :=
  ForcingActiveIndependent.construction_kernel_certificate rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v alpha beta sa sb d A0 A1 fixing0 fixing1 delta da db za zb z r sigma0 sigma1 actA actB x y

-- Pinned LocalQuotients.active_equal:67: arbitrary overlaps, SAME internal L.
example {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v alpha beta sa sb d A0 A1 fixing0 fixing1 delta da db za zb z r sigma0 sigma1 actA actB x y : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative
        (ForcingActiveEquality.constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v alpha beta sa sb d A0 A1 fixing0 fixing1 delta da db za zb z r sigma0 sigma1 actA actB x y))) :=
  ForcingActiveEquality.construction_kernel_certificate rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v alpha beta sa sb d A0 A1 fixing0 fixing1 delta da db za zb z r sigma0 sigma1 actA actB x y

-- Pinned LocalQuotients.support_descent:132: one actual root-supported HS witness.
example {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1 : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative
        (ForcingSupportDescent.constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1))) :=
  ForcingSupportDescent.construction_kernel_certificate rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1


-- Pinned ProductNames Bit laws on the actual internal condition action.
example : FirstOrder.Derives nativeZF [] (Translation.sentence ForcingProductBits.coeSentence) :=
  ForcingProductBits.coe_kernel_certificate

example : FirstOrder.Derives nativeZF [] (Translation.sentence ForcingProductBits.topSentence) :=
  ForcingProductBits.top_kernel_certificate

example : FirstOrder.Derives nativeZF [] (Translation.sentence ForcingProductBits.monoSentence) :=
  ForcingProductBits.mono_kernel_certificate

example : FirstOrder.Derives nativeZF [] (Translation.sentence ForcingProductBits.functionalSentence) :=
  ForcingProductBits.functional_kernel_certificate

example : FirstOrder.Derives nativeZF [] (Translation.sentence ForcingProductBits.moveSentence) :=
  ForcingProductBits.move_kernel_certificate


-- Actual pinned ProductNames label and full labelSet, with constructed families.
example : FirstOrder.Derives nativeZF [] (Translation.sentence ForcingLabelNames.existenceSentence) :=
  ForcingLabelNames.existence_kernel_certificate

example : FirstOrder.Derives nativeZF [] (Translation.sentence ForcingLabelNames.uniquenessSentence) :=
  ForcingLabelNames.uniqueness_kernel_certificate

example : FirstOrder.Derives nativeZF [] (Translation.sentence ForcingLabelSet.existenceSentence) :=
  ForcingLabelSet.existence_kernel_certificate

example : FirstOrder.Derives nativeZF [] (Translation.sentence ForcingLabelSet.uniquenessSentence) :=
  ForcingLabelSet.uniqueness_kernel_certificate

example {k : Nat} (rho : Fin 7 → Fin k) (I K B w c t j j' b pi A name name' : Fin k) :
    FirstOrder.Derives nativeZF []
      (Translation.sentence (ForcingLabelNames.moveSentence rho I K B w c t j j' b pi A name name')) :=
  ForcingLabelNames.move_kernel_certificate rho I K B w c t j j' b pi A name name'

example {k : Nat} (rho : Fin 7 → Fin k) (I K B w mu G F c t j b : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ForcingLabelNames.constructionSentence rho I K B w mu G F c t j b)) :=
  ForcingLabelNames.construction_kernel_certificate rho I K B w mu G F c t j b

example {k : Nat} (rho : Fin 7 → Fin k) (I K B w mu G F c t b : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ForcingLabelSet.constructionSentence rho I K B w mu G F c t b)) :=
  ForcingLabelSet.construction_kernel_certificate rho I K B w mu G F c t b


-- Pinned LocalQuotients bounds and actual ground LocalName carrier/restrictions.
example : FirstOrder.Derives nativeZF [] (Translation.sentence ForcingLabelBound.equationSentence) :=
  ForcingLabelBound.equation_kernel_certificate

example {k : Nat} (rho : Fin 7 → Fin k) (I K c t b sigma B nu p G F mul : Fin k) :
    FirstOrder.Derives nativeZF []
      (Translation.sentence (ForcingLabelBound.subsetSentence rho I K c t b sigma B nu p G F mul)) :=
  ForcingLabelBound.subset_kernel_certificate rho I K c t b sigma B nu p G F mul

example {k : Nat} (rho : Fin 7 → Fin k) (G F B H : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ForcingLocalNames.existenceSentence rho G F B H)) :=
  ForcingLocalNames.existence_kernel_certificate rho G F B H

example {k : Nat} (rho : Fin 7 → Fin k) (G F B H X Y : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ForcingLocalNames.uniquenessSentence rho G F B H X Y)) :=
  ForcingLocalNames.uniqueness_kernel_certificate rho G F B H X Y

example {k : Nat} (rho : Fin 7 → Fin k) (G F B J K HJ HK X Y : Fin k) :
    FirstOrder.Derives nativeZF []
      (Translation.sentence (ForcingLocalNames.restrictionSentence rho G F B J K HJ HK X Y)) :=
  ForcingLocalNames.restriction_kernel_certificate rho G F B J K HJ HK X Y

example : FirstOrder.Derives nativeZF [] (Translation.sentence ForcingLocalNames.compositionSentence) :=
  ForcingLocalNames.composition_kernel_certificate


-- Actual LocalName normalization and descent at the original supporting roots.
example {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu c t b J H bound e G F mul sigma nu : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence
        (ForcingLocalNormalize.constructionSentence rho I K B w mu c t b J H bound e G F mul sigma nu)) :=
  ForcingLocalNormalize.construction_kernel_certificate rho I K B w mu c t b J H bound e G F mul sigma nu

example {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1 c t b labels nameBound : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative
        (ForcingLocalNameDescent.constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1 c t b labels nameBound))) :=
  ForcingLocalNameDescent.construction_kernel_certificate rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1 c t b labels nameBound

-- Actual local quotients and their representative-preserving restriction graphs.
example {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w e mul g r G F nameBound J H : Fin k) :
    FirstOrder.Derives nativeZF []
      (Translation.sentence (ForcingLocalQuotient.constructionSentence rho I K B w e mul g r G F nameBound J H)) :=
  ForcingLocalQuotient.construction_kernel_certificate rho I K B w e mul g r G F nameBound J H

example {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w e mul g r s G F nameBound J L HJ HL X Y Q T pr ps : Fin k) :
    FirstOrder.Derives nativeZF []
      (Translation.sentence (ForcingLocalRestriction.constructionSentence rho I K B w e mul g r s G F nameBound J L HJ HL X Y Q T pr ps)) :=
  ForcingLocalRestriction.construction_kernel_certificate rho I K B w e mul g r s G F nameBound J L HJ HL X Y Q T pr ps

example {k : Nat} (R : Formula (k+2)) (W g r X Q pr f : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ForcingLocalRestriction.identitySentence R W g r X Q pr f)) :=
  ForcingLocalRestriction.identity_kernel_certificate R W g r X Q pr f

example {k : Nat} (X Y Z Q T U pr ps pt f g h : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ForcingLocalRestriction.compositionSentence X Y Z Q T U pr ps pt f g h)) :=
  ForcingLocalRestriction.composition_kernel_certificate X Y Z Q T U pr ps pt f g h

example :
    FirstOrder.Derives nativeZF [] (Translation.sentence ForcingLocalRestriction.representativeSentence) :=
  ForcingLocalRestriction.representative_kernel_certificate

-- Actual quotient injectivity and exact intersection, in the same existing internal L.
example {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative (ForcingLocalInjectivity.constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f))) :=
  ForcingLocalInjectivity.construction_kernel_certificate rho w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f

example {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative (ForcingLocalIntersection.constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y))) :=
  ForcingLocalIntersection.construction_kernel_certificate rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y

-- Exact isClass eligibility, root reflection and actual below-root object carrier.
example {k : Nat} (rho : Fin 7 → Fin k) (I K B w e G F mul g r labels E X pr sigma cls : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ForcingEligibility.representativeSentence rho I K B w e G F mul g r labels E X pr sigma cls)) :=
  ForcingEligibility.representative_kernel_certificate rho I K B w e G F mul g r labels E X pr sigma cls

example {k : Nat} (rho : Fin 7 → Fin k) (I K B w e G F mul g r s labels E X pr ps f x y : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ForcingEligibility.restrictionSentence rho I K B w e G F mul g r s labels E X pr ps f x y)) :=
  ForcingEligibility.restriction_kernel_certificate rho I K B w e G F mul g r s labels E X pr ps f x y

example {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing c t b labels E nameBound X Y pr ps f x y : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative (ForcingEligibilityReflection.constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing c t b labels E nameBound X Y pr ps f x y))) :=
  ForcingEligibilityReflection.construction_kernel_certificate rho w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing c t b labels E nameBound X Y pr ps f x y

example {k : Nat} (rho : Fin 7 → Fin k) (G F mul g r q labels E pr Q : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ForcingEligibleObjects.constructionSentence rho G F mul g r q labels E pr Q)) :=
  ForcingEligibleObjects.construction_kernel_certificate rho G F mul g r q labels E pr Q


-- Actual eligible Obj restriction and transfer of the three existing quotient map laws.
example {k : Nat} (rho : Fin 7 → Fin k) (I K B w e G F mul g r s q labels E X pr ps Q T V U f : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ForcingEligibleRestriction.constructionSentence rho I K B w e G F mul g r s q labels E X pr ps Q T V U f)) :=
  ForcingEligibleRestriction.construction_kernel_certificate rho I K B w e G F mul g r s q labels E X pr ps Q T V U f

example : FirstOrder.Derives nativeZF [] (Translation.sentence ForcingEligibleRestriction.identitySentence) :=
  ForcingEligibleRestriction.identity_kernel_certificate

example : FirstOrder.Derives nativeZF [] (Translation.sentence ForcingEligibleRestriction.compositionSentence) :=
  ForcingEligibleRestriction.composition_kernel_certificate

example : FirstOrder.Derives nativeZF [] (Translation.sentence ForcingEligibleRestriction.injectivitySentence) :=
  ForcingEligibleRestriction.injectivity_kernel_certificate


-- Actual eligible intersection and discharge of all three quotient-map law premises.
example {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y q Aq fixingQ E O0 O1 OP a0 a1 b0 b1 : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative (ForcingEligibleIntersection.constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y q Aq fixingQ E O0 O1 OP a0 a1 b0 b1))) :=
  ForcingEligibleIntersection.construction_kernel_certificate rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP c t b labels nameBound g X0 X1 XP XV Q0 Q1 QP pr0 pr1 prP prv f0 f1 k0 k1 x0 x1 y q Aq fixingQ E O0 O1 OP a0 a1 b0 b1

example {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (D mul W g r q labels E X Q pr f V a : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ForcingEligibleLaws.identitySentence R Hdom D mul W g r q labels E X Q pr f V a)) :=
  ForcingEligibleLaws.identity_kernel_certificate R Hdom D mul W g r q labels E X Q pr f V a

example {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (D mul W g r q labels E X Y Z Q T U pr ps pt f01 f12 f02 V J a01 a12 a02 : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ForcingEligibleLaws.compositionSentence R Hdom D mul W g r q labels E X Y Z Q T U pr ps pt f01 f12 f02 V J a01 a12 a02)) :=
  ForcingEligibleLaws.composition_kernel_certificate R Hdom D mul W g r q labels E X Y Z Q T U pr ps pt f01 f12 f02 V J a01 a12 a02

example {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f V J a : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative (ForcingEligibleLaws.constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f V J a))) :=
  ForcingEligibleLaws.construction_kernel_certificate rho w mu history kappa e mark H C incoming base I K B G F mul p s g A fixing nameBound X Y Q T pr ps f V J a


-- One actual internal object/map family over all diagrams and all comparable pairs.
example {k : Nat} (rho : Fin 7 → Fin k) (G F mul g q nameBound labels E I diagrams : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ForcingEligibleFamily.constructionSentence rho G F mul g q nameBound labels E I diagrams)) :=
  ForcingEligibleFamily.construction_kernel_certificate rho G F mul g q nameBound labels E I diagrams

example {k : Nat} (rho : Fin 7 → Fin k) (I K B w e G F mul g q nameBound labels E : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ForcingEligibleMapFamily.constructionSentence rho I K B w e G F mul g q nameBound labels E)) :=
  ForcingEligibleMapFamily.construction_kernel_certificate rho I K B w e G F mul g q nameBound labels E


-- Actual System existence: same internal object/map families and all four laws.
example {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative
        (ForcingEligibleSystem.constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E))) :=
  ForcingEligibleSystem.construction_kernel_certificate rho w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E


-- Actual availability ideals, both for an internal System and for the constructed eligibleSystem.
example {k : Nat} (D I mul e diagrams objImage objects S mapImage maps : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ForcingSystemAvailability.systemSentence D I mul e diagrams objImage objects S mapImage maps)) :=
  ForcingSystemAvailability.system_kernel_certificate D I mul e diagrams objImage objects S mapImage maps

example {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative
        (ForcingSystemAvailability.constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E))) :=
  ForcingSystemAvailability.construction_kernel_certificate rho w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E


-- Exact availability contraction and actual fiber bijections.
example {k : Nat} (D I mul e diagrams objImage objects S mapImage maps r s Or Os a n c z f y x U V : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ForcingSystemFibers.contractionSentence D I mul e diagrams objImage objects S mapImage maps r s Or Os a n c z f y x U V)) :=
  ForcingSystemFibers.contraction_kernel_certificate D I mul e diagrams objImage objects S mapImage maps r s Or Os a n c z f y x U V

example {k : Nat} (D I mul e diagrams objImage objects S mapImage maps : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ForcingSystemFibers.systemSentence D I mul e diagrams objImage objects S mapImage maps)) :=
  ForcingSystemFibers.system_kernel_certificate D I mul e diagrams objImage objects S mapImage maps

example {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative
        (ForcingSystemFibers.constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E))) :=
  ForcingSystemFibers.construction_kernel_certificate rho w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E

-- All internal Component vertices carry one exact fiber family; actual arrows are coherent.
example {k : Nat} (D I mul e q diagrams objImage objects S mapImage maps : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence
        (ForcingComponentFibers.constructionSentence D I mul e q diagrams objImage objects S mapImage maps)) :=
  ForcingComponentFibers.construction_kernel_certificate D I mul e q diagrams objImage objects S mapImage maps

-- Actual Matches equivalence and the entire glued component, in the original native ZF kernel.
example {k : Nat} (D I mul e q diagrams objImage objects S mapImage maps : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ForcingComponentMatches.constructionSentence D I mul e q diagrams objImage objects S mapImage maps)) :=
  ForcingComponentMatches.construction_kernel_certificate D I mul e q diagrams objImage objects S mapImage maps

example {k : Nat} (D I mul e q diagrams objImage objects S mapImage maps root : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ForcingComponentGluing.constructionSentence D I mul e q diagrams objImage objects S mapImage maps root)) :=
  ForcingComponentGluing.construction_kernel_certificate D I mul e q diagrams objImage objects S mapImage maps root


-- Literal label System and exact fiber/glued cardinalities in the native kernel.
example {k : Nat} (D I mul e : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ForcingLabelSystem.constructionSentence D I mul e)) :=
  ForcingLabelSystem.construction_kernel_certificate D I mul e

example {k : Nat} (D I mul e q r a U K mu mark b : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ForcingLabelCardinality.constructionSentence D I mul e q r a U K mu mark b)) :=
  ForcingLabelCardinality.construction_kernel_certificate D I mul e q r a U K mu mark b


-- Consume the same completed final Target; no probe/cardinality hypotheses remain.
example {k : Nat} (w Q R top zero mu history kappa D I mul e mark H C incoming base : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ForcingConcreteLabels.targetSentence w Q R top zero mu history kappa D I mul e mark H C incoming base)) :=
  ForcingConcreteLabels.target_kernel_certificate w Q R top zero mu history kappa D I mul e mark H C incoming base

example : FirstOrder.Derives nativeZF []
    (SetTheory.Definitional.Project.fo_sentence (ConstructibleGround.relative ForcingConcreteLabels.constructionSentence)) :=
  ForcingConcreteLabels.construction_kernel_certificate


-- Reindexing keeps source/target systems distinct; the label instance constructs actual apps.
example {k : Nat} (D I mul e diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ForcingReindexSystem.transportSentence D I mul e diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi)) :=
  ForcingReindexSystem.transport_kernel_certificate D I mul e diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi

example {k : Nat} (D I mul e pi : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ForcingLabelTransport.constructionSentence D I mul e pi)) :=
  ForcingLabelTransport.construction_kernel_certificate D I mul e pi


-- Actual vertex movement and root-fiber transport on the entire component.
example {k : Nat} (D I mul q A pi : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ForcingComponentMove.constructionSentence D I mul q A pi)) :=
  ForcingComponentMove.construction_kernel_certificate D I mul q A pi

example {k : Nat} (D I mul e q diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi v : Fin k) :
    FirstOrder.Derives nativeZF []
      (SetTheory.Definitional.Project.fo_sentence (ForcingGluedTransport.constructionSentence D I mul e q diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi v)) :=
  ForcingGluedTransport.construction_kernel_certificate D I mul e q diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi v


-- Move the actual Cohen filter; transport local equality on all internal names.
example {k : Nat} (rho : Fin 7 → Fin k) (mul a I K B w pi g : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ForcingLocalTransport.constructionSentence rho mul a I K B w pi g)) :=
  ForcingLocalTransport.construction_kernel_certificate rho mul a I K B w pi g

example {k : Nat} (rho : Fin 7 → Fin k) (mul I K B w pi g : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ForcingLocalTransport.assemblySentence rho mul I K B w pi g)) :=
  ForcingLocalTransport.assembly_kernel_certificate rho mul I K B w pi g


-- Actual LocalName bijection and descended moved-filter quotient transport.
example {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mu pi inv c a ai bound J : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ForcingLocalNameTransport.constructionSentence rho I K B w G F mu pi inv c a ai bound J)) :=
  ForcingLocalNameTransport.construction_kernel_certificate rho I K B w G F mu pi inv c a ai bound J

example {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mu pi inv c a ai labelMap top bit labels bound J : Fin k) :
    FirstOrder.Derives nativeZF [] (SetTheory.Definitional.Project.fo_sentence (ForcingLocalNameTransport.literalSentence rho I K B w G F mu pi inv c a ai labelMap top bit labels bound J)) :=
  ForcingLocalNameTransport.literal_kernel_certificate rho I K B w G F mu pi inv c a ai labelMap top bit labels bound J

example {k : Nat} (rho : Fin 7 → Fin k) (I K B w e mul a G F mu pi inv c ai bound J JT H HT X Y g r rT : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ForcingLocalQuotientTransport.constructionSentence rho I K B w e mul a G F mu pi inv c ai bound J JT H HT X Y g r rT)) :=
  ForcingLocalQuotientTransport.construction_kernel_certificate rho I K B w e mul a G F mu pi inv c ai bound J JT H HT X Y g r rT

example {k : Nat} (W a X Y YS Q QS T TS pr ps prT psT nf fr fs sr st c d b e : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ForcingLocalQuotientTransport.naturalitySentence W a X Y YS Q QS T TS pr ps prT psT nf fr fs sr st c d b e)) :=
  ForcingLocalQuotientTransport.naturality_kernel_certificate W a X Y YS Q QS T TS pr ps prT psT nf fr fs sr st c d b e


-- Actual coordinate eligibility and root-supported app construction.
example {k : Nat} (rho : Fin 7 → Fin k) (G F mul I K B w pi a ac g gT r rT labels E ET sigma sigmaT : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (ForcingEligibleTransport.nameSentence rho G F mul I K B w pi a ac g gT r rT labels E ET sigma sigmaT)) :=
  ForcingEligibleTransport.name_kernel_certificate rho G F mul I K B w pi a ac g gT r rT labels E ET sigma sigmaT

example {k : Nat} (rho : Fin 7 → Fin k) (G F mul I K B w e mu pi inv c a ai ac g gT r rT q A Hq labelMap top bit labels E X Y pr ps f Q T V U : Fin k) :
    FirstOrder.Derives nativeZF [] (SetTheory.Definitional.Project.fo_sentence (ForcingEligibleTransport.rootSentence rho G F mul I K B w e mu pi inv c a ai ac g gT r rT q A Hq labelMap top bit labels E X Y pr ps f Q T V U)) :=
  ForcingEligibleTransport.root_kernel_certificate rho G F mul I K B w e mu pi inv c a ai ac g gT r rT q A Hq labelMap top bit labels E X Y pr ps f Q T V U

example {k : Nat} (rho : Fin 7 → Fin k) (G F mul a I K B w e mu pi inv c ai ac g gT r rT q A Hq labelMap top bit labels E bound Ar Hr X Q pr V AT HT Y T ps U : Fin k) :
    FirstOrder.Derives nativeZF [] (SetTheory.Definitional.Project.fo_sentence (ForcingEligibleTransport.assemblySentence rho G F mul a I K B w e mu pi inv c ai ac g gT r rT q A Hq labelMap top bit labels E bound Ar Hr X Q pr V AT HT Y T ps U)) :=
  ForcingEligibleTransport.assembly_kernel_certificate rho G F mul a I K B w e mu pi inv c ai ac g gT r rT q A Hq labelMap top bit labels E bound Ar Hr X Q pr V AT HT Y T ps U

-- Actual all-diagram eligibleSystemTransport with the same family and naturality.
example {k : Nat} (rho : Fin 7 → Fin k) (G F mul a I K B w e mu pi inv c ai ac g gT q A Hq labelMap top bit labels E bound objImage objects targetImage targets arrows maps targetMaps : Fin k) :
    FirstOrder.Derives nativeZF [] (SetTheory.Definitional.Project.fo_sentence (ForcingEligibleReindex.constructionSentence rho G F mul a I K B w e mu pi inv c ai ac g gT q A Hq labelMap top bit labels E bound objImage objects targetImage targets arrows maps targetMaps)) :=
  ForcingEligibleReindex.construction_kernel_certificate rho G F mul a I K B w e mu pi inv c ai ac g gT q A Hq labelMap top bit labels E bound objImage objects targetImage targets arrows maps targetMaps

-- Literal local-name codes over the entire internal omega, in the existing L.
example {k : Nat} (rho : Fin 7 → Fin k) (I G F mul g q bound labels E objects maps root gluePr w names chain objImage Q P vertices zero b : Fin k) :
    FirstOrder.Derives nativeZF [] (SetTheory.Definitional.Project.fo_sentence
      (ConstructibleGround.relative (ForcingTailCodes.constructionSentence rho I G F mul g q bound labels E objects maps root gluePr w names chain objImage Q P vertices zero b))) :=
  ForcingTailCodes.construction_kernel_certificate rho I G F mul g q bound labels E objects maps root gluePr w names chain objImage Q P vertices zero b

end PPAC.Migration.Step4Checks
