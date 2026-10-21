import PPAC

/-! 第四步当前验收内部有限序列、自然递推及基本数值加乘；不是完整ProofZF/U或Con验收。 -/
namespace PPAC.Migration.Step4Checks
open Source GraphSyntax OmegaSyntax Internal
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

end PPAC.Migration.Step4Checks
