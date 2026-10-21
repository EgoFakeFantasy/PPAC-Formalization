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

end PPAC.Migration.Step4Checks
