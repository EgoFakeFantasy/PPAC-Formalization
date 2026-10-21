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

end PPAC.Migration.Step4Checks
