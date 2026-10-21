import PPAC

/-! 第四步当前只验收内部有限序列基础；不是完整ProofZF/U或Con验收。 -/
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
end PPAC.Migration.Step4Checks
