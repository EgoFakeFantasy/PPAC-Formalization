import PPAC.Migration.Internal.SyntaxContextCarrier

/-! 实际上下文/状态载体的完整闭句及原nativeZF证书；不假设宿主集合存在。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxContextCarrier
open Source SourceAlgebra SourceLogic PairSyntax RestrictionSyntax PowerSetSyntax SyntaxContextCarrierSyntax

def pairSubsetSentence {m} (p b f w : Fin m) : Source.Sentence := ((pair p b f).imp ((Formula.mem b w).imp ((Formula.mem f w).imp (subset p w)))).close

theorem source_pairSubset {m} (p b f w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pairSubsetSentence p b f w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem f w) (Context.add (Formula.mem b w) (Context.add (pair p b f) (Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (pair p b f) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem f w) := .hyp (Or.inl rfl)
  exact SyntaxContextCarrier.pair_subset p b f w h0 h1 h2

theorem pairSubset_kernel_certificate {m} (p b f w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pairSubsetSentence p b f w)) := TheoryTransport.sentence (source_pairSubset p b f w)

theorem native_pairSubset {m} (p b f w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pairSubsetSentence p b f w)) := ZFReplay.replay (pairSubset_kernel_certificate p b f w)

def orderedMemberSentence {m} (w a c b f p : Fin m) : Source.Sentence := ((powerOf a w).imp ((powerOf c a).imp ((Formula.mem b w).imp ((Formula.mem f w).imp ((ordered p b f).imp (Formula.mem p c)))))).close

theorem source_orderedMember {m} (w a c b f p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (orderedMemberSentence w a c b f p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ordered p b f) (Context.add (Formula.mem f w) (Context.add (Formula.mem b w) (Context.add (powerOf c a) (Context.add (powerOf a w) (Source.SetLanguage.ZF.at m)))))
  have h0 : Derives Δ (powerOf a w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (powerOf c a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem f w) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (ordered p b f) := .hyp (Or.inl rfl)
  exact SyntaxContextCarrier.ordered_member w a c b f p h0 h1 h2 h3 h4

theorem orderedMember_kernel_certificate {m} (w a c b f p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (orderedMemberSentence w a c b f p)) := TheoryTransport.sentence (source_orderedMember w a c b f p)

theorem native_orderedMember {m} (w a c b f p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (orderedMemberSentence w a c b f p)) := ZFReplay.replay (orderedMember_kernel_certificate w a c b f p)

def pairExistsSentence {m} (w a c b f : Fin m) : Source.Sentence := ((powerOf a w).imp ((powerOf c a).imp ((Formula.mem b w).imp ((Formula.mem f w).imp (pairExistsIn c b f))))).close

theorem source_pairExists {m} (w a c b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pairExistsSentence w a c b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem f w) (Context.add (Formula.mem b w) (Context.add (powerOf c a) (Context.add (powerOf a w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (powerOf a w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (powerOf c a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem f w) := .hyp (Or.inl rfl)
  exact SyntaxContextCarrier.pair_exists hZ w a c b f h0 h1 h2 h3

theorem pairExists_kernel_certificate {m} (w a c b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pairExistsSentence w a c b f)) := TheoryTransport.sentence (source_pairExists w a c b f)

theorem native_pairExists {m} (w a c b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pairExistsSentence w a c b f)) := ZFReplay.replay (pairExists_kernel_certificate w a c b f)

def stateMemberSentence {m} (c u v : Fin m) : Source.Sentence := ((powerOf u c).imp ((subset v c).imp (Formula.mem v u))).close

theorem source_stateMember {m} (c u v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (stateMemberSentence c u v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (subset v c) (Context.add (powerOf u c) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (powerOf u c) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (subset v c) := .hyp (Or.inl rfl)
  exact SyntaxContextCarrier.state_member c u v h0 h1

theorem stateMember_kernel_certificate {m} (c u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (stateMemberSentence c u v)) := TheoryTransport.sentence (source_stateMember c u v)

theorem native_stateMember {m} (c u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (stateMemberSentence c u v)) := ZFReplay.replay (stateMember_kernel_certificate c u v)

def existsSentence {m} (w : Fin m) : Source.Sentence := (existsTower w).close

theorem source_exists {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsSentence w) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact SyntaxContextCarrier.exists_tower hZ w

theorem exists_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsSentence w)) := TheoryTransport.sentence (source_exists w)

theorem native_exists {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsSentence w)) := ZFReplay.replay (exists_kernel_certificate w)

def uniqueSentence {m} (w a c u v d t : Fin m) : Source.Sentence := ((tower w a c u).imp ((tower w v d t).imp ((Formula.equal a v).conj ((Formula.equal c d).conj (.equal u t))))).close

theorem source_unique {m} (w a c u v d t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniqueSentence w a c u v d t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (tower w v d t) (Context.add (tower w a c u) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (tower w a c u) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (tower w v d t) := .hyp (Or.inl rfl)
  exact SyntaxContextCarrier.tower_unique hZ w a c u v d t h0 h1

theorem unique_kernel_certificate {m} (w a c u v d t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniqueSentence w a c u v d t)) := TheoryTransport.sentence (source_unique w a c u v d t)

theorem native_unique {m} (w a c u v d t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniqueSentence w a c u v d t)) := ZFReplay.replay (unique_kernel_certificate w a c u v d t)
end PPAC.Migration.Internal.ObjectSyntaxContextCarrier
