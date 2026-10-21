import PPAC.Migration.Internal.CheckedSequence

/-! 内部有限序列基础的八个完整闭句，有限原公理、源ZF与原Hilbert核实际证书。 -/
namespace PPAC.Migration.Internal.ObjectSequences
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax SequenceSyntax

def assumptions : Theory := fun q => q = Source.SetLanguage.extensionality ∨ q = Source.SetLanguage.pairing ∨
  q = Source.SetLanguage.union ∨ q = Source.SetLanguage.foundation ∨
  q = Source.SetLanguage.separation existenceMatrix ∨ q = Source.SetLanguage.separation RestrictionSyntax.matrix

def emptySentence : Source.Sentence := ((empty (0 : Fin 2)).imp (sequence 0 0 1)).close
def valueSentence : Source.Sentence := ((sequence (0 : Fin 4) 1 2).imp ((Formula.mem 3 1).imp (value 0 3 2))).close
def appendSentence : Source.Sentence := ((sequence (1 : Fin 5) 2 4).imp ((Formula.mem 3 4).imp
  ((successor 0 2).imp (appendUnique 0 1 2 3 4)))).close
def existenceSentence : Source.Sentence := ((omega (0 : Fin 2)).imp ((MinimalPredicates.inhabited 1).imp
  (.all ((Formula.mem (Fin.last 2) (0 : Fin 2).castSucc).imp (existsSequence (Fin.last 2) (1 : Fin 2).castSucc))))).close
def naturalSentence : Source.Sentence := ((omega (0 : Fin 1)).imp
  (.all ((Formula.mem (Fin.last 1) (0 : Fin 1).castSucc).imp (existsSequence (Fin.last 1) (0 : Fin 1).castSucc)))).close
def naturalAppendSentence : Source.Sentence := ((omega (3 : Fin 4)).imp ((sequence 0 1 3).imp
  ((Formula.mem 1 3).imp ((Formula.mem 2 3).imp (SequenceExistence.naturalAppendExists 0 1 2 3))))).close
def prefixSentence : Source.Sentence := ((sequence (0 : Fin 4) 1 3).imp ((RestrictionSyntax.subset 2 1).imp
  (SequencePrefix.existsPrefix 0 2 3))).close
def prefixUniqueSentence : Source.Sentence := ((SequencePrefix.witness (0 : Fin 5) 2 3 4).imp
  ((SequencePrefix.witness 1 2 3 4).imp (.equal 0 1))).close

theorem evidence (m : Nat) : SequenceContext.Evidence (assumptions.at m) :=
  ⟨.hyp ⟨_, Or.inl rfl, rfl⟩,
   .hyp ⟨_, Or.inr (Or.inl rfl), rfl⟩,
   .hyp ⟨_, Or.inr (Or.inr (Or.inl rfl)), rfl⟩,
   .hyp ⟨_, Or.inr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩⟩

theorem induction_separation_at (m : Nat) : Derives (assumptions.at m)
    ((Source.SetLanguage.separation existenceMatrix).rename Fin.elim0) :=
  .hyp ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), rfl⟩
theorem restriction_separation_at (m : Nat) : Derives (assumptions.at m)
    ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0) :=
  .hyp ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), rfl⟩

theorem source_empty : Derives (assumptions.at 0) emptySentence := by
  apply close_derives
  apply Derives.impI
  exact SequenceLogic.empty_sequence 0 1 (.hyp (Or.inl rfl))

theorem source_value : Derives (assumptions.at 0) valueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact SequenceLogic.value_at 0 1 2 3 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_append : Derives (assumptions.at 0) appendSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact SequenceAppend.exists_unique (SequenceContext.add (SequenceContext.add (SequenceContext.add (evidence 5) _) _) _)
    0 1 2 3 4 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_existence : Derives (assumptions.at 0) existenceSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact SequenceExistence.all_inhabited (SequenceContext.add (SequenceContext.add (evidence 2) _) _) 0 1
    (add (add (induction_separation_at 2) _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_natural : Derives (assumptions.at 0) naturalSentence := by
  apply close_derives
  apply Derives.impI
  exact SequenceExistence.all_natural (SequenceContext.add (evidence 1) _) 0
    (add (induction_separation_at 1) _) (.hyp (Or.inl rfl))

theorem source_naturalAppend : Derives (assumptions.at 0) naturalAppendSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact SequenceExistence.natural_append (SequenceContext.add (SequenceContext.add (SequenceContext.add (SequenceContext.add (evidence 4) _) _) _) _)
    0 1 2 3 (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_prefix : Derives (assumptions.at 0) prefixSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact SequencePrefix.exists_prefix 0 1 2 3 (add (add (restriction_separation_at 4) _) _)
    (add (add (evidence 4).extensionality _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_prefixUnique : Derives (assumptions.at 0) prefixUniqueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact SequencePrefix.unique 0 1 2 3 4 (add (add (evidence 5).extensionality _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_ZF_replay {p : Source.Sentence} (h : Derives (assumptions.at 0) p) : Derives (Source.SetLanguage.ZF.at 0) p := by
  refine Derives.weaken ?_ h
  rintro q ⟨s, hs, rfl⟩
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.pairing, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.union, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.foundation, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.separation existenceMatrix, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.separation RestrictionSyntax.matrix, rfl⟩

theorem native_replay {p : YesMetaZFC.Logic.FirstOrder.Sentence ℒ}
    (h : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) [] p) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] p := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := h)
  rintro q ⟨s, hs, rfl⟩
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ZFEquivalence.source_extensionality
  · exact ZFEquivalence.source_pairing
  · exact ZFEquivalence.source_union
  · exact ZFEquivalence.source_foundation
  · exact SeparationSyntax.source_separation existenceMatrix
  · exact SeparationSyntax.source_separation RestrictionSyntax.matrix


theorem empty_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence emptySentence) := TheoryTransport.sentence source_empty
theorem source_ZF_empty : Derives (Source.SetLanguage.ZF.at 0) emptySentence := source_ZF_replay source_empty
theorem native_empty : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence emptySentence) :=
  native_replay empty_kernel_certificate


theorem value_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence valueSentence) := TheoryTransport.sentence source_value
theorem source_ZF_value : Derives (Source.SetLanguage.ZF.at 0) valueSentence := source_ZF_replay source_value
theorem native_value : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence valueSentence) :=
  native_replay value_kernel_certificate


theorem append_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence appendSentence) := TheoryTransport.sentence source_append
theorem source_ZF_append : Derives (Source.SetLanguage.ZF.at 0) appendSentence := source_ZF_replay source_append
theorem native_append : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence appendSentence) :=
  native_replay append_kernel_certificate


theorem existence_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence existenceSentence) := TheoryTransport.sentence source_existence
theorem source_ZF_existence : Derives (Source.SetLanguage.ZF.at 0) existenceSentence := source_ZF_replay source_existence
theorem native_existence : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence existenceSentence) :=
  native_replay existence_kernel_certificate


theorem natural_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence naturalSentence) := TheoryTransport.sentence source_natural
theorem source_ZF_natural : Derives (Source.SetLanguage.ZF.at 0) naturalSentence := source_ZF_replay source_natural
theorem native_natural : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence naturalSentence) :=
  native_replay natural_kernel_certificate


theorem naturalAppend_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence naturalAppendSentence) := TheoryTransport.sentence source_naturalAppend
theorem source_ZF_naturalAppend : Derives (Source.SetLanguage.ZF.at 0) naturalAppendSentence := source_ZF_replay source_naturalAppend
theorem native_naturalAppend : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence naturalAppendSentence) :=
  native_replay naturalAppend_kernel_certificate


theorem prefix_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence prefixSentence) := TheoryTransport.sentence source_prefix
theorem source_ZF_prefix : Derives (Source.SetLanguage.ZF.at 0) prefixSentence := source_ZF_replay source_prefix
theorem native_prefix : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence prefixSentence) :=
  native_replay prefix_kernel_certificate


theorem prefixUnique_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence prefixUniqueSentence) := TheoryTransport.sentence source_prefixUnique
theorem source_ZF_prefixUnique : Derives (Source.SetLanguage.ZF.at 0) prefixUniqueSentence := source_ZF_replay source_prefixUnique
theorem native_prefixUnique : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence prefixUniqueSentence) :=
  native_replay prefixUnique_kernel_certificate
end PPAC.Migration.Internal.ObjectSequences
