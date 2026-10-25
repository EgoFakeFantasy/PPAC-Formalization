import PPAC.Migration.Internal.StructuralListReverseConsContract

/-! Actual internal list reversal exists uniquely, has exact reflected fields, is involutive, and obeys original Nil/Cons-snoc recursion. EOF return connection, full reader bridge, Basic AST, Proof and Con remain unproved -/
namespace PPAC.Migration.Internal.ObjectStructuralListReverse
open Source SourceAlgebra SourceLogic OmegaSyntax

def structuralListReverseEveryInternalPositionHasMirrorSentence {m} (w l i : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem l w).imp ((Formula.mem i l).imp ((StructuralReverseIndexSyntax.existsMirror w l i))))).close

theorem source_structuralListReverseEveryInternalPositionHasMirror {m} (w l i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (structuralListReverseEveryInternalPositionHasMirrorSentence w l i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i l) (Context.add (Formula.mem l w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem l w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem i l) := .hyp (Or.inl rfl)
  exact StructuralReverseIndexExistence.exists_partner hZ w l i h0 h1 h2

theorem structuralListReverseEveryInternalPositionHasMirror_kernel_certificate {m} (w l i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (structuralListReverseEveryInternalPositionHasMirrorSentence w l i)) := TheoryTransport.sentence (source_structuralListReverseEveryInternalPositionHasMirror w l i)

theorem native_structuralListReverseEveryInternalPositionHasMirror {m} (w l i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (structuralListReverseEveryInternalPositionHasMirrorSentence w l i)) := ZFReplay.replay (structuralListReverseEveryInternalPositionHasMirror_kernel_certificate w l i)

def structuralListReverseMirrorCandidateUniqueSentence {m} (w l i j k : Fin m) : Source.Sentence := ((omega w).imp ((StructuralReverseIndexSyntax.mirror w l i j).imp ((StructuralReverseIndexSyntax.mirror w l i k).imp ((Formula.equal j k))))).close

theorem source_structuralListReverseMirrorCandidateUnique {m} (w l i j k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (structuralListReverseMirrorCandidateUniqueSentence w l i j k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralReverseIndexSyntax.mirror w l i k) (Context.add (StructuralReverseIndexSyntax.mirror w l i j) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (StructuralReverseIndexSyntax.mirror w l i j) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (StructuralReverseIndexSyntax.mirror w l i k) := .hyp (Or.inl rfl)
  exact StructuralReverseIndexArithmetic.unique hZ w l i j k h0 h1 h2

theorem structuralListReverseMirrorCandidateUnique_kernel_certificate {m} (w l i j k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (structuralListReverseMirrorCandidateUniqueSentence w l i j k)) := TheoryTransport.sentence (source_structuralListReverseMirrorCandidateUnique w l i j k)

theorem native_structuralListReverseMirrorCandidateUnique {m} (w l i j k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (structuralListReverseMirrorCandidateUniqueSentence w l i j k)) := ZFReplay.replay (structuralListReverseMirrorCandidateUnique_kernel_certificate w l i j k)

def structuralListReverseMirrorSymmetricSentence {m} (w l i j : Fin m) : Source.Sentence := ((omega w).imp ((StructuralReverseIndexSyntax.mirror w l i j).imp ((StructuralReverseIndexSyntax.mirror w l j i)))).close

theorem source_structuralListReverseMirrorSymmetric {m} (w l i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (structuralListReverseMirrorSymmetricSentence w l i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralReverseIndexSyntax.mirror w l i j) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (StructuralReverseIndexSyntax.mirror w l i j) := .hyp (Or.inl rfl)
  exact StructuralReverseIndexArithmetic.symmetric hZ w l i j h0 h1

theorem structuralListReverseMirrorSymmetric_kernel_certificate {m} (w l i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (structuralListReverseMirrorSymmetricSentence w l i j)) := TheoryTransport.sentence (source_structuralListReverseMirrorSymmetric w l i j)

theorem native_structuralListReverseMirrorSymmetric {m} (w l i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (structuralListReverseMirrorSymmetricSentence w l i j)) := ZFReplay.replay (structuralListReverseMirrorSymmetric_kernel_certificate w l i j)

def structuralListReverseMirrorInputInRangeSentence {m} (w l i j : Fin m) : Source.Sentence := ((omega w).imp ((StructuralReverseIndexSyntax.mirror w l i j).imp ((Formula.mem i l)))).close

theorem source_structuralListReverseMirrorInputInRange {m} (w l i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (structuralListReverseMirrorInputInRangeSentence w l i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralReverseIndexSyntax.mirror w l i j) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (StructuralReverseIndexSyntax.mirror w l i j) := .hyp (Or.inl rfl)
  exact StructuralReverseIndexArithmetic.input_bound hZ w l i j h0 h1

theorem structuralListReverseMirrorInputInRange_kernel_certificate {m} (w l i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (structuralListReverseMirrorInputInRangeSentence w l i j)) := TheoryTransport.sentence (source_structuralListReverseMirrorInputInRange w l i j)

theorem native_structuralListReverseMirrorInputInRange {m} (w l i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (structuralListReverseMirrorInputInRangeSentence w l i j)) := ZFReplay.replay (structuralListReverseMirrorInputInRange_kernel_certificate w l i j)

def structuralListReverseMirrorOutputInRangeSentence {m} (w l i j : Fin m) : Source.Sentence := ((omega w).imp ((StructuralReverseIndexSyntax.mirror w l i j).imp ((Formula.mem j l)))).close

theorem source_structuralListReverseMirrorOutputInRange {m} (w l i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (structuralListReverseMirrorOutputInRangeSentence w l i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralReverseIndexSyntax.mirror w l i j) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (StructuralReverseIndexSyntax.mirror w l i j) := .hyp (Or.inl rfl)
  exact StructuralReverseIndexArithmetic.output_bound hZ w l i j h0 h1

theorem structuralListReverseMirrorOutputInRange_kernel_certificate {m} (w l i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (structuralListReverseMirrorOutputInRangeSentence w l i j)) := TheoryTransport.sentence (source_structuralListReverseMirrorOutputInRange w l i j)

theorem native_structuralListReverseMirrorOutputInRange {m} (w l i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (structuralListReverseMirrorOutputInRangeSentence w l i j)) := ZFReplay.replay (structuralListReverseMirrorOutputInRange_kernel_certificate w l i j)

def structuralListReverseActualReverseFieldExistsUniqueSentence {m} (w n l i : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem l w).imp ((Formula.mem i l).imp ((StructuralReverseFieldSyntax.valueFiber w n l i))))).close

theorem source_structuralListReverseActualReverseFieldExistsUnique {m} (w n l i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (structuralListReverseActualReverseFieldExistsUniqueSentence w n l i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i l) (Context.add (Formula.mem l w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem l w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem i l) := .hyp (Or.inl rfl)
  exact StructuralReverseFieldValues.exists_unique hZ w n l i h0 h1 h2

theorem structuralListReverseActualReverseFieldExistsUnique_kernel_certificate {m} (w n l i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (structuralListReverseActualReverseFieldExistsUniqueSentence w n l i)) := TheoryTransport.sentence (source_structuralListReverseActualReverseFieldExistsUnique w n l i)

theorem native_structuralListReverseActualReverseFieldExistsUnique {m} (w n l i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (structuralListReverseActualReverseFieldExistsUniqueSentence w n l i)) := ZFReplay.replay (structuralListReverseActualReverseFieldExistsUnique_kernel_certificate w n l i)

def structuralListReverseActualReverseFieldNaturalSentence {m} (w n l i y : Fin m) : Source.Sentence := ((omega w).imp ((StructuralReverseFieldSyntax.value w n l i y).imp ((Formula.mem y w)))).close

theorem source_structuralListReverseActualReverseFieldNatural {m} (w n l i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (structuralListReverseActualReverseFieldNaturalSentence w n l i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralReverseFieldSyntax.value w n l i y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (StructuralReverseFieldSyntax.value w n l i y) := .hyp (Or.inl rfl)
  exact StructuralReverseFieldValues.range hZ w n l i y h0 h1

theorem structuralListReverseActualReverseFieldNatural_kernel_certificate {m} (w n l i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (structuralListReverseActualReverseFieldNaturalSentence w n l i y)) := TheoryTransport.sentence (source_structuralListReverseActualReverseFieldNatural w n l i y)

theorem native_structuralListReverseActualReverseFieldNatural {m} (w n l i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (structuralListReverseActualReverseFieldNaturalSentence w n l i y)) := ZFReplay.replay (structuralListReverseActualReverseFieldNatural_kernel_certificate w n l i y)

def structuralListReverseReverseFieldExactAtMirrorSentence {m} (w n l i j y : Fin m) : Source.Sentence := ((omega w).imp ((StructuralReverseIndexSyntax.mirror w l i j).imp (((StructuralReverseFieldSyntax.value w n l i y).iff (StructuralListFieldSyntax.field w n j y))))).close

theorem source_structuralListReverseReverseFieldExactAtMirror {m} (w n l i j y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (structuralListReverseReverseFieldExactAtMirrorSentence w n l i j y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralReverseIndexSyntax.mirror w l i j) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (StructuralReverseIndexSyntax.mirror w l i j) := .hyp (Or.inl rfl)
  exact StructuralReverseFieldAtMirror.at_mirror hZ w n l i j y h0 h1

theorem structuralListReverseReverseFieldExactAtMirror_kernel_certificate {m} (w n l i j y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (structuralListReverseReverseFieldExactAtMirrorSentence w n l i j y)) := TheoryTransport.sentence (source_structuralListReverseReverseFieldExactAtMirror w n l i j y)

theorem native_structuralListReverseReverseFieldExactAtMirror {m} (w n l i j y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (structuralListReverseReverseFieldExactAtMirrorSentence w n l i j y)) := ZFReplay.replay (structuralListReverseReverseFieldExactAtMirror_kernel_certificate w n l i j y)

def structuralListReverseOriginalReplacementConstructsExactReverseGraphSentence {m} (w n l : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem l w).imp ((StructuralReverseFieldSyntax.existsGraph w n l)))).close

theorem source_structuralListReverseOriginalReplacementConstructsExactReverseGraph {m} (w n l : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (structuralListReverseOriginalReplacementConstructsExactReverseGraphSentence w n l) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem l w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem l w) := .hyp (Or.inl rfl)
  exact StructuralReverseFieldGraph.exists_graph hZ w n l h0 h1

theorem structuralListReverseOriginalReplacementConstructsExactReverseGraph_kernel_certificate {m} (w n l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (structuralListReverseOriginalReplacementConstructsExactReverseGraphSentence w n l)) := TheoryTransport.sentence (source_structuralListReverseOriginalReplacementConstructsExactReverseGraph w n l)

theorem native_structuralListReverseOriginalReplacementConstructsExactReverseGraph {m} (w n l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (structuralListReverseOriginalReplacementConstructsExactReverseGraphSentence w n l)) := ZFReplay.replay (structuralListReverseOriginalReplacementConstructsExactReverseGraph_kernel_certificate w n l)

def structuralListReverseExactReverseGraphIsActualSequenceSentence {m} (w n l g : Fin m) : Source.Sentence := ((omega w).imp ((StructuralReverseFieldSyntax.graph w n l g).imp ((SequenceSyntax.sequence g l w)))).close

theorem source_structuralListReverseExactReverseGraphIsActualSequence {m} (w n l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (structuralListReverseExactReverseGraphIsActualSequenceSentence w n l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralReverseFieldSyntax.graph w n l g) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (StructuralReverseFieldSyntax.graph w n l g) := .hyp (Or.inl rfl)
  exact StructuralReverseFieldGraph.sequence hZ w n l g h0 h1

theorem structuralListReverseExactReverseGraphIsActualSequence_kernel_certificate {m} (w n l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (structuralListReverseExactReverseGraphIsActualSequenceSentence w n l g)) := TheoryTransport.sentence (source_structuralListReverseExactReverseGraphIsActualSequence w n l g)

theorem native_structuralListReverseExactReverseGraphIsActualSequence {m} (w n l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (structuralListReverseExactReverseGraphIsActualSequenceSentence w n l g)) := ZFReplay.replay (structuralListReverseExactReverseGraphIsActualSequence_kernel_certificate w n l g)

def structuralListReverseExactReverseGraphUniqueSentence {m} (w n l g h : Fin m) : Source.Sentence := ((StructuralReverseFieldSyntax.graph w n l g).imp ((StructuralReverseFieldSyntax.graph w n l h).imp ((Formula.equal g h)))).close

theorem source_structuralListReverseExactReverseGraphUnique {m} (w n l g h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (structuralListReverseExactReverseGraphUniqueSentence w n l g h) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralReverseFieldSyntax.graph w n l h) (Context.add (StructuralReverseFieldSyntax.graph w n l g) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (StructuralReverseFieldSyntax.graph w n l g) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (StructuralReverseFieldSyntax.graph w n l h) := .hyp (Or.inl rfl)
  exact StructuralReverseFieldGraph.unique_graph hZ w n l g h h0 h1

theorem structuralListReverseExactReverseGraphUnique_kernel_certificate {m} (w n l g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (structuralListReverseExactReverseGraphUniqueSentence w n l g h)) := TheoryTransport.sentence (source_structuralListReverseExactReverseGraphUnique w n l g h)

theorem native_structuralListReverseExactReverseGraphUnique {m} (w n l g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (structuralListReverseExactReverseGraphUniqueSentence w n l g h)) := ZFReplay.replay (structuralListReverseExactReverseGraphUnique_kernel_certificate w n l g h)

def structuralListReverseEveryValidInternalListHasActualReverseSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListTraceSyntax.valid w n).imp ((StructuralListReverseSyntax.existsReverse w n)))).close

theorem source_structuralListReverseEveryValidInternalListHasActualReverse {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (structuralListReverseEveryValidInternalListHasActualReverseSentence w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListTraceSyntax.valid w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (StructuralListTraceSyntax.valid w n) := .hyp (Or.inl rfl)
  exact StructuralListReverseEncoding.exists_reverse hZ w n h0 h1

theorem structuralListReverseEveryValidInternalListHasActualReverse_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (structuralListReverseEveryValidInternalListHasActualReverseSentence w n)) := TheoryTransport.sentence (source_structuralListReverseEveryValidInternalListHasActualReverse w n)

theorem native_structuralListReverseEveryValidInternalListHasActualReverse {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (structuralListReverseEveryValidInternalListHasActualReverseSentence w n)) := ZFReplay.replay (structuralListReverseEveryValidInternalListHasActualReverse_kernel_certificate w n)

def structuralListReverseActualReverseCodeUniqueSentence {m} (w n r s : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListReverseSyntax.reverses w n r).imp ((StructuralListReverseSyntax.reverses w n s).imp ((Formula.equal r s))))).close

theorem source_structuralListReverseActualReverseCodeUnique {m} (w n r s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (structuralListReverseActualReverseCodeUniqueSentence w n r s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListReverseSyntax.reverses w n s) (Context.add (StructuralListReverseSyntax.reverses w n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (StructuralListReverseSyntax.reverses w n r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (StructuralListReverseSyntax.reverses w n s) := .hyp (Or.inl rfl)
  exact StructuralListReverseUnique.unique hZ w n r s h0 h1 h2

theorem structuralListReverseActualReverseCodeUnique_kernel_certificate {m} (w n r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (structuralListReverseActualReverseCodeUniqueSentence w n r s)) := TheoryTransport.sentence (source_structuralListReverseActualReverseCodeUnique w n r s)

theorem native_structuralListReverseActualReverseCodeUnique {m} (w n r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (structuralListReverseActualReverseCodeUniqueSentence w n r s)) := ZFReplay.replay (structuralListReverseActualReverseCodeUnique_kernel_certificate w n r s)

def structuralListReverseActualReverseCodeExistsUniqueSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListTraceSyntax.valid w n).imp ((StructuralListReverseSyntax.fiber w n)))).close

theorem source_structuralListReverseActualReverseCodeExistsUnique {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (structuralListReverseActualReverseCodeExistsUniqueSentence w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListTraceSyntax.valid w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (StructuralListTraceSyntax.valid w n) := .hyp (Or.inl rfl)
  exact StructuralListReverseUnique.exists_unique hZ w n h0 h1

theorem structuralListReverseActualReverseCodeExistsUnique_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (structuralListReverseActualReverseCodeExistsUniqueSentence w n)) := TheoryTransport.sentence (source_structuralListReverseActualReverseCodeExistsUnique w n)

theorem native_structuralListReverseActualReverseCodeExistsUnique {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (structuralListReverseActualReverseCodeExistsUniqueSentence w n)) := ZFReplay.replay (structuralListReverseActualReverseCodeExistsUnique_kernel_certificate w n)

def structuralListReverseActualReverseRequiresValidInputSentence {m} (w n r : Fin m) : Source.Sentence := ((StructuralListReverseSyntax.reverses w n r).imp ((StructuralListTraceSyntax.valid w n))).close

theorem source_structuralListReverseActualReverseRequiresValidInput {m} (w n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (structuralListReverseActualReverseRequiresValidInputSentence w n r) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListReverseSyntax.reverses w n r) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (StructuralListReverseSyntax.reverses w n r) := .hyp (Or.inl rfl)
  exact StructuralListReverseUnique.valid_input w n r h0

theorem structuralListReverseActualReverseRequiresValidInput_kernel_certificate {m} (w n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (structuralListReverseActualReverseRequiresValidInputSentence w n r)) := TheoryTransport.sentence (source_structuralListReverseActualReverseRequiresValidInput w n r)

theorem native_structuralListReverseActualReverseRequiresValidInput {m} (w n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (structuralListReverseActualReverseRequiresValidInputSentence w n r)) := ZFReplay.replay (structuralListReverseActualReverseRequiresValidInput_kernel_certificate w n r)

def structuralListReverseActualReverseHasValidOutputSentence {m} (w n r : Fin m) : Source.Sentence := ((StructuralListReverseSyntax.reverses w n r).imp ((StructuralListTraceSyntax.valid w r))).close

theorem source_structuralListReverseActualReverseHasValidOutput {m} (w n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (structuralListReverseActualReverseHasValidOutputSentence w n r) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListReverseSyntax.reverses w n r) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (StructuralListReverseSyntax.reverses w n r) := .hyp (Or.inl rfl)
  exact StructuralListReverseUnique.valid_output w n r h0

theorem structuralListReverseActualReverseHasValidOutput_kernel_certificate {m} (w n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (structuralListReverseActualReverseHasValidOutputSentence w n r)) := TheoryTransport.sentence (source_structuralListReverseActualReverseHasValidOutput w n r)

theorem native_structuralListReverseActualReverseHasValidOutput {m} (w n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (structuralListReverseActualReverseHasValidOutputSentence w n r)) := ZFReplay.replay (structuralListReverseActualReverseHasValidOutput_kernel_certificate w n r)

def structuralListReverseActualReverseFieldsExactlyReflectedSentence {m} (w n l r i j y : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListReverseSyntax.reading w n l r).imp ((StructuralReverseIndexSyntax.mirror w l i j).imp (((StructuralListFieldSyntax.field w r i y).iff (StructuralListFieldSyntax.field w n j y)))))).close

theorem source_structuralListReverseActualReverseFieldsExactlyReflected {m} (w n l r i j y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (structuralListReverseActualReverseFieldsExactlyReflectedSentence w n l r i j y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralReverseIndexSyntax.mirror w l i j) (Context.add (StructuralListReverseSyntax.reading w n l r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (StructuralListReverseSyntax.reading w n l r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (StructuralReverseIndexSyntax.mirror w l i j) := .hyp (Or.inl rfl)
  exact StructuralListReverseLaws.field_at_mirror hZ w n l r i j y h0 h1 h2

theorem structuralListReverseActualReverseFieldsExactlyReflected_kernel_certificate {m} (w n l r i j y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (structuralListReverseActualReverseFieldsExactlyReflectedSentence w n l r i j y)) := TheoryTransport.sentence (source_structuralListReverseActualReverseFieldsExactlyReflected w n l r i j y)

theorem native_structuralListReverseActualReverseFieldsExactlyReflected {m} (w n l r i j y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (structuralListReverseActualReverseFieldsExactlyReflectedSentence w n l r i j y)) := ZFReplay.replay (structuralListReverseActualReverseFieldsExactlyReflected_kernel_certificate w n l r i j y)

def structuralListReverseActualReverseSymmetricSentence {m} (w n r : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListReverseSyntax.reverses w n r).imp ((StructuralListReverseSyntax.reverses w r n)))).close

theorem source_structuralListReverseActualReverseSymmetric {m} (w n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (structuralListReverseActualReverseSymmetricSentence w n r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListReverseSyntax.reverses w n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (StructuralListReverseSyntax.reverses w n r) := .hyp (Or.inl rfl)
  exact StructuralListReverseLaws.symmetric hZ w n r h0 h1

theorem structuralListReverseActualReverseSymmetric_kernel_certificate {m} (w n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (structuralListReverseActualReverseSymmetricSentence w n r)) := TheoryTransport.sentence (source_structuralListReverseActualReverseSymmetric w n r)

theorem native_structuralListReverseActualReverseSymmetric {m} (w n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (structuralListReverseActualReverseSymmetricSentence w n r)) := ZFReplay.replay (structuralListReverseActualReverseSymmetric_kernel_certificate w n r)

def structuralListReverseActualReverseInvolutiveSentence {m} (w n r s : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListReverseSyntax.reverses w n r).imp ((StructuralListReverseSyntax.reverses w r s).imp ((Formula.equal s n))))).close

theorem source_structuralListReverseActualReverseInvolutive {m} (w n r s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (structuralListReverseActualReverseInvolutiveSentence w n r s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListReverseSyntax.reverses w r s) (Context.add (StructuralListReverseSyntax.reverses w n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (StructuralListReverseSyntax.reverses w n r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (StructuralListReverseSyntax.reverses w r s) := .hyp (Or.inl rfl)
  exact StructuralListReverseLaws.involutive hZ w n r s h0 h1 h2

theorem structuralListReverseActualReverseInvolutive_kernel_certificate {m} (w n r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (structuralListReverseActualReverseInvolutiveSentence w n r s)) := TheoryTransport.sentence (source_structuralListReverseActualReverseInvolutive w n r s)

theorem native_structuralListReverseActualReverseInvolutive {m} (w n r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (structuralListReverseActualReverseInvolutiveSentence w n r s)) := ZFReplay.replay (structuralListReverseActualReverseInvolutive_kernel_certificate w n r s)

def structuralListReverseExactNilReversalSentence {m} (w n r : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListSyntax.nilCode w n).imp (((StructuralListReverseSyntax.reverses w n r).iff (StructuralListSyntax.nilCode w r))))).close

theorem source_structuralListReverseExactNilReversal {m} (w n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (structuralListReverseExactNilReversalSentence w n r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.nilCode w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (StructuralListSyntax.nilCode w n) := .hyp (Or.inl rfl)
  exact StructuralListReverseNil.nil_iff hZ w n r h0 h1

theorem structuralListReverseExactNilReversal_kernel_certificate {m} (w n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (structuralListReverseExactNilReversalSentence w n r)) := TheoryTransport.sentence (source_structuralListReverseExactNilReversal w n r)

theorem native_structuralListReverseExactNilReversal {m} (w n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (structuralListReverseExactNilReversalSentence w n r)) := ZFReplay.replay (structuralListReverseExactNilReversal_kernel_certificate w n r)

def structuralListReverseNormalizeEveryActualLengthSentence {m} (w n l r : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListLengthSyntax.hasLength w n l).imp ((StructuralListReverseSyntax.reverses w n r).imp ((StructuralListReverseSyntax.atLength w n l r))))).close

theorem source_structuralListReverseNormalizeEveryActualLength {m} (w n l r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (structuralListReverseNormalizeEveryActualLengthSentence w n l r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListReverseSyntax.reverses w n r) (Context.add (StructuralListLengthSyntax.hasLength w n l) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (StructuralListLengthSyntax.hasLength w n l) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (StructuralListReverseSyntax.reverses w n r) := .hyp (Or.inl rfl)
  exact StructuralListReverseNil.normalize_length hZ w n l r h0 h1 h2

theorem structuralListReverseNormalizeEveryActualLength_kernel_certificate {m} (w n l r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (structuralListReverseNormalizeEveryActualLengthSentence w n l r)) := TheoryTransport.sentence (source_structuralListReverseNormalizeEveryActualLength w n l r)

theorem native_structuralListReverseNormalizeEveryActualLength {m} (w n l r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (structuralListReverseNormalizeEveryActualLengthSentence w n l r)) := ZFReplay.replay (structuralListReverseNormalizeEveryActualLength_kernel_certificate w n l r)

def structuralListReverseExactConsSnocReversalSentence {m} (w h t n l L u r : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem h w).imp ((StructuralListSyntax.consCode w h t n).imp ((StructuralListLengthSyntax.hasLength w t l).imp ((successor L l).imp ((StructuralListReverseSyntax.reverses w t u).imp (((StructuralListReverseSyntax.reverses w n r).iff (StructuralListReverseConsContract.snoc w u l L h r))))))))).close

theorem source_structuralListReverseExactConsSnocReversal {m} (w h t n l L u r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (structuralListReverseExactConsSnocReversalSentence w h t n l L u r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListReverseSyntax.reverses w t u) (Context.add (successor L l) (Context.add (StructuralListLengthSyntax.hasLength w t l) (Context.add (StructuralListSyntax.consCode w h t n) (Context.add (Formula.mem h w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (Formula.mem h w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (StructuralListSyntax.consCode w h t n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (StructuralListLengthSyntax.hasLength w t l) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (successor L l) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (StructuralListReverseSyntax.reverses w t u) := .hyp (Or.inl rfl)
  exact StructuralListReverseConsContract.cons_iff hZ w h t n l L u r h0 h1 h2 h3 h4 h5

theorem structuralListReverseExactConsSnocReversal_kernel_certificate {m} (w h t n l L u r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (structuralListReverseExactConsSnocReversalSentence w h t n l L u r)) := TheoryTransport.sentence (source_structuralListReverseExactConsSnocReversal w h t n l L u r)

theorem native_structuralListReverseExactConsSnocReversal {m} (w h t n l L u r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (structuralListReverseExactConsSnocReversalSentence w h t n l L u r)) := ZFReplay.replay (structuralListReverseExactConsSnocReversal_kernel_certificate w h t n l L u r)

def structuralListReverseActualSnocCodeUniqueSentence {m} (w u l L h r s : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListReverseConsContract.snoc w u l L h r).imp ((StructuralListReverseConsContract.snoc w u l L h s).imp ((Formula.equal r s))))).close

theorem source_structuralListReverseActualSnocCodeUnique {m} (w u l L h r s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (structuralListReverseActualSnocCodeUniqueSentence w u l L h r s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListReverseConsContract.snoc w u l L h s) (Context.add (StructuralListReverseConsContract.snoc w u l L h r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (StructuralListReverseConsContract.snoc w u l L h r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (StructuralListReverseConsContract.snoc w u l L h s) := .hyp (Or.inl rfl)
  exact StructuralListReverseConsContract.snoc_unique hZ w u l L h r s h0 h1 h2

theorem structuralListReverseActualSnocCodeUnique_kernel_certificate {m} (w u l L h r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (structuralListReverseActualSnocCodeUniqueSentence w u l L h r s)) := TheoryTransport.sentence (source_structuralListReverseActualSnocCodeUnique w u l L h r s)

theorem native_structuralListReverseActualSnocCodeUnique {m} (w u l L h r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (structuralListReverseActualSnocCodeUniqueSentence w u l L h r s)) := ZFReplay.replay (structuralListReverseActualSnocCodeUnique_kernel_certificate w u l L h r s)

end PPAC.Migration.Internal.ObjectStructuralListReverse
