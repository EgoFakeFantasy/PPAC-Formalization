import PPAC.Migration.Internal.SyntaxForallClosureOutput

/-! Arbitrary internal closure counts and exact scope typing in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectForallClosure
open Source SourceAlgebra SourceLogic OmegaSyntax

def unaryIterationExistsUniqueSentence {m} (tag : Nat) (w a n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp ((Formula.mem n w).imp ((SyntaxUnaryIterationSyntax.fiber tag w a n))))).close

theorem source_unaryIterationExistsUnique {m} (tag : Nat) (w a n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (unaryIterationExistsUniqueSentence tag w a n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem n w) (Context.add (Formula.mem a w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem a w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem n w) := .hyp (Or.inl rfl)
  exact SyntaxUnaryIterationCore.exists_unique hZ tag w a n h0 h1 h2

theorem unaryIterationExistsUnique_kernel_certificate {m} (tag : Nat) (w a n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (unaryIterationExistsUniqueSentence tag w a n)) := TheoryTransport.sentence (source_unaryIterationExistsUnique tag w a n)

theorem native_unaryIterationExistsUnique {m} (tag : Nat) (w a n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (unaryIterationExistsUniqueSentence tag w a n)) := ZFReplay.replay (unaryIterationExistsUnique_kernel_certificate tag w a n)

def unaryIterationNaturalRangeSentence {m} (tag : Nat) (w a n y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp ((SyntaxUnaryIterationSyntax.iterate tag w a n y).imp ((Formula.mem y w))))).close

theorem source_unaryIterationNaturalRange {m} (tag : Nat) (w a n y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (unaryIterationNaturalRangeSentence tag w a n y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxUnaryIterationSyntax.iterate tag w a n y) (Context.add (Formula.mem a w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem a w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxUnaryIterationSyntax.iterate tag w a n y) := .hyp (Or.inl rfl)
  exact SyntaxUnaryIterationCore.range hZ tag w a n y h0 h1 h2

theorem unaryIterationNaturalRange_kernel_certificate {m} (tag : Nat) (w a n y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (unaryIterationNaturalRangeSentence tag w a n y)) := TheoryTransport.sentence (source_unaryIterationNaturalRange tag w a n y)

theorem native_unaryIterationNaturalRange {m} (tag : Nat) (w a n y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (unaryIterationNaturalRangeSentence tag w a n y)) := ZFReplay.replay (unaryIterationNaturalRange_kernel_certificate tag w a n y)

def unaryIterationUniqueSentence {m} (tag : Nat) (w a n y z : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((SyntaxUnaryIterationSyntax.iterate tag w a n y).imp ((SyntaxUnaryIterationSyntax.iterate tag w a n z).imp ((Formula.equal y z)))))).close

theorem source_unaryIterationUnique {m} (tag : Nat) (w a n y z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (unaryIterationUniqueSentence tag w a n y z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxUnaryIterationSyntax.iterate tag w a n z) (Context.add (SyntaxUnaryIterationSyntax.iterate tag w a n y) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxUnaryIterationSyntax.iterate tag w a n y) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxUnaryIterationSyntax.iterate tag w a n z) := .hyp (Or.inl rfl)
  exact SyntaxUnaryIterationCore.unique hZ tag w a n y z h0 h1 h2 h3

theorem unaryIterationUnique_kernel_certificate {m} (tag : Nat) (w a n y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (unaryIterationUniqueSentence tag w a n y z)) := TheoryTransport.sentence (source_unaryIterationUnique tag w a n y z)

theorem native_unaryIterationUnique {m} (tag : Nat) (w a n y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (unaryIterationUniqueSentence tag w a n y z)) := ZFReplay.replay (unaryIterationUnique_kernel_certificate tag w a n y z)

def unaryIterationZeroIffSentence {m} (tag : Nat) (w a z y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp ((empty z).imp (((SyntaxUnaryIterationSyntax.iterate tag w a z y).iff (.equal y a)))))).close

theorem source_unaryIterationZeroIff {m} (tag : Nat) (w a z y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (unaryIterationZeroIffSentence tag w a z y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (Formula.mem a w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem a w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact SyntaxUnaryIterationLaws.zero_iff hZ tag w a z y h0 h1 h2

theorem unaryIterationZeroIff_kernel_certificate {m} (tag : Nat) (w a z y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (unaryIterationZeroIffSentence tag w a z y)) := TheoryTransport.sentence (source_unaryIterationZeroIff tag w a z y)

theorem native_unaryIterationZeroIff {m} (tag : Nat) (w a z y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (unaryIterationZeroIffSentence tag w a z y)) := ZFReplay.replay (unaryIterationZeroIff_kernel_certificate tag w a z y)

def unaryIterationSuccessorIffSentence {m} (tag : Nat) (w a n s y z : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp ((Formula.mem n w).imp ((successor s n).imp ((SyntaxUnaryIterationSyntax.iterate tag w a n y).imp (((SyntaxUnaryIterationSyntax.iterate tag w a s z).iff (SyntaxNodeSyntax.constructor 1 tag w (fun _ => y) z)))))))).close

theorem source_unaryIterationSuccessorIff {m} (tag : Nat) (w a n s y z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (unaryIterationSuccessorIffSentence tag w a n s y z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxUnaryIterationSyntax.iterate tag w a n y) (Context.add (successor s n) (Context.add (Formula.mem n w) (Context.add (Formula.mem a w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem a w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (successor s n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxUnaryIterationSyntax.iterate tag w a n y) := .hyp (Or.inl rfl)
  exact SyntaxUnaryIterationLaws.successor_iff hZ tag w a n s y z h0 h1 h2 h3 h4

theorem unaryIterationSuccessorIff_kernel_certificate {m} (tag : Nat) (w a n s y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (unaryIterationSuccessorIffSentence tag w a n s y z)) := TheoryTransport.sentence (source_unaryIterationSuccessorIff tag w a n s y z)

theorem native_unaryIterationSuccessorIff {m} (tag : Nat) (w a n s y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (unaryIterationSuccessorIffSentence tag w a n s y z)) := ZFReplay.replay (unaryIterationSuccessorIff_kernel_certificate tag w a n s y z)

def unaryIterationAllInternalCountsSentence {m} (tag : Nat) (w a : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp ((.all ((Formula.mem (Fin.last m) w.castSucc).imp (SyntaxUnaryIterationSyntax.fiber tag w.castSucc a.castSucc (Fin.last m))))))).close

theorem source_unaryIterationAllInternalCounts {m} (tag : Nat) (w a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (unaryIterationAllInternalCountsSentence tag w a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem a w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem a w) := .hyp (Or.inl rfl)
  exact SyntaxUnaryIterationLaws.all_internal_counts hZ tag w a h0 h1

theorem unaryIterationAllInternalCounts_kernel_certificate {m} (tag : Nat) (w a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (unaryIterationAllInternalCountsSentence tag w a)) := TheoryTransport.sentence (source_unaryIterationAllInternalCounts tag w a)

theorem native_unaryIterationAllInternalCounts {m} (tag : Nat) (w a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (unaryIterationAllInternalCountsSentence tag w a)) := ZFReplay.replay (unaryIterationAllInternalCounts_kernel_certificate tag w a)

def forallClosureUniformTypingSentence {m} (w a source f : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp ((Formula.mem f w).imp ((.all ((Formula.mem (Fin.last m) w.castSucc).imp (SyntaxForallClosureTypingSyntax.correct w.castSucc a.castSucc source.castSucc f.castSucc (Fin.last m)))))))).close

theorem source_forallClosureUniformTyping {m} (w a source f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallClosureUniformTypingSentence w a source f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem f w) (Context.add (Formula.mem a w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem a w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem f w) := .hyp (Or.inl rfl)
  exact SyntaxForallClosureTyping.all_correct hZ w a source f h0 h1 h2

theorem forallClosureUniformTyping_kernel_certificate {m} (w a source f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallClosureUniformTypingSentence w a source f)) := TheoryTransport.sentence (source_forallClosureUniformTyping w a source f)

theorem native_forallClosureUniformTyping {m} (w a source f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallClosureUniformTypingSentence w a source f)) := ZFReplay.replay (forallClosureUniformTyping_kernel_certificate w a source f)

def forallClosureTypingIffSentence {m} (w a source f n b y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp ((Formula.mem f w).imp ((Formula.mem n w).imp ((Formula.mem b w).imp ((NaturalAdditionSyntax.sum w n b source).imp ((SyntaxUnaryIterationSyntax.forallClosure w a n y).imp (((FormulaCodeSyntax.formulaCode w y b f).iff (FormulaCodeSyntax.formulaCode w a source f)))))))))).close

theorem source_forallClosureTypingIff {m} (w a source f n b y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallClosureTypingIffSentence w a source f n b y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxUnaryIterationSyntax.forallClosure w a n y) (Context.add (NaturalAdditionSyntax.sum w n b source) (Context.add (Formula.mem b w) (Context.add (Formula.mem n w) (Context.add (Formula.mem f w) (Context.add (Formula.mem a w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h1 : Derives Δ (Formula.mem a w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (Formula.mem f w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (NaturalAdditionSyntax.sum w n b source) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxUnaryIterationSyntax.forallClosure w a n y) := .hyp (Or.inl rfl)
  exact SyntaxForallClosureTyping.typed_iff hZ w a source f n b y h0 h1 h2 h3 h4 h5 h6

theorem forallClosureTypingIff_kernel_certificate {m} (w a source f n b y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallClosureTypingIffSentence w a source f n b y)) := TheoryTransport.sentence (source_forallClosureTypingIff w a source f n b y)

theorem native_forallClosureTypingIff {m} (w a source f n b y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallClosureTypingIffSentence w a source f n b y)) := ZFReplay.replay (forallClosureTypingIff_kernel_certificate w a source f n b y)

def forallClosureClosedIffSentence {m} (w a n z y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp ((Formula.mem n w).imp ((empty z).imp ((SyntaxUnaryIterationSyntax.forallClosure w a n y).imp (((FormulaCodeSyntax.formulaCode w y z z).iff (FormulaCodeSyntax.formulaCode w a n z)))))))).close

theorem source_forallClosureClosedIff {m} (w a n z y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallClosureClosedIffSentence w a n z y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxUnaryIterationSyntax.forallClosure w a n y) (Context.add (empty z) (Context.add (Formula.mem n w) (Context.add (Formula.mem a w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem a w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxUnaryIterationSyntax.forallClosure w a n y) := .hyp (Or.inl rfl)
  exact SyntaxForallClosureOutput.closed_iff hZ w a n z y h0 h1 h2 h3 h4

theorem forallClosureClosedIff_kernel_certificate {m} (w a n z y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallClosureClosedIffSentence w a n z y)) := TheoryTransport.sentence (source_forallClosureClosedIff w a n z y)

theorem native_forallClosureClosedIff {m} (w a n z y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallClosureClosedIffSentence w a n z y)) := ZFReplay.replay (forallClosureClosedIff_kernel_certificate w a n z y)

def forallClosureClosedExistsUniqueSentence {m} (w a n z : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((FormulaCodeSyntax.formulaCode w a n z).imp ((SyntaxForallClosureOutput.fiber w a n z))))).close

theorem source_forallClosureClosedExistsUnique {m} (w a n z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallClosureClosedExistsUniqueSentence w a n z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w a n z) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FormulaCodeSyntax.formulaCode w a n z) := .hyp (Or.inl rfl)
  exact SyntaxForallClosureOutput.closed_exists_unique hZ w a n z h0 h1 h2

theorem forallClosureClosedExistsUnique_kernel_certificate {m} (w a n z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallClosureClosedExistsUniqueSentence w a n z)) := TheoryTransport.sentence (source_forallClosureClosedExistsUnique w a n z)

theorem native_forallClosureClosedExistsUnique {m} (w a n z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallClosureClosedExistsUniqueSentence w a n z)) := ZFReplay.replay (forallClosureClosedExistsUnique_kernel_certificate w a n z)

def forallClosureAllInternalCountsSentence {m} (w a : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp ((.all ((Formula.mem (Fin.last m) w.castSucc).imp (SyntaxUnaryIterationSyntax.fiber 9 w.castSucc a.castSucc (Fin.last m))))))).close

theorem source_forallClosureAllInternalCounts {m} (w a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallClosureAllInternalCountsSentence w a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem a w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem a w) := .hyp (Or.inl rfl)
  exact SyntaxUnaryIterationLaws.all_internal_counts hZ 9 w a h0 h1

theorem forallClosureAllInternalCounts_kernel_certificate {m} (w a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallClosureAllInternalCountsSentence w a)) := TheoryTransport.sentence (source_forallClosureAllInternalCounts w a)

theorem native_forallClosureAllInternalCounts {m} (w a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallClosureAllInternalCountsSentence w a)) := ZFReplay.replay (forallClosureAllInternalCounts_kernel_certificate w a)

end PPAC.Migration.Internal.ObjectForallClosure
