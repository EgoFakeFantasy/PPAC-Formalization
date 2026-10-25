import PPAC.Migration.Internal.PacketReaderTokensRoundtrip

/-! All internal token lists have unique independent varint encoding, exact original reader consumption and actual output order. Bounded inverse, full reader specification, Basic AST, Proof and Con remain unproved -/
namespace PPAC.Migration.Internal.ObjectPacketReaderTokens
open Source SourceAlgebra SourceLogic OmegaSyntax

def tokensReaderActualZeroUnitAffineEquationSentence {m} (w z o n : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((successor o z).imp ((Formula.mem n w).imp ((PacketAffineSyntax.equation w n z o n)))))).close

theorem source_tokensReaderActualZeroUnitAffineEquation {m} (w z o n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensReaderActualZeroUnitAffineEquationSentence w z o n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem n w) (Context.add (successor o z) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor o z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem n w) := .hyp (Or.inl rfl)
  exact PacketReaderTokenUnits.equation_zero_unit hZ w z o n h0 h1 h2 h3

theorem tokensReaderActualZeroUnitAffineEquation_kernel_certificate {m} (w z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensReaderActualZeroUnitAffineEquationSentence w z o n)) := TheoryTransport.sentence (source_tokensReaderActualZeroUnitAffineEquation w z o n)

theorem native_tokensReaderActualZeroUnitAffineEquation {m} (w z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensReaderActualZeroUnitAffineEquationSentence w z o n)) := ZFReplay.replay (tokensReaderActualZeroUnitAffineEquation_kernel_certificate w z o n)

def tokensReaderActualEmptyInputExactReturnSentence {m} (w B z o L a R p : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp ((successor o z).imp ((StructuralListTraceSyntax.valid w a).imp ((StructuralListSyntax.nilCode w L).imp ((StructuralListReverseSyntax.reverses w a R).imp (((PacketReaderEvalSyntax.eval w B z o L z o a p).iff (PacketReaderReturnSyntax.some w R p)))))))))).close

theorem source_tokensReaderActualEmptyInputExactReturn {m} (w B z o L a R p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensReaderActualEmptyInputExactReturnSentence w B z o L a R p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListReverseSyntax.reverses w a R) (Context.add (StructuralListSyntax.nilCode w L) (Context.add (StructuralListTraceSyntax.valid w a) (Context.add (successor o z) (Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (successor o z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (StructuralListTraceSyntax.valid w a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (StructuralListSyntax.nilCode w L) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (StructuralListReverseSyntax.reverses w a R) := .hyp (Or.inl rfl)
  exact PacketReaderTokenUnits.empty_eval_exact hZ w B z o L a R p h0 h1 h2 h3 h4 h5 h6

theorem tokensReaderActualEmptyInputExactReturn_kernel_certificate {m} (w B z o L a R p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensReaderActualEmptyInputExactReturnSentence w B z o L a R p)) := TheoryTransport.sentence (source_tokensReaderActualEmptyInputExactReturn w B z o L a R p)

theorem native_tokensReaderActualEmptyInputExactReturn {m} (w B z o L a R p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensReaderActualEmptyInputExactReturnSentence w B z o L a R p)) := ZFReplay.replay (tokensReaderActualEmptyInputExactReturn_kernel_certificate w B z o L a R p)

def tokensSpliceExactRightNilSentence {m} (w n e a : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListSyntax.nilCode w e).imp (((StructuralListSpliceSyntax.splice w n e a).iff ((StructuralListTraceSyntax.valid w n).conj (Formula.equal a n)))))).close

theorem source_tokensSpliceExactRightNil {m} (w n e a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensSpliceExactRightNilSentence w n e a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.nilCode w e) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (StructuralListSyntax.nilCode w e) := .hyp (Or.inl rfl)
  exact StructuralListSpliceAlgebra.right_nil_iff hZ w n e a h0 h1

theorem tokensSpliceExactRightNil_kernel_certificate {m} (w n e a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensSpliceExactRightNilSentence w n e a)) := TheoryTransport.sentence (source_tokensSpliceExactRightNil w n e a)

theorem native_tokensSpliceExactRightNil {m} (w n e a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensSpliceExactRightNilSentence w n e a)) := ZFReplay.replay (tokensSpliceExactRightNil_kernel_certificate w n e a)

def tokensSpliceAllCandidateAssociativitySentence {m} (w A B C AB BC O : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListSpliceSyntax.splice w A B AB).imp ((StructuralListSpliceSyntax.splice w B C BC).imp (((StructuralListSpliceSyntax.splice w AB C O).iff (StructuralListSpliceSyntax.splice w A BC O)))))).close

theorem source_tokensSpliceAllCandidateAssociativity {m} (w A B C AB BC O : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensSpliceAllCandidateAssociativitySentence w A B C AB BC O) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSpliceSyntax.splice w B C BC) (Context.add (StructuralListSpliceSyntax.splice w A B AB) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (StructuralListSpliceSyntax.splice w A B AB) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (StructuralListSpliceSyntax.splice w B C BC) := .hyp (Or.inl rfl)
  exact StructuralListSpliceAlgebra.associative_iff hZ w A B C AB BC O h0 h1 h2

theorem tokensSpliceAllCandidateAssociativity_kernel_certificate {m} (w A B C AB BC O : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensSpliceAllCandidateAssociativitySentence w A B C AB BC O)) := TheoryTransport.sentence (source_tokensSpliceAllCandidateAssociativity w A B C AB BC O)

theorem native_tokensSpliceAllCandidateAssociativity {m} (w A B C AB BC O : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensSpliceAllCandidateAssociativitySentence w A B C AB BC O)) := ZFReplay.replay (tokensSpliceAllCandidateAssociativity_kernel_certificate w A B C AB BC O)

def tokensSpliceExactSingletonSentence {m} (w h e S T O : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem h w).imp ((StructuralListSyntax.nilCode w e).imp ((StructuralListSyntax.consCode w h e S).imp ((StructuralListTraceSyntax.valid w T).imp (((StructuralListSpliceSyntax.splice w S T O).iff (StructuralListSyntax.consCode w h T O)))))))).close

theorem source_tokensSpliceExactSingleton {m} (w h e S T O : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensSpliceExactSingletonSentence w h e S T O) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListTraceSyntax.valid w T) (Context.add (StructuralListSyntax.consCode w h e S) (Context.add (StructuralListSyntax.nilCode w e) (Context.add (Formula.mem h w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem h w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (StructuralListSyntax.nilCode w e) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (StructuralListSyntax.consCode w h e S) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (StructuralListTraceSyntax.valid w T) := .hyp (Or.inl rfl)
  exact StructuralListSpliceAlgebra.singleton_iff hZ w h e S T O h0 h1 h2 h3 h4

theorem tokensSpliceExactSingleton_kernel_certificate {m} (w h e S T O : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensSpliceExactSingletonSentence w h e S T O)) := TheoryTransport.sentence (source_tokensSpliceExactSingleton w h e S T O)

theorem native_tokensSpliceExactSingleton {m} (w h e S T O : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensSpliceExactSingletonSentence w h e S T O)) := ZFReplay.replay (tokensSpliceExactSingleton_kernel_certificate w h e S T O)

def tokensSpliceExactSnocConsReassociationSentence {m} (w A e h S AH T HT O : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem h w).imp ((StructuralListSyntax.nilCode w e).imp ((StructuralListSyntax.consCode w h e S).imp ((StructuralListSpliceSyntax.splice w A S AH).imp ((StructuralListTraceSyntax.valid w T).imp ((StructuralListSyntax.consCode w h T HT).imp (((StructuralListSpliceSyntax.splice w AH T O).iff (StructuralListSpliceSyntax.splice w A HT O)))))))))).close

theorem source_tokensSpliceExactSnocConsReassociation {m} (w A e h S AH T HT O : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensSpliceExactSnocConsReassociationSentence w A e h S AH T HT O) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.consCode w h T HT) (Context.add (StructuralListTraceSyntax.valid w T) (Context.add (StructuralListSpliceSyntax.splice w A S AH) (Context.add (StructuralListSyntax.consCode w h e S) (Context.add (StructuralListSyntax.nilCode w e) (Context.add (Formula.mem h w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (Formula.mem h w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (StructuralListSyntax.nilCode w e) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (StructuralListSyntax.consCode w h e S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (StructuralListSpliceSyntax.splice w A S AH) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (StructuralListTraceSyntax.valid w T) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (StructuralListSyntax.consCode w h T HT) := .hyp (Or.inl rfl)
  exact StructuralListSpliceAlgebra.snoc_cons_iff hZ w A e h S AH T HT O h0 h1 h2 h3 h4 h5 h6

theorem tokensSpliceExactSnocConsReassociation_kernel_certificate {m} (w A e h S AH T HT O : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensSpliceExactSnocConsReassociationSentence w A e h S AH T HT O)) := TheoryTransport.sentence (source_tokensSpliceExactSnocConsReassociation w A e h S AH T HT O)

theorem native_tokensSpliceExactSnocConsReassociation {m} (w A e h S AH T HT O : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensSpliceExactSnocConsReassociationSentence w A e h S AH T HT O)) := ZFReplay.replay (tokensSpliceExactSnocConsReassociation_kernel_certificate w A e h S AH T HT O)

def tokensSpliceSingletonSpliceIsActualSnocSentence {m} (w n h S r l L : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem h w).imp ((StructuralListLengthSyntax.hasLength w n l).imp ((PacketVarintCanonicalRecursionSyntax.singleton w h S).imp ((StructuralListSpliceSyntax.splice w n S r).imp ((successor L l).imp ((StructuralListReverseConsContract.snoc w n l L h r)))))))).close

theorem source_tokensSpliceSingletonSpliceIsActualSnoc {m} (w n h S r l L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensSpliceSingletonSpliceIsActualSnocSentence w n h S r l L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor L l) (Context.add (StructuralListSpliceSyntax.splice w n S r) (Context.add (PacketVarintCanonicalRecursionSyntax.singleton w h S) (Context.add (StructuralListLengthSyntax.hasLength w n l) (Context.add (Formula.mem h w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h2 : Derives Δ (StructuralListLengthSyntax.hasLength w n l) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (PacketVarintCanonicalRecursionSyntax.singleton w h S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (StructuralListSpliceSyntax.splice w n S r) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (successor L l) := .hyp (Or.inl rfl)
  exact StructuralListSpliceSnoc.at_splice hZ w n h S r l L h0 h1 h2 h3 h4 h5

theorem tokensSpliceSingletonSpliceIsActualSnoc_kernel_certificate {m} (w n h S r l L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensSpliceSingletonSpliceIsActualSnocSentence w n h S r l L)) := TheoryTransport.sentence (source_tokensSpliceSingletonSpliceIsActualSnoc w n h S r l L)

theorem native_tokensSpliceSingletonSpliceIsActualSnoc {m} (w n h S r l L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensSpliceSingletonSpliceIsActualSnocSentence w n h S r l L)) := ZFReplay.replay (tokensSpliceSingletonSpliceIsActualSnoc_kernel_certificate w n h S r l L)

def tokensReaderReverseConsThroughActualSpliceSentence {m} (w h A A1 R S R1 : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem h w).imp ((StructuralListSyntax.consCode w h A A1).imp ((StructuralListReverseSyntax.reverses w A R).imp ((PacketVarintCanonicalRecursionSyntax.singleton w h S).imp ((StructuralListSpliceSyntax.splice w R S R1).imp ((StructuralListReverseSyntax.reverses w A1 R1)))))))).close

theorem source_tokensReaderReverseConsThroughActualSplice {m} (w h A A1 R S R1 : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensReaderReverseConsThroughActualSpliceSentence w h A A1 R S R1) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSpliceSyntax.splice w R S R1) (Context.add (PacketVarintCanonicalRecursionSyntax.singleton w h S) (Context.add (StructuralListReverseSyntax.reverses w A R) (Context.add (StructuralListSyntax.consCode w h A A1) (Context.add (Formula.mem h w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h2 : Derives Δ (StructuralListSyntax.consCode w h A A1) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (StructuralListReverseSyntax.reverses w A R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (PacketVarintCanonicalRecursionSyntax.singleton w h S) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (StructuralListSpliceSyntax.splice w R S R1) := .hyp (Or.inl rfl)
  exact PacketReaderOutputOrder.reverse_cons_splice hZ w h A A1 R S R1 h0 h1 h2 h3 h4 h5

theorem tokensReaderReverseConsThroughActualSplice_kernel_certificate {m} (w h A A1 R S R1 : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensReaderReverseConsThroughActualSpliceSentence w h A A1 R S R1)) := TheoryTransport.sentence (source_tokensReaderReverseConsThroughActualSplice w h A A1 R S R1)

theorem native_tokensReaderReverseConsThroughActualSplice {m} (w h A A1 R S R1 : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensReaderReverseConsThroughActualSpliceSentence w h A A1 R S R1)) := ZFReplay.replay (tokensReaderReverseConsThroughActualSplice_kernel_certificate w h A A1 R S R1)

def tokensReaderNilRemainingTokensGiveActualReverseSentence {m} (w A T O : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListSyntax.nilCode w T).imp ((PacketReaderOutputOrder.output w A T O).imp ((StructuralListReverseSyntax.reverses w A O))))).close

theorem source_tokensReaderNilRemainingTokensGiveActualReverse {m} (w A T O : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensReaderNilRemainingTokensGiveActualReverseSentence w A T O) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderOutputOrder.output w A T O) (Context.add (StructuralListSyntax.nilCode w T) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (StructuralListSyntax.nilCode w T) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderOutputOrder.output w A T O) := .hyp (Or.inl rfl)
  exact PacketReaderOutputOrder.nil_output hZ w A T O h0 h1 h2

theorem tokensReaderNilRemainingTokensGiveActualReverse_kernel_certificate {m} (w A T O : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensReaderNilRemainingTokensGiveActualReverseSentence w A T O)) := TheoryTransport.sentence (source_tokensReaderNilRemainingTokensGiveActualReverse w A T O)

theorem native_tokensReaderNilRemainingTokensGiveActualReverse {m} (w A T O : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensReaderNilRemainingTokensGiveActualReverseSentence w A T O)) := ZFReplay.replay (tokensReaderNilRemainingTokensGiveActualReverse_kernel_certificate w A T O)

def tokensReaderConsPreservesExactOutputOrderSentence {m} (w h A A1 e T HT O : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem h w).imp ((StructuralListSyntax.nilCode w e).imp ((StructuralListSyntax.consCode w h A A1).imp ((StructuralListTraceSyntax.valid w T).imp ((StructuralListSyntax.consCode w h T HT).imp ((PacketReaderOutputOrder.output w A HT O).imp ((PacketReaderOutputOrder.output w A1 T O))))))))).close

theorem source_tokensReaderConsPreservesExactOutputOrder {m} (w h A A1 e T HT O : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensReaderConsPreservesExactOutputOrderSentence w h A A1 e T HT O) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderOutputOrder.output w A HT O) (Context.add (StructuralListSyntax.consCode w h T HT) (Context.add (StructuralListTraceSyntax.valid w T) (Context.add (StructuralListSyntax.consCode w h A A1) (Context.add (StructuralListSyntax.nilCode w e) (Context.add (Formula.mem h w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (Formula.mem h w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (StructuralListSyntax.nilCode w e) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (StructuralListSyntax.consCode w h A A1) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (StructuralListTraceSyntax.valid w T) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (StructuralListSyntax.consCode w h T HT) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (PacketReaderOutputOrder.output w A HT O) := .hyp (Or.inl rfl)
  exact PacketReaderOutputCons.step hZ w h A A1 e T HT O h0 h1 h2 h3 h4 h5 h6

theorem tokensReaderConsPreservesExactOutputOrder_kernel_certificate {m} (w h A A1 e T HT O : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensReaderConsPreservesExactOutputOrderSentence w h A A1 e T HT O)) := TheoryTransport.sentence (source_tokensReaderConsPreservesExactOutputOrder w h A A1 e T HT O)

theorem native_tokensReaderConsPreservesExactOutputOrder {m} (w h A A1 e T HT O : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensReaderConsPreservesExactOutputOrderSentence w h A A1 e T HT O)) := ZFReplay.replay (tokensReaderConsPreservesExactOutputOrder_kernel_certificate w h A A1 e T HT O)

def tokensBytesSeededExactNilSentence {m} (w n t a : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListSyntax.nilCode w n).imp (((PacketTokensBytesSyntax.seeded w n t a).iff ((StructuralListTraceSyntax.valid w t).conj (Formula.equal t a)))))).close

theorem source_tokensBytesSeededExactNil {m} (w n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensBytesSeededExactNilSentence w n t a) := by
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
  exact PacketTokensBytesSeeded.nil_iff hZ w n t a h0 h1

theorem tokensBytesSeededExactNil_kernel_certificate {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensBytesSeededExactNilSentence w n t a)) := TheoryTransport.sentence (source_tokensBytesSeededExactNil w n t a)

theorem native_tokensBytesSeededExactNil {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensBytesSeededExactNilSentence w n t a)) := ZFReplay.replay (tokensBytesSeededExactNil_kernel_certificate w n t a)

def tokensBytesSeededExactConsSentence {m} (w h x n t a : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem h w).imp ((Formula.mem x w).imp ((StructuralListSyntax.consCode w h x n).imp (((PacketTokensBytesSyntax.seeded w n t a).iff (PacketTokensBytesSeeded.remaining w h x t a))))))).close

theorem source_tokensBytesSeededExactCons {m} (w h x n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensBytesSeededExactConsSentence w h x n t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.consCode w h x n) (Context.add (Formula.mem x w) (Context.add (Formula.mem h w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem h w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem x w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralListSyntax.consCode w h x n) := .hyp (Or.inl rfl)
  exact PacketTokensBytesSeeded.cons_iff hZ w h x n t a h0 h1 h2 h3

theorem tokensBytesSeededExactCons_kernel_certificate {m} (w h x n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensBytesSeededExactConsSentence w h x n t a)) := TheoryTransport.sentence (source_tokensBytesSeededExactCons w h x n t a)

theorem native_tokensBytesSeededExactCons {m} (w h x n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensBytesSeededExactConsSentence w h x n t a)) := ZFReplay.replay (tokensBytesSeededExactCons_kernel_certificate w h x n t a)

def tokensBytesSeededEveryActualInputAndTailHaveUniqueEncodingSentence {m} (w n t : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListTraceSyntax.valid w n).imp ((StructuralListTraceSyntax.valid w t).imp ((PacketTokensBytesSeededTotalSyntax.fiber w n t))))).close

theorem source_tokensBytesSeededEveryActualInputAndTailHaveUniqueEncoding {m} (w n t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensBytesSeededEveryActualInputAndTailHaveUniqueEncodingSentence w n t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListTraceSyntax.valid w t) (Context.add (StructuralListTraceSyntax.valid w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (StructuralListTraceSyntax.valid w n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (StructuralListTraceSyntax.valid w t) := .hyp (Or.inl rfl)
  exact PacketTokensBytesSeededTotal.exists_unique hZ w n t h0 h1 h2

theorem tokensBytesSeededEveryActualInputAndTailHaveUniqueEncoding_kernel_certificate {m} (w n t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensBytesSeededEveryActualInputAndTailHaveUniqueEncodingSentence w n t)) := TheoryTransport.sentence (source_tokensBytesSeededEveryActualInputAndTailHaveUniqueEncoding w n t)

theorem native_tokensBytesSeededEveryActualInputAndTailHaveUniqueEncoding {m} (w n t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensBytesSeededEveryActualInputAndTailHaveUniqueEncodingSentence w n t)) := ZFReplay.replay (tokensBytesSeededEveryActualInputAndTailHaveUniqueEncoding_kernel_certificate w n t)

def tokensBytesSeededAllCandidateOutputsUniqueSentence {m} (w n t a b : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokensBytesSyntax.seeded w n t a).imp ((PacketTokensBytesSyntax.seeded w n t b).imp ((Formula.equal a b))))).close

theorem source_tokensBytesSeededAllCandidateOutputsUnique {m} (w n t a b : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensBytesSeededAllCandidateOutputsUniqueSentence w n t a b) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokensBytesSyntax.seeded w n t b) (Context.add (PacketTokensBytesSyntax.seeded w n t a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketTokensBytesSyntax.seeded w n t a) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketTokensBytesSyntax.seeded w n t b) := .hyp (Or.inl rfl)
  exact PacketTokensBytesSeededTotal.unique hZ w n t a b h0 h1 h2

theorem tokensBytesSeededAllCandidateOutputsUnique_kernel_certificate {m} (w n t a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensBytesSeededAllCandidateOutputsUniqueSentence w n t a b)) := TheoryTransport.sentence (source_tokensBytesSeededAllCandidateOutputsUnique w n t a b)

theorem native_tokensBytesSeededAllCandidateOutputsUnique {m} (w n t a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensBytesSeededAllCandidateOutputsUniqueSentence w n t a b)) := ZFReplay.replay (tokensBytesSeededAllCandidateOutputsUnique_kernel_certificate w n t a b)

def tokensBytesIndependentEncodingExactNilSentence {m} (w n a : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListSyntax.nilCode w n).imp (((PacketTokensBytes.encoded w n a).iff (StructuralListSyntax.nilCode w a))))).close

theorem source_tokensBytesIndependentEncodingExactNil {m} (w n a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensBytesIndependentEncodingExactNilSentence w n a) := by
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
  exact PacketTokensBytes.nil_iff hZ w n a h0 h1

theorem tokensBytesIndependentEncodingExactNil_kernel_certificate {m} (w n a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensBytesIndependentEncodingExactNilSentence w n a)) := TheoryTransport.sentence (source_tokensBytesIndependentEncodingExactNil w n a)

theorem native_tokensBytesIndependentEncodingExactNil {m} (w n a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensBytesIndependentEncodingExactNilSentence w n a)) := ZFReplay.replay (tokensBytesIndependentEncodingExactNil_kernel_certificate w n a)

def tokensBytesIndependentEncodingExactConsSentence {m} (w h x n a : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem h w).imp ((Formula.mem x w).imp ((StructuralListSyntax.consCode w h x n).imp (((PacketTokensBytes.encoded w n a).iff (PacketTokensBytes.consCase w h x a))))))).close

theorem source_tokensBytesIndependentEncodingExactCons {m} (w h x n a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensBytesIndependentEncodingExactConsSentence w h x n a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.consCode w h x n) (Context.add (Formula.mem x w) (Context.add (Formula.mem h w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem h w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem x w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralListSyntax.consCode w h x n) := .hyp (Or.inl rfl)
  exact PacketTokensBytes.cons_iff hZ w h x n a h0 h1 h2 h3

theorem tokensBytesIndependentEncodingExactCons_kernel_certificate {m} (w h x n a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensBytesIndependentEncodingExactConsSentence w h x n a)) := TheoryTransport.sentence (source_tokensBytesIndependentEncodingExactCons w h x n a)

theorem native_tokensBytesIndependentEncodingExactCons {m} (w h x n a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensBytesIndependentEncodingExactConsSentence w h x n a)) := ZFReplay.replay (tokensBytesIndependentEncodingExactCons_kernel_certificate w h x n a)

def tokensBytesIndependentEncodingRequiresActualInputSentence {m} (w n a : Fin m) : Source.Sentence := ((PacketTokensBytes.encoded w n a).imp ((StructuralListTraceSyntax.valid w n))).close

theorem source_tokensBytesIndependentEncodingRequiresActualInput {m} (w n a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensBytesIndependentEncodingRequiresActualInputSentence w n a) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokensBytes.encoded w n a) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (PacketTokensBytes.encoded w n a) := .hyp (Or.inl rfl)
  exact PacketTokensBytes.input_valid w n a h0

theorem tokensBytesIndependentEncodingRequiresActualInput_kernel_certificate {m} (w n a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensBytesIndependentEncodingRequiresActualInputSentence w n a)) := TheoryTransport.sentence (source_tokensBytesIndependentEncodingRequiresActualInput w n a)

theorem native_tokensBytesIndependentEncodingRequiresActualInput {m} (w n a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensBytesIndependentEncodingRequiresActualInputSentence w n a)) := ZFReplay.replay (tokensBytesIndependentEncodingRequiresActualInput_kernel_certificate w n a)

def tokensBytesIndependentEncodingRequiresActualOutputSentence {m} (w n a : Fin m) : Source.Sentence := ((PacketTokensBytes.encoded w n a).imp ((StructuralListTraceSyntax.valid w a))).close

theorem source_tokensBytesIndependentEncodingRequiresActualOutput {m} (w n a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensBytesIndependentEncodingRequiresActualOutputSentence w n a) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokensBytes.encoded w n a) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (PacketTokensBytes.encoded w n a) := .hyp (Or.inl rfl)
  exact PacketTokensBytes.output_valid w n a h0

theorem tokensBytesIndependentEncodingRequiresActualOutput_kernel_certificate {m} (w n a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensBytesIndependentEncodingRequiresActualOutputSentence w n a)) := TheoryTransport.sentence (source_tokensBytesIndependentEncodingRequiresActualOutput w n a)

theorem native_tokensBytesIndependentEncodingRequiresActualOutput {m} (w n a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensBytesIndependentEncodingRequiresActualOutputSentence w n a)) := ZFReplay.replay (tokensBytesIndependentEncodingRequiresActualOutput_kernel_certificate w n a)

def tokensBytesEveryActualInputHasUniqueIndependentEncodingSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListTraceSyntax.valid w n).imp ((PacketTokensBytes.fiber w n)))).close

theorem source_tokensBytesEveryActualInputHasUniqueIndependentEncoding {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensBytesEveryActualInputHasUniqueIndependentEncodingSentence w n) := by
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
  exact PacketTokensBytes.exists_unique hZ w n h0 h1

theorem tokensBytesEveryActualInputHasUniqueIndependentEncoding_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensBytesEveryActualInputHasUniqueIndependentEncodingSentence w n)) := TheoryTransport.sentence (source_tokensBytesEveryActualInputHasUniqueIndependentEncoding w n)

theorem native_tokensBytesEveryActualInputHasUniqueIndependentEncoding {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensBytesEveryActualInputHasUniqueIndependentEncodingSentence w n)) := ZFReplay.replay (tokensBytesEveryActualInputHasUniqueIndependentEncoding_kernel_certificate w n)

def tokensBytesIndependentEncodingExactDomainSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp (((PacketTokensBytes.fiber w n).iff (StructuralListTraceSyntax.valid w n)))).close

theorem source_tokensBytesIndependentEncodingExactDomain {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensBytesIndependentEncodingExactDomainSentence w n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketTokensBytes.fiber_iff hZ w n h0

theorem tokensBytesIndependentEncodingExactDomain_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensBytesIndependentEncodingExactDomainSentence w n)) := TheoryTransport.sentence (source_tokensBytesIndependentEncodingExactDomain w n)

theorem native_tokensBytesIndependentEncodingExactDomain {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensBytesIndependentEncodingExactDomainSentence w n)) := ZFReplay.replay (tokensBytesIndependentEncodingExactDomain_kernel_certificate w n)

def tokensBytesIndependentEncodingAllCandidateOutputsUniqueSentence {m} (w n a b : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokensBytes.encoded w n a).imp ((PacketTokensBytes.encoded w n b).imp ((Formula.equal a b))))).close

theorem source_tokensBytesIndependentEncodingAllCandidateOutputsUnique {m} (w n a b : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensBytesIndependentEncodingAllCandidateOutputsUniqueSentence w n a b) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokensBytes.encoded w n b) (Context.add (PacketTokensBytes.encoded w n a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketTokensBytes.encoded w n a) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketTokensBytes.encoded w n b) := .hyp (Or.inl rfl)
  exact PacketTokensBytes.unique hZ w n a b h0 h1 h2

theorem tokensBytesIndependentEncodingAllCandidateOutputsUnique_kernel_certificate {m} (w n a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensBytesIndependentEncodingAllCandidateOutputsUniqueSentence w n a b)) := TheoryTransport.sentence (source_tokensBytesIndependentEncodingAllCandidateOutputsUnique w n a b)

theorem native_tokensBytesIndependentEncodingAllCandidateOutputsUnique {m} (w n a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensBytesIndependentEncodingAllCandidateOutputsUniqueSentence w n a b)) := ZFReplay.replay (tokensBytesIndependentEncodingAllCandidateOutputsUnique_kernel_certificate w n a b)

def tokensReaderAllInternalTokenListPropertiesSentence {m} (w B z o : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((empty z).imp ((successor o z).imp ((PacketReaderTokensSyntax.allProperties w B z o)))))).close

theorem source_tokensReaderAllInternalTokenListProperties {m} (w B z o : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensReaderAllInternalTokenListPropertiesSentence w B z o) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor o z) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor o z) := .hyp (Or.inl rfl)
  exact PacketReaderTokensInduction.all_properties hZ w B z o h0 h1 h2 h3

theorem tokensReaderAllInternalTokenListProperties_kernel_certificate {m} (w B z o : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensReaderAllInternalTokenListPropertiesSentence w B z o)) := TheoryTransport.sentence (source_tokensReaderAllInternalTokenListProperties w B z o)

theorem native_tokensReaderAllInternalTokenListProperties {m} (w B z o : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensReaderAllInternalTokenListPropertiesSentence w B z o)) := ZFReplay.replay (tokensReaderAllInternalTokenListProperties_kernel_certificate w B z o)

def tokensReaderAllInternalEncodedSegmentsAndOutputOrderSentence {m} (w B z o n bytes A O p : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((empty z).imp ((successor o z).imp ((StructuralListTraceSyntax.valid w n).imp ((StructuralListTraceSyntax.valid w A).imp ((PacketTokensBytes.encoded w n bytes).imp ((PacketReaderOutputOrder.output w A n O).imp ((PacketReaderTokensSyntax.agreement w B z o bytes A O p)))))))))).close

theorem source_tokensReaderAllInternalEncodedSegmentsAndOutputOrder {m} (w B z o n bytes A O p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensReaderAllInternalEncodedSegmentsAndOutputOrderSentence w B z o n bytes A O p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderOutputOrder.output w A n O) (Context.add (PacketTokensBytes.encoded w n bytes) (Context.add (StructuralListTraceSyntax.valid w A) (Context.add (StructuralListTraceSyntax.valid w n) (Context.add (successor o z) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (successor o z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (StructuralListTraceSyntax.valid w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (StructuralListTraceSyntax.valid w A) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (PacketTokensBytes.encoded w n bytes) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (PacketReaderOutputOrder.output w A n O) := .hyp (Or.inl rfl)
  exact PacketReaderTokensInduction.tokens hZ w B z o n bytes A O p h0 h1 h2 h3 h4 h5 h6 h7

theorem tokensReaderAllInternalEncodedSegmentsAndOutputOrder_kernel_certificate {m} (w B z o n bytes A O p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensReaderAllInternalEncodedSegmentsAndOutputOrderSentence w B z o n bytes A O p)) := TheoryTransport.sentence (source_tokensReaderAllInternalEncodedSegmentsAndOutputOrder w B z o n bytes A O p)

theorem native_tokensReaderAllInternalEncodedSegmentsAndOutputOrder {m} (w B z o n bytes A O p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensReaderAllInternalEncodedSegmentsAndOutputOrderSentence w B z o n bytes A O p)) := ZFReplay.replay (tokensReaderAllInternalEncodedSegmentsAndOutputOrder_kernel_certificate w B z o n bytes A O p)

def tokensReaderInitializedExactOriginalTokensSentence {m} (w n bytes p : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokensBytes.encoded w n bytes).imp (((PacketReaderInitSyntax.parse w bytes p).iff (PacketReaderReturnSyntax.some w n p))))).close

theorem source_tokensReaderInitializedExactOriginalTokens {m} (w n bytes p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensReaderInitializedExactOriginalTokensSentence w n bytes p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokensBytes.encoded w n bytes) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketTokensBytes.encoded w n bytes) := .hyp (Or.inl rfl)
  exact PacketReaderTokensInitialized.at_encoded hZ w n bytes p h0 h1

theorem tokensReaderInitializedExactOriginalTokens_kernel_certificate {m} (w n bytes p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensReaderInitializedExactOriginalTokensSentence w n bytes p)) := TheoryTransport.sentence (source_tokensReaderInitializedExactOriginalTokens w n bytes p)

theorem native_tokensReaderInitializedExactOriginalTokens {m} (w n bytes p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensReaderInitializedExactOriginalTokensSentence w n bytes p)) := ZFReplay.replay (tokensReaderInitializedExactOriginalTokens_kernel_certificate w n bytes p)

def tokensReaderUniqueActualEncodedInputAndAllReturnsSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListTraceSyntax.valid w n).imp ((PacketReaderTokensRoundtrip.complete w n)))).close

theorem source_tokensReaderUniqueActualEncodedInputAndAllReturns {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensReaderUniqueActualEncodedInputAndAllReturnsSentence w n) := by
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
  exact PacketReaderTokensRoundtrip.exists_unique hZ w n h0 h1

theorem tokensReaderUniqueActualEncodedInputAndAllReturns_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensReaderUniqueActualEncodedInputAndAllReturnsSentence w n)) := TheoryTransport.sentence (source_tokensReaderUniqueActualEncodedInputAndAllReturns w n)

theorem native_tokensReaderUniqueActualEncodedInputAndAllReturns {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensReaderUniqueActualEncodedInputAndAllReturnsSentence w n)) := ZFReplay.replay (tokensReaderUniqueActualEncodedInputAndAllReturns_kernel_certificate w n)

end PPAC.Migration.Internal.ObjectPacketReaderTokens
