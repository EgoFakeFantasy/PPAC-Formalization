import PPAC.Migration.Internal.PacketReaderInitEmpty

/-! Actual 128/0/1/Nil initialization and exact input domain, original terminal run equation and initialized empty-input return. Varint segmentation, full program bridge, Basic AST, Proof and Con remain unproved -/
namespace PPAC.Migration.Internal.ObjectPacketReaderInit
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetReaderInitActualInitialStateSentence {m} (w z o L : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((successor o z).imp ((StructuralListTraceSyntax.valid w L).imp ((PacketReaderStepSyntax.state w L z o o)))))).close

theorem source_packetReaderInitActualInitialState {m} (w z o L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInitActualInitialStateSentence w z o L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListTraceSyntax.valid w L) (Context.add (successor o z) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor o z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralListTraceSyntax.valid w L) := .hyp (Or.inl rfl)
  exact PacketReaderInitSeed.state hZ w z o L h0 h1 h2 h3

theorem packetReaderInitActualInitialState_kernel_certificate {m} (w z o L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInitActualInitialStateSentence w z o L)) := TheoryTransport.sentence (source_packetReaderInitActualInitialState w z o L)

theorem native_packetReaderInitActualInitialState {m} (w z o L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInitActualInitialStateSentence w z o L)) := ZFReplay.replay (packetReaderInitActualInitialState_kernel_certificate w z o L)

def packetReaderInitActualInitialCodeExistsSentence {m} (w z o L : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((successor o z).imp ((StructuralListTraceSyntax.valid w L).imp ((PacketReaderInitSyntax.existsSeed w z o L)))))).close

theorem source_packetReaderInitActualInitialCodeExists {m} (w z o L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInitActualInitialCodeExistsSentence w z o L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListTraceSyntax.valid w L) (Context.add (successor o z) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor o z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralListTraceSyntax.valid w L) := .hyp (Or.inl rfl)
  exact PacketReaderInitSeed.exists_seed hZ w z o L h0 h1 h2 h3

theorem packetReaderInitActualInitialCodeExists_kernel_certificate {m} (w z o L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInitActualInitialCodeExistsSentence w z o L)) := TheoryTransport.sentence (source_packetReaderInitActualInitialCodeExists w z o L)

theorem native_packetReaderInitActualInitialCodeExists {m} (w z o L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInitActualInitialCodeExistsSentence w z o L)) := ZFReplay.replay (packetReaderInitActualInitialCodeExists_kernel_certificate w z o L)

def packetReaderInitActualInitialCodeUniqueSentence {m} (w z o L n r : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderInitSyntax.seed w z o L n).imp ((PacketReaderInitSyntax.seed w z o L r).imp ((Formula.equal n r))))).close

theorem source_packetReaderInitActualInitialCodeUnique {m} (w z o L n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInitActualInitialCodeUniqueSentence w z o L n r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderInitSyntax.seed w z o L r) (Context.add (PacketReaderInitSyntax.seed w z o L n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketReaderInitSyntax.seed w z o L n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderInitSyntax.seed w z o L r) := .hyp (Or.inl rfl)
  exact PacketReaderInitSeed.unique hZ w z o L n r h0 h1 h2

theorem packetReaderInitActualInitialCodeUnique_kernel_certificate {m} (w z o L n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInitActualInitialCodeUniqueSentence w z o L n r)) := TheoryTransport.sentence (source_packetReaderInitActualInitialCodeUnique w z o L n r)

theorem native_packetReaderInitActualInitialCodeUnique {m} (w z o L n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInitActualInitialCodeUniqueSentence w z o L n r)) := ZFReplay.replay (packetReaderInitActualInitialCodeUnique_kernel_certificate w z o L n r)

def packetReaderInitActualInitialCodeNaturalSentence {m} (w z o L n : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderInitSyntax.seed w z o L n).imp ((Formula.mem n w)))).close

theorem source_packetReaderInitActualInitialCodeNatural {m} (w z o L n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInitActualInitialCodeNaturalSentence w z o L n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderInitSyntax.seed w z o L n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderInitSyntax.seed w z o L n) := .hyp (Or.inl rfl)
  exact PacketReaderInitSeed.natural hZ w z o L n h0 h1

theorem packetReaderInitActualInitialCodeNatural_kernel_certificate {m} (w z o L n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInitActualInitialCodeNaturalSentence w z o L n)) := TheoryTransport.sentence (source_packetReaderInitActualInitialCodeNatural w z o L n)

theorem native_packetReaderInitActualInitialCodeNatural {m} (w z o L n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInitActualInitialCodeNaturalSentence w z o L n)) := ZFReplay.replay (packetReaderInitActualInitialCodeNatural_kernel_certificate w z o L n)

def packetReaderInitSeededNormalizeAtActualInitialCodeSentence {m} (w B z o L n q : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderInitSyntax.seed w z o L n).imp (((PacketReaderInitSyntax.seeded w B z o L q).iff (PacketReaderReturnCodedSyntax.run w B z o n q))))).close

theorem source_packetReaderInitSeededNormalizeAtActualInitialCode {m} (w B z o L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInitSeededNormalizeAtActualInitialCodeSentence w B z o L n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderInitSyntax.seed w z o L n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderInitSyntax.seed w z o L n) := .hyp (Or.inl rfl)
  exact PacketReaderInitSeeded.at_seed hZ w B z o L n q h0 h1

theorem packetReaderInitSeededNormalizeAtActualInitialCode_kernel_certificate {m} (w B z o L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInitSeededNormalizeAtActualInitialCodeSentence w B z o L n q)) := TheoryTransport.sentence (source_packetReaderInitSeededNormalizeAtActualInitialCode w B z o L n q)

theorem native_packetReaderInitSeededNormalizeAtActualInitialCode {m} (w B z o L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInitSeededNormalizeAtActualInitialCodeSentence w B z o L n q)) := ZFReplay.replay (packetReaderInitSeededNormalizeAtActualInitialCode_kernel_certificate w B z o L n q)

def packetReaderInitSeededReturnExistsSentence {m} (w B z o L : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp ((successor o z).imp ((StructuralListTraceSyntax.valid w L).imp ((PacketReaderInitSyntax.existsSeeded w B z o L))))))).close

theorem source_packetReaderInitSeededReturnExists {m} (w B z o L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInitSeededReturnExistsSentence w B z o L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListTraceSyntax.valid w L) (Context.add (successor o z) (Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (successor o z) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (StructuralListTraceSyntax.valid w L) := .hyp (Or.inl rfl)
  exact PacketReaderInitSeeded.exists_return hZ w B z o L h0 h1 h2 h3 h4

theorem packetReaderInitSeededReturnExists_kernel_certificate {m} (w B z o L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInitSeededReturnExistsSentence w B z o L)) := TheoryTransport.sentence (source_packetReaderInitSeededReturnExists w B z o L)

theorem native_packetReaderInitSeededReturnExists {m} (w B z o L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInitSeededReturnExistsSentence w B z o L)) := ZFReplay.replay (packetReaderInitSeededReturnExists_kernel_certificate w B z o L)

def packetReaderInitSeededCandidateUniqueSentence {m} (w B z o L p q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderInitSyntax.seeded w B z o L p).imp ((PacketReaderInitSyntax.seeded w B z o L q).imp ((Formula.equal p q)))))).close

theorem source_packetReaderInitSeededCandidateUnique {m} (w B z o L p q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInitSeededCandidateUniqueSentence w B z o L p q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderInitSyntax.seeded w B z o L q) (Context.add (PacketReaderInitSyntax.seeded w B z o L p) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderInitSyntax.seeded w B z o L p) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderInitSyntax.seeded w B z o L q) := .hyp (Or.inl rfl)
  exact PacketReaderInitSeeded.unique hZ w B z o L p q h0 h1 h2 h3

theorem packetReaderInitSeededCandidateUnique_kernel_certificate {m} (w B z o L p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInitSeededCandidateUniqueSentence w B z o L p q)) := TheoryTransport.sentence (source_packetReaderInitSeededCandidateUnique w B z o L p q)

theorem native_packetReaderInitSeededCandidateUnique {m} (w B z o L p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInitSeededCandidateUniqueSentence w B z o L p q)) := ZFReplay.replay (packetReaderInitSeededCandidateUnique_kernel_certificate w B z o L p q)

def packetReaderInitSeededValueNaturalSentence {m} (w B z o L q : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderInitSyntax.seeded w B z o L q).imp ((Formula.mem q w)))).close

theorem source_packetReaderInitSeededValueNatural {m} (w B z o L q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInitSeededValueNaturalSentence w B z o L q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderInitSyntax.seeded w B z o L q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderInitSyntax.seeded w B z o L q) := .hyp (Or.inl rfl)
  exact PacketReaderInitSeeded.natural hZ w B z o L q h0 h1

theorem packetReaderInitSeededValueNatural_kernel_certificate {m} (w B z o L q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInitSeededValueNaturalSentence w B z o L q)) := TheoryTransport.sentence (source_packetReaderInitSeededValueNatural w B z o L q)

theorem native_packetReaderInitSeededValueNatural {m} (w B z o L q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInitSeededValueNaturalSentence w B z o L q)) := ZFReplay.replay (packetReaderInitSeededValueNatural_kernel_certificate w B z o L q)

def packetReaderInitSeededDomainExactlyValidInputSentence {m} (w B z o L : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp ((successor o z).imp (((PacketReaderInitSyntax.existsSeeded w B z o L).iff (StructuralListTraceSyntax.valid w L))))))).close

theorem source_packetReaderInitSeededDomainExactlyValidInput {m} (w B z o L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInitSeededDomainExactlyValidInputSentence w B z o L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor o z) (Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor o z) := .hyp (Or.inl rfl)
  exact PacketReaderInitSeeded.exact_domain hZ w B z o L h0 h1 h2 h3

theorem packetReaderInitSeededDomainExactlyValidInput_kernel_certificate {m} (w B z o L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInitSeededDomainExactlyValidInputSentence w B z o L)) := TheoryTransport.sentence (source_packetReaderInitSeededDomainExactlyValidInput w B z o L)

theorem native_packetReaderInitSeededDomainExactlyValidInput {m} (w B z o L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInitSeededDomainExactlyValidInputSentence w B z o L)) := ZFReplay.replay (packetReaderInitSeededDomainExactlyValidInput_kernel_certificate w B z o L)

def packetReaderInitFixedParserExactlyActualLiteralsSentence {m} (w B z o L q : Fin m) : Source.Sentence := ((SyntaxNumeralSyntax.numeral 128 B).imp ((empty z).imp ((successor o z).imp (((PacketReaderInitSyntax.parse w L q).iff (PacketReaderInitSyntax.seeded w B z o L q)))))).close

theorem source_packetReaderInitFixedParserExactlyActualLiterals {m} (w B z o L q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInitFixedParserExactlyActualLiteralsSentence w B z o L q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor o z) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor o z) := .hyp (Or.inl rfl)
  exact PacketReaderInitLiterals.at_literals hZ w B z o L q h0 h1 h2

theorem packetReaderInitFixedParserExactlyActualLiterals_kernel_certificate {m} (w B z o L q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInitFixedParserExactlyActualLiteralsSentence w B z o L q)) := TheoryTransport.sentence (source_packetReaderInitFixedParserExactlyActualLiterals w B z o L q)

theorem native_packetReaderInitFixedParserExactlyActualLiterals {m} (w B z o L q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInitFixedParserExactlyActualLiteralsSentence w B z o L q)) := ZFReplay.replay (packetReaderInitFixedParserExactlyActualLiterals_kernel_certificate w B z o L q)

def packetReaderInitEveryInternalInputHasInitializedReturnSentence {m} (w L : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListTraceSyntax.valid w L).imp ((PacketReaderInitSyntax.existsParse w L)))).close

theorem source_packetReaderInitEveryInternalInputHasInitializedReturn {m} (w L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInitEveryInternalInputHasInitializedReturnSentence w L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListTraceSyntax.valid w L) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (StructuralListTraceSyntax.valid w L) := .hyp (Or.inl rfl)
  exact PacketReaderInitParser.exists_return hZ w L h0 h1

theorem packetReaderInitEveryInternalInputHasInitializedReturn_kernel_certificate {m} (w L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInitEveryInternalInputHasInitializedReturnSentence w L)) := TheoryTransport.sentence (source_packetReaderInitEveryInternalInputHasInitializedReturn w L)

theorem native_packetReaderInitEveryInternalInputHasInitializedReturn {m} (w L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInitEveryInternalInputHasInitializedReturnSentence w L)) := ZFReplay.replay (packetReaderInitEveryInternalInputHasInitializedReturn_kernel_certificate w L)

def packetReaderInitInitializedCandidateUniqueSentence {m} (w L p q : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderInitSyntax.parse w L p).imp ((PacketReaderInitSyntax.parse w L q).imp ((Formula.equal p q))))).close

theorem source_packetReaderInitInitializedCandidateUnique {m} (w L p q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInitInitializedCandidateUniqueSentence w L p q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderInitSyntax.parse w L q) (Context.add (PacketReaderInitSyntax.parse w L p) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketReaderInitSyntax.parse w L p) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderInitSyntax.parse w L q) := .hyp (Or.inl rfl)
  exact PacketReaderInitParser.unique hZ w L p q h0 h1 h2

theorem packetReaderInitInitializedCandidateUnique_kernel_certificate {m} (w L p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInitInitializedCandidateUniqueSentence w L p q)) := TheoryTransport.sentence (source_packetReaderInitInitializedCandidateUnique w L p q)

theorem native_packetReaderInitInitializedCandidateUnique {m} (w L p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInitInitializedCandidateUniqueSentence w L p q)) := ZFReplay.replay (packetReaderInitInitializedCandidateUnique_kernel_certificate w L p q)

def packetReaderInitInitializedValueNaturalSentence {m} (w L q : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderInitSyntax.parse w L q).imp ((Formula.mem q w)))).close

theorem source_packetReaderInitInitializedValueNatural {m} (w L q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInitInitializedValueNaturalSentence w L q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderInitSyntax.parse w L q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderInitSyntax.parse w L q) := .hyp (Or.inl rfl)
  exact PacketReaderInitParser.natural hZ w L q h0 h1

theorem packetReaderInitInitializedValueNatural_kernel_certificate {m} (w L q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInitInitializedValueNaturalSentence w L q)) := TheoryTransport.sentence (source_packetReaderInitInitializedValueNatural w L q)

theorem native_packetReaderInitInitializedValueNatural {m} (w L q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInitInitializedValueNaturalSentence w L q)) := ZFReplay.replay (packetReaderInitInitializedValueNatural_kernel_certificate w L q)

def packetReaderInitInitializedDomainExactlyValidInputSentence {m} (w L : Fin m) : Source.Sentence := ((omega w).imp (((PacketReaderInitSyntax.existsParse w L).iff (StructuralListTraceSyntax.valid w L)))).close

theorem source_packetReaderInitInitializedDomainExactlyValidInput {m} (w L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInitInitializedDomainExactlyValidInputSentence w L) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketReaderInitParser.exact_domain hZ w L h0

theorem packetReaderInitInitializedDomainExactlyValidInput_kernel_certificate {m} (w L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInitInitializedDomainExactlyValidInputSentence w L)) := TheoryTransport.sentence (source_packetReaderInitInitializedDomainExactlyValidInput w L)

theorem native_packetReaderInitInitializedDomainExactlyValidInput {m} (w L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInitInitializedDomainExactlyValidInputSentence w L)) := ZFReplay.replay (packetReaderInitInitializedDomainExactlyValidInput_kernel_certificate w L)

def packetReaderInitInitializedObjectExistsUniqueFiberSentence {m} (w L : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListTraceSyntax.valid w L).imp ((PacketReaderInitSyntax.parseFiber w L)))).close

theorem source_packetReaderInitInitializedObjectExistsUniqueFiber {m} (w L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInitInitializedObjectExistsUniqueFiberSentence w L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListTraceSyntax.valid w L) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (StructuralListTraceSyntax.valid w L) := .hyp (Or.inl rfl)
  exact PacketReaderInitParser.exists_unique hZ w L h0 h1

theorem packetReaderInitInitializedObjectExistsUniqueFiber_kernel_certificate {m} (w L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInitInitializedObjectExistsUniqueFiberSentence w L)) := TheoryTransport.sentence (source_packetReaderInitInitializedObjectExistsUniqueFiber w L)

theorem native_packetReaderInitInitializedObjectExistsUniqueFiber {m} (w L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInitInitializedObjectExistsUniqueFiberSentence w L)) := ZFReplay.replay (packetReaderInitInitializedObjectExistsUniqueFiber_kernel_certificate w L)

def packetReaderInitFixedSuccessExactActualOptionSentence {m} (w B z o L v s a u q : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderInputSyntax.eofSuccess w z o L v s a).imp ((StructuralListReverseSyntax.reverses w a u).imp (((PacketReaderReturnSyntax.result w B z o L v s a q).iff (PacketReaderReturnSyntax.some w u q)))))).close

theorem source_packetReaderInitFixedSuccessExactActualOption {m} (w B z o L v s a u q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInitFixedSuccessExactActualOptionSentence w B z o L v s a u q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListReverseSyntax.reverses w a u) (Context.add (PacketReaderInputSyntax.eofSuccess w z o L v s a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketReaderInputSyntax.eofSuccess w z o L v s a) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (StructuralListReverseSyntax.reverses w a u) := .hyp (Or.inl rfl)
  exact PacketReaderFixedReturn.at_success hZ w B z o L v s a u q h0 h1 h2

theorem packetReaderInitFixedSuccessExactActualOption_kernel_certificate {m} (w B z o L v s a u q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInitFixedSuccessExactActualOptionSentence w B z o L v s a u q)) := TheoryTransport.sentence (source_packetReaderInitFixedSuccessExactActualOption w B z o L v s a u q)

theorem native_packetReaderInitFixedSuccessExactActualOption {m} (w B z o L v s a u q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInitFixedSuccessExactActualOptionSentence w B z o L v s a u q)) := ZFReplay.replay (packetReaderInitFixedSuccessExactActualOption_kernel_certificate w B z o L v s a u q)

def packetReaderInitFixedRejectionExactActualOptionSentence {m} (w B z o L v s a q : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderReturnSyntax.rejection w B z o L v s a).imp (((PacketReaderReturnSyntax.result w B z o L v s a q).iff (PacketReaderReturnSyntax.none w q))))).close

theorem source_packetReaderInitFixedRejectionExactActualOption {m} (w B z o L v s a q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInitFixedRejectionExactActualOptionSentence w B z o L v s a q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnSyntax.rejection w B z o L v s a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderReturnSyntax.rejection w B z o L v s a) := .hyp (Or.inl rfl)
  exact PacketReaderFixedReturn.at_rejection hZ w B z o L v s a q h0 h1

theorem packetReaderInitFixedRejectionExactActualOption_kernel_certificate {m} (w B z o L v s a q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInitFixedRejectionExactActualOptionSentence w B z o L v s a q)) := TheoryTransport.sentence (source_packetReaderInitFixedRejectionExactActualOption w B z o L v s a q)

theorem native_packetReaderInitFixedRejectionExactActualOption {m} (w B z o L v s a q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInitFixedRejectionExactActualOptionSentence w B z o L v s a q)) := ZFReplay.replay (packetReaderInitFixedRejectionExactActualOption_kernel_certificate w B z o L v s a q)

def packetReaderInitActualZeroHistoryImplementsLocalReturnSentence {m} (w B z o L v s a n q : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((successor o z).imp ((PacketReaderStateSyntax.code w L v s a n).imp ((PacketReaderReturnSyntax.result w B z o L v s a q).imp ((PacketReaderReturnCodedSyntax.run w B z o n q))))))).close

theorem source_packetReaderInitActualZeroHistoryImplementsLocalReturn {m} (w B z o L v s a n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInitActualZeroHistoryImplementsLocalReturnSentence w B z o L v s a n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnSyntax.result w B z o L v s a q) (Context.add (PacketReaderStateSyntax.code w L v s a n) (Context.add (successor o z) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (successor o z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (PacketReaderStateSyntax.code w L v s a n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketReaderReturnSyntax.result w B z o L v s a q) := .hyp (Or.inl rfl)
  exact PacketReaderTerminalZero.from_local hZ w B z o L v s a n q h0 h1 h2 h3 h4

theorem packetReaderInitActualZeroHistoryImplementsLocalReturn_kernel_certificate {m} (w B z o L v s a n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInitActualZeroHistoryImplementsLocalReturnSentence w B z o L v s a n q)) := TheoryTransport.sentence (source_packetReaderInitActualZeroHistoryImplementsLocalReturn w B z o L v s a n q)

theorem native_packetReaderInitActualZeroHistoryImplementsLocalReturn {m} (w B z o L v s a n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInitActualZeroHistoryImplementsLocalReturnSentence w B z o L v s a n q)) := ZFReplay.replay (packetReaderInitActualZeroHistoryImplementsLocalReturn_kernel_certificate w B z o L v s a n q)

def packetReaderInitActualTerminalRunEquationSentence {m} (w B z o L v s a n q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp ((successor o z).imp ((PacketReaderStateSyntax.code w L v s a n).imp ((PacketReaderTerminalSyntax.raw w B z o L v s a).imp (((PacketReaderReturnCodedSyntax.run w B z o n q).iff (PacketReaderReturnSyntax.result w B z o L v s a q))))))))).close

theorem source_packetReaderInitActualTerminalRunEquation {m} (w B z o L v s a n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInitActualTerminalRunEquationSentence w B z o L v s a n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderTerminalSyntax.raw w B z o L v s a) (Context.add (PacketReaderStateSyntax.code w L v s a n) (Context.add (successor o z) (Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (successor o z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (PacketReaderStateSyntax.code w L v s a n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (PacketReaderTerminalSyntax.raw w B z o L v s a) := .hyp (Or.inl rfl)
  exact PacketReaderTerminalZero.at_terminal hZ w B z o L v s a n q h0 h1 h2 h3 h4 h5

theorem packetReaderInitActualTerminalRunEquation_kernel_certificate {m} (w B z o L v s a n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInitActualTerminalRunEquationSentence w B z o L v s a n q)) := TheoryTransport.sentence (source_packetReaderInitActualTerminalRunEquation w B z o L v s a n q)

theorem native_packetReaderInitActualTerminalRunEquation {m} (w B z o L v s a n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInitActualTerminalRunEquationSentence w B z o L v s a n q)) := ZFReplay.replay (packetReaderInitActualTerminalRunEquation_kernel_certificate w B z o L v s a n q)

def packetReaderInitSeededEmptyInputExactSomeNilSentence {m} (w B z o L q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp ((successor o z).imp ((StructuralListSyntax.nilCode w L).imp (((PacketReaderInitSyntax.seeded w B z o L q).iff (PacketReaderReturnSyntax.some w o q)))))))).close

theorem source_packetReaderInitSeededEmptyInputExactSomeNil {m} (w B z o L q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInitSeededEmptyInputExactSomeNilSentence w B z o L q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.nilCode w L) (Context.add (successor o z) (Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (successor o z) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (StructuralListSyntax.nilCode w L) := .hyp (Or.inl rfl)
  exact PacketReaderInitEmpty.seeded_empty hZ w B z o L q h0 h1 h2 h3 h4

theorem packetReaderInitSeededEmptyInputExactSomeNil_kernel_certificate {m} (w B z o L q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInitSeededEmptyInputExactSomeNilSentence w B z o L q)) := TheoryTransport.sentence (source_packetReaderInitSeededEmptyInputExactSomeNil w B z o L q)

theorem native_packetReaderInitSeededEmptyInputExactSomeNil {m} (w B z o L q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInitSeededEmptyInputExactSomeNilSentence w B z o L q)) := ZFReplay.replay (packetReaderInitSeededEmptyInputExactSomeNil_kernel_certificate w B z o L q)

def packetReaderInitInitializedEmptyInputExactSomeNilSentence {m} (w L u q : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListSyntax.nilCode w L).imp ((StructuralListSyntax.nilCode w u).imp (((PacketReaderInitSyntax.parse w L q).iff (PacketReaderReturnSyntax.some w u q)))))).close

theorem source_packetReaderInitInitializedEmptyInputExactSomeNil {m} (w L u q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInitInitializedEmptyInputExactSomeNilSentence w L u q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.nilCode w u) (Context.add (StructuralListSyntax.nilCode w L) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (StructuralListSyntax.nilCode w L) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (StructuralListSyntax.nilCode w u) := .hyp (Or.inl rfl)
  exact PacketReaderInitEmpty.at_empty hZ w L u q h0 h1 h2

theorem packetReaderInitInitializedEmptyInputExactSomeNil_kernel_certificate {m} (w L u q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInitInitializedEmptyInputExactSomeNilSentence w L u q)) := TheoryTransport.sentence (source_packetReaderInitInitializedEmptyInputExactSomeNil w L u q)

theorem native_packetReaderInitInitializedEmptyInputExactSomeNil {m} (w L u q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInitInitializedEmptyInputExactSomeNilSentence w L u q)) := ZFReplay.replay (packetReaderInitInitializedEmptyInputExactSomeNil_kernel_certificate w L u q)

end PPAC.Migration.Internal.ObjectPacketReaderInit
