import PPAC.Migration.Internal.SyntaxRenameStateSystem

/-! 实际映射自然码、量词码提升和七自然字段状态及解码的原nativeZF闭句。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxMapCodeState
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxMapCodeSyntax (encoded mapCode)
open SyntaxMapLiftSyntax (codedLift outputAt existsLiftCode)
open SyntaxRenameStateSyntax (seven cell legal state equalParams uniqueParams recognized decodedFiber stateFiber)

def omegaSequenceSentence {m} (w r a c : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIndexMapSyntax.indexMap w r a c).imp ((SequenceSyntax.sequence r a w)))).close

theorem source_omegaSequence {m} (w r a c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (omegaSequenceSentence w r a c) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIndexMapSyntax.indexMap w r a c) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxIndexMapSyntax.indexMap w r a c) := .hyp (Or.inl rfl)
  exact SyntaxMapCode.omega_sequence hZ w r a c h0 h1

theorem omegaSequence_kernel_certificate {m} (w r a c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (omegaSequenceSentence w r a c)) := TheoryTransport.sentence (source_omegaSequence w r a c)

theorem native_omegaSequence {m} (w r a c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (omegaSequenceSentence w r a c)) := ZFReplay.replay (omegaSequence_kernel_certificate w r a c)

def codeNaturalSentence {m} (w r a c k : Fin m) : Source.Sentence := ((encoded w r a c k).imp ((Formula.mem k w))).close

theorem source_codeNatural {m} (w r a c k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeNaturalSentence w r a c k) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (encoded w r a c k) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (encoded w r a c k) := .hyp (Or.inl rfl)
  exact SyntaxMapCode.code_natural w r a c k h0

theorem codeNatural_kernel_certificate {m} (w r a c k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeNaturalSentence w r a c k)) := TheoryTransport.sentence (source_codeNatural w r a c k)

theorem native_codeNatural {m} (w r a c k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeNaturalSentence w r a c k)) := ZFReplay.replay (codeNatural_kernel_certificate w r a c k)

def codeValidSentence {m} (w r a c k : Fin m) : Source.Sentence := ((encoded w r a c k).imp ((StructuralListTraceSyntax.valid w k))).close

theorem source_codeValid {m} (w r a c k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeValidSentence w r a c k) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (encoded w r a c k) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (encoded w r a c k) := .hyp (Or.inl rfl)
  exact SyntaxMapCode.code_valid w r a c k h0

theorem codeValid_kernel_certificate {m} (w r a c k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeValidSentence w r a c k)) := TheoryTransport.sentence (source_codeValid w r a c k)

theorem native_codeValid {m} (w r a c k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeValidSentence w r a c k)) := ZFReplay.replay (codeValid_kernel_certificate w r a c k)

def uniqueCodeSentence {m} (w r a c k l : Fin m) : Source.Sentence := ((omega w).imp ((encoded w r a c k).imp ((encoded w r a c l).imp ((Formula.equal k l))))).close

theorem source_uniqueCode {m} (w r a c k l : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniqueCodeSentence w r a c k l) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (encoded w r a c l) (Context.add (encoded w r a c k) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (encoded w r a c k) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (encoded w r a c l) := .hyp (Or.inl rfl)
  exact SyntaxMapCode.unique_code hZ w r a c k l h0 h1 h2

theorem uniqueCode_kernel_certificate {m} (w r a c k l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniqueCodeSentence w r a c k l)) := TheoryTransport.sentence (source_uniqueCode w r a c k l)

theorem native_uniqueCode {m} (w r a c k l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniqueCodeSentence w r a c k l)) := ZFReplay.replay (uniqueCode_kernel_certificate w r a c k l)

def uniqueGraphSentence {m} (w r s a c k : Fin m) : Source.Sentence := ((encoded w r a c k).imp ((encoded w s a c k).imp ((Formula.equal r s)))).close

theorem source_uniqueGraph {m} (w r s a c k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniqueGraphSentence w r s a c k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (encoded w s a c k) (Context.add (encoded w r a c k) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (encoded w r a c k) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (encoded w s a c k) := .hyp (Or.inl rfl)
  exact SyntaxMapCode.unique_graph hZ w r s a c k h0 h1

theorem uniqueGraph_kernel_certificate {m} (w r s a c k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniqueGraphSentence w r s a c k)) := TheoryTransport.sentence (source_uniqueGraph w r s a c k)

theorem native_uniqueGraph {m} (w r s a c k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniqueGraphSentence w r s a c k)) := ZFReplay.replay (uniqueGraph_kernel_certificate w r s a c k)

def sourceGraphRecoverySentence {m} (w r s a b c d k : Fin m) : Source.Sentence := ((omega w).imp ((encoded w r a c k).imp ((encoded w s b d k).imp (((Formula.equal b a).conj (.equal s r)))))).close

theorem source_sourceGraphRecovery {m} (w r s a b c d k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (sourceGraphRecoverySentence w r s a b c d k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (encoded w s b d k) (Context.add (encoded w r a c k) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (encoded w r a c k) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (encoded w s b d k) := .hyp (Or.inl rfl)
  exact SyntaxMapCode.source_and_graph_recovery hZ w r s a b c d k h0 h1 h2

theorem sourceGraphRecovery_kernel_certificate {m} (w r s a b c d k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (sourceGraphRecoverySentence w r s a b c d k)) := TheoryTransport.sentence (source_sourceGraphRecovery w r s a b c d k)

theorem native_sourceGraphRecovery {m} (w r s a b c d k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (sourceGraphRecoverySentence w r s a b c d k)) := ZFReplay.replay (sourceGraphRecovery_kernel_certificate w r s a b c d k)

def existsMapCodeSentence {m} (w r a c : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIndexMapSyntax.indexMap w r a c).imp ((SyntaxMapCodeSyntax.existsCode w r a c)))).close

theorem source_existsMapCode {m} (w r a c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsMapCodeSentence w r a c) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIndexMapSyntax.indexMap w r a c) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxIndexMapSyntax.indexMap w r a c) := .hyp (Or.inl rfl)
  exact SyntaxMapCodeExistence.exists_code hZ w r a c h0 h1

theorem existsMapCode_kernel_certificate {m} (w r a c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsMapCodeSentence w r a c)) := TheoryTransport.sentence (source_existsMapCode w r a c)

theorem native_existsMapCode {m} (w r a c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsMapCodeSentence w r a c)) := ZFReplay.replay (existsMapCode_kernel_certificate w r a c)

def codeFiberSentence {m} (w r a c : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIndexMapSyntax.indexMap w r a c).imp ((SyntaxMapCodeSyntax.codeFiber w r a c)))).close

theorem source_codeFiber {m} (w r a c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeFiberSentence w r a c) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIndexMapSyntax.indexMap w r a c) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxIndexMapSyntax.indexMap w r a c) := .hyp (Or.inl rfl)
  exact SyntaxMapCodeExistence.actual_code_fiber hZ w r a c h0 h1

theorem codeFiber_kernel_certificate {m} (w r a c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeFiberSentence w r a c)) := TheoryTransport.sentence (source_codeFiber w r a c)

theorem native_codeFiber {m} (w r a c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeFiberSentence w r a c)) := ZFReplay.replay (codeFiber_kernel_certificate w r a c)

def mapNaturalSentence {m} (w a c k : Fin m) : Source.Sentence := ((mapCode w a c k).imp ((Formula.mem k w))).close

theorem source_mapNatural {m} (w a c k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mapNaturalSentence w a c k) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (mapCode w a c k) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (mapCode w a c k) := .hyp (Or.inl rfl)
  exact SyntaxMapCodeDecode.natural w a c k h0

theorem mapNatural_kernel_certificate {m} (w a c k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mapNaturalSentence w a c k)) := TheoryTransport.sentence (source_mapNatural w a c k)

theorem native_mapNatural {m} (w a c k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mapNaturalSentence w a c k)) := ZFReplay.replay (mapNatural_kernel_certificate w a c k)

def mapContextsSentence {m} (w a c k : Fin m) : Source.Sentence := ((mapCode w a c k).imp ((SyntaxTermSyntax.contexts w a c))).close

theorem source_mapContexts {m} (w a c k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mapContextsSentence w a c k) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (mapCode w a c k) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (mapCode w a c k) := .hyp (Or.inl rfl)
  exact SyntaxMapCodeDecode.contexts w a c k h0

theorem mapContexts_kernel_certificate {m} (w a c k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mapContextsSentence w a c k)) := TheoryTransport.sentence (source_mapContexts w a c k)

theorem native_mapContexts {m} (w a c k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mapContextsSentence w a c k)) := ZFReplay.replay (mapContexts_kernel_certificate w a c k)

def mapValidSentence {m} (w a c k : Fin m) : Source.Sentence := ((mapCode w a c k).imp ((StructuralListTraceSyntax.valid w k))).close

theorem source_mapValid {m} (w a c k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mapValidSentence w a c k) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (mapCode w a c k) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (mapCode w a c k) := .hyp (Or.inl rfl)
  exact SyntaxMapCodeDecode.valid w a c k h0

theorem mapValid_kernel_certificate {m} (w a c k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mapValidSentence w a c k)) := TheoryTransport.sentence (source_mapValid w a c k)

theorem native_mapValid {m} (w a c k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mapValidSentence w a c k)) := ZFReplay.replay (mapValid_kernel_certificate w a c k)

def graphFiberSentence {m} (w a c k : Fin m) : Source.Sentence := ((mapCode w a c k).imp ((SyntaxMapCodeSyntax.graphFiber w a c k))).close

theorem source_graphFiber {m} (w a c k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphFiberSentence w a c k) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (mapCode w a c k) ((Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (mapCode w a c k) := .hyp (Or.inl rfl)
  exact SyntaxMapCodeDecode.actual_graph_fiber hZ w a c k h0

theorem graphFiber_kernel_certificate {m} (w a c k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphFiberSentence w a c k)) := TheoryTransport.sentence (source_graphFiber w a c k)

theorem native_graphFiber {m} (w a c k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphFiberSentence w a c k)) := ZFReplay.replay (graphFiber_kernel_certificate w a c k)

def mapFiberIffSentence {m} (w a c k : Fin m) : Source.Sentence := (((mapCode w a c k).iff (SyntaxMapCodeSyntax.graphFiber w a c k))).close

theorem source_mapFiberIff {m} (w a c k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mapFiberIffSentence w a c k) := by
  apply close_derives
  let Δ : Context m := (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact SyntaxMapCodeDecode.fiber_iff hZ w a c k

theorem mapFiberIff_kernel_certificate {m} (w a c k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mapFiberIffSentence w a c k)) := TheoryTransport.sentence (source_mapFiberIff w a c k)

theorem native_mapFiberIff {m} (w a c k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mapFiberIffSentence w a c k)) := ZFReplay.replay (mapFiberIff_kernel_certificate w a c k)

def liftAtSourceSentence {m} (w r a c k u v l : Fin m) : Source.Sentence := ((encoded w r a c k).imp ((codedLift w a c k u v l).imp ((outputAt w r a c u v l)))).close

theorem source_liftAtSource {m} (w r a c k u v l : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftAtSourceSentence w r a c k u v l) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (codedLift w a c k u v l) (Context.add (encoded w r a c k) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (encoded w r a c k) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (codedLift w a c k u v l) := .hyp (Or.inl rfl)
  exact SyntaxMapLift.at_source hZ w r a c k u v l h0 h1

theorem liftAtSource_kernel_certificate {m} (w r a c k u v l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftAtSourceSentence w r a c k u v l)) := TheoryTransport.sentence (source_liftAtSource w r a c k u v l)

theorem native_liftAtSource {m} (w r a c k u v l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftAtSourceSentence w r a c k u v l)) := ZFReplay.replay (liftAtSource_kernel_certificate w r a c k u v l)

def liftExistsAtSourceSentence {m} (w r a c k u v : Fin m) : Source.Sentence := ((omega w).imp ((encoded w r a c k).imp ((successor u a).imp ((successor v c).imp ((existsLiftCode w a c k u v)))))).close

theorem source_liftExistsAtSource {m} (w r a c k u v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftExistsAtSourceSentence w r a c k u v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor v c) (Context.add (successor u a) (Context.add (encoded w r a c k) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (encoded w r a c k) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor u a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor v c) := .hyp (Or.inl rfl)
  exact SyntaxMapLift.exists_at_source hZ w r a c k u v h0 h1 h2 h3

theorem liftExistsAtSource_kernel_certificate {m} (w r a c k u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftExistsAtSourceSentence w r a c k u v)) := TheoryTransport.sentence (source_liftExistsAtSource w r a c k u v)

theorem native_liftExistsAtSource {m} (w r a c k u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftExistsAtSourceSentence w r a c k u v)) := ZFReplay.replay (liftExistsAtSource_kernel_certificate w r a c k u v)

def liftExistsSentence {m} (w a c k u v : Fin m) : Source.Sentence := ((omega w).imp ((mapCode w a c k).imp ((successor u a).imp ((successor v c).imp ((existsLiftCode w a c k u v)))))).close

theorem source_liftExists {m} (w a c k u v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftExistsSentence w a c k u v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor v c) (Context.add (successor u a) (Context.add (mapCode w a c k) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (mapCode w a c k) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor u a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor v c) := .hyp (Or.inl rfl)
  exact SyntaxMapLift.exists_code hZ w a c k u v h0 h1 h2 h3

theorem liftExists_kernel_certificate {m} (w a c k u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftExistsSentence w a c k u v)) := TheoryTransport.sentence (source_liftExists w a c k u v)

theorem native_liftExists {m} (w a c k u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftExistsSentence w a c k u v)) := ZFReplay.replay (liftExists_kernel_certificate w a c k u v)

def liftUniqueAtSourceSentence {m} (w r a c k u v l q : Fin m) : Source.Sentence := ((omega w).imp ((encoded w r a c k).imp ((codedLift w a c k u v l).imp ((codedLift w a c k u v q).imp ((Formula.equal l q)))))).close

theorem source_liftUniqueAtSource {m} (w r a c k u v l q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftUniqueAtSourceSentence w r a c k u v l q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (codedLift w a c k u v q) (Context.add (codedLift w a c k u v l) (Context.add (encoded w r a c k) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (encoded w r a c k) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (codedLift w a c k u v l) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (codedLift w a c k u v q) := .hyp (Or.inl rfl)
  exact SyntaxMapLift.unique_at_source hZ w r a c k u v l q h0 h1 h2 h3

theorem liftUniqueAtSource_kernel_certificate {m} (w r a c k u v l q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftUniqueAtSourceSentence w r a c k u v l q)) := TheoryTransport.sentence (source_liftUniqueAtSource w r a c k u v l q)

theorem native_liftUniqueAtSource {m} (w r a c k u v l q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftUniqueAtSourceSentence w r a c k u v l q)) := ZFReplay.replay (liftUniqueAtSource_kernel_certificate w r a c k u v l q)

def liftInputCodeSentence {m} (w a c k u v l : Fin m) : Source.Sentence := ((codedLift w a c k u v l).imp ((mapCode w a c k))).close

theorem source_liftInputCode {m} (w a c k u v l : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftInputCodeSentence w a c k u v l) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (codedLift w a c k u v l) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (codedLift w a c k u v l) := .hyp (Or.inl rfl)
  exact SyntaxMapLiftFiber.input_code w a c k u v l h0

theorem liftInputCode_kernel_certificate {m} (w a c k u v l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftInputCodeSentence w a c k u v l)) := TheoryTransport.sentence (source_liftInputCode w a c k u v l)

theorem native_liftInputCode {m} (w a c k u v l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftInputCodeSentence w a c k u v l)) := ZFReplay.replay (liftInputCode_kernel_certificate w a c k u v l)

def liftOutputCodeSentence {m} (w a c k u v l : Fin m) : Source.Sentence := ((codedLift w a c k u v l).imp ((mapCode w u v l))).close

theorem source_liftOutputCode {m} (w a c k u v l : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftOutputCodeSentence w a c k u v l) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (codedLift w a c k u v l) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (codedLift w a c k u v l) := .hyp (Or.inl rfl)
  exact SyntaxMapLiftFiber.output_code w a c k u v l h0

theorem liftOutputCode_kernel_certificate {m} (w a c k u v l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftOutputCodeSentence w a c k u v l)) := TheoryTransport.sentence (source_liftOutputCode w a c k u v l)

theorem native_liftOutputCode {m} (w a c k u v l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftOutputCodeSentence w a c k u v l)) := ZFReplay.replay (liftOutputCode_kernel_certificate w a c k u v l)

def liftOutputNaturalSentence {m} (w a c k u v l : Fin m) : Source.Sentence := ((codedLift w a c k u v l).imp ((Formula.mem l w))).close

theorem source_liftOutputNatural {m} (w a c k u v l : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftOutputNaturalSentence w a c k u v l) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (codedLift w a c k u v l) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (codedLift w a c k u v l) := .hyp (Or.inl rfl)
  exact SyntaxMapLiftFiber.output_natural w a c k u v l h0

theorem liftOutputNatural_kernel_certificate {m} (w a c k u v l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftOutputNaturalSentence w a c k u v l)) := TheoryTransport.sentence (source_liftOutputNatural w a c k u v l)

theorem native_liftOutputNatural {m} (w a c k u v l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftOutputNaturalSentence w a c k u v l)) := ZFReplay.replay (liftOutputNatural_kernel_certificate w a c k u v l)

def liftCodeUniqueSentence {m} (w a c k u v l q : Fin m) : Source.Sentence := ((omega w).imp ((codedLift w a c k u v l).imp ((codedLift w a c k u v q).imp ((Formula.equal l q))))).close

theorem source_liftCodeUnique {m} (w a c k u v l q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftCodeUniqueSentence w a c k u v l q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (codedLift w a c k u v q) (Context.add (codedLift w a c k u v l) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (codedLift w a c k u v l) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (codedLift w a c k u v q) := .hyp (Or.inl rfl)
  exact SyntaxMapLiftFiber.unique hZ w a c k u v l q h0 h1 h2

theorem liftCodeUnique_kernel_certificate {m} (w a c k u v l q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftCodeUniqueSentence w a c k u v l q)) := TheoryTransport.sentence (source_liftCodeUnique w a c k u v l q)

theorem native_liftCodeUnique {m} (w a c k u v l q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftCodeUniqueSentence w a c k u v l q)) := ZFReplay.replay (liftCodeUnique_kernel_certificate w a c k u v l q)

def liftCodeFiberSentence {m} (w a c k u v : Fin m) : Source.Sentence := ((omega w).imp ((mapCode w a c k).imp ((successor u a).imp ((successor v c).imp ((SyntaxMapLiftSyntax.fiber w a c k u v)))))).close

theorem source_liftCodeFiber {m} (w a c k u v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftCodeFiberSentence w a c k u v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor v c) (Context.add (successor u a) (Context.add (mapCode w a c k) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (mapCode w a c k) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor u a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor v c) := .hyp (Or.inl rfl)
  exact SyntaxMapLiftFiber.actual_fiber hZ w a c k u v h0 h1 h2 h3

theorem liftCodeFiber_kernel_certificate {m} (w a c k u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftCodeFiberSentence w a c k u v)) := TheoryTransport.sentence (source_liftCodeFiber w a c k u v)

theorem native_liftCodeFiber {m} (w a c k u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftCodeFiberSentence w a c k u v)) := ZFReplay.replay (liftCodeFiber_kernel_certificate w a c k u v)

def stateInputsSentence {m} (w r s a b c d q : Fin m) : Source.Sentence := ((legal w r s a b c d q).imp ((SyntaxForestSyntax.inputs 7 w (seven r s a b c d q)))).close

theorem source_stateInputs {m} (w r s a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (stateInputsSentence w r s a b c d q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (legal w r s a b c d q) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (legal w r s a b c d q) := .hyp (Or.inl rfl)
  exact SyntaxRenameState.legal_inputs w r s a b c d q h0

theorem stateInputs_kernel_certificate {m} (w r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (stateInputsSentence w r s a b c d q)) := TheoryTransport.sentence (source_stateInputs w r s a b c d q)

theorem native_stateInputs {m} (w r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (stateInputsSentence w r s a b c d q)) := ZFReplay.replay (stateInputs_kernel_certificate w r s a b c d q)

def cellNaturalSentence {m} (w r s a b c d q h : Fin m) : Source.Sentence := ((omega w).imp ((cell w r s a b c d q h).imp ((Formula.mem h w)))).close

theorem source_cellNatural {m} (w r s a b c d q h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (cellNaturalSentence w r s a b c d q h) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (cell w r s a b c d q h) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (cell w r s a b c d q h) := .hyp (Or.inl rfl)
  exact SyntaxRenameState.natural hZ w r s a b c d q h h0 h1

theorem cellNatural_kernel_certificate {m} (w r s a b c d q h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (cellNaturalSentence w r s a b c d q h)) := TheoryTransport.sentence (source_cellNatural w r s a b c d q h)

theorem native_cellNatural {m} (w r s a b c d q h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (cellNaturalSentence w r s a b c d q h)) := ZFReplay.replay (cellNatural_kernel_certificate w r s a b c d q h)

def fieldNaturalSentence {m} (w r s a b c d q h : Fin m) (j : Fin 7) : Source.Sentence := ((cell w r s a b c d q h).imp ((Formula.mem (seven r s a b c d q j) w))).close

theorem source_fieldNatural {m} (w r s a b c d q h : Fin m) (j : Fin 7) : Derives (Source.SetLanguage.ZF.at 0) (fieldNaturalSentence w r s a b c d q h j) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (cell w r s a b c d q h) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (cell w r s a b c d q h) := .hyp (Or.inl rfl)
  exact SyntaxRenameState.field_natural w r s a b c d q h j h0

theorem fieldNatural_kernel_certificate {m} (w r s a b c d q h : Fin m) (j : Fin 7) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fieldNaturalSentence w r s a b c d q h j)) := TheoryTransport.sentence (source_fieldNatural w r s a b c d q h j)

theorem native_fieldNatural {m} (w r s a b c d q h : Fin m) (j : Fin 7) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fieldNaturalSentence w r s a b c d q h j)) := ZFReplay.replay (fieldNatural_kernel_certificate w r s a b c d q h j)

def sameFieldSentence {m} (w h r s a b c d q r1 s1 a1 b1 c1 d1 q1 : Fin m) (j : Fin 7) : Source.Sentence := ((omega w).imp ((cell w r s a b c d q h).imp ((cell w r1 s1 a1 b1 c1 d1 q1 h).imp ((Formula.equal (seven r s a b c d q j) (seven r1 s1 a1 b1 c1 d1 q1 j)))))).close

theorem source_sameField {m} (w h r s a b c d q r1 s1 a1 b1 c1 d1 q1 : Fin m) (j : Fin 7) : Derives (Source.SetLanguage.ZF.at 0) (sameFieldSentence w h r s a b c d q r1 s1 a1 b1 c1 d1 q1 j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (cell w r1 s1 a1 b1 c1 d1 q1 h) (Context.add (cell w r s a b c d q h) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (cell w r s a b c d q h) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (cell w r1 s1 a1 b1 c1 d1 q1 h) := .hyp (Or.inl rfl)
  exact SyntaxRenameState.same_field hZ w h r s a b c d q r1 s1 a1 b1 c1 d1 q1 j h0 h1 h2

theorem sameField_kernel_certificate {m} (w h r s a b c d q r1 s1 a1 b1 c1 d1 q1 : Fin m) (j : Fin 7) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (sameFieldSentence w h r s a b c d q r1 s1 a1 b1 c1 d1 q1 j)) := TheoryTransport.sentence (source_sameField w h r s a b c d q r1 s1 a1 b1 c1 d1 q1 j)

theorem native_sameField {m} (w h r s a b c d q r1 s1 a1 b1 c1 d1 q1 : Fin m) (j : Fin 7) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (sameFieldSentence w h r s a b c d q r1 s1 a1 b1 c1 d1 q1 j)) := ZFReplay.replay (sameField_kernel_certificate w h r s a b c d q r1 s1 a1 b1 c1 d1 q1 j)

def sameFieldsSentence {m} (w h r s a b c d q r1 s1 a1 b1 c1 d1 q1 : Fin m) : Source.Sentence := ((omega w).imp ((cell w r s a b c d q h).imp ((cell w r1 s1 a1 b1 c1 d1 q1 h).imp ((equalParams r s a b c d q r1 s1 a1 b1 c1 d1 q1))))).close

theorem source_sameFields {m} (w h r s a b c d q r1 s1 a1 b1 c1 d1 q1 : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (sameFieldsSentence w h r s a b c d q r1 s1 a1 b1 c1 d1 q1) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (cell w r1 s1 a1 b1 c1 d1 q1 h) (Context.add (cell w r s a b c d q h) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (cell w r s a b c d q h) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (cell w r1 s1 a1 b1 c1 d1 q1 h) := .hyp (Or.inl rfl)
  exact SyntaxRenameState.same_fields hZ w h r s a b c d q r1 s1 a1 b1 c1 d1 q1 h0 h1 h2

theorem sameFields_kernel_certificate {m} (w h r s a b c d q r1 s1 a1 b1 c1 d1 q1 : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (sameFieldsSentence w h r s a b c d q r1 s1 a1 b1 c1 d1 q1)) := TheoryTransport.sentence (source_sameFields w h r s a b c d q r1 s1 a1 b1 c1 d1 q1)

theorem native_sameFields {m} (w h r s a b c d q r1 s1 a1 b1 c1 d1 q1 : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (sameFieldsSentence w h r s a b c d q r1 s1 a1 b1 c1 d1 q1)) := ZFReplay.replay (sameFields_kernel_certificate w h r s a b c d q r1 s1 a1 b1 c1 d1 q1)

def uniqueCellSentence {m} (w r s a b c d q h t : Fin m) : Source.Sentence := ((omega w).imp ((cell w r s a b c d q h).imp ((cell w r s a b c d q t).imp ((Formula.equal h t))))).close

theorem source_uniqueCell {m} (w r s a b c d q h t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniqueCellSentence w r s a b c d q h t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (cell w r s a b c d q t) (Context.add (cell w r s a b c d q h) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (cell w r s a b c d q h) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (cell w r s a b c d q t) := .hyp (Or.inl rfl)
  exact SyntaxRenameState.unique hZ w r s a b c d q h t h0 h1 h2

theorem uniqueCell_kernel_certificate {m} (w r s a b c d q h t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniqueCellSentence w r s a b c d q h t)) := TheoryTransport.sentence (source_uniqueCell w r s a b c d q h t)

theorem native_uniqueCell {m} (w r s a b c d q h t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniqueCellSentence w r s a b c d q h t)) := ZFReplay.replay (uniqueCell_kernel_certificate w r s a b c d q h t)

def stateFiberSentence {m} (w r s a b c d q : Fin m) : Source.Sentence := ((omega w).imp ((legal w r s a b c d q).imp ((stateFiber w r s a b c d q)))).close

theorem source_stateFiber {m} (w r s a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (stateFiberSentence w r s a b c d q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (legal w r s a b c d q) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (legal w r s a b c d q) := .hyp (Or.inl rfl)
  exact SyntaxRenameState.actual_fiber hZ w r s a b c d q h0 h1

theorem stateFiber_kernel_certificate {m} (w r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (stateFiberSentence w r s a b c d q)) := TheoryTransport.sentence (source_stateFiber w r s a b c d q)

theorem native_stateFiber {m} (w r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (stateFiberSentence w r s a b c d q)) := ZFReplay.replay (stateFiber_kernel_certificate w r s a b c d q)

def uniqueParamsSentence {m} (w h r s a b c d q : Fin m) : Source.Sentence := ((omega w).imp ((cell w r s a b c d q h).imp ((uniqueParams w h r s a b c d q)))).close

theorem source_uniqueParams {m} (w h r s a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniqueParamsSentence w h r s a b c d q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (cell w r s a b c d q h) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (cell w r s a b c d q h) := .hyp (Or.inl rfl)
  exact SyntaxRenameStateDecode.unique_params hZ w h r s a b c d q h0 h1

theorem uniqueParams_kernel_certificate {m} (w h r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniqueParamsSentence w h r s a b c d q)) := TheoryTransport.sentence (source_uniqueParams w h r s a b c d q)

theorem native_uniqueParams {m} (w h r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniqueParamsSentence w h r s a b c d q)) := ZFReplay.replay (uniqueParams_kernel_certificate w h r s a b c d q)

def actualDecodeSentence {m} (w h : Fin m) : Source.Sentence := ((omega w).imp ((recognized w h).imp ((decodedFiber w h)))).close

theorem source_actualDecode {m} (w h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualDecodeSentence w h) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (recognized w h) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (recognized w h) := .hyp (Or.inl rfl)
  exact SyntaxRenameStateDecode.actual_decode hZ w h h0 h1

theorem actualDecode_kernel_certificate {m} (w h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualDecodeSentence w h)) := TheoryTransport.sentence (source_actualDecode w h)

theorem native_actualDecode {m} (w h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualDecodeSentence w h)) := ZFReplay.replay (actualDecode_kernel_certificate w h)

def recognizedNaturalSentence {m} (w h : Fin m) : Source.Sentence := ((omega w).imp ((recognized w h).imp ((Formula.mem h w)))).close

theorem source_recognizedNatural {m} (w h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (recognizedNaturalSentence w h) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (recognized w h) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (recognized w h) := .hyp (Or.inl rfl)
  exact SyntaxRenameStateDecode.recognized_natural hZ w h h0 h1

theorem recognizedNatural_kernel_certificate {m} (w h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (recognizedNaturalSentence w h)) := TheoryTransport.sentence (source_recognizedNatural w h)

theorem native_recognizedNatural {m} (w h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (recognizedNaturalSentence w h)) := ZFReplay.replay (recognizedNatural_kernel_certificate w h)

def stateDecodeIffSentence {m} (w h : Fin m) : Source.Sentence := ((omega w).imp (((recognized w h).iff (decodedFiber w h)))).close

theorem source_stateDecodeIff {m} (w h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (stateDecodeIffSentence w h) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) ((Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxRenameStateDecode.fiber_iff hZ w h h0

theorem stateDecodeIff_kernel_certificate {m} (w h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (stateDecodeIffSentence w h)) := TheoryTransport.sentence (source_stateDecodeIff w h)

theorem native_stateDecodeIff {m} (w h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (stateDecodeIffSentence w h)) := ZFReplay.replay (stateDecodeIff_kernel_certificate w h)

def actualStateSystemSentence {m} (w r s a b c d q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIndexMapSyntax.maps w r s a b c d).imp ((FormulaCodeSyntax.formulaCode w q c d).imp ((SyntaxRenameStateSystem.system w r s a b c d q))))).close

theorem source_actualStateSystem {m} (w r s a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualStateSystemSentence w r s a b c d q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w q c d) (Context.add (SyntaxIndexMapSyntax.maps w r s a b c d) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxIndexMapSyntax.maps w r s a b c d) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FormulaCodeSyntax.formulaCode w q c d) := .hyp (Or.inl rfl)
  exact SyntaxRenameStateSystem.actual_system hZ w r s a b c d q h0 h1 h2

theorem actualStateSystem_kernel_certificate {m} (w r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualStateSystemSentence w r s a b c d q)) := TheoryTransport.sentence (source_actualStateSystem w r s a b c d q)

theorem native_actualStateSystem {m} (w r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualStateSystemSentence w r s a b c d q)) := ZFReplay.replay (actualStateSystem_kernel_certificate w r s a b c d q)

def introStateRecognitionSentence {m} (w h r s a b c d q : Fin m) : Source.Sentence := ((state w r s a b c d q h).imp ((recognized w h))).close

theorem source_introStateRecognition {m} (w h r s a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (introStateRecognitionSentence w h r s a b c d q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (state w r s a b c d q h) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (state w r s a b c d q h) := .hyp (Or.inl rfl)
  exact SyntaxRenameStateSyntax.intro_recognized w h r s a b c d q h0

theorem introStateRecognition_kernel_certificate {m} (w h r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (introStateRecognitionSentence w h r s a b c d q)) := TheoryTransport.sentence (source_introStateRecognition w h r s a b c d q)

theorem native_introStateRecognition {m} (w h r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (introStateRecognitionSentence w h r s a b c d q)) := ZFReplay.replay (introStateRecognition_kernel_certificate w h r s a b c d q)

end PPAC.Migration.Internal.ObjectSyntaxMapCodeState
