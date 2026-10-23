import PPAC.Migration.Internal.SyntaxTopFormulaAtCodes

/-! 首槽实际完整表、原数值环境码对和混合公式唯一输出纤维的原YesMetaZFC核证书。 -/
namespace PPAC.Migration.Internal.ObjectTopEnvironment
open Source SourceAlgebra SourceLogic OmegaSyntax

def variableImageExistsSentence {m} (bound : Bool) (w r a c d : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxVariableImageSyntax.input bound w r a c d).imp ((SyntaxVariableImageSyntax.existsMap bound w r a c d)))).close

theorem source_variableImageExists {m} (bound : Bool) (w r a c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (variableImageExistsSentence bound w r a c d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableImageSyntax.input bound w r a c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxVariableImageSyntax.input bound w r a c d) := .hyp (Or.inl rfl)
  exact SyntaxVariableImageGraph.exists_map hZ bound w r a c d h0 h1

theorem variableImageExists_kernel_certificate {m} (bound : Bool) (w r a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (variableImageExistsSentence bound w r a c d)) := TheoryTransport.sentence (source_variableImageExists bound w r a c d)

theorem native_variableImageExists {m} (bound : Bool) (w r a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (variableImageExistsSentence bound w r a c d)) := ZFReplay.replay (variableImageExists_kernel_certificate bound w r a c d)

def variableImageUniqueSentence {m} (bound : Bool) (w r a c d f g : Fin m) : Source.Sentence := ((SyntaxVariableImageSyntax.mapped bound w r a c d f).imp ((SyntaxVariableImageSyntax.mapped bound w r a c d g).imp ((Formula.equal f g)))).close

theorem source_variableImageUnique {m} (bound : Bool) (w r a c d f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (variableImageUniqueSentence bound w r a c d f g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableImageSyntax.mapped bound w r a c d g) (Context.add (SyntaxVariableImageSyntax.mapped bound w r a c d f) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxVariableImageSyntax.mapped bound w r a c d f) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxVariableImageSyntax.mapped bound w r a c d g) := .hyp (Or.inl rfl)
  exact SyntaxVariableImageGraph.unique hZ bound w r a c d f g h0 h1

theorem variableImageUnique_kernel_certificate {m} (bound : Bool) (w r a c d f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (variableImageUniqueSentence bound w r a c d f g)) := TheoryTransport.sentence (source_variableImageUnique bound w r a c d f g)

theorem native_variableImageUnique {m} (bound : Bool) (w r a c d f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (variableImageUniqueSentence bound w r a c d f g)) := ZFReplay.replay (variableImageUnique_kernel_certificate bound w r a c d f g)

def variableImageEdgesSentence {m} (bound : Bool) (w r a c d f i q : Fin m) : Source.Sentence := ((SyntaxVariableImageSyntax.mapped bound w r a c d f).imp (((GraphSyntax.edge f i q).iff (SyntaxVariableImageSyntax.value bound w r c d i q)))).close

theorem source_variableImageEdges {m} (bound : Bool) (w r a c d f i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (variableImageEdgesSentence bound w r a c d f i q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableImageSyntax.mapped bound w r a c d f) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxVariableImageSyntax.mapped bound w r a c d f) := .hyp (Or.inl rfl)
  exact SyntaxVariableImageGraph.edge_iff hZ bound w r a c d f i q h0

theorem variableImageEdges_kernel_certificate {m} (bound : Bool) (w r a c d f i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (variableImageEdgesSentence bound w r a c d f i q)) := TheoryTransport.sentence (source_variableImageEdges bound w r a c d f i q)

theorem native_variableImageEdges {m} (bound : Bool) (w r a c d f i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (variableImageEdgesSentence bound w r a c d f i q)) := ZFReplay.replay (variableImageEdges_kernel_certificate bound w r a c d f i q)

def variableImageAtIndexSentence {m} (bound : Bool) (w r a c d f i j q : Fin m) : Source.Sentence := ((SyntaxVariableImageSyntax.mapped bound w r a c d f).imp ((GraphSyntax.edge r i j).imp (((GraphSyntax.edge f i q).iff (SyntaxVariableSyntax.code bound w j q))))).close

theorem source_variableImageAtIndex {m} (bound : Bool) (w r a c d f i j q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (variableImageAtIndexSentence bound w r a c d f i j q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (GraphSyntax.edge r i j) (Context.add (SyntaxVariableImageSyntax.mapped bound w r a c d f) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxVariableImageSyntax.mapped bound w r a c d f) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (GraphSyntax.edge r i j) := .hyp (Or.inl rfl)
  exact SyntaxVariableImageFields.at_index hZ bound w r a c d f i j q h0 h1

theorem variableImageAtIndex_kernel_certificate {m} (bound : Bool) (w r a c d f i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (variableImageAtIndexSentence bound w r a c d f i j q)) := TheoryTransport.sentence (source_variableImageAtIndex bound w r a c d f i j q)

theorem native_variableImageAtIndex {m} (bound : Bool) (w r a c d f i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (variableImageAtIndexSentence bound w r a c d f i j q)) := ZFReplay.replay (variableImageAtIndex_kernel_certificate bound w r a c d f i j q)

def identityTableExistsSentence {m} (bound : Bool) (w c d : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermSyntax.contexts w c d).imp ((SyntaxVariableTableSyntax.existsIdentity bound w c d)))).close

theorem source_identityTableExists {m} (bound : Bool) (w c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (identityTableExistsSentence bound w c d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.contexts w c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTermSyntax.contexts w c d) := .hyp (Or.inl rfl)
  exact SyntaxVariableTableExistence.identity_exists hZ bound w c d h0 h1

theorem identityTableExists_kernel_certificate {m} (bound : Bool) (w c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (identityTableExistsSentence bound w c d)) := TheoryTransport.sentence (source_identityTableExists bound w c d)

theorem native_identityTableExists {m} (bound : Bool) (w c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (identityTableExistsSentence bound w c d)) := ZFReplay.replay (identityTableExists_kernel_certificate bound w c d)

def shiftedTableExistsSentence {m} (bound : Bool) (w a c d : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermSyntax.contexts w c d).imp ((Formula.mem a w).imp ((successor (SyntaxTermSyntax.limit bound c d) a).imp ((SyntaxVariableTableSyntax.existsShifted bound w a c d)))))).close

theorem source_shiftedTableExists {m} (bound : Bool) (w a c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (shiftedTableExistsSentence bound w a c d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor (SyntaxTermSyntax.limit bound c d) a) (Context.add (Formula.mem a w) (Context.add (SyntaxTermSyntax.contexts w c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxTermSyntax.contexts w c d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem a w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor (SyntaxTermSyntax.limit bound c d) a) := .hyp (Or.inl rfl)
  exact SyntaxVariableTableExistence.shifted_exists hZ bound w a c d h0 h1 h2 h3

theorem shiftedTableExists_kernel_certificate {m} (bound : Bool) (w a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (shiftedTableExistsSentence bound w a c d)) := TheoryTransport.sentence (source_shiftedTableExists bound w a c d)

theorem native_shiftedTableExists {m} (bound : Bool) (w a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (shiftedTableExistsSentence bound w a c d)) := ZFReplay.replay (shiftedTableExists_kernel_certificate bound w a c d)

def identityTableUniqueSentence {m} (bound : Bool) (w c d f g : Fin m) : Source.Sentence := ((SyntaxVariableTableSyntax.identity bound w c d f).imp ((SyntaxVariableTableSyntax.identity bound w c d g).imp ((Formula.equal f g)))).close

theorem source_identityTableUnique {m} (bound : Bool) (w c d f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (identityTableUniqueSentence bound w c d f g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableTableSyntax.identity bound w c d g) (Context.add (SyntaxVariableTableSyntax.identity bound w c d f) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxVariableTableSyntax.identity bound w c d f) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxVariableTableSyntax.identity bound w c d g) := .hyp (Or.inl rfl)
  exact SyntaxVariableTableUnique.identity_unique hZ bound w c d f g h0 h1

theorem identityTableUnique_kernel_certificate {m} (bound : Bool) (w c d f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (identityTableUniqueSentence bound w c d f g)) := TheoryTransport.sentence (source_identityTableUnique bound w c d f g)

theorem native_identityTableUnique {m} (bound : Bool) (w c d f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (identityTableUniqueSentence bound w c d f g)) := ZFReplay.replay (identityTableUnique_kernel_certificate bound w c d f g)

def shiftedTableUniqueSentence {m} (bound : Bool) (w a c d f g : Fin m) : Source.Sentence := ((SyntaxVariableTableSyntax.shifted bound w a c d f).imp ((SyntaxVariableTableSyntax.shifted bound w a c d g).imp ((Formula.equal f g)))).close

theorem source_shiftedTableUnique {m} (bound : Bool) (w a c d f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (shiftedTableUniqueSentence bound w a c d f g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableTableSyntax.shifted bound w a c d g) (Context.add (SyntaxVariableTableSyntax.shifted bound w a c d f) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxVariableTableSyntax.shifted bound w a c d f) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxVariableTableSyntax.shifted bound w a c d g) := .hyp (Or.inl rfl)
  exact SyntaxVariableTableUnique.shifted_unique hZ bound w a c d f g h0 h1

theorem shiftedTableUnique_kernel_certificate {m} (bound : Bool) (w a c d f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (shiftedTableUniqueSentence bound w a c d f g)) := TheoryTransport.sentence (source_shiftedTableUnique bound w a c d f g)

theorem native_shiftedTableUnique {m} (bound : Bool) (w a c d f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (shiftedTableUniqueSentence bound w a c d f g)) := ZFReplay.replay (shiftedTableUnique_kernel_certificate bound w a c d f g)

def identityTableAtSentence {m} (bound : Bool) (w c d f i q : Fin m) : Source.Sentence := ((SyntaxVariableTableSyntax.identity bound w c d f).imp ((Formula.mem i (SyntaxTermSyntax.limit bound c d)).imp (((GraphSyntax.edge f i q).iff (SyntaxVariableSyntax.code bound w i q))))).close

theorem source_identityTableAt {m} (bound : Bool) (w c d f i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (identityTableAtSentence bound w c d f i q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i (SyntaxTermSyntax.limit bound c d)) (Context.add (SyntaxVariableTableSyntax.identity bound w c d f) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxVariableTableSyntax.identity bound w c d f) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem i (SyntaxTermSyntax.limit bound c d)) := .hyp (Or.inl rfl)
  exact SyntaxVariableTableFields.identity_at hZ bound w c d f i q h0 h1

theorem identityTableAt_kernel_certificate {m} (bound : Bool) (w c d f i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (identityTableAtSentence bound w c d f i q)) := TheoryTransport.sentence (source_identityTableAt bound w c d f i q)

theorem native_identityTableAt {m} (bound : Bool) (w c d f i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (identityTableAtSentence bound w c d f i q)) := ZFReplay.replay (identityTableAt_kernel_certificate bound w c d f i q)

def shiftedTableAtSentence {m} (bound : Bool) (w a c d f i j q : Fin m) : Source.Sentence := ((SyntaxVariableTableSyntax.shifted bound w a c d f).imp ((Formula.mem i a).imp ((successor j i).imp (((GraphSyntax.edge f i q).iff (SyntaxVariableSyntax.code bound w j q)))))).close

theorem source_shiftedTableAt {m} (bound : Bool) (w a c d f i j q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (shiftedTableAtSentence bound w a c d f i j q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor j i) (Context.add (Formula.mem i a) (Context.add (SyntaxVariableTableSyntax.shifted bound w a c d f) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxVariableTableSyntax.shifted bound w a c d f) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem i a) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor j i) := .hyp (Or.inl rfl)
  exact SyntaxVariableTableFields.shifted_at hZ bound w a c d f i j q h0 h1 h2

theorem shiftedTableAt_kernel_certificate {m} (bound : Bool) (w a c d f i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (shiftedTableAtSentence bound w a c d f i j q)) := TheoryTransport.sentence (source_shiftedTableAt bound w a c d f i j q)

theorem native_shiftedTableAt {m} (bound : Bool) (w a c d f i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (shiftedTableAtSentence bound w a c d f i j q)) := ZFReplay.replay (shiftedTableAt_kernel_certificate bound w a c d f i j q)

def instantiateActualExistsSentence {m} (w a b A t : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopEnvironmentSyntax.instantiateInput w a b A t).imp ((SyntaxTopEnvironmentSyntax.existsInstantiate w a b A t)))).close

theorem source_instantiateActualExists {m} (w a b A t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateActualExistsSentence w a b A t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopEnvironmentSyntax.instantiateInput w a b A t) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTopEnvironmentSyntax.instantiateInput w a b A t) := .hyp (Or.inl rfl)
  exact SyntaxTopInstantiateExistence.exists_pair hZ w a b A t h0 h1

theorem instantiateActualExists_kernel_certificate {m} (w a b A t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateActualExistsSentence w a b A t)) := TheoryTransport.sentence (source_instantiateActualExists w a b A t)

theorem native_instantiateActualExists {m} (w a b A t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateActualExistsSentence w a b A t)) := ZFReplay.replay (instantiateActualExists_kernel_certificate w a b A t)

def instantiateActualInputSentence {m} (w a b A t f g : Fin m) : Source.Sentence := ((SyntaxTopEnvironmentSyntax.instantiateEnv w a b A t f g).imp ((SyntaxTopEnvironmentSyntax.instantiateInput w a b A t))).close

theorem source_instantiateActualInput {m} (w a b A t f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateActualInputSentence w a b A t f g) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopEnvironmentSyntax.instantiateEnv w a b A t f g) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxTopEnvironmentSyntax.instantiateEnv w a b A t f g) := .hyp (Or.inl rfl)
  exact SyntaxTopEnvironmentTyping.instantiate_input w a b A t f g h0

theorem instantiateActualInput_kernel_certificate {m} (w a b A t f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateActualInputSentence w a b A t f g)) := TheoryTransport.sentence (source_instantiateActualInput w a b A t f g)

theorem native_instantiateActualInput {m} (w a b A t f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateActualInputSentence w a b A t f g)) := ZFReplay.replay (instantiateActualInput_kernel_certificate w a b A t f g)

def instantiateActualMapsSentence {m} (w a b A t f g : Fin m) : Source.Sentence := ((SyntaxTopEnvironmentSyntax.instantiateEnv w a b A t f g).imp ((SyntaxTermImageSyntax.maps w f g A b a b))).close

theorem source_instantiateActualMaps {m} (w a b A t f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateActualMapsSentence w a b A t f g) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopEnvironmentSyntax.instantiateEnv w a b A t f g) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxTopEnvironmentSyntax.instantiateEnv w a b A t f g) := .hyp (Or.inl rfl)
  exact SyntaxTopEnvironmentTyping.instantiate_maps w a b A t f g h0

theorem instantiateActualMaps_kernel_certificate {m} (w a b A t f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateActualMapsSentence w a b A t f g)) := TheoryTransport.sentence (source_instantiateActualMaps w a b A t f g)

theorem native_instantiateActualMaps {m} (w a b A t f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateActualMapsSentence w a b A t f g)) := ZFReplay.replay (instantiateActualMaps_kernel_certificate w a b A t f g)

def instantiateActualUniqueSentence {m} (w a b A t f g F G : Fin m) : Source.Sentence := ((SyntaxTopEnvironmentSyntax.instantiateEnv w a b A t f g).imp ((SyntaxTopEnvironmentSyntax.instantiateEnv w a b A t F G).imp (((Formula.equal f F).conj (Formula.equal g G))))).close

theorem source_instantiateActualUnique {m} (w a b A t f g F G : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateActualUniqueSentence w a b A t f g F G) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopEnvironmentSyntax.instantiateEnv w a b A t F G) (Context.add (SyntaxTopEnvironmentSyntax.instantiateEnv w a b A t f g) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxTopEnvironmentSyntax.instantiateEnv w a b A t f g) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTopEnvironmentSyntax.instantiateEnv w a b A t F G) := .hyp (Or.inl rfl)
  exact SyntaxTopEnvironmentUnique.instantiate_unique hZ w a b A t f g F G h0 h1

theorem instantiateActualUnique_kernel_certificate {m} (w a b A t f g F G : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateActualUniqueSentence w a b A t f g F G)) := TheoryTransport.sentence (source_instantiateActualUnique w a b A t f g F G)

theorem native_instantiateActualUnique {m} (w a b A t f g F G : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateActualUniqueSentence w a b A t f g F G)) := ZFReplay.replay (instantiateActualUnique_kernel_certificate w a b A t f g F G)

def instantiateCodeExistsSentence {m} (w a b A t : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopEnvironmentSyntax.instantiateInput w a b A t).imp ((SyntaxTopCodedEnvironmentSyntax.existsInstantiate w a b A t)))).close

theorem source_instantiateCodeExists {m} (w a b A t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateCodeExistsSentence w a b A t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopEnvironmentSyntax.instantiateInput w a b A t) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTopEnvironmentSyntax.instantiateInput w a b A t) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentExistence.instantiate_exists hZ w a b A t h0 h1

theorem instantiateCodeExists_kernel_certificate {m} (w a b A t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateCodeExistsSentence w a b A t)) := TheoryTransport.sentence (source_instantiateCodeExists w a b A t)

theorem native_instantiateCodeExists {m} (w a b A t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateCodeExistsSentence w a b A t)) := ZFReplay.replay (instantiateCodeExists_kernel_certificate w a b A t)

def instantiateCodeInputSentence {m} (w a b A t R S : Fin m) : Source.Sentence := ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S).imp ((SyntaxTopEnvironmentSyntax.instantiateInput w a b A t))).close

theorem source_instantiateCodeInput {m} (w a b A t R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateCodeInputSentence w a b A t R S) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentTyping.instantiate_input w a b A t R S h0

theorem instantiateCodeInput_kernel_certificate {m} (w a b A t R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateCodeInputSentence w a b A t R S)) := TheoryTransport.sentence (source_instantiateCodeInput w a b A t R S)

theorem native_instantiateCodeInput {m} (w a b A t R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateCodeInputSentence w a b A t R S)) := ZFReplay.replay (instantiateCodeInput_kernel_certificate w a b A t R S)

def instantiateCodeListsSentence {m} (w a b A t R S : Fin m) : Source.Sentence := ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S).imp ((SyntaxMixedImageCodeSyntax.termLists w A b a b R S))).close

theorem source_instantiateCodeLists {m} (w a b A t R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateCodeListsSentence w a b A t R S) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentTyping.instantiate_lists w a b A t R S h0

theorem instantiateCodeLists_kernel_certificate {m} (w a b A t R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateCodeListsSentence w a b A t R S)) := TheoryTransport.sentence (source_instantiateCodeLists w a b A t R S)

theorem native_instantiateCodeLists {m} (w a b A t R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateCodeListsSentence w a b A t R S)) := ZFReplay.replay (instantiateCodeLists_kernel_certificate w a b A t R S)

def instantiateCodeNaturalSentence {m} (w a b A t R S : Fin m) : Source.Sentence := ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S).imp (((Formula.mem R w).conj (Formula.mem S w)))).close

theorem source_instantiateCodeNatural {m} (w a b A t R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateCodeNaturalSentence w a b A t R S) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentTyping.instantiate_natural w a b A t R S h0

theorem instantiateCodeNatural_kernel_certificate {m} (w a b A t R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateCodeNaturalSentence w a b A t R S)) := TheoryTransport.sentence (source_instantiateCodeNatural w a b A t R S)

theorem native_instantiateCodeNatural {m} (w a b A t R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateCodeNaturalSentence w a b A t R S)) := ZFReplay.replay (instantiateCodeNatural_kernel_certificate w a b A t R S)

def instantiateCodeUniqueSentence {m} (w a b A t R S U V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S).imp ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t U V).imp (((Formula.equal R U).conj (Formula.equal S V)))))).close

theorem source_instantiateCodeUnique {m} (w a b A t R S U V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateCodeUniqueSentence w a b A t R S U V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t U V) (Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t U V) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentUnique.instantiate_unique hZ w a b A t R S U V h0 h1 h2

theorem instantiateCodeUnique_kernel_certificate {m} (w a b A t R S U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateCodeUniqueSentence w a b A t R S U V)) := TheoryTransport.sentence (source_instantiateCodeUnique w a b A t R S U V)

theorem native_instantiateCodeUnique {m} (w a b A t R S U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateCodeUniqueSentence w a b A t R S U V)) := ZFReplay.replay (instantiateCodeUnique_kernel_certificate w a b A t R S U V)

def instantiateCodeUniqueOutputSentence {m} (w a b A t R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S).imp ((SyntaxTopCodedEnvironmentFiber.instantiateUnique w a b A t R S)))).close

theorem source_instantiateCodeUniqueOutput {m} (w a b A t R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateCodeUniqueOutputSentence w a b A t R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentFiber.instantiate_unique_output hZ w a b A t R S h0 h1

theorem instantiateCodeUniqueOutput_kernel_certificate {m} (w a b A t R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateCodeUniqueOutputSentence w a b A t R S)) := TheoryTransport.sentence (source_instantiateCodeUniqueOutput w a b A t R S)

theorem native_instantiateCodeUniqueOutput {m} (w a b A t R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateCodeUniqueOutputSentence w a b A t R S)) := ZFReplay.replay (instantiateCodeUniqueOutput_kernel_certificate w a b A t R S)

def instantiateCodeFiberSentence {m} (w a b A t : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopEnvironmentSyntax.instantiateInput w a b A t).imp ((SyntaxTopCodedEnvironmentFiber.instantiateFiber w a b A t)))).close

theorem source_instantiateCodeFiber {m} (w a b A t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateCodeFiberSentence w a b A t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopEnvironmentSyntax.instantiateInput w a b A t) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTopEnvironmentSyntax.instantiateInput w a b A t) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentFiber.instantiate_actual_fiber hZ w a b A t h0 h1

theorem instantiateCodeFiber_kernel_certificate {m} (w a b A t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateCodeFiberSentence w a b A t)) := TheoryTransport.sentence (source_instantiateCodeFiber w a b A t)

theorem native_instantiateCodeFiber {m} (w a b A t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateCodeFiberSentence w a b A t)) := ZFReplay.replay (instantiateCodeFiber_kernel_certificate w a b A t)

def instantiateCodeExistsIffSentence {m} (w a b A t : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxTopCodedEnvironmentSyntax.existsInstantiate w a b A t).iff (SyntaxTopEnvironmentSyntax.instantiateInput w a b A t)))).close

theorem source_instantiateCodeExistsIff {m} (w a b A t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateCodeExistsIffSentence w a b A t) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentFiber.instantiate_exists_iff hZ w a b A t h0

theorem instantiateCodeExistsIff_kernel_certificate {m} (w a b A t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateCodeExistsIffSentence w a b A t)) := TheoryTransport.sentence (source_instantiateCodeExistsIff w a b A t)

theorem native_instantiateCodeExistsIff {m} (w a b A t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateCodeExistsIffSentence w a b A t)) := ZFReplay.replay (instantiateCodeExistsIff_kernel_certificate w a b A t)

def instantiateCodeFiberIffSentence {m} (w a b A t : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxTopCodedEnvironmentFiber.instantiateFiber w a b A t).iff (SyntaxTopEnvironmentSyntax.instantiateInput w a b A t)))).close

theorem source_instantiateCodeFiberIff {m} (w a b A t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateCodeFiberIffSentence w a b A t) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentFiber.instantiate_fiber_iff hZ w a b A t h0

theorem instantiateCodeFiberIff_kernel_certificate {m} (w a b A t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateCodeFiberIffSentence w a b A t)) := TheoryTransport.sentence (source_instantiateCodeFiberIff w a b A t)

theorem native_instantiateCodeFiberIff {m} (w a b A t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateCodeFiberIffSentence w a b A t)) := ZFReplay.replay (instantiateCodeFiberIff_kernel_certificate w a b A t)

def instantiateFormulaFiberSentence {m} (w a b A t R S n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S).imp ((FormulaCodeSyntax.formulaCode w n A b).imp ((SyntaxMixedFormulaOutputSyntax.fiber w R S A b a b n))))).close

theorem source_instantiateFormulaFiber {m} (w a b A t R S n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateFormulaFiberSentence w a b A t R S n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w n A b) (Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FormulaCodeSyntax.formulaCode w n A b) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaAtCodes.instantiate_formula_fiber hZ w a b A t R S n h0 h1 h2

theorem instantiateFormulaFiber_kernel_certificate {m} (w a b A t R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateFormulaFiberSentence w a b A t R S n)) := TheoryTransport.sentence (source_instantiateFormulaFiber w a b A t R S n)

theorem native_instantiateFormulaFiber {m} (w a b A t R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateFormulaFiberSentence w a b A t R S n)) := ZFReplay.replay (instantiateFormulaFiber_kernel_certificate w a b A t R S n)

def instantiateFormulaExistsSentence {m} (w a b A t R S n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S).imp ((FormulaCodeSyntax.formulaCode w n A b).imp ((SyntaxMixedFormulaOutputSyntax.existsOutput w R S A b a b n))))).close

theorem source_instantiateFormulaExists {m} (w a b A t R S n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateFormulaExistsSentence w a b A t R S n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w n A b) (Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FormulaCodeSyntax.formulaCode w n A b) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaAtCodes.instantiate_formula_exists hZ w a b A t R S n h0 h1 h2

theorem instantiateFormulaExists_kernel_certificate {m} (w a b A t R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateFormulaExistsSentence w a b A t R S n)) := TheoryTransport.sentence (source_instantiateFormulaExists w a b A t R S n)

theorem native_instantiateFormulaExists {m} (w a b A t R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateFormulaExistsSentence w a b A t R S n)) := ZFReplay.replay (instantiateFormulaExists_kernel_certificate w a b A t R S n)

def instantiateActualZeroSentence {m} (w a b A t f g i q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopEnvironmentSyntax.instantiateEnv w a b A t f g).imp ((empty i).imp (((GraphSyntax.edge f i q).iff (Formula.equal q t)))))).close

theorem source_instantiateActualZero {m} (w a b A t f g i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateActualZeroSentence w a b A t f g i q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty i) (Context.add (SyntaxTopEnvironmentSyntax.instantiateEnv w a b A t f g) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxTopEnvironmentSyntax.instantiateEnv w a b A t f g) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty i) := .hyp (Or.inl rfl)
  exact SyntaxTopEnvironmentFields.instantiate_zero hZ w a b A t f g i q h0 h1 h2

theorem instantiateActualZero_kernel_certificate {m} (w a b A t f g i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateActualZeroSentence w a b A t f g i q)) := TheoryTransport.sentence (source_instantiateActualZero w a b A t f g i q)

theorem native_instantiateActualZero {m} (w a b A t f g i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateActualZeroSentence w a b A t f g i q)) := ZFReplay.replay (instantiateActualZero_kernel_certificate w a b A t f g i q)

def instantiateCodeZeroSentence {m} (w a b A t R S i q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S).imp ((empty i).imp ((((Formula.mem i A).conj (StructuralListFieldSyntax.field w R i q)).iff (Formula.equal q t)))))).close

theorem source_instantiateCodeZero {m} (w a b A t R S i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateCodeZeroSentence w a b A t R S i q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty i) (Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty i) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentFields.instantiate_zero hZ w a b A t R S i q h0 h1 h2

theorem instantiateCodeZero_kernel_certificate {m} (w a b A t R S i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateCodeZeroSentence w a b A t R S i q)) := TheoryTransport.sentence (source_instantiateCodeZero w a b A t R S i q)

theorem native_instantiateCodeZero {m} (w a b A t R S i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateCodeZeroSentence w a b A t R S i q)) := ZFReplay.replay (instantiateCodeZero_kernel_certificate w a b A t R S i q)

def instantiateActualBoundSentence {m} (w a b A t f g i j q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopEnvironmentSyntax.instantiateEnv w a b A t f g).imp ((Formula.mem j a).imp ((successor i j).imp (((GraphSyntax.edge f i q).iff (SyntaxVariableSyntax.code true w j q))))))).close

theorem source_instantiateActualBound {m} (w a b A t f g i j q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateActualBoundSentence w a b A t f g i j q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor i j) (Context.add (Formula.mem j a) (Context.add (SyntaxTopEnvironmentSyntax.instantiateEnv w a b A t f g) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxTopEnvironmentSyntax.instantiateEnv w a b A t f g) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem j a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor i j) := .hyp (Or.inl rfl)
  exact SyntaxTopEnvironmentFields.instantiate_bound hZ w a b A t f g i j q h0 h1 h2 h3

theorem instantiateActualBound_kernel_certificate {m} (w a b A t f g i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateActualBoundSentence w a b A t f g i j q)) := TheoryTransport.sentence (source_instantiateActualBound w a b A t f g i j q)

theorem native_instantiateActualBound {m} (w a b A t f g i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateActualBoundSentence w a b A t f g i j q)) := ZFReplay.replay (instantiateActualBound_kernel_certificate w a b A t f g i j q)

def instantiateCodeBoundSentence {m} (w a b A t R S i j q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S).imp ((Formula.mem j a).imp ((successor i j).imp ((((Formula.mem i A).conj (StructuralListFieldSyntax.field w R i q)).iff (SyntaxVariableSyntax.code true w j q))))))).close

theorem source_instantiateCodeBound {m} (w a b A t R S i j q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateCodeBoundSentence w a b A t R S i j q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor i j) (Context.add (Formula.mem j a) (Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem j a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor i j) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentFields.instantiate_bound hZ w a b A t R S i j q h0 h1 h2 h3

theorem instantiateCodeBound_kernel_certificate {m} (w a b A t R S i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateCodeBoundSentence w a b A t R S i j q)) := TheoryTransport.sentence (source_instantiateCodeBound w a b A t R S i j q)

theorem native_instantiateCodeBound {m} (w a b A t R S i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateCodeBoundSentence w a b A t R S i j q)) := ZFReplay.replay (instantiateCodeBound_kernel_certificate w a b A t R S i j q)

def instantiateActualFreeSentence {m} (w a b A t f g i q : Fin m) : Source.Sentence := ((SyntaxTopEnvironmentSyntax.instantiateEnv w a b A t f g).imp ((Formula.mem i b).imp (((GraphSyntax.edge g i q).iff (SyntaxVariableSyntax.code false w i q))))).close

theorem source_instantiateActualFree {m} (w a b A t f g i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateActualFreeSentence w a b A t f g i q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i b) (Context.add (SyntaxTopEnvironmentSyntax.instantiateEnv w a b A t f g) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxTopEnvironmentSyntax.instantiateEnv w a b A t f g) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem i b) := .hyp (Or.inl rfl)
  exact SyntaxTopEnvironmentFields.instantiate_free hZ w a b A t f g i q h0 h1

theorem instantiateActualFree_kernel_certificate {m} (w a b A t f g i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateActualFreeSentence w a b A t f g i q)) := TheoryTransport.sentence (source_instantiateActualFree w a b A t f g i q)

theorem native_instantiateActualFree {m} (w a b A t f g i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateActualFreeSentence w a b A t f g i q)) := ZFReplay.replay (instantiateActualFree_kernel_certificate w a b A t f g i q)

def instantiateCodeFreeSentence {m} (w a b A t R S i q : Fin m) : Source.Sentence := ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S).imp ((Formula.mem i b).imp ((((Formula.mem i b).conj (StructuralListFieldSyntax.field w S i q)).iff (SyntaxVariableSyntax.code false w i q))))).close

theorem source_instantiateCodeFree {m} (w a b A t R S i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateCodeFreeSentence w a b A t R S i q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i b) (Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem i b) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentFields.instantiate_free hZ w a b A t R S i q h0 h1

theorem instantiateCodeFree_kernel_certificate {m} (w a b A t R S i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateCodeFreeSentence w a b A t R S i q)) := TheoryTransport.sentence (source_instantiateCodeFree w a b A t R S i q)

theorem native_instantiateCodeFree {m} (w a b A t R S i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateCodeFreeSentence w a b A t R S i q)) := ZFReplay.replay (instantiateCodeFree_kernel_certificate w a b A t R S i q)

def abstractActualExistsSentence {m} (w a b A B : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopEnvironmentSyntax.abstractInput w a b A B).imp ((SyntaxTopEnvironmentSyntax.existsAbstract w a b A B)))).close

theorem source_abstractActualExists {m} (w a b A B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractActualExistsSentence w a b A B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopEnvironmentSyntax.abstractInput w a b A B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTopEnvironmentSyntax.abstractInput w a b A B) := .hyp (Or.inl rfl)
  exact SyntaxTopAbstractExistence.exists_pair hZ w a b A B h0 h1

theorem abstractActualExists_kernel_certificate {m} (w a b A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractActualExistsSentence w a b A B)) := TheoryTransport.sentence (source_abstractActualExists w a b A B)

theorem native_abstractActualExists {m} (w a b A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractActualExistsSentence w a b A B)) := ZFReplay.replay (abstractActualExists_kernel_certificate w a b A B)

def abstractActualInputSentence {m} (w a b A B f g : Fin m) : Source.Sentence := ((SyntaxTopEnvironmentSyntax.abstractEnv w a b A B f g).imp ((SyntaxTopEnvironmentSyntax.abstractInput w a b A B))).close

theorem source_abstractActualInput {m} (w a b A B f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractActualInputSentence w a b A B f g) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopEnvironmentSyntax.abstractEnv w a b A B f g) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxTopEnvironmentSyntax.abstractEnv w a b A B f g) := .hyp (Or.inl rfl)
  exact SyntaxTopEnvironmentTyping.abstract_input w a b A B f g h0

theorem abstractActualInput_kernel_certificate {m} (w a b A B f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractActualInputSentence w a b A B f g)) := TheoryTransport.sentence (source_abstractActualInput w a b A B f g)

theorem native_abstractActualInput {m} (w a b A B f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractActualInputSentence w a b A B f g)) := ZFReplay.replay (abstractActualInput_kernel_certificate w a b A B f g)

def abstractActualMapsSentence {m} (w a b A B f g : Fin m) : Source.Sentence := ((SyntaxTopEnvironmentSyntax.abstractEnv w a b A B f g).imp ((SyntaxTermImageSyntax.maps w f g a B A b))).close

theorem source_abstractActualMaps {m} (w a b A B f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractActualMapsSentence w a b A B f g) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopEnvironmentSyntax.abstractEnv w a b A B f g) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxTopEnvironmentSyntax.abstractEnv w a b A B f g) := .hyp (Or.inl rfl)
  exact SyntaxTopEnvironmentTyping.abstract_maps w a b A B f g h0

theorem abstractActualMaps_kernel_certificate {m} (w a b A B f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractActualMapsSentence w a b A B f g)) := TheoryTransport.sentence (source_abstractActualMaps w a b A B f g)

theorem native_abstractActualMaps {m} (w a b A B f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractActualMapsSentence w a b A B f g)) := ZFReplay.replay (abstractActualMaps_kernel_certificate w a b A B f g)

def abstractActualUniqueSentence {m} (w a b A B f g F G : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopEnvironmentSyntax.abstractEnv w a b A B f g).imp ((SyntaxTopEnvironmentSyntax.abstractEnv w a b A B F G).imp (((Formula.equal f F).conj (Formula.equal g G)))))).close

theorem source_abstractActualUnique {m} (w a b A B f g F G : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractActualUniqueSentence w a b A B f g F G) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopEnvironmentSyntax.abstractEnv w a b A B F G) (Context.add (SyntaxTopEnvironmentSyntax.abstractEnv w a b A B f g) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxTopEnvironmentSyntax.abstractEnv w a b A B f g) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxTopEnvironmentSyntax.abstractEnv w a b A B F G) := .hyp (Or.inl rfl)
  exact SyntaxTopEnvironmentUnique.abstract_unique hZ w a b A B f g F G h0 h1 h2

theorem abstractActualUnique_kernel_certificate {m} (w a b A B f g F G : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractActualUniqueSentence w a b A B f g F G)) := TheoryTransport.sentence (source_abstractActualUnique w a b A B f g F G)

theorem native_abstractActualUnique {m} (w a b A B f g F G : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractActualUniqueSentence w a b A B f g F G)) := ZFReplay.replay (abstractActualUnique_kernel_certificate w a b A B f g F G)

def abstractCodeExistsSentence {m} (w a b A B : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopEnvironmentSyntax.abstractInput w a b A B).imp ((SyntaxTopCodedEnvironmentSyntax.existsAbstract w a b A B)))).close

theorem source_abstractCodeExists {m} (w a b A B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractCodeExistsSentence w a b A B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopEnvironmentSyntax.abstractInput w a b A B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTopEnvironmentSyntax.abstractInput w a b A B) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentExistence.abstract_exists hZ w a b A B h0 h1

theorem abstractCodeExists_kernel_certificate {m} (w a b A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractCodeExistsSentence w a b A B)) := TheoryTransport.sentence (source_abstractCodeExists w a b A B)

theorem native_abstractCodeExists {m} (w a b A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractCodeExistsSentence w a b A B)) := ZFReplay.replay (abstractCodeExists_kernel_certificate w a b A B)

def abstractCodeInputSentence {m} (w a b A B R S : Fin m) : Source.Sentence := ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((SyntaxTopEnvironmentSyntax.abstractInput w a b A B))).close

theorem source_abstractCodeInput {m} (w a b A B R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractCodeInputSentence w a b A B R S) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentTyping.abstract_input w a b A B R S h0

theorem abstractCodeInput_kernel_certificate {m} (w a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractCodeInputSentence w a b A B R S)) := TheoryTransport.sentence (source_abstractCodeInput w a b A B R S)

theorem native_abstractCodeInput {m} (w a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractCodeInputSentence w a b A B R S)) := ZFReplay.replay (abstractCodeInput_kernel_certificate w a b A B R S)

def abstractCodeListsSentence {m} (w a b A B R S : Fin m) : Source.Sentence := ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((SyntaxMixedImageCodeSyntax.termLists w a B A b R S))).close

theorem source_abstractCodeLists {m} (w a b A B R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractCodeListsSentence w a b A B R S) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentTyping.abstract_lists w a b A B R S h0

theorem abstractCodeLists_kernel_certificate {m} (w a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractCodeListsSentence w a b A B R S)) := TheoryTransport.sentence (source_abstractCodeLists w a b A B R S)

theorem native_abstractCodeLists {m} (w a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractCodeListsSentence w a b A B R S)) := ZFReplay.replay (abstractCodeLists_kernel_certificate w a b A B R S)

def abstractCodeNaturalSentence {m} (w a b A B R S : Fin m) : Source.Sentence := ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp (((Formula.mem R w).conj (Formula.mem S w)))).close

theorem source_abstractCodeNatural {m} (w a b A B R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractCodeNaturalSentence w a b A B R S) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentTyping.abstract_natural w a b A B R S h0

theorem abstractCodeNatural_kernel_certificate {m} (w a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractCodeNaturalSentence w a b A B R S)) := TheoryTransport.sentence (source_abstractCodeNatural w a b A B R S)

theorem native_abstractCodeNatural {m} (w a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractCodeNaturalSentence w a b A B R S)) := ZFReplay.replay (abstractCodeNatural_kernel_certificate w a b A B R S)

def abstractCodeUniqueSentence {m} (w a b A B R S U V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B U V).imp (((Formula.equal R U).conj (Formula.equal S V)))))).close

theorem source_abstractCodeUnique {m} (w a b A B R S U V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractCodeUniqueSentence w a b A B R S U V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B U V) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B U V) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentUnique.abstract_unique hZ w a b A B R S U V h0 h1 h2

theorem abstractCodeUnique_kernel_certificate {m} (w a b A B R S U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractCodeUniqueSentence w a b A B R S U V)) := TheoryTransport.sentence (source_abstractCodeUnique w a b A B R S U V)

theorem native_abstractCodeUnique {m} (w a b A B R S U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractCodeUniqueSentence w a b A B R S U V)) := ZFReplay.replay (abstractCodeUnique_kernel_certificate w a b A B R S U V)

def abstractCodeUniqueOutputSentence {m} (w a b A B R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((SyntaxTopCodedEnvironmentFiber.abstractUnique w a b A B R S)))).close

theorem source_abstractCodeUniqueOutput {m} (w a b A B R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractCodeUniqueOutputSentence w a b A B R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentFiber.abstract_unique_output hZ w a b A B R S h0 h1

theorem abstractCodeUniqueOutput_kernel_certificate {m} (w a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractCodeUniqueOutputSentence w a b A B R S)) := TheoryTransport.sentence (source_abstractCodeUniqueOutput w a b A B R S)

theorem native_abstractCodeUniqueOutput {m} (w a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractCodeUniqueOutputSentence w a b A B R S)) := ZFReplay.replay (abstractCodeUniqueOutput_kernel_certificate w a b A B R S)

def abstractCodeFiberSentence {m} (w a b A B : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopEnvironmentSyntax.abstractInput w a b A B).imp ((SyntaxTopCodedEnvironmentFiber.abstractFiber w a b A B)))).close

theorem source_abstractCodeFiber {m} (w a b A B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractCodeFiberSentence w a b A B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopEnvironmentSyntax.abstractInput w a b A B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTopEnvironmentSyntax.abstractInput w a b A B) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentFiber.abstract_actual_fiber hZ w a b A B h0 h1

theorem abstractCodeFiber_kernel_certificate {m} (w a b A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractCodeFiberSentence w a b A B)) := TheoryTransport.sentence (source_abstractCodeFiber w a b A B)

theorem native_abstractCodeFiber {m} (w a b A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractCodeFiberSentence w a b A B)) := ZFReplay.replay (abstractCodeFiber_kernel_certificate w a b A B)

def abstractCodeExistsIffSentence {m} (w a b A B : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxTopCodedEnvironmentSyntax.existsAbstract w a b A B).iff (SyntaxTopEnvironmentSyntax.abstractInput w a b A B)))).close

theorem source_abstractCodeExistsIff {m} (w a b A B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractCodeExistsIffSentence w a b A B) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentFiber.abstract_exists_iff hZ w a b A B h0

theorem abstractCodeExistsIff_kernel_certificate {m} (w a b A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractCodeExistsIffSentence w a b A B)) := TheoryTransport.sentence (source_abstractCodeExistsIff w a b A B)

theorem native_abstractCodeExistsIff {m} (w a b A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractCodeExistsIffSentence w a b A B)) := ZFReplay.replay (abstractCodeExistsIff_kernel_certificate w a b A B)

def abstractCodeFiberIffSentence {m} (w a b A B : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxTopCodedEnvironmentFiber.abstractFiber w a b A B).iff (SyntaxTopEnvironmentSyntax.abstractInput w a b A B)))).close

theorem source_abstractCodeFiberIff {m} (w a b A B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractCodeFiberIffSentence w a b A B) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentFiber.abstract_fiber_iff hZ w a b A B h0

theorem abstractCodeFiberIff_kernel_certificate {m} (w a b A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractCodeFiberIffSentence w a b A B)) := TheoryTransport.sentence (source_abstractCodeFiberIff w a b A B)

theorem native_abstractCodeFiberIff {m} (w a b A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractCodeFiberIffSentence w a b A B)) := ZFReplay.replay (abstractCodeFiberIff_kernel_certificate w a b A B)

def abstractFormulaFiberSentence {m} (w a b A B R S n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((FormulaCodeSyntax.formulaCode w n a B).imp ((SyntaxMixedFormulaOutputSyntax.fiber w R S a B A b n))))).close

theorem source_abstractFormulaFiber {m} (w a b A B R S n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractFormulaFiberSentence w a b A B R S n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w n a B) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FormulaCodeSyntax.formulaCode w n a B) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaAtCodes.abstract_formula_fiber hZ w a b A B R S n h0 h1 h2

theorem abstractFormulaFiber_kernel_certificate {m} (w a b A B R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractFormulaFiberSentence w a b A B R S n)) := TheoryTransport.sentence (source_abstractFormulaFiber w a b A B R S n)

theorem native_abstractFormulaFiber {m} (w a b A B R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractFormulaFiberSentence w a b A B R S n)) := ZFReplay.replay (abstractFormulaFiber_kernel_certificate w a b A B R S n)

def abstractFormulaExistsSentence {m} (w a b A B R S n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((FormulaCodeSyntax.formulaCode w n a B).imp ((SyntaxMixedFormulaOutputSyntax.existsOutput w R S a B A b n))))).close

theorem source_abstractFormulaExists {m} (w a b A B R S n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractFormulaExistsSentence w a b A B R S n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w n a B) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FormulaCodeSyntax.formulaCode w n a B) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaAtCodes.abstract_formula_exists hZ w a b A B R S n h0 h1 h2

theorem abstractFormulaExists_kernel_certificate {m} (w a b A B R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractFormulaExistsSentence w a b A B R S n)) := TheoryTransport.sentence (source_abstractFormulaExists w a b A B R S n)

theorem native_abstractFormulaExists {m} (w a b A B R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractFormulaExistsSentence w a b A B R S n)) := ZFReplay.replay (abstractFormulaExists_kernel_certificate w a b A B R S n)

def abstractActualZeroSentence {m} (w a b A B f g i q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopEnvironmentSyntax.abstractEnv w a b A B f g).imp ((empty i).imp (((GraphSyntax.edge g i q).iff (SyntaxVariableSyntax.code true w i q)))))).close

theorem source_abstractActualZero {m} (w a b A B f g i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractActualZeroSentence w a b A B f g i q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty i) (Context.add (SyntaxTopEnvironmentSyntax.abstractEnv w a b A B f g) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxTopEnvironmentSyntax.abstractEnv w a b A B f g) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty i) := .hyp (Or.inl rfl)
  exact SyntaxTopEnvironmentFields.abstract_zero hZ w a b A B f g i q h0 h1 h2

theorem abstractActualZero_kernel_certificate {m} (w a b A B f g i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractActualZeroSentence w a b A B f g i q)) := TheoryTransport.sentence (source_abstractActualZero w a b A B f g i q)

theorem native_abstractActualZero {m} (w a b A B f g i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractActualZeroSentence w a b A B f g i q)) := ZFReplay.replay (abstractActualZero_kernel_certificate w a b A B f g i q)

def abstractCodeZeroSentence {m} (w a b A B R S i q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((empty i).imp ((((Formula.mem i B).conj (StructuralListFieldSyntax.field w S i q)).iff (SyntaxVariableSyntax.code true w i q)))))).close

theorem source_abstractCodeZero {m} (w a b A B R S i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractCodeZeroSentence w a b A B R S i q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty i) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty i) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentFields.abstract_zero hZ w a b A B R S i q h0 h1 h2

theorem abstractCodeZero_kernel_certificate {m} (w a b A B R S i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractCodeZeroSentence w a b A B R S i q)) := TheoryTransport.sentence (source_abstractCodeZero w a b A B R S i q)

theorem native_abstractCodeZero {m} (w a b A B R S i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractCodeZeroSentence w a b A B R S i q)) := ZFReplay.replay (abstractCodeZero_kernel_certificate w a b A B R S i q)

def abstractActualBoundSentence {m} (w a b A B f g i j q : Fin m) : Source.Sentence := ((SyntaxTopEnvironmentSyntax.abstractEnv w a b A B f g).imp ((Formula.mem i a).imp ((successor j i).imp (((GraphSyntax.edge f i q).iff (SyntaxVariableSyntax.code true w j q)))))).close

theorem source_abstractActualBound {m} (w a b A B f g i j q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractActualBoundSentence w a b A B f g i j q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor j i) (Context.add (Formula.mem i a) (Context.add (SyntaxTopEnvironmentSyntax.abstractEnv w a b A B f g) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxTopEnvironmentSyntax.abstractEnv w a b A B f g) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem i a) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor j i) := .hyp (Or.inl rfl)
  exact SyntaxTopEnvironmentFields.abstract_bound hZ w a b A B f g i j q h0 h1 h2

theorem abstractActualBound_kernel_certificate {m} (w a b A B f g i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractActualBoundSentence w a b A B f g i j q)) := TheoryTransport.sentence (source_abstractActualBound w a b A B f g i j q)

theorem native_abstractActualBound {m} (w a b A B f g i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractActualBoundSentence w a b A B f g i j q)) := ZFReplay.replay (abstractActualBound_kernel_certificate w a b A B f g i j q)

def abstractCodeBoundSentence {m} (w a b A B R S i j q : Fin m) : Source.Sentence := ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((Formula.mem i a).imp ((successor j i).imp ((((Formula.mem i a).conj (StructuralListFieldSyntax.field w R i q)).iff (SyntaxVariableSyntax.code true w j q)))))).close

theorem source_abstractCodeBound {m} (w a b A B R S i j q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractCodeBoundSentence w a b A B R S i j q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor j i) (Context.add (Formula.mem i a) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem i a) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor j i) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentFields.abstract_bound hZ w a b A B R S i j q h0 h1 h2

theorem abstractCodeBound_kernel_certificate {m} (w a b A B R S i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractCodeBoundSentence w a b A B R S i j q)) := TheoryTransport.sentence (source_abstractCodeBound w a b A B R S i j q)

theorem native_abstractCodeBound {m} (w a b A B R S i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractCodeBoundSentence w a b A B R S i j q)) := ZFReplay.replay (abstractCodeBound_kernel_certificate w a b A B R S i j q)

def abstractActualFreeSentence {m} (w a b A B f g i j q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopEnvironmentSyntax.abstractEnv w a b A B f g).imp ((Formula.mem j b).imp ((successor i j).imp (((GraphSyntax.edge g i q).iff (SyntaxVariableSyntax.code false w j q))))))).close

theorem source_abstractActualFree {m} (w a b A B f g i j q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractActualFreeSentence w a b A B f g i j q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor i j) (Context.add (Formula.mem j b) (Context.add (SyntaxTopEnvironmentSyntax.abstractEnv w a b A B f g) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxTopEnvironmentSyntax.abstractEnv w a b A B f g) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem j b) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor i j) := .hyp (Or.inl rfl)
  exact SyntaxTopEnvironmentFields.abstract_free hZ w a b A B f g i j q h0 h1 h2 h3

theorem abstractActualFree_kernel_certificate {m} (w a b A B f g i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractActualFreeSentence w a b A B f g i j q)) := TheoryTransport.sentence (source_abstractActualFree w a b A B f g i j q)

theorem native_abstractActualFree {m} (w a b A B f g i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractActualFreeSentence w a b A B f g i j q)) := ZFReplay.replay (abstractActualFree_kernel_certificate w a b A B f g i j q)

def abstractCodeFreeSentence {m} (w a b A B R S i j q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((Formula.mem j b).imp ((successor i j).imp ((((Formula.mem i B).conj (StructuralListFieldSyntax.field w S i q)).iff (SyntaxVariableSyntax.code false w j q))))))).close

theorem source_abstractCodeFree {m} (w a b A B R S i j q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractCodeFreeSentence w a b A B R S i j q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor i j) (Context.add (Formula.mem j b) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem j b) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor i j) := .hyp (Or.inl rfl)
  exact SyntaxTopCodedEnvironmentFields.abstract_free hZ w a b A B R S i j q h0 h1 h2 h3

theorem abstractCodeFree_kernel_certificate {m} (w a b A B R S i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractCodeFreeSentence w a b A B R S i j q)) := TheoryTransport.sentence (source_abstractCodeFree w a b A B R S i j q)

theorem native_abstractCodeFree {m} (w a b A B R S i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractCodeFreeSentence w a b A B R S i j q)) := ZFReplay.replay (abstractCodeFree_kernel_certificate w a b A B R S i j q)

end PPAC.Migration.Internal.ObjectTopEnvironment
