import PPAC.Migration.Internal.SchemaIndexSites

/-! Actual three schema index graphs, list codes and uniform full-formula renaming in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectSchemaIndex
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SchemaIndexSyntax

def doubleShiftExistsSentence {m} (w n b c : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((successor b n).imp ((successor c b).imp ((SchemaDoubleShiftSyntax.existsMap w n b c)))))).close

theorem source_doubleShiftExists {m} (w n b c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (doubleShiftExistsSentence w n b c) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor c b) (Context.add (successor b n) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor b n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor c b) := .hyp (Or.inl rfl)
  exact SchemaDoubleShiftGraph.exists_map hZ w n b c h0 h1 h2 h3

theorem doubleShiftExists_kernel_certificate {m} (w n b c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (doubleShiftExistsSentence w n b c)) := TheoryTransport.sentence (source_doubleShiftExists w n b c)

theorem native_doubleShiftExists {m} (w n b c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (doubleShiftExistsSentence w n b c)) := ZFReplay.replay (doubleShiftExists_kernel_certificate w n b c)

def doubleShiftMapSentence {m} (w n b c g : Fin m) : Source.Sentence := ((SchemaDoubleShiftSyntax.map w n b c g).imp ((SyntaxIndexMapSyntax.indexMap w g n c))).close

theorem source_doubleShiftMap {m} (w n b c g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (doubleShiftMapSentence w n b c g) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SchemaDoubleShiftSyntax.map w n b c g) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SchemaDoubleShiftSyntax.map w n b c g) := .hyp (Or.inl rfl)
  exact SchemaDoubleShiftGraph.index_map w n b c g h0

theorem doubleShiftMap_kernel_certificate {m} (w n b c g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (doubleShiftMapSentence w n b c g)) := TheoryTransport.sentence (source_doubleShiftMap w n b c g)

theorem native_doubleShiftMap {m} (w n b c g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (doubleShiftMapSentence w n b c g)) := ZFReplay.replay (doubleShiftMap_kernel_certificate w n b c g)

def doubleShiftEdgesIffSentence {m} (w n b c g i j : Fin m) : Source.Sentence := ((SchemaDoubleShiftSyntax.map w n b c g).imp (((edge g i j).iff ((Formula.mem i n).conj (SchemaDoubleShiftSyntax.displacement i j))))).close

theorem source_doubleShiftEdgesIff {m} (w n b c g i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (doubleShiftEdgesIffSentence w n b c g i j) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SchemaDoubleShiftSyntax.map w n b c g) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SchemaDoubleShiftSyntax.map w n b c g) := .hyp (Or.inl rfl)
  exact SchemaDoubleShiftGraph.edge_iff hZ w n b c g i j h0

theorem doubleShiftEdgesIff_kernel_certificate {m} (w n b c g i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (doubleShiftEdgesIffSentence w n b c g i j)) := TheoryTransport.sentence (source_doubleShiftEdgesIff w n b c g i j)

theorem native_doubleShiftEdgesIff {m} (w n b c g i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (doubleShiftEdgesIffSentence w n b c g i j)) := ZFReplay.replay (doubleShiftEdgesIff_kernel_certificate w n b c g i j)

def doubleShiftUniqueSentence {m} (w n b c g h : Fin m) : Source.Sentence := ((SchemaDoubleShiftSyntax.map w n b c g).imp ((SchemaDoubleShiftSyntax.map w n b c h).imp ((Formula.equal g h)))).close

theorem source_doubleShiftUnique {m} (w n b c g h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (doubleShiftUniqueSentence w n b c g h) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SchemaDoubleShiftSyntax.map w n b c h) (Context.add (SchemaDoubleShiftSyntax.map w n b c g) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SchemaDoubleShiftSyntax.map w n b c g) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SchemaDoubleShiftSyntax.map w n b c h) := .hyp (Or.inl rfl)
  exact SchemaDoubleShiftGraph.unique_map hZ w n b c g h h0 h1

theorem doubleShiftUnique_kernel_certificate {m} (w n b c g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (doubleShiftUniqueSentence w n b c g h)) := TheoryTransport.sentence (source_doubleShiftUnique w n b c g h)

theorem native_doubleShiftUnique {m} (w n b c g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (doubleShiftUniqueSentence w n b c g h)) := ZFReplay.replay (doubleShiftUnique_kernel_certificate w n b c g h)

def schemaIndexGraphExistsSentence {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((chain n scopes).imp ((existsGraph site w n scopes))))).close

theorem source_schemaIndexGraphExists {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (schemaIndexGraphExistsSentence site scopes w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (chain n scopes) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (chain n scopes) := .hyp (Or.inl rfl)
  exact SchemaIndexGraphExistence.exists_graph hZ site w n scopes h0 h1 h2

theorem schemaIndexGraphExists_kernel_certificate {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (schemaIndexGraphExistsSentence site scopes w n)) := TheoryTransport.sentence (source_schemaIndexGraphExists site scopes w n)

theorem native_schemaIndexGraphExists {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (schemaIndexGraphExistsSentence site scopes w n)) := ZFReplay.replay (schemaIndexGraphExists_kernel_certificate site scopes w n)

def schemaIndexMapSentence {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w n g : Fin m) : Source.Sentence := ((SchemaIndexSyntax.graph site w n scopes g).imp ((SyntaxIndexMapSyntax.indexMap w g (sourceScope site scopes) (targetScope site scopes)))).close

theorem source_schemaIndexMap {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w n g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (schemaIndexMapSentence site scopes w n g) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SchemaIndexSyntax.graph site w n scopes g) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SchemaIndexSyntax.graph site w n scopes g) := .hyp (Or.inl rfl)
  exact SchemaIndexFacts.graph_map site w n scopes g h0

theorem schemaIndexMap_kernel_certificate {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w n g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (schemaIndexMapSentence site scopes w n g)) := TheoryTransport.sentence (source_schemaIndexMap site scopes w n g)

theorem native_schemaIndexMap {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w n g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (schemaIndexMapSentence site scopes w n g)) := ZFReplay.replay (schemaIndexMap_kernel_certificate site scopes w n g)

def schemaIndexZeroIffSentence {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w n g z y : Fin m) : Source.Sentence := ((omega w).imp ((SchemaIndexSyntax.graph site w n scopes g).imp ((empty z).imp (((edge g z y).iff (empty y)))))).close

theorem source_schemaIndexZeroIff {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w n g z y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (schemaIndexZeroIffSentence site scopes w n g z y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (SchemaIndexSyntax.graph site w n scopes g) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SchemaIndexSyntax.graph site w n scopes g) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact SchemaIndexFacts.graph_zero_iff hZ site w n scopes g z y h0 h1 h2

theorem schemaIndexZeroIff_kernel_certificate {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w n g z y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (schemaIndexZeroIffSentence site scopes w n g z y)) := TheoryTransport.sentence (source_schemaIndexZeroIff site scopes w n g z y)

theorem native_schemaIndexZeroIff {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w n g z y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (schemaIndexZeroIffSentence site scopes w n g z y)) := ZFReplay.replay (schemaIndexZeroIff_kernel_certificate site scopes w n g z y)

def schemaCollectionOneIffSentence {m} (image : Bool) (scopes : Fin 4 → Fin m) (w n g p y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((state (if image then 2 else 1) w n scopes g).imp ((SyntaxNumeralSyntax.numeral 1 p).imp (((edge g p y).iff (Formula.equal y p))))))).close

theorem source_schemaCollectionOneIff {m} (image : Bool) (scopes : Fin 4 → Fin m) (w n g p y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (schemaCollectionOneIffSentence image scopes w n g p y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 1 p) (Context.add (state (if image then 2 else 1) w n scopes g) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (state (if image then 2 else 1) w n scopes g) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral 1 p) := .hyp (Or.inl rfl)
  exact SchemaIndexHead.one_iff hZ image w n scopes g p y h0 h1 h2 h3

theorem schemaCollectionOneIff_kernel_certificate {m} (image : Bool) (scopes : Fin 4 → Fin m) (w n g p y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (schemaCollectionOneIffSentence image scopes w n g p y)) := TheoryTransport.sentence (source_schemaCollectionOneIff image scopes w n g p y)

theorem native_schemaCollectionOneIff {m} (image : Bool) (scopes : Fin 4 → Fin m) (w n g p y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (schemaCollectionOneIffSentence image scopes w n g p y)) := ZFReplay.replay (schemaCollectionOneIff_kernel_certificate image scopes w n g p y)

def schemaSeparationTailIffSentence {m} (scopes : Fin 4 → Fin m) (w n g i I j J : Fin m) : Source.Sentence := ((omega w).imp ((state 0 w n scopes g).imp ((Formula.mem i n).imp ((successor I i).imp ((successor J j).imp (((edge g I J).iff (SchemaDoubleShiftSyntax.displacement i j)))))))).close

theorem source_schemaSeparationTailIff {m} (scopes : Fin 4 → Fin m) (w n g i I j J : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (schemaSeparationTailIffSentence scopes w n g i I j J) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor J j) (Context.add (successor I i) (Context.add (Formula.mem i n) (Context.add (state 0 w n scopes g) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (state 0 w n scopes g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem i n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (successor I i) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (successor J j) := .hyp (Or.inl rfl)
  exact SchemaIndexTail.separation_graph hZ w n scopes g i I j J h0 h1 h2 h3 h4

theorem schemaSeparationTailIff_kernel_certificate {m} (scopes : Fin 4 → Fin m) (w n g i I j J : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (schemaSeparationTailIffSentence scopes w n g i I j J)) := TheoryTransport.sentence (source_schemaSeparationTailIff scopes w n g i I j J)

theorem native_schemaSeparationTailIff {m} (scopes : Fin 4 → Fin m) (w n g i I j J : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (schemaSeparationTailIffSentence scopes w n g i I j J)) := ZFReplay.replay (schemaSeparationTailIff_kernel_certificate scopes w n g i I j J)

def schemaCollectionTailIffSentence {m} (image : Bool) (scopes : Fin 4 → Fin m) (w n g i u I j v J : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((state (if image then 2 else 1) w n scopes g).imp ((Formula.mem i n).imp ((successor u i).imp ((successor I u).imp ((successor v j).imp ((successor J v).imp (((edge g I J).iff (if image then SchemaDoubleShiftSyntax.displacement i j else successor j i))))))))))).close

theorem source_schemaCollectionTailIff {m} (image : Bool) (scopes : Fin 4 → Fin m) (w n g i u I j v J : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (schemaCollectionTailIffSentence image scopes w n g i u I j v J) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor J v) (Context.add (successor v j) (Context.add (successor I u) (Context.add (successor u i) (Context.add (Formula.mem i n) (Context.add (state (if image then 2 else 1) w n scopes g) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
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
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (state (if image then 2 else 1) w n scopes g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (Formula.mem i n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (successor u i) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (successor I u) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (successor v j) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (successor J v) := .hyp (Or.inl rfl)
  exact SchemaIndexTail.collection_graph hZ image w n scopes g i u I j v J h0 h1 h2 h3 h4 h5 h6 h7

theorem schemaCollectionTailIff_kernel_certificate {m} (image : Bool) (scopes : Fin 4 → Fin m) (w n g i u I j v J : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (schemaCollectionTailIffSentence image scopes w n g i u I j v J)) := TheoryTransport.sentence (source_schemaCollectionTailIff image scopes w n g i u I j v J)

theorem native_schemaCollectionTailIff {m} (image : Bool) (scopes : Fin 4 → Fin m) (w n g i u I j v J : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (schemaCollectionTailIffSentence image scopes w n g i u I j v J)) := ZFReplay.replay (schemaCollectionTailIff_kernel_certificate image scopes w n g i u I j v J)

def schemaIndexStateExistsSentence {m} (site : Fin 3) (w n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((existsState site w n)))).close

theorem source_schemaIndexStateExists {m} (site : Fin 3) (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (schemaIndexStateExistsSentence site w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inl rfl)
  exact SchemaIndexScopes.exists_state hZ site w n h0 h1

theorem schemaIndexStateExists_kernel_certificate {m} (site : Fin 3) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (schemaIndexStateExistsSentence site w n)) := TheoryTransport.sentence (source_schemaIndexStateExists site w n)

theorem native_schemaIndexStateExists {m} (site : Fin 3) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (schemaIndexStateExistsSentence site w n)) := ZFReplay.replay (schemaIndexStateExists_kernel_certificate site w n)

def schemaIndexCodeExistsSentence {m} (site : Fin 3) (w n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((existsCodedState site w n)))).close

theorem source_schemaIndexCodeExists {m} (site : Fin 3) (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (schemaIndexCodeExistsSentence site w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inl rfl)
  exact SchemaIndexCoded.exists_coded_state hZ site w n h0 h1

theorem schemaIndexCodeExists_kernel_certificate {m} (site : Fin 3) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (schemaIndexCodeExistsSentence site w n)) := TheoryTransport.sentence (source_schemaIndexCodeExists site w n)

theorem native_schemaIndexCodeExists {m} (site : Fin 3) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (schemaIndexCodeExistsSentence site w n)) := ZFReplay.replay (schemaIndexCodeExists_kernel_certificate site w n)

def schemaIndexRenameLawSentence {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w g R S z : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w g (sourceScope site scopes) (targetScope site scopes) R).imp ((SyntaxIdentityMapSyntax.identityCode w z S).imp ((SchemaIndexRenameSystem.law site w scopes R S z))))).close

theorem source_schemaIndexRenameLaw {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w g R S z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (schemaIndexRenameLawSentence site scopes w g R S z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIdentityMapSyntax.identityCode w z S) (Context.add (SyntaxMapCodeSyntax.encoded w g (sourceScope site scopes) (targetScope site scopes) R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.encoded w g (sourceScope site scopes) (targetScope site scopes) R) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w z S) := .hyp (Or.inl rfl)
  exact SchemaIndexRenameSystem.law_proved hZ site w scopes g R S z h0 h1 h2

theorem schemaIndexRenameLaw_kernel_certificate {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w g R S z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (schemaIndexRenameLawSentence site scopes w g R S z)) := TheoryTransport.sentence (source_schemaIndexRenameLaw site scopes w g R S z)

theorem native_schemaIndexRenameLaw {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w g R S z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (schemaIndexRenameLawSentence site scopes w g R S z)) := ZFReplay.replay (schemaIndexRenameLaw_kernel_certificate site scopes w g R S z)

def schemaIndexRenameAtSentence {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w R S z a : Fin m) : Source.Sentence := ((SchemaIndexRenameSystem.law site w scopes R S z).imp ((FormulaCodeSyntax.formulaCode w a (sourceScope site scopes) z).imp ((SyntaxRenameOutputSyntax.fiber w R S (sourceScope site scopes) z (targetScope site scopes) z a)))).close

theorem source_schemaIndexRenameAt {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w R S z a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (schemaIndexRenameAtSentence site scopes w R S z a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w a (sourceScope site scopes) z) (Context.add (SchemaIndexRenameSystem.law site w scopes R S z) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SchemaIndexRenameSystem.law site w scopes R S z) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FormulaCodeSyntax.formulaCode w a (sourceScope site scopes) z) := .hyp (Or.inl rfl)
  exact SchemaIndexRenameSystem.law_at site w scopes R S z a h0 h1

theorem schemaIndexRenameAt_kernel_certificate {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w R S z a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (schemaIndexRenameAtSentence site scopes w R S z a)) := TheoryTransport.sentence (source_schemaIndexRenameAt site scopes w R S z a)

theorem native_schemaIndexRenameAt {m} (site : Fin 3) (scopes : Fin 4 → Fin m) (w R S z a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (schemaIndexRenameAtSentence site scopes w R S z a)) := ZFReplay.replay (schemaIndexRenameAt_kernel_certificate site scopes w R S z a)

def schemaIndexSystemExistsSentence {m} (site : Fin 3) (w n z : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((empty z).imp ((SchemaIndexRenameSystem.existsSystem site w n z))))).close

theorem source_schemaIndexSystemExists {m} (site : Fin 3) (w n z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (schemaIndexSystemExistsSentence site w n z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact SchemaIndexRenameSystem.exists_system hZ site w n z h0 h1 h2

theorem schemaIndexSystemExists_kernel_certificate {m} (site : Fin 3) (w n z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (schemaIndexSystemExistsSentence site w n z)) := TheoryTransport.sentence (source_schemaIndexSystemExists site w n z)

theorem native_schemaIndexSystemExists {m} (site : Fin 3) (w n z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (schemaIndexSystemExistsSentence site w n z)) := ZFReplay.replay (schemaIndexSystemExists_kernel_certificate site w n z)

end PPAC.Migration.Internal.ObjectSchemaIndex
