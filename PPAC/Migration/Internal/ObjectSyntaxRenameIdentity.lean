import PPAC.Migration.Internal.SyntaxIdentityInduction

/-! 实际恒等图/自然映射码、binder提升恒等及所有内部公式恒等的源和YesMetaZFC原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxRenameIdentity
open Source SourceAlgebra SourceLogic OmegaSyntax

def graphExistsSentence {m} (a : Fin m) : Source.Sentence := (Formula.ex (SyntaxIdentityMapSyntax.graph a.castSucc (Fin.last m))).close

theorem source_graphExists {m} (a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphExistsSentence a) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact SyntaxIdentityGraph.exists_graph hZ a

theorem graphExists_kernel_certificate {m} (a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphExistsSentence a)) := TheoryTransport.sentence (source_graphExists a)

theorem native_graphExists {m} (a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphExistsSentence a)) := ZFReplay.replay (graphExists_kernel_certificate a)

def graphEdgesSentence {m} (a r i j : Fin m) : Source.Sentence := ((SyntaxIdentityMapSyntax.graph a r).imp ((GraphSyntax.edge r i j).iff ((Formula.mem i a).conj (.equal i j)))).close

theorem source_graphEdges {m} (a r i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphEdgesSentence a r i j) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIdentityMapSyntax.graph a r) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxIdentityMapSyntax.graph a r) := .hyp (Or.inl rfl)
  exact SyntaxIdentityGraph.edge_iff a r i j h0

theorem graphEdges_kernel_certificate {m} (a r i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphEdgesSentence a r i j)) := TheoryTransport.sentence (source_graphEdges a r i j)

theorem native_graphEdges {m} (a r i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphEdgesSentence a r i j)) := ZFReplay.replay (graphEdges_kernel_certificate a r i j)

def graphUniqueSentence {m} (a r s : Fin m) : Source.Sentence := ((SyntaxIdentityMapSyntax.graph a r).imp ((SyntaxIdentityMapSyntax.graph a s).imp (.equal r s))).close

theorem source_graphUnique {m} (a r s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphUniqueSentence a r s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIdentityMapSyntax.graph a s) (Context.add (SyntaxIdentityMapSyntax.graph a r) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxIdentityMapSyntax.graph a r) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.graph a s) := .hyp (Or.inl rfl)
  exact SyntaxIdentityGraph.unique_graph hZ a r s h0 h1

theorem graphUnique_kernel_certificate {m} (a r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphUniqueSentence a r s)) := TheoryTransport.sentence (source_graphUnique a r s)

theorem native_graphUnique {m} (a r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphUniqueSentence a r s)) := ZFReplay.replay (graphUnique_kernel_certificate a r s)

def graphDiagonalSentence {m} (a r : Fin m) : Source.Sentence := ((SyntaxIdentityMapSyntax.graph a r).imp (SyntaxRenameTermIdentity.diagonal r)).close

theorem source_graphDiagonal {m} (a r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphDiagonalSentence a r) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIdentityMapSyntax.graph a r) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxIdentityMapSyntax.graph a r) := .hyp (Or.inl rfl)
  exact SyntaxIdentityGraph.diagonal a r h0

theorem graphDiagonal_kernel_certificate {m} (a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphDiagonalSentence a r)) := TheoryTransport.sentence (source_graphDiagonal a r)

theorem native_graphDiagonal {m} (a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphDiagonalSentence a r)) := ZFReplay.replay (graphDiagonal_kernel_certificate a r)

def graphIndexMapSentence {m} (w a r : Fin m) : Source.Sentence := ((Formula.mem a w).imp ((SyntaxIdentityMapSyntax.graph a r).imp (SyntaxIndexMapSyntax.indexMap w r a a))).close

theorem source_graphIndexMap {m} (w a r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphIndexMapSentence w a r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIdentityMapSyntax.graph a r) (Context.add (Formula.mem a w) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (Formula.mem a w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.graph a r) := .hyp (Or.inl rfl)
  exact SyntaxIdentityGraph.index_map w a r h0 h1

theorem graphIndexMap_kernel_certificate {m} (w a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphIndexMapSentence w a r)) := TheoryTransport.sentence (source_graphIndexMap w a r)

theorem native_graphIndexMap {m} (w a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphIndexMapSentence w a r)) := ZFReplay.replay (graphIndexMap_kernel_certificate w a r)

def mapExistsSentence {m} (w a : Fin m) : Source.Sentence := ((Formula.mem a w).imp (SyntaxIdentityMapSyntax.existsMap w a)).close

theorem source_mapExists {m} (w a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mapExistsSentence w a) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem a w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (Formula.mem a w) := .hyp (Or.inl rfl)
  exact SyntaxIdentityGraph.exists_map hZ w a h0

theorem mapExists_kernel_certificate {m} (w a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mapExistsSentence w a)) := TheoryTransport.sentence (source_mapExists w a)

theorem native_mapExists {m} (w a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mapExistsSentence w a)) := ZFReplay.replay (mapExists_kernel_certificate w a)

def codeExistsSentence {m} (w a : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp (SyntaxIdentityMapSyntax.existsCode w a))).close

theorem source_codeExists {m} (w a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeExistsSentence w a) := by
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
  exact SyntaxIdentityCode.exists_code hZ w a h0 h1

theorem codeExists_kernel_certificate {m} (w a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeExistsSentence w a)) := TheoryTransport.sentence (source_codeExists w a)

theorem native_codeExists {m} (w a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeExistsSentence w a)) := ZFReplay.replay (codeExists_kernel_certificate w a)

def codeMapSentence {m} (w a R : Fin m) : Source.Sentence := ((SyntaxIdentityMapSyntax.identityCode w a R).imp (SyntaxMapCodeSyntax.mapCode w a a R)).close

theorem source_codeMap {m} (w a R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeMapSentence w a R) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIdentityMapSyntax.identityCode w a R) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a R) := .hyp (Or.inl rfl)
  exact SyntaxIdentityCode.map_code w a R h0

theorem codeMap_kernel_certificate {m} (w a R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeMapSentence w a R)) := TheoryTransport.sentence (source_codeMap w a R)

theorem native_codeMap {m} (w a R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeMapSentence w a R)) := ZFReplay.replay (codeMap_kernel_certificate w a R)

def codeAtGraphSentence {m} (w a R r : Fin m) : Source.Sentence := ((SyntaxIdentityMapSyntax.identityCode w a R).imp ((SyntaxMapCodeSyntax.encoded w r a a R).imp (SyntaxRenameTermIdentity.diagonal r))).close

theorem source_codeAtGraph {m} (w a R r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeAtGraphSentence w a R r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapCodeSyntax.encoded w r a a R) (Context.add (SyntaxIdentityMapSyntax.identityCode w a R) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a R) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a a R) := .hyp (Or.inl rfl)
  exact SyntaxIdentityCode.at_graph hZ w a R r h0 h1

theorem codeAtGraph_kernel_certificate {m} (w a R r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeAtGraphSentence w a R r)) := TheoryTransport.sentence (source_codeAtGraph w a R r)

theorem native_codeAtGraph {m} (w a R r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeAtGraphSentence w a R r)) := ZFReplay.replay (codeAtGraph_kernel_certificate w a R r)

def codeEncodedIffSentence {m} (w a R r : Fin m) : Source.Sentence := ((SyntaxMapCodeSyntax.encoded w r a a R).imp ((SyntaxIdentityMapSyntax.identityCode w a R).iff (SyntaxRenameTermIdentity.diagonal r))).close

theorem source_codeEncodedIff {m} (w a R r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeEncodedIffSentence w a R r) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapCodeSyntax.encoded w r a a R) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a a R) := .hyp (Or.inl rfl)
  exact SyntaxIdentityCode.encoded_iff hZ w a R r h0

theorem codeEncodedIff_kernel_certificate {m} (w a R r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeEncodedIffSentence w a R r)) := TheoryTransport.sentence (source_codeEncodedIff w a R r)

theorem native_codeEncodedIff {m} (w a R r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeEncodedIffSentence w a R r)) := ZFReplay.replay (codeEncodedIff_kernel_certificate w a R r)

def liftValueDiagonalSentence {m} (r a i j : Fin m) : Source.Sentence := ((SyntaxRenameTermIdentity.diagonal r).imp ((SyntaxIndexLiftSyntax.value r a i j).imp (.equal i j))).close

theorem source_liftValueDiagonal {m} (r a i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftValueDiagonalSentence r a i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIndexLiftSyntax.value r a i j) (Context.add (SyntaxRenameTermIdentity.diagonal r) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxRenameTermIdentity.diagonal r) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxIndexLiftSyntax.value r a i j) := .hyp (Or.inl rfl)
  exact SyntaxIdentityLift.value_diagonal hZ r a i j h0 h1

theorem liftValueDiagonal_kernel_certificate {m} (r a i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftValueDiagonalSentence r a i j)) := TheoryTransport.sentence (source_liftValueDiagonal r a i j)

theorem native_liftValueDiagonal {m} (r a i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftValueDiagonalSentence r a i j)) := ZFReplay.replay (liftValueDiagonal_kernel_certificate r a i j)

def liftGraphDiagonalSentence {m} (w r a c u v g : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameTermIdentity.diagonal r).imp ((SyntaxIndexLiftSyntax.lifted w r a c u v g).imp (SyntaxRenameTermIdentity.diagonal g)))).close

theorem source_liftGraphDiagonal {m} (w r a c u v g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftGraphDiagonalSentence w r a c u v g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIndexLiftSyntax.lifted w r a c u v g) (Context.add (SyntaxRenameTermIdentity.diagonal r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxRenameTermIdentity.diagonal r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxIndexLiftSyntax.lifted w r a c u v g) := .hyp (Or.inl rfl)
  exact SyntaxIdentityLift.graph_diagonal hZ w r a c u v g h0 h1 h2

theorem liftGraphDiagonal_kernel_certificate {m} (w r a c u v g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftGraphDiagonalSentence w r a c u v g)) := TheoryTransport.sentence (source_liftGraphDiagonal w r a c u v g)

theorem native_liftGraphDiagonal {m} (w r a c u v g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftGraphDiagonalSentence w r a c u v g)) := ZFReplay.replay (liftGraphDiagonal_kernel_certificate w r a c u v g)

def liftCodeSentence {m} (w a R u v L : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w a R).imp ((SyntaxMapLiftSyntax.codedLift w a a R u v L).imp ((Formula.equal u v).conj (SyntaxIdentityMapSyntax.identityCode w u L))))).close

theorem source_liftCode {m} (w a R u v L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftCodeSentence w a R u v L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapLiftSyntax.codedLift w a a R u v L) (Context.add (SyntaxIdentityMapSyntax.identityCode w a R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a R) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMapLiftSyntax.codedLift w a a R u v L) := .hyp (Or.inl rfl)
  exact SyntaxIdentityLift.code_lift hZ w a R u v L h0 h1 h2

theorem liftCode_kernel_certificate {m} (w a R u v L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftCodeSentence w a R u v L)) := TheoryTransport.sentence (source_liftCode w a R u v L)

theorem native_liftCode {m} (w a R u v L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftCodeSentence w a R u v L)) := ZFReplay.replay (liftCode_kernel_certificate w a R u v L)

def formulaReflexiveSentence {m} (w R S a b n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w a R).imp ((SyntaxIdentityMapSyntax.identityCode w b S).imp ((FormulaCodeSyntax.formulaCode w n a b).imp (SyntaxRenameIdentitySyntax.self w R S a b n))))).close

theorem source_formulaReflexive {m} (w R S a b n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaReflexiveSentence w R S a b n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (SyntaxIdentityMapSyntax.identityCode w b S) (Context.add (SyntaxIdentityMapSyntax.identityCode w a R) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w b S) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inl rfl)
  exact SyntaxIdentityInduction.reflexive hZ w R S a b n h0 h1 h2 h3

theorem formulaReflexive_kernel_certificate {m} (w R S a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaReflexiveSentence w R S a b n)) := TheoryTransport.sentence (source_formulaReflexive w R S a b n)

theorem native_formulaReflexive {m} (w R S a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaReflexiveSentence w R S a b n)) := ZFReplay.replay (formulaReflexive_kernel_certificate w R S a b n)

def formulaIdentitySentence {m} (w R S a b n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w a R).imp ((SyntaxIdentityMapSyntax.identityCode w b S).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b a b n q).imp (.equal n q))))).close

theorem source_formulaIdentity {m} (w R S a b n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaIdentitySentence w R S a b n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b a b n q) (Context.add (SyntaxIdentityMapSyntax.identityCode w b S) (Context.add (SyntaxIdentityMapSyntax.identityCode w a R) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w b S) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b a b n q) := .hyp (Or.inl rfl)
  exact SyntaxIdentityInduction.identity hZ w R S a b n q h0 h1 h2 h3

theorem formulaIdentity_kernel_certificate {m} (w R S a b n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaIdentitySentence w R S a b n q)) := TheoryTransport.sentence (source_formulaIdentity w R S a b n q)

theorem native_formulaIdentity {m} (w R S a b n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaIdentitySentence w R S a b n q)) := ZFReplay.replay (formulaIdentity_kernel_certificate w R S a b n q)

def formulaIdentityIffSentence {m} (w R S a b n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w a R).imp ((SyntaxIdentityMapSyntax.identityCode w b S).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b a b n q).iff ((FormulaCodeSyntax.formulaCode w n a b).conj (.equal n q)))))).close

theorem source_formulaIdentityIff {m} (w R S a b n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaIdentityIffSentence w R S a b n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIdentityMapSyntax.identityCode w b S) (Context.add (SyntaxIdentityMapSyntax.identityCode w a R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a R) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w b S) := .hyp (Or.inl rfl)
  exact SyntaxIdentityInduction.identity_iff hZ w R S a b n q h0 h1 h2

theorem formulaIdentityIff_kernel_certificate {m} (w R S a b n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaIdentityIffSentence w R S a b n q)) := TheoryTransport.sentence (source_formulaIdentityIff w R S a b n q)

theorem native_formulaIdentityIff {m} (w R S a b n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaIdentityIffSentence w R S a b n q)) := ZFReplay.replay (formulaIdentityIff_kernel_certificate w R S a b n q)

end PPAC.Migration.Internal.ObjectSyntaxRenameIdentity
