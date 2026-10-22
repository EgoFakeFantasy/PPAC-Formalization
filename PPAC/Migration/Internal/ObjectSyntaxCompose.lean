import PPAC.Migration.Internal.SyntaxComposeTermFactor

/-! 实际完整图/原自然码复合与项复合的源及YesMetaZFC原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxCompose
open Source SourceAlgebra SourceLogic OmegaSyntax

def valueSourceSentence {m} (w r t a c i j : Fin m) : Source.Sentence := ((SyntaxIndexMapSyntax.indexMap w r a c).imp ((SyntaxComposeSyntax.value r t i j).imp (Formula.mem i a))).close

theorem source_valueSource {m} (w r t a c i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (valueSourceSentence w r t a c i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxComposeSyntax.value r t i j) (Context.add (SyntaxIndexMapSyntax.indexMap w r a c) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxIndexMapSyntax.indexMap w r a c) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxComposeSyntax.value r t i j) := .hyp (Or.inl rfl)
  exact SyntaxComposePoint.source_member hZ w r t a c i j h0 h1

theorem valueSource_kernel_certificate {m} (w r t a c i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (valueSourceSentence w r t a c i j)) := TheoryTransport.sentence (source_valueSource w r t a c i j)

theorem native_valueSource {m} (w r t a c i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (valueSourceSentence w r t a c i j)) := ZFReplay.replay (valueSource_kernel_certificate w r t a c i j)

def valueTargetSentence {m} (w r t c e i j : Fin m) : Source.Sentence := ((SyntaxIndexMapSyntax.indexMap w t c e).imp ((SyntaxComposeSyntax.value r t i j).imp (Formula.mem j e))).close

theorem source_valueTarget {m} (w r t c e i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (valueTargetSentence w r t c e i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxComposeSyntax.value r t i j) (Context.add (SyntaxIndexMapSyntax.indexMap w t c e) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxIndexMapSyntax.indexMap w t c e) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxComposeSyntax.value r t i j) := .hyp (Or.inl rfl)
  exact SyntaxComposePoint.target_member w r t c e i j h0 h1

theorem valueTarget_kernel_certificate {m} (w r t c e i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (valueTargetSentence w r t c e i j)) := TheoryTransport.sentence (source_valueTarget w r t c e i j)

theorem native_valueTarget {m} (w r t c e i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (valueTargetSentence w r t c e i j)) := ZFReplay.replay (valueTarget_kernel_certificate w r t c e i j)

def valueUniqueSentence {m} (w r t a c e i j l : Fin m) : Source.Sentence := ((SyntaxIndexMapSyntax.indexMap w r a c).imp ((SyntaxIndexMapSyntax.indexMap w t c e).imp ((SyntaxComposeSyntax.value r t i j).imp ((SyntaxComposeSyntax.value r t i l).imp (Formula.equal j l))))).close

theorem source_valueUnique {m} (w r t a c e i j l : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (valueUniqueSentence w r t a c e i j l) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxComposeSyntax.value r t i l) (Context.add (SyntaxComposeSyntax.value r t i j) (Context.add (SyntaxIndexMapSyntax.indexMap w t c e) (Context.add (SyntaxIndexMapSyntax.indexMap w r a c) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxIndexMapSyntax.indexMap w r a c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxIndexMapSyntax.indexMap w t c e) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxComposeSyntax.value r t i j) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxComposeSyntax.value r t i l) := .hyp (Or.inl rfl)
  exact SyntaxComposePoint.unique hZ w r t a c e i j l h0 h1 h2 h3

theorem valueUnique_kernel_certificate {m} (w r t a c e i j l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (valueUniqueSentence w r t a c e i j l)) := TheoryTransport.sentence (source_valueUnique w r t a c e i j l)

theorem native_valueUnique {m} (w r t a c e i j l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (valueUniqueSentence w r t a c e i j l)) := ZFReplay.replay (valueUnique_kernel_certificate w r t a c e i j l)

def pointExistsSentence {m} (w r t a c e i : Fin m) : Source.Sentence := ((SyntaxIndexMapSyntax.indexMap w r a c).imp ((SyntaxIndexMapSyntax.indexMap w t c e).imp ((Formula.mem i a).imp (ReplacementPredicates.hasValue SyntaxComposeSyntax.matrix (Source.SetLanguage.args2 r t) i)))).close

theorem source_pointExists {m} (w r t a c e i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pointExistsSentence w r t a c e i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i a) (Context.add (SyntaxIndexMapSyntax.indexMap w t c e) (Context.add (SyntaxIndexMapSyntax.indexMap w r a c) (Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (SyntaxIndexMapSyntax.indexMap w r a c) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxIndexMapSyntax.indexMap w t c e) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem i a) := .hyp (Or.inl rfl)
  exact SyntaxComposeExistence.point_exists (Source.SetLanguage.args2 r t) w a c e i h0 h1 h2

theorem pointExists_kernel_certificate {m} (w r t a c e i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pointExistsSentence w r t a c e i)) := TheoryTransport.sentence (source_pointExists w r t a c e i)

theorem native_pointExists {m} (w r t a c e i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pointExistsSentence w r t a c e i)) := ZFReplay.replay (pointExists_kernel_certificate w r t a c e i)

def pointFiberSentence {m} (w r t a c e i : Fin m) : Source.Sentence := ((SyntaxIndexMapSyntax.indexMap w r a c).imp ((SyntaxIndexMapSyntax.indexMap w t c e).imp ((Formula.mem i a).imp (ReplacementPredicates.fiber SyntaxComposeSyntax.matrix (Source.SetLanguage.args2 r t) i)))).close

theorem source_pointFiber {m} (w r t a c e i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pointFiberSentence w r t a c e i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i a) (Context.add (SyntaxIndexMapSyntax.indexMap w t c e) (Context.add (SyntaxIndexMapSyntax.indexMap w r a c) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxIndexMapSyntax.indexMap w r a c) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxIndexMapSyntax.indexMap w t c e) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem i a) := .hyp (Or.inl rfl)
  exact SyntaxComposeExistence.point_fiber hZ (Source.SetLanguage.args2 r t) w a c e i h0 h1 h2

theorem pointFiber_kernel_certificate {m} (w r t a c e i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pointFiberSentence w r t a c e i)) := TheoryTransport.sentence (source_pointFiber w r t a c e i)

theorem native_pointFiber {m} (w r t a c e i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pointFiberSentence w r t a c e i)) := ZFReplay.replay (pointFiber_kernel_certificate w r t a c e i)

def relationTotalSentence {m} (w r t a c e : Fin m) : Source.Sentence := ((SyntaxIndexMapSyntax.indexMap w r a c).imp ((SyntaxIndexMapSyntax.indexMap w t c e).imp (ReplacementPredicates.total SyntaxComposeSyntax.matrix (Source.SetLanguage.args2 r t) a))).close

theorem source_relationTotal {m} (w r t a c e : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (relationTotalSentence w r t a c e) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIndexMapSyntax.indexMap w t c e) (Context.add (SyntaxIndexMapSyntax.indexMap w r a c) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxIndexMapSyntax.indexMap w r a c) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxIndexMapSyntax.indexMap w t c e) := .hyp (Or.inl rfl)
  exact SyntaxComposeExistence.total hZ (Source.SetLanguage.args2 r t) w a c e h0 h1

theorem relationTotal_kernel_certificate {m} (w r t a c e : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (relationTotalSentence w r t a c e)) := TheoryTransport.sentence (source_relationTotal w r t a c e)

theorem native_relationTotal {m} (w r t a c e : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (relationTotalSentence w r t a c e)) := ZFReplay.replay (relationTotal_kernel_certificate w r t a c e)

def graphExistsSentence {m} (w r t a c e : Fin m) : Source.Sentence := ((SyntaxIndexMapSyntax.indexMap w r a c).imp ((SyntaxIndexMapSyntax.indexMap w t c e).imp (SyntaxComposeSyntax.existsGraph w r t a c e))).close

theorem source_graphExists {m} (w r t a c e : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphExistsSentence w r t a c e) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIndexMapSyntax.indexMap w t c e) (Context.add (SyntaxIndexMapSyntax.indexMap w r a c) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxIndexMapSyntax.indexMap w r a c) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxIndexMapSyntax.indexMap w t c e) := .hyp (Or.inl rfl)
  exact SyntaxComposeGraph.exists_graph hZ w r t a c e h0 h1

theorem graphExists_kernel_certificate {m} (w r t a c e : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphExistsSentence w r t a c e)) := TheoryTransport.sentence (source_graphExists w r t a c e)

theorem native_graphExists {m} (w r t a c e : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphExistsSentence w r t a c e)) := ZFReplay.replay (graphExists_kernel_certificate w r t a c e)

def graphFiberSentence {m} (w r t a c e : Fin m) : Source.Sentence := ((SyntaxIndexMapSyntax.indexMap w r a c).imp ((SyntaxIndexMapSyntax.indexMap w t c e).imp (SyntaxComposeSyntax.graphFiber w r t a c e))).close

theorem source_graphFiber {m} (w r t a c e : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphFiberSentence w r t a c e) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIndexMapSyntax.indexMap w t c e) (Context.add (SyntaxIndexMapSyntax.indexMap w r a c) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxIndexMapSyntax.indexMap w r a c) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxIndexMapSyntax.indexMap w t c e) := .hyp (Or.inl rfl)
  exact SyntaxComposeGraph.actual_fiber hZ w r t a c e h0 h1

theorem graphFiber_kernel_certificate {m} (w r t a c e : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphFiberSentence w r t a c e)) := TheoryTransport.sentence (source_graphFiber w r t a c e)

theorem native_graphFiber {m} (w r t a c e : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphFiberSentence w r t a c e)) := ZFReplay.replay (graphFiber_kernel_certificate w r t a c e)

def graphUniqueSentence {m} (w r t a c e g h : Fin m) : Source.Sentence := ((SyntaxComposeSyntax.composed w r t a c e g).imp ((SyntaxComposeSyntax.composed w r t a c e h).imp (Formula.equal g h))).close

theorem source_graphUnique {m} (w r t a c e g h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphUniqueSentence w r t a c e g h) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxComposeSyntax.composed w r t a c e h) (Context.add (SyntaxComposeSyntax.composed w r t a c e g) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxComposeSyntax.composed w r t a c e g) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxComposeSyntax.composed w r t a c e h) := .hyp (Or.inl rfl)
  exact SyntaxComposeGraph.unique hZ w r t a c e g h h0 h1

theorem graphUnique_kernel_certificate {m} (w r t a c e g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphUniqueSentence w r t a c e g h)) := TheoryTransport.sentence (source_graphUnique w r t a c e g h)

theorem native_graphUnique {m} (w r t a c e g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphUniqueSentence w r t a c e g h)) := ZFReplay.replay (graphUnique_kernel_certificate w r t a c e g h)

def graphEdgesSentence {m} (w r t a c e g i j : Fin m) : Source.Sentence := ((SyntaxComposeSyntax.composed w r t a c e g).imp ((GraphSyntax.edge g i j).iff (SyntaxComposeSyntax.value r t i j))).close

theorem source_graphEdges {m} (w r t a c e g i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphEdgesSentence w r t a c e g i j) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxComposeSyntax.composed w r t a c e g) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxComposeSyntax.composed w r t a c e g) := .hyp (Or.inl rfl)
  exact SyntaxComposeGraph.edge_iff hZ w r t a c e g i j h0

theorem graphEdges_kernel_certificate {m} (w r t a c e g i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphEdgesSentence w r t a c e g i j)) := TheoryTransport.sentence (source_graphEdges w r t a c e g i j)

theorem native_graphEdges {m} (w r t a c e g i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphEdgesSentence w r t a c e g i j)) := ZFReplay.replay (graphEdges_kernel_certificate w r t a c e g i j)

def graphTargetMapSentence {m} (w r t a c e g : Fin m) : Source.Sentence := ((SyntaxComposeSyntax.composed w r t a c e g).imp (SyntaxIndexMapSyntax.indexMap w g a e)).close

theorem source_graphTargetMap {m} (w r t a c e g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphTargetMapSentence w r t a c e g) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxComposeSyntax.composed w r t a c e g) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxComposeSyntax.composed w r t a c e g) := .hyp (Or.inl rfl)
  exact SyntaxComposeGraph.target_map w r t a c e g h0

theorem graphTargetMap_kernel_certificate {m} (w r t a c e g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphTargetMapSentence w r t a c e g)) := TheoryTransport.sentence (source_graphTargetMap w r t a c e g)

theorem native_graphTargetMap {m} (w r t a c e g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphTargetMapSentence w r t a c e g)) := ZFReplay.replay (graphTargetMap_kernel_certificate w r t a c e g)

def codeFirstSentence {m} (w a c e R T K : Fin m) : Source.Sentence := ((SyntaxComposeCodeSyntax.coded w a c e R T K).imp (SyntaxMapCodeSyntax.mapCode w a c R)).close

theorem source_codeFirst {m} (w a c e R T K : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeFirstSentence w a c e R T K) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxComposeCodeSyntax.coded w a c e R T K) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxComposeCodeSyntax.coded w a c e R T K) := .hyp (Or.inl rfl)
  exact SyntaxComposeCodeReadback.first_code w a c e R T K h0

theorem codeFirst_kernel_certificate {m} (w a c e R T K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeFirstSentence w a c e R T K)) := TheoryTransport.sentence (source_codeFirst w a c e R T K)

theorem native_codeFirst {m} (w a c e R T K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeFirstSentence w a c e R T K)) := ZFReplay.replay (codeFirst_kernel_certificate w a c e R T K)

def codeSecondSentence {m} (w a c e R T K : Fin m) : Source.Sentence := ((SyntaxComposeCodeSyntax.coded w a c e R T K).imp (SyntaxMapCodeSyntax.mapCode w c e T)).close

theorem source_codeSecond {m} (w a c e R T K : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeSecondSentence w a c e R T K) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxComposeCodeSyntax.coded w a c e R T K) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxComposeCodeSyntax.coded w a c e R T K) := .hyp (Or.inl rfl)
  exact SyntaxComposeCodeReadback.second_code w a c e R T K h0

theorem codeSecond_kernel_certificate {m} (w a c e R T K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeSecondSentence w a c e R T K)) := TheoryTransport.sentence (source_codeSecond w a c e R T K)

theorem native_codeSecond {m} (w a c e R T K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeSecondSentence w a c e R T K)) := ZFReplay.replay (codeSecond_kernel_certificate w a c e R T K)

def codeOutputSentence {m} (w a c e R T K : Fin m) : Source.Sentence := ((SyntaxComposeCodeSyntax.coded w a c e R T K).imp (SyntaxMapCodeSyntax.mapCode w a e K)).close

theorem source_codeOutput {m} (w a c e R T K : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeOutputSentence w a c e R T K) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxComposeCodeSyntax.coded w a c e R T K) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxComposeCodeSyntax.coded w a c e R T K) := .hyp (Or.inl rfl)
  exact SyntaxComposeCodeReadback.output_code w a c e R T K h0

theorem codeOutput_kernel_certificate {m} (w a c e R T K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeOutputSentence w a c e R T K)) := TheoryTransport.sentence (source_codeOutput w a c e R T K)

theorem native_codeOutput {m} (w a c e R T K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeOutputSentence w a c e R T K)) := ZFReplay.replay (codeOutput_kernel_certificate w a c e R T K)

def codeReadSourcesSentence {m} (w r t a c e R T K : Fin m) : Source.Sentence := ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w t c e T).imp ((SyntaxComposeCodeSyntax.coded w a c e R T K).imp (SyntaxComposeCodeSyntax.outputAt w r t a c e K)))).close

theorem source_codeReadSources {m} (w r t a c e R T K : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeReadSourcesSentence w r t a c e R T K) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxComposeCodeSyntax.coded w a c e R T K) (Context.add (SyntaxMapCodeSyntax.encoded w t c e T) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.encoded w t c e T) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxComposeCodeSyntax.coded w a c e R T K) := .hyp (Or.inl rfl)
  exact SyntaxComposeCodeReadback.at_sources hZ w r t a c e R T K h0 h1 h2

theorem codeReadSources_kernel_certificate {m} (w r t a c e R T K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeReadSourcesSentence w r t a c e R T K)) := TheoryTransport.sentence (source_codeReadSources w r t a c e R T K)

theorem native_codeReadSources {m} (w r t a c e R T K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeReadSourcesSentence w r t a c e R T K)) := ZFReplay.replay (codeReadSources_kernel_certificate w r t a c e R T K)

def codeReadGraphsSentence {m} (w r t a c e R T K g : Fin m) : Source.Sentence := ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w t c e T).imp ((SyntaxMapCodeSyntax.encoded w g a e K).imp ((SyntaxComposeCodeSyntax.coded w a c e R T K).imp (SyntaxComposeSyntax.composed w r t a c e g))))).close

theorem source_codeReadGraphs {m} (w r t a c e R T K g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeReadGraphsSentence w r t a c e R T K g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxComposeCodeSyntax.coded w a c e R T K) (Context.add (SyntaxMapCodeSyntax.encoded w g a e K) (Context.add (SyntaxMapCodeSyntax.encoded w t c e T) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.encoded w t c e T) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w g a e K) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxComposeCodeSyntax.coded w a c e R T K) := .hyp (Or.inl rfl)
  exact SyntaxComposeCodeReadback.at_graphs hZ w r t a c e R T K g h0 h1 h2 h3

theorem codeReadGraphs_kernel_certificate {m} (w r t a c e R T K g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeReadGraphsSentence w r t a c e R T K g)) := TheoryTransport.sentence (source_codeReadGraphs w r t a c e R T K g)

theorem native_codeReadGraphs {m} (w r t a c e R T K g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeReadGraphsSentence w r t a c e R T K g)) := ZFReplay.replay (codeReadGraphs_kernel_certificate w r t a c e R T K g)

def codeEncodedIffSentence {m} (w r t a c e R T K g : Fin m) : Source.Sentence := ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w t c e T).imp ((SyntaxMapCodeSyntax.encoded w g a e K).imp ((SyntaxComposeCodeSyntax.coded w a c e R T K).iff (SyntaxComposeSyntax.composed w r t a c e g))))).close

theorem source_codeEncodedIff {m} (w r t a c e R T K g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeEncodedIffSentence w r t a c e R T K g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapCodeSyntax.encoded w g a e K) (Context.add (SyntaxMapCodeSyntax.encoded w t c e T) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.encoded w t c e T) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w g a e K) := .hyp (Or.inl rfl)
  exact SyntaxComposeCodeReadback.encoded_iff hZ w r t a c e R T K g h0 h1 h2

theorem codeEncodedIff_kernel_certificate {m} (w r t a c e R T K g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeEncodedIffSentence w r t a c e R T K g)) := TheoryTransport.sentence (source_codeEncodedIff w r t a c e R T K g)

theorem native_codeEncodedIff {m} (w r t a c e R T K g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeEncodedIffSentence w r t a c e R T K g)) := ZFReplay.replay (codeEncodedIff_kernel_certificate w r t a c e R T K g)

def codeEdgesSentence {m} (w r t a c e R T K g i j : Fin m) : Source.Sentence := ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w t c e T).imp ((SyntaxMapCodeSyntax.encoded w g a e K).imp ((SyntaxComposeCodeSyntax.coded w a c e R T K).imp ((GraphSyntax.edge g i j).iff (SyntaxComposeSyntax.value r t i j)))))).close

theorem source_codeEdges {m} (w r t a c e R T K g i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeEdgesSentence w r t a c e R T K g i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxComposeCodeSyntax.coded w a c e R T K) (Context.add (SyntaxMapCodeSyntax.encoded w g a e K) (Context.add (SyntaxMapCodeSyntax.encoded w t c e T) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.encoded w t c e T) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w g a e K) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxComposeCodeSyntax.coded w a c e R T K) := .hyp (Or.inl rfl)
  exact SyntaxComposeCodeReadback.edge_iff hZ w r t a c e R T K g i j h0 h1 h2 h3

theorem codeEdges_kernel_certificate {m} (w r t a c e R T K g i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeEdgesSentence w r t a c e R T K g i j)) := TheoryTransport.sentence (source_codeEdges w r t a c e R T K g i j)

theorem native_codeEdges {m} (w r t a c e R T K g i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeEdgesSentence w r t a c e R T K g i j)) := ZFReplay.replay (codeEdges_kernel_certificate w r t a c e R T K g i j)

def codeExistsAtSourcesSentence {m} (w r t a c e R T : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w t c e T).imp (SyntaxComposeCodeSyntax.existsCode w a c e R T)))).close

theorem source_codeExistsAtSources {m} (w r t a c e R T : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeExistsAtSourcesSentence w r t a c e R T) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapCodeSyntax.encoded w t c e T) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w t c e T) := .hyp (Or.inl rfl)
  exact SyntaxComposeCodeExistence.exists_at_sources hZ w r t a c e R T h0 h1 h2

theorem codeExistsAtSources_kernel_certificate {m} (w r t a c e R T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeExistsAtSourcesSentence w r t a c e R T)) := TheoryTransport.sentence (source_codeExistsAtSources w r t a c e R T)

theorem native_codeExistsAtSources {m} (w r t a c e R T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeExistsAtSourcesSentence w r t a c e R T)) := ZFReplay.replay (codeExistsAtSources_kernel_certificate w r t a c e R T)

def codeExistsSentence {m} (w a c e R T : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.mapCode w a c R).imp ((SyntaxMapCodeSyntax.mapCode w c e T).imp (SyntaxComposeCodeSyntax.existsCode w a c e R T)))).close

theorem source_codeExists {m} (w a c e R T : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeExistsSentence w a c e R T) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapCodeSyntax.mapCode w c e T) (Context.add (SyntaxMapCodeSyntax.mapCode w a c R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.mapCode w a c R) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.mapCode w c e T) := .hyp (Or.inl rfl)
  exact SyntaxComposeCodeExistence.exists_code hZ w a c e R T h0 h1 h2

theorem codeExists_kernel_certificate {m} (w a c e R T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeExistsSentence w a c e R T)) := TheoryTransport.sentence (source_codeExists w a c e R T)

theorem native_codeExists {m} (w a c e R T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeExistsSentence w a c e R T)) := ZFReplay.replay (codeExists_kernel_certificate w a c e R T)

def codeUniqueSentence {m} (w a c e R T K L : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeCodeSyntax.coded w a c e R T K).imp ((SyntaxComposeCodeSyntax.coded w a c e R T L).imp (Formula.equal K L)))).close

theorem source_codeUnique {m} (w a c e R T K L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeUniqueSentence w a c e R T K L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxComposeCodeSyntax.coded w a c e R T L) (Context.add (SyntaxComposeCodeSyntax.coded w a c e R T K) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxComposeCodeSyntax.coded w a c e R T K) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxComposeCodeSyntax.coded w a c e R T L) := .hyp (Or.inl rfl)
  exact SyntaxComposeCodeUnique.unique hZ w a c e R T K L h0 h1 h2

theorem codeUnique_kernel_certificate {m} (w a c e R T K L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeUniqueSentence w a c e R T K L)) := TheoryTransport.sentence (source_codeUnique w a c e R T K L)

theorem native_codeUnique {m} (w a c e R T K L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeUniqueSentence w a c e R T K L)) := ZFReplay.replay (codeUnique_kernel_certificate w a c e R T K L)

def codeFiberSentence {m} (w a c e R T : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.mapCode w a c R).imp ((SyntaxMapCodeSyntax.mapCode w c e T).imp (SyntaxComposeCodeSyntax.codeFiber w a c e R T)))).close

theorem source_codeFiber {m} (w a c e R T : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeFiberSentence w a c e R T) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapCodeSyntax.mapCode w c e T) (Context.add (SyntaxMapCodeSyntax.mapCode w a c R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.mapCode w a c R) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.mapCode w c e T) := .hyp (Or.inl rfl)
  exact SyntaxComposeCodeUnique.actual_fiber hZ w a c e R T h0 h1 h2

theorem codeFiber_kernel_certificate {m} (w a c e R T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeFiberSentence w a c e R T)) := TheoryTransport.sentence (source_codeFiber w a c e R T)

theorem native_codeFiber {m} (w a c e R T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeFiberSentence w a c e R T)) := ZFReplay.replay (codeFiber_kernel_certificate w a c e R T)

def codeInputIffSentence {m} (w a c e R T : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeCodeSyntax.existsCode w a c e R T).iff ((SyntaxMapCodeSyntax.mapCode w a c R).conj (SyntaxMapCodeSyntax.mapCode w c e T)))).close

theorem source_codeInputIff {m} (w a c e R T : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeInputIffSentence w a c e R T) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxComposeCodeUnique.exists_iff_input hZ w a c e R T h0

theorem codeInputIff_kernel_certificate {m} (w a c e R T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeInputIffSentence w a c e R T)) := TheoryTransport.sentence (source_codeInputIff w a c e R T)

theorem native_codeInputIff {m} (w a c e R T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeInputIffSentence w a c e R T)) := ZFReplay.replay (codeInputIff_kernel_certificate w a c e R T)

def termBranchSentence {m} (bound : Bool) (w r t a c e g n q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeSyntax.composed w r t a c e g).imp ((SyntaxRenameTermSyntax.branch bound w r a n q).imp ((SyntaxRenameTermSyntax.branch bound w t c q v).imp (SyntaxRenameTermSyntax.branch bound w g a n v))))).close

theorem source_termBranch {m} (bound : Bool) (w r t a c e g n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termBranchSentence bound w r t a c e g n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameTermSyntax.branch bound w t c q v) (Context.add (SyntaxRenameTermSyntax.branch bound w r a n q) (Context.add (SyntaxComposeSyntax.composed w r t a c e g) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxComposeSyntax.composed w r t a c e g) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxRenameTermSyntax.branch bound w r a n q) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxRenameTermSyntax.branch bound w t c q v) := .hyp (Or.inl rfl)
  exact SyntaxComposeTerms.branch_compose hZ bound w r t a c e g n q v h0 h1 h2 h3

theorem termBranch_kernel_certificate {m} (bound : Bool) (w r t a c e g n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termBranchSentence bound w r t a c e g n q v)) := TheoryTransport.sentence (source_termBranch bound w r t a c e g n q v)

theorem native_termBranch {m} (bound : Bool) (w r t a c e g n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termBranchSentence bound w r t a c e g n q v)) := ZFReplay.replay (termBranch_kernel_certificate bound w r t a c e g n q v)

def termComposeSentence {m} (w r s t u g h a b c d e f n q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeSyntax.composed w r t a c e g).imp ((SyntaxComposeSyntax.composed w s u b d f h).imp ((SyntaxRenameTermSyntax.renamed w r s a b c d n q).imp ((SyntaxRenameTermSyntax.renamed w t u c d e f q v).imp (SyntaxRenameTermSyntax.renamed w g h a b e f n v)))))).close

theorem source_termCompose {m} (w r s t u g h a b c d e f n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termComposeSentence w r s t u g h a b c d e f n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameTermSyntax.renamed w t u c d e f q v) (Context.add (SyntaxRenameTermSyntax.renamed w r s a b c d n q) (Context.add (SyntaxComposeSyntax.composed w s u b d f h) (Context.add (SyntaxComposeSyntax.composed w r t a c e g) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxComposeSyntax.composed w r t a c e g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxComposeSyntax.composed w s u b d f h) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxRenameTermSyntax.renamed w r s a b c d n q) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxRenameTermSyntax.renamed w t u c d e f q v) := .hyp (Or.inl rfl)
  exact SyntaxComposeTerms.forward hZ w r s t u g h a b c d e f n q v h0 h1 h2 h3 h4

theorem termCompose_kernel_certificate {m} (w r s t u g h a b c d e f n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termComposeSentence w r s t u g h a b c d e f n q v)) := TheoryTransport.sentence (source_termCompose w r s t u g h a b c d e f n q v)

theorem native_termCompose {m} (w r s t u g h a b c d e f n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termComposeSentence w r s t u g h a b c d e f n q v)) := ZFReplay.replay (termCompose_kernel_certificate w r s t u g h a b c d e f n q v)

def termFactorSentence {m} (w r s t u g h a b c d e f n v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeSyntax.composed w r t a c e g).imp ((SyntaxComposeSyntax.composed w s u b d f h).imp ((SyntaxRenameTermSyntax.renamed w g h a b e f n v).imp (SyntaxComposeTermFactor.sequential w r s t u a b c d e f n v))))).close

theorem source_termFactor {m} (w r s t u g h a b c d e f n v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termFactorSentence w r s t u g h a b c d e f n v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameTermSyntax.renamed w g h a b e f n v) (Context.add (SyntaxComposeSyntax.composed w s u b d f h) (Context.add (SyntaxComposeSyntax.composed w r t a c e g) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxComposeSyntax.composed w r t a c e g) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxComposeSyntax.composed w s u b d f h) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxRenameTermSyntax.renamed w g h a b e f n v) := .hyp (Or.inl rfl)
  exact SyntaxComposeTermFactor.factor hZ w r s t u g h a b c d e f n v h0 h1 h2 h3

theorem termFactor_kernel_certificate {m} (w r s t u g h a b c d e f n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termFactorSentence w r s t u g h a b c d e f n v)) := TheoryTransport.sentence (source_termFactor w r s t u g h a b c d e f n v)

theorem native_termFactor {m} (w r s t u g h a b c d e f n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termFactorSentence w r s t u g h a b c d e f n v)) := ZFReplay.replay (termFactor_kernel_certificate w r s t u g h a b c d e f n v)

def termCollapseSentence {m} (w r s t u g h a b c d e f n v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeSyntax.composed w r t a c e g).imp ((SyntaxComposeSyntax.composed w s u b d f h).imp ((SyntaxComposeTermFactor.sequential w r s t u a b c d e f n v).imp (SyntaxRenameTermSyntax.renamed w g h a b e f n v))))).close

theorem source_termCollapse {m} (w r s t u g h a b c d e f n v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termCollapseSentence w r s t u g h a b c d e f n v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxComposeTermFactor.sequential w r s t u a b c d e f n v) (Context.add (SyntaxComposeSyntax.composed w s u b d f h) (Context.add (SyntaxComposeSyntax.composed w r t a c e g) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxComposeSyntax.composed w r t a c e g) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxComposeSyntax.composed w s u b d f h) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxComposeTermFactor.sequential w r s t u a b c d e f n v) := .hyp (Or.inl rfl)
  exact SyntaxComposeTermFactor.collapse hZ w r s t u g h a b c d e f n v h0 h1 h2 h3

theorem termCollapse_kernel_certificate {m} (w r s t u g h a b c d e f n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termCollapseSentence w r s t u g h a b c d e f n v)) := TheoryTransport.sentence (source_termCollapse w r s t u g h a b c d e f n v)

theorem native_termCollapse {m} (w r s t u g h a b c d e f n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termCollapseSentence w r s t u g h a b c d e f n v)) := ZFReplay.replay (termCollapse_kernel_certificate w r s t u g h a b c d e f n v)

def termComposeIffSentence {m} (w r s t u g h a b c d e f n v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeSyntax.composed w r t a c e g).imp ((SyntaxComposeSyntax.composed w s u b d f h).imp ((SyntaxRenameTermSyntax.renamed w g h a b e f n v).iff (SyntaxComposeTermFactor.sequential w r s t u a b c d e f n v))))).close

theorem source_termComposeIff {m} (w r s t u g h a b c d e f n v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termComposeIffSentence w r s t u g h a b c d e f n v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxComposeSyntax.composed w s u b d f h) (Context.add (SyntaxComposeSyntax.composed w r t a c e g) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxComposeSyntax.composed w r t a c e g) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxComposeSyntax.composed w s u b d f h) := .hyp (Or.inl rfl)
  exact SyntaxComposeTermFactor.compose_iff hZ w r s t u g h a b c d e f n v h0 h1 h2

theorem termComposeIff_kernel_certificate {m} (w r s t u g h a b c d e f n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termComposeIffSentence w r s t u g h a b c d e f n v)) := TheoryTransport.sentence (source_termComposeIff w r s t u g h a b c d e f n v)

theorem native_termComposeIff {m} (w r s t u g h a b c d e f n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termComposeIffSentence w r s t u g h a b c d e f n v)) := ZFReplay.replay (termComposeIff_kernel_certificate w r s t u g h a b c d e f n v)

end PPAC.Migration.Internal.ObjectSyntaxCompose
