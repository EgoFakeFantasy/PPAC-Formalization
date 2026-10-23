import PPAC.Migration.Internal.PureQuotationSyntax

/-! 原树/纯语法quotation模式实际内部码的总唯一的原YesMetaZFC核证书。 -/
namespace PPAC.Migration.Internal.ObjectOriginalQuotation
open Source SourceAlgebra SourceLogic OmegaSyntax

def treeExistsSentence {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTreeQuotationSyntax.treeExists input w))).close

theorem source_treeExists {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (treeExistsSentence input w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact OriginalTreeQuotationExistence.tree_exists hZ input w h0

theorem treeExists_kernel_certificate {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (treeExistsSentence input w)) := TheoryTransport.sentence (source_treeExists input w)

theorem native_treeExists {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (treeExistsSentence input w)) := ZFReplay.replay (treeExists_kernel_certificate input w)

def treeRangeSentence {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w n : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTreeQuotationSyntax.tree input w n).imp ((Formula.mem n w)))).close

theorem source_treeRange {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (treeRangeSentence input w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTreeQuotationSyntax.tree input w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (OriginalTreeQuotationSyntax.tree input w n) := .hyp (Or.inl rfl)
  exact OriginalTreeQuotationProperties.tree_range hZ input w n h0 h1

theorem treeRange_kernel_certificate {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (treeRangeSentence input w n)) := TheoryTransport.sentence (source_treeRange input w n)

theorem native_treeRange {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (treeRangeSentence input w n)) := ZFReplay.replay (treeRange_kernel_certificate input w n)

def treeUniqueSentence {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w n v : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTreeQuotationSyntax.tree input w n).imp ((OriginalTreeQuotationSyntax.tree input w v).imp ((Formula.equal n v))))).close

theorem source_treeUnique {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w n v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (treeUniqueSentence input w n v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTreeQuotationSyntax.tree input w v) (Context.add (OriginalTreeQuotationSyntax.tree input w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (OriginalTreeQuotationSyntax.tree input w n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (OriginalTreeQuotationSyntax.tree input w v) := .hyp (Or.inl rfl)
  exact OriginalTreeQuotationUnique.tree_unique hZ input w n v h0 h1 h2

theorem treeUnique_kernel_certificate {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (treeUniqueSentence input w n v)) := TheoryTransport.sentence (source_treeUnique input w n v)

theorem native_treeUnique {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (treeUniqueSentence input w n v)) := ZFReplay.replay (treeUnique_kernel_certificate input w n v)

def treeUniqueOutputSentence {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w n : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTreeQuotationSyntax.tree input w n).imp ((OriginalTreeQuotationSyntax.treeUnique input w n)))).close

theorem source_treeUniqueOutput {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (treeUniqueOutputSentence input w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTreeQuotationSyntax.tree input w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (OriginalTreeQuotationSyntax.tree input w n) := .hyp (Or.inl rfl)
  exact OriginalTreeQuotationFiber.tree_unique_output hZ input w n h0 h1

theorem treeUniqueOutput_kernel_certificate {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (treeUniqueOutputSentence input w n)) := TheoryTransport.sentence (source_treeUniqueOutput input w n)

theorem native_treeUniqueOutput {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (treeUniqueOutputSentence input w n)) := ZFReplay.replay (treeUniqueOutput_kernel_certificate input w n)

def treeFiberSentence {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTreeQuotationSyntax.treeFiber input w))).close

theorem source_treeFiber {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (treeFiberSentence input w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact OriginalTreeQuotationFiber.tree_actual_fiber hZ input w h0

theorem treeFiber_kernel_certificate {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (treeFiberSentence input w)) := TheoryTransport.sentence (source_treeFiber input w)

theorem native_treeFiber {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (treeFiberSentence input w)) := ZFReplay.replay (treeFiber_kernel_certificate input w)

def forestExistsSentence {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTreeQuotationSyntax.forestExists input w))).close

theorem source_forestExists {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forestExistsSentence input w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact OriginalTreeQuotationExistence.forest_exists hZ input w h0

theorem forestExists_kernel_certificate {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forestExistsSentence input w)) := TheoryTransport.sentence (source_forestExists input w)

theorem native_forestExists {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forestExistsSentence input w)) := ZFReplay.replay (forestExists_kernel_certificate input w)

def forestRangeSentence {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w n : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTreeQuotationSyntax.forest input w n).imp ((Formula.mem n w)))).close

theorem source_forestRange {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forestRangeSentence input w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTreeQuotationSyntax.forest input w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (OriginalTreeQuotationSyntax.forest input w n) := .hyp (Or.inl rfl)
  exact OriginalTreeQuotationProperties.forest_range hZ input w n h0 h1

theorem forestRange_kernel_certificate {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forestRangeSentence input w n)) := TheoryTransport.sentence (source_forestRange input w n)

theorem native_forestRange {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forestRangeSentence input w n)) := ZFReplay.replay (forestRange_kernel_certificate input w n)

def forestUniqueSentence {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w n v : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTreeQuotationSyntax.forest input w n).imp ((OriginalTreeQuotationSyntax.forest input w v).imp ((Formula.equal n v))))).close

theorem source_forestUnique {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w n v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forestUniqueSentence input w n v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTreeQuotationSyntax.forest input w v) (Context.add (OriginalTreeQuotationSyntax.forest input w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (OriginalTreeQuotationSyntax.forest input w n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (OriginalTreeQuotationSyntax.forest input w v) := .hyp (Or.inl rfl)
  exact OriginalTreeQuotationUnique.forest_unique hZ input w n v h0 h1 h2

theorem forestUnique_kernel_certificate {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forestUniqueSentence input w n v)) := TheoryTransport.sentence (source_forestUnique input w n v)

theorem native_forestUnique {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forestUniqueSentence input w n v)) := ZFReplay.replay (forestUnique_kernel_certificate input w n v)

def forestUniqueOutputSentence {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w n : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTreeQuotationSyntax.forest input w n).imp ((OriginalTreeQuotationSyntax.forestUnique input w n)))).close

theorem source_forestUniqueOutput {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forestUniqueOutputSentence input w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTreeQuotationSyntax.forest input w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (OriginalTreeQuotationSyntax.forest input w n) := .hyp (Or.inl rfl)
  exact OriginalTreeQuotationFiber.forest_unique_output hZ input w n h0 h1

theorem forestUniqueOutput_kernel_certificate {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forestUniqueOutputSentence input w n)) := TheoryTransport.sentence (source_forestUniqueOutput input w n)

theorem native_forestUniqueOutput {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forestUniqueOutputSentence input w n)) := ZFReplay.replay (forestUniqueOutput_kernel_certificate input w n)

def forestFiberSentence {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTreeQuotationSyntax.forestFiber input w))).close

theorem source_forestFiber {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forestFiberSentence input w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact OriginalTreeQuotationFiber.forest_actual_fiber hZ input w h0

theorem forestFiber_kernel_certificate {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forestFiberSentence input w)) := TheoryTransport.sentence (source_forestFiber input w)

theorem native_forestFiber {m} (input : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forestFiberSentence input w)) := ZFReplay.replay (forestFiber_kernel_certificate input w)

def termExistsSentence {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTreeQuotationSyntax.treeExists (PureSyntaxQuotation.termTree input) w))).close

theorem source_termExists {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termExistsSentence input w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact OriginalTreeQuotationExistence.tree_exists hZ (PureSyntaxQuotation.termTree input) w h0

theorem termExists_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termExistsSentence input w)) := TheoryTransport.sentence (source_termExists input w)

theorem native_termExists {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termExistsSentence input w)) := ZFReplay.replay (termExists_kernel_certificate input w)

def termRangeSentence {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w n : Fin m) : Source.Sentence := ((omega w).imp ((PureQuotationSyntax.term input w n).imp ((Formula.mem n w)))).close

theorem source_termRange {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termRangeSentence input w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureQuotationSyntax.term input w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PureQuotationSyntax.term input w n) := .hyp (Or.inl rfl)
  exact OriginalTreeQuotationProperties.tree_range hZ (PureSyntaxQuotation.termTree input) w n h0 h1

theorem termRange_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termRangeSentence input w n)) := TheoryTransport.sentence (source_termRange input w n)

theorem native_termRange {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termRangeSentence input w n)) := ZFReplay.replay (termRange_kernel_certificate input w n)

def termUniqueSentence {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w n v : Fin m) : Source.Sentence := ((omega w).imp ((PureQuotationSyntax.term input w n).imp ((PureQuotationSyntax.term input w v).imp ((Formula.equal n v))))).close

theorem source_termUnique {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w n v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termUniqueSentence input w n v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureQuotationSyntax.term input w v) (Context.add (PureQuotationSyntax.term input w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PureQuotationSyntax.term input w n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PureQuotationSyntax.term input w v) := .hyp (Or.inl rfl)
  exact PureQuotationSyntax.term_unique hZ input w n v h0 h1 h2

theorem termUnique_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termUniqueSentence input w n v)) := TheoryTransport.sentence (source_termUnique input w n v)

theorem native_termUnique {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termUniqueSentence input w n v)) := ZFReplay.replay (termUnique_kernel_certificate input w n v)

def termFiberSentence {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTreeQuotationSyntax.treeFiber (PureSyntaxQuotation.termTree input) w))).close

theorem source_termFiber {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termFiberSentence input w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact OriginalTreeQuotationFiber.tree_actual_fiber hZ (PureSyntaxQuotation.termTree input) w h0

theorem termFiber_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termFiberSentence input w)) := TheoryTransport.sentence (source_termFiber input w)

theorem native_termFiber {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termFiberSentence input w)) := ZFReplay.replay (termFiber_kernel_certificate input w)

def formulaExistsSentence {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTreeQuotationSyntax.treeExists (PureSyntaxQuotation.formulaTree input) w))).close

theorem source_formulaExists {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaExistsSentence input w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact OriginalTreeQuotationExistence.tree_exists hZ (PureSyntaxQuotation.formulaTree input) w h0

theorem formulaExists_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaExistsSentence input w)) := TheoryTransport.sentence (source_formulaExists input w)

theorem native_formulaExists {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaExistsSentence input w)) := ZFReplay.replay (formulaExists_kernel_certificate input w)

def formulaRangeSentence {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w n : Fin m) : Source.Sentence := ((omega w).imp ((PureQuotationSyntax.formula input w n).imp ((Formula.mem n w)))).close

theorem source_formulaRange {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaRangeSentence input w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureQuotationSyntax.formula input w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PureQuotationSyntax.formula input w n) := .hyp (Or.inl rfl)
  exact OriginalTreeQuotationProperties.tree_range hZ (PureSyntaxQuotation.formulaTree input) w n h0 h1

theorem formulaRange_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaRangeSentence input w n)) := TheoryTransport.sentence (source_formulaRange input w n)

theorem native_formulaRange {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaRangeSentence input w n)) := ZFReplay.replay (formulaRange_kernel_certificate input w n)

def formulaUniqueSentence {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w n v : Fin m) : Source.Sentence := ((omega w).imp ((PureQuotationSyntax.formula input w n).imp ((PureQuotationSyntax.formula input w v).imp ((Formula.equal n v))))).close

theorem source_formulaUnique {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w n v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaUniqueSentence input w n v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureQuotationSyntax.formula input w v) (Context.add (PureQuotationSyntax.formula input w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PureQuotationSyntax.formula input w n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PureQuotationSyntax.formula input w v) := .hyp (Or.inl rfl)
  exact PureQuotationSyntax.formula_unique hZ input w n v h0 h1 h2

theorem formulaUnique_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaUniqueSentence input w n v)) := TheoryTransport.sentence (source_formulaUnique input w n v)

theorem native_formulaUnique {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaUniqueSentence input w n v)) := ZFReplay.replay (formulaUnique_kernel_certificate input w n v)

def formulaFiberSentence {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTreeQuotationSyntax.treeFiber (PureSyntaxQuotation.formulaTree input) w))).close

theorem source_formulaFiber {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaFiberSentence input w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact OriginalTreeQuotationFiber.tree_actual_fiber hZ (PureSyntaxQuotation.formulaTree input) w h0

theorem formulaFiber_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaFiberSentence input w)) := TheoryTransport.sentence (source_formulaFiber input w)

theorem native_formulaFiber {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaFiberSentence input w)) := ZFReplay.replay (formulaFiber_kernel_certificate input w)

end PPAC.Migration.Internal.ObjectOriginalQuotation
