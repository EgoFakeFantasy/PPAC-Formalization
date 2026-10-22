import PPAC.Migration.Internal.SyntaxRenameHistory

/-! 实际重命名状态查询、全11类矩阵、Separation状态算子及全内部递归的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxRenameOperator
open Source SourceAlgebra SourceLogic OmegaSyntax

def containsAtStateSentence {m} (w v r s a b c d q t : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameStateSyntax.state w r s a b c d q t).imp (((SyntaxRenameQuerySyntax.contains w v r s a b c d q).iff (.mem t v))))).close

theorem source_containsAtState {m} (w v r s a b c d q t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (containsAtStateSentence w v r s a b c d q t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameStateSyntax.state w r s a b c d q t) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameStateSyntax.state w r s a b c d q t) := .hyp (Or.inl rfl)
  exact SyntaxRenameQuery.contains_at_state hZ w v r s a b c d q t h0 h1

theorem containsAtState_kernel_certificate {m} (w v r s a b c d q t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (containsAtStateSentence w v r s a b c d q t)) := TheoryTransport.sentence (source_containsAtState w v r s a b c d q t)

theorem native_containsAtState {m} (w v r s a b c d q t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (containsAtStateSentence w v r s a b c d q t)) := ZFReplay.replay (containsAtState_kernel_certificate w v r s a b c d q t)

def queryAtValueSentence {m} (w h D x v r s a b c d q : Fin m) : Source.Sentence := ((GraphSyntax.functionOn h D).imp ((GraphSyntax.edge h x v).imp (((SyntaxRenameQuerySyntax.read w h x r s a b c d q).iff (SyntaxRenameQuerySyntax.contains w v r s a b c d q))))).close

theorem source_queryAtValue {m} (w h D x v r s a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (queryAtValueSentence w h D x v r s a b c d q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (GraphSyntax.edge h x v) (Context.add (GraphSyntax.functionOn h D) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (GraphSyntax.functionOn h D) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (GraphSyntax.edge h x v) := .hyp (Or.inl rfl)
  exact SyntaxRenameQuery.at_value hZ w h D x v r s a b c d q h0 h1

theorem queryAtValue_kernel_certificate {m} (w h D x v r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (queryAtValueSentence w h D x v r s a b c d q)) := TheoryTransport.sentence (source_queryAtValue w h D x v r s a b c d q)

theorem native_queryAtValue {m} (w h D x v r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (queryAtValueSentence w h D x v r s a b c d q)) := ZFReplay.replay (queryAtValue_kernel_certificate w h D x v r s a b c d q)

def queryAtStateSentence {m} (w h D x v r s a b c d q t : Fin m) : Source.Sentence := ((omega w).imp ((GraphSyntax.functionOn h D).imp ((GraphSyntax.edge h x v).imp ((SyntaxRenameStateSyntax.state w r s a b c d q t).imp (((SyntaxRenameQuerySyntax.read w h x r s a b c d q).iff (.mem t v))))))).close

theorem source_queryAtState {m} (w h D x v r s a b c d q t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (queryAtStateSentence w h D x v r s a b c d q t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameStateSyntax.state w r s a b c d q t) (Context.add (GraphSyntax.edge h x v) (Context.add (GraphSyntax.functionOn h D) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (GraphSyntax.functionOn h D) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (GraphSyntax.edge h x v) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxRenameStateSyntax.state w r s a b c d q t) := .hyp (Or.inl rfl)
  exact SyntaxRenameQuery.at_state hZ w h D x v r s a b c d q t h0 h1 h2 h3

theorem queryAtState_kernel_certificate {m} (w h D x v r s a b c d q t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (queryAtStateSentence w h D x v r s a b c d q t)) := TheoryTransport.sentence (source_queryAtState w h D x v r s a b c d q t)

theorem native_queryAtState {m} (w h D x v r s a b c d q t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (queryAtStateSentence w h D x v r s a b c d q t)) := ZFReplay.replay (queryAtState_kernel_certificate w h D x v r s a b c d q t)

def advancedFreeMapSentence {m} (w h x r s a b c d q : Fin m) : Source.Sentence := ((SyntaxRenameQuerySyntax.advanced w h x r s a b c d q).imp ((SyntaxMapCodeSyntax.mapCode w b d s))).close

theorem source_advancedFreeMap {m} (w h x r s a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (advancedFreeMapSentence w h x r s a b c d q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameQuerySyntax.advanced w h x r s a b c d q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxRenameQuerySyntax.advanced w h x r s a b c d q) := .hyp (Or.inl rfl)
  exact SyntaxRenameQuery.advanced_free_map w h x r s a b c d q h0

theorem advancedFreeMap_kernel_certificate {m} (w h x r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (advancedFreeMapSentence w h x r s a b c d q)) := TheoryTransport.sentence (source_advancedFreeMap w h x r s a b c d q)

theorem native_advancedFreeMap {m} (w h x r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (advancedFreeMapSentence w h x r s a b c d q)) := ZFReplay.replay (advancedFreeMap_kernel_certificate w h x r s a b c d q)

def advancedIntroSentence {m} (w h x r s a b c d q u v l : Fin m) : Source.Sentence := ((SyntaxMapLiftSyntax.codedLift w a c r u v l).imp ((SyntaxRenameQuerySyntax.read w h x l s u b v d q).imp ((SyntaxRenameQuerySyntax.advanced w h x r s a b c d q)))).close

theorem source_advancedIntro {m} (w h x r s a b c d q u v l : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (advancedIntroSentence w h x r s a b c d q u v l) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameQuerySyntax.read w h x l s u b v d q) (Context.add (SyntaxMapLiftSyntax.codedLift w a c r u v l) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxMapLiftSyntax.codedLift w a c r u v l) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameQuerySyntax.read w h x l s u b v d q) := .hyp (Or.inl rfl)
  exact SyntaxRenameQuerySyntax.intro_advanced w h x r s a b c d q u v l h0 h1

theorem advancedIntro_kernel_certificate {m} (w h x r s a b c d q u v l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (advancedIntroSentence w h x r s a b c d q u v l)) := TheoryTransport.sentence (source_advancedIntro w h x r s a b c d q u v l)

theorem native_advancedIntro {m} (w h x r s a b c d q u v l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (advancedIntroSentence w h x r s a b c d q u v l)) := ZFReplay.replay (advancedIntro_kernel_certificate w h x r s a b c d q u v l)

def nullaryCaseSentence {m} (truth : Bool) (w R S r s a b c d h n q : Fin m) : Source.Sentence := ((SyntaxRenameAtomSyntax.nullary truth w a b c d n q).imp ((SyntaxRenameLocalSyntax.cases w R S r s a b c d h n q))).close

theorem source_nullaryCase {m} (truth : Bool) (w R S r s a b c d h n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nullaryCaseSentence truth w R S r s a b c d h n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameAtomSyntax.nullary truth w a b c d n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxRenameAtomSyntax.nullary truth w a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameLocalSyntax.case_nullary truth w R S r s a b c d h n q h0

theorem nullaryCase_kernel_certificate {m} (truth : Bool) (w R S r s a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nullaryCaseSentence truth w R S r s a b c d h n q)) := TheoryTransport.sentence (source_nullaryCase truth w R S r s a b c d h n q)

theorem native_nullaryCase {m} (truth : Bool) (w R S r s a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nullaryCaseSentence truth w R S r s a b c d h n q)) := ZFReplay.replay (nullaryCase_kernel_certificate truth w R S r s a b c d h n q)

def membershipCaseSentence {m} (w R S r s a b c d h n q : Fin m) : Source.Sentence := ((SyntaxRenameAtomSyntax.membership w r s a b c d n q).imp ((SyntaxRenameLocalSyntax.cases w R S r s a b c d h n q))).close

theorem source_membershipCase {m} (w R S r s a b c d h n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (membershipCaseSentence w R S r s a b c d h n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameAtomSyntax.membership w r s a b c d n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxRenameAtomSyntax.membership w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameLocalSyntax.case_membership w R S r s a b c d h n q h0

theorem membershipCase_kernel_certificate {m} (w R S r s a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (membershipCaseSentence w R S r s a b c d h n q)) := TheoryTransport.sentence (source_membershipCase w R S r s a b c d h n q)

theorem native_membershipCase {m} (w R S r s a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (membershipCaseSentence w R S r s a b c d h n q)) := ZFReplay.replay (membershipCase_kernel_certificate w R S r s a b c d h n q)

def equalityCaseSentence {m} (w R S r s a b c d h n q : Fin m) : Source.Sentence := ((SyntaxRenameAtomSyntax.equality w r s a b c d n q).imp ((SyntaxRenameLocalSyntax.cases w R S r s a b c d h n q))).close

theorem source_equalityCase {m} (w R S r s a b c d h n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalityCaseSentence w R S r s a b c d h n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameAtomSyntax.equality w r s a b c d n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxRenameAtomSyntax.equality w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameLocalSyntax.case_equality w R S r s a b c d h n q h0

theorem equalityCase_kernel_certificate {m} (w R S r s a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalityCaseSentence w R S r s a b c d h n q)) := TheoryTransport.sentence (source_equalityCase w R S r s a b c d h n q)

theorem native_equalityCase {m} (w R S r s a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalityCaseSentence w R S r s a b c d h n q)) := ZFReplay.replay (equalityCase_kernel_certificate w R S r s a b c d h n q)

def negationCaseSentence {m} (w R S r s a b c d h n q : Fin m) : Source.Sentence := ((SyntaxRenameLogicalSyntax.single 4 false w h R S a b c d n q).imp ((SyntaxRenameLocalSyntax.cases w R S r s a b c d h n q))).close

theorem source_negationCase {m} (w R S r s a b c d h n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationCaseSentence w R S r s a b c d h n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameLogicalSyntax.single 4 false w h R S a b c d n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxRenameLogicalSyntax.single 4 false w h R S a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameLocalSyntax.case_negation w R S r s a b c d h n q h0

theorem negationCase_kernel_certificate {m} (w R S r s a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationCaseSentence w R S r s a b c d h n q)) := TheoryTransport.sentence (source_negationCase w R S r s a b c d h n q)

theorem native_negationCase {m} (w R S r s a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationCaseSentence w R S r s a b c d h n q)) := ZFReplay.replay (negationCase_kernel_certificate w R S r s a b c d h n q)

def binaryCaseSentence {m} (kind : Fin 4) (w R S r s a b c d h n q : Fin m) : Source.Sentence := ((SyntaxRenameLogicalSyntax.binary kind w h R S a b c d n q).imp ((SyntaxRenameLocalSyntax.cases w R S r s a b c d h n q))).close

theorem source_binaryCase {m} (kind : Fin 4) (w R S r s a b c d h n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryCaseSentence kind w R S r s a b c d h n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameLogicalSyntax.binary kind w h R S a b c d n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxRenameLogicalSyntax.binary kind w h R S a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameLocalSyntax.case_binary kind w R S r s a b c d h n q h0

theorem binaryCase_kernel_certificate {m} (kind : Fin 4) (w R S r s a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryCaseSentence kind w R S r s a b c d h n q)) := TheoryTransport.sentence (source_binaryCase kind w R S r s a b c d h n q)

theorem native_binaryCase {m} (kind : Fin 4) (w R S r s a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryCaseSentence kind w R S r s a b c d h n q)) := ZFReplay.replay (binaryCase_kernel_certificate kind w R S r s a b c d h n q)

def quantifierCaseSentence {m} (universal : Bool) (w R S r s a b c d h n q : Fin m) : Source.Sentence := ((SyntaxRenameLogicalSyntax.single (SyntaxLogicalSyntax.quantifierTag universal) true w h R S a b c d n q).imp ((SyntaxRenameLocalSyntax.cases w R S r s a b c d h n q))).close

theorem source_quantifierCase {m} (universal : Bool) (w R S r s a b c d h n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (quantifierCaseSentence universal w R S r s a b c d h n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameLogicalSyntax.single (SyntaxLogicalSyntax.quantifierTag universal) true w h R S a b c d n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxRenameLogicalSyntax.single (SyntaxLogicalSyntax.quantifierTag universal) true w h R S a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameLocalSyntax.case_quantified universal w R S r s a b c d h n q h0

theorem quantifierCase_kernel_certificate {m} (universal : Bool) (w R S r s a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (quantifierCaseSentence universal w R S r s a b c d h n q)) := TheoryTransport.sentence (source_quantifierCase universal w R S r s a b c d h n q)

theorem native_quantifierCase {m} (universal : Bool) (w R S r s a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (quantifierCaseSentence universal w R S r s a b c d h n q)) := ZFReplay.replay (quantifierCase_kernel_certificate universal w R S r s a b c d h n q)

def localGraphsSentence {m} (w R S r s a b c d h n q : Fin m) : Source.Sentence := ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxRenameLocalSyntax.cases w R S r s a b c d h n q).imp ((SyntaxRenameLocalSyntax.localRename w R S a b c d h n q))))).close

theorem source_localGraphs {m} (w R S r s a b c d h n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (localGraphsSentence w R S r s a b c d h n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameLocalSyntax.cases w R S r s a b c d h n q) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameLocalSyntax.cases w R S r s a b c d h n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameLocalSyntax.intro_localRename w R S a b c d h n q r s (.conjI h0 (.conjI h1 h2))

theorem localGraphs_kernel_certificate {m} (w R S r s a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (localGraphsSentence w R S r s a b c d h n q)) := TheoryTransport.sentence (source_localGraphs w R S r s a b c d h n q)

theorem native_localGraphs {m} (w R S r s a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (localGraphsSentence w R S r s a b c d h n q)) := ZFReplay.replay (localGraphs_kernel_certificate w R S r s a b c d h n q)

def rowIntroSentence {m} (w n h p R S a b c d q : Fin m) : Source.Sentence := ((SyntaxRenameStateSyntax.state w R S a b c d q p).imp ((SyntaxRenameLocalSyntax.content w R S a b c d h n q).imp ((SyntaxRenameOperatorSyntax.row w n h p)))).close

theorem source_rowIntro {m} (w n h p R S a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rowIntroSentence w n h p R S a b c d q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameLocalSyntax.content w R S a b c d h n q) (Context.add (SyntaxRenameStateSyntax.state w R S a b c d q p) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxRenameStateSyntax.state w R S a b c d q p) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameLocalSyntax.content w R S a b c d h n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameOperatorSyntax.intro_row w n h p R S a b c d q h0 h1

theorem rowIntro_kernel_certificate {m} (w n h p R S a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rowIntroSentence w n h p R S a b c d q)) := TheoryTransport.sentence (source_rowIntro w n h p R S a b c d q)

theorem native_rowIntro {m} (w n h p R S a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rowIntroSentence w n h p R S a b c d q)) := ZFReplay.replay (rowIntro_kernel_certificate w n h p R S a b c d q)

def rowAtStateSentence {m} (w n h p R S a b c d q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameStateSyntax.state w R S a b c d q p).imp (((SyntaxRenameOperatorSyntax.row w n h p).iff (SyntaxRenameLocalSyntax.content w R S a b c d h n q))))).close

theorem source_rowAtState {m} (w n h p R S a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rowAtStateSentence w n h p R S a b c d q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameStateSyntax.state w R S a b c d q p) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameStateSyntax.state w R S a b c d q p) := .hyp (Or.inl rfl)
  exact SyntaxRenameOperatorRows.state_iff hZ w n h p R S a b c d q h0 h1

theorem rowAtState_kernel_certificate {m} (w n h p R S a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rowAtStateSentence w n h p R S a b c d q)) := TheoryTransport.sentence (source_rowAtState w n h p R S a b c d q)

theorem native_rowAtState {m} (w n h p R S a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rowAtStateSentence w n h p R S a b c d q)) := ZFReplay.replay (rowAtState_kernel_certificate w n h p R S a b c d q)

def rowRecognizedSentence {m} (w n h p : Fin m) : Source.Sentence := ((SyntaxRenameOperatorSyntax.row w n h p).imp ((SyntaxRenameStateSyntax.recognized w p))).close

theorem source_rowRecognized {m} (w n h p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rowRecognizedSentence w n h p) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameOperatorSyntax.row w n h p) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxRenameOperatorSyntax.row w n h p) := .hyp (Or.inl rfl)
  exact SyntaxRenameOperatorRows.recognized w n h p h0

theorem rowRecognized_kernel_certificate {m} (w n h p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rowRecognizedSentence w n h p)) := TheoryTransport.sentence (source_rowRecognized w n h p)

theorem native_rowRecognized {m} (w n h p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rowRecognizedSentence w n h p)) := ZFReplay.replay (rowRecognized_kernel_certificate w n h p)

def rowSourceNaturalSentence {m} (w n h p : Fin m) : Source.Sentence := ((SyntaxRenameOperatorSyntax.row w n h p).imp ((Formula.mem n w))).close

theorem source_rowSourceNatural {m} (w n h p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rowSourceNaturalSentence w n h p) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameOperatorSyntax.row w n h p) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxRenameOperatorSyntax.row w n h p) := .hyp (Or.inl rfl)
  exact SyntaxRenameOperatorRows.source_natural w n h p h0

theorem rowSourceNatural_kernel_certificate {m} (w n h p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rowSourceNaturalSentence w n h p)) := TheoryTransport.sentence (source_rowSourceNatural w n h p)

theorem native_rowSourceNatural {m} (w n h p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rowSourceNaturalSentence w n h p)) := ZFReplay.replay (rowSourceNatural_kernel_certificate w n h p)

def valueMemberSentence {m} (w n h v p : Fin m) : Source.Sentence := ((SyntaxRenameOperatorSyntax.value w n h v).imp (((Formula.mem p v).iff ((Formula.mem p w).conj (SyntaxRenameOperatorSyntax.row w n h p))))).close

theorem source_valueMember {m} (w n h v p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (valueMemberSentence w n h v p) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameOperatorSyntax.value w n h v) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxRenameOperatorSyntax.value w n h v) := .hyp (Or.inl rfl)
  exact SyntaxRenameOperatorSyntax.value_at w n h v p h0

theorem valueMember_kernel_certificate {m} (w n h v p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (valueMemberSentence w n h v p)) := TheoryTransport.sentence (source_valueMember w n h v p)

theorem native_valueMember {m} (w n h v p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (valueMemberSentence w n h v p)) := ZFReplay.replay (valueMember_kernel_certificate w n h v p)

def valueExistsSentence {m} (w n h : Fin m) : Source.Sentence := ((SyntaxRenameOperatorSyntax.existsValue w n h)).close

theorem source_valueExists {m} (w n h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (valueExistsSentence w n h) := by
  apply close_derives
  have hZ : ZFContext.Evidence (Source.SetLanguage.ZF.at m) := by
    exact ZFContext.source_ZF m
  exact SyntaxRenameOperatorExistence.exists_value hZ w n h

theorem valueExists_kernel_certificate {m} (w n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (valueExistsSentence w n h)) := TheoryTransport.sentence (source_valueExists w n h)

theorem native_valueExists {m} (w n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (valueExistsSentence w n h)) := ZFReplay.replay (valueExists_kernel_certificate w n h)

def valueSubsetSentence {m} (w n h v : Fin m) : Source.Sentence := ((SyntaxRenameOperatorSyntax.value w n h v).imp ((RestrictionSyntax.subset v w))).close

theorem source_valueSubset {m} (w n h v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (valueSubsetSentence w n h v) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameOperatorSyntax.value w n h v) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxRenameOperatorSyntax.value w n h v) := .hyp (Or.inl rfl)
  exact SyntaxRenameOperatorExistence.subset w n h v h0

theorem valueSubset_kernel_certificate {m} (w n h v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (valueSubsetSentence w n h v)) := TheoryTransport.sentence (source_valueSubset w n h v)

theorem native_valueSubset {m} (w n h v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (valueSubsetSentence w n h v)) := ZFReplay.replay (valueSubset_kernel_certificate w n h v)

def valueUniverseSentence {m} (w u n h v : Fin m) : Source.Sentence := ((PowerSetSyntax.powerOf u w).imp ((SyntaxRenameOperatorSyntax.value w n h v).imp ((Formula.mem v u)))).close

theorem source_valueUniverse {m} (w u n h v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (valueUniverseSentence w u n h v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameOperatorSyntax.value w n h v) (Context.add (PowerSetSyntax.powerOf u w) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (PowerSetSyntax.powerOf u w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameOperatorSyntax.value w n h v) := .hyp (Or.inl rfl)
  exact SyntaxRenameOperatorExistence.member_universe w u n h v h0 h1

theorem valueUniverse_kernel_certificate {m} (w u n h v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (valueUniverseSentence w u n h v)) := TheoryTransport.sentence (source_valueUniverse w u n h v)

theorem native_valueUniverse {m} (w u n h v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (valueUniverseSentence w u n h v)) := ZFReplay.replay (valueUniverse_kernel_certificate w u n h v)

def valueUniqueSentence {m} (w n h v t : Fin m) : Source.Sentence := ((SyntaxRenameOperatorSyntax.value w n h v).imp ((SyntaxRenameOperatorSyntax.value w n h t).imp ((Formula.equal v t)))).close

theorem source_valueUnique {m} (w n h v t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (valueUniqueSentence w n h v t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameOperatorSyntax.value w n h t) (Context.add (SyntaxRenameOperatorSyntax.value w n h v) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxRenameOperatorSyntax.value w n h v) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameOperatorSyntax.value w n h t) := .hyp (Or.inl rfl)
  exact SyntaxRenameOperatorExistence.unique hZ w n h v t h0 h1

theorem valueUnique_kernel_certificate {m} (w n h v t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (valueUniqueSentence w n h v t)) := TheoryTransport.sentence (source_valueUnique w n h v t)

theorem native_valueUnique {m} (w n h v t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (valueUniqueSentence w n h v t)) := ZFReplay.replay (valueUnique_kernel_certificate w n h v t)

def valueFiberSentence {m} (w n h : Fin m) : Source.Sentence := ((SyntaxRenameOperatorSyntax.fiber w n h)).close

theorem source_valueFiber {m} (w n h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (valueFiberSentence w n h) := by
  apply close_derives
  have hZ : ZFContext.Evidence (Source.SetLanguage.ZF.at m) := by
    exact ZFContext.source_ZF m
  exact SyntaxRenameOperatorExistence.actual_fiber hZ w n h

theorem valueFiber_kernel_certificate {m} (w n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (valueFiberSentence w n h)) := TheoryTransport.sentence (source_valueFiber w n h)

theorem native_valueFiber {m} (w n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (valueFiberSentence w n h)) := ZFReplay.replay (valueFiber_kernel_certificate w n h)

def memberRecognizedSentence {m} (w n h v p : Fin m) : Source.Sentence := ((SyntaxRenameOperatorSyntax.value w n h v).imp ((Formula.mem p v).imp ((SyntaxRenameStateSyntax.recognized w p)))).close

theorem source_memberRecognized {m} (w n h v p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberRecognizedSentence w n h v p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem p v) (Context.add (SyntaxRenameOperatorSyntax.value w n h v) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxRenameOperatorSyntax.value w n h v) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem p v) := .hyp (Or.inl rfl)
  exact SyntaxRenameOperatorMembership.member_recognized w n h v p h0 h1

theorem memberRecognized_kernel_certificate {m} (w n h v p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberRecognizedSentence w n h v p)) := TheoryTransport.sentence (source_memberRecognized w n h v p)

theorem native_memberRecognized {m} (w n h v p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberRecognizedSentence w n h v p)) := ZFReplay.replay (memberRecognized_kernel_certificate w n h v p)

def valueAtStateSentence {m} (w n h v p R S a b c d q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOperatorSyntax.value w n h v).imp ((SyntaxRenameStateSyntax.state w R S a b c d q p).imp (((Formula.mem p v).iff (SyntaxRenameLocalSyntax.content w R S a b c d h n q)))))).close

theorem source_valueAtState {m} (w n h v p R S a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (valueAtStateSentence w n h v p R S a b c d q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameStateSyntax.state w R S a b c d q p) (Context.add (SyntaxRenameOperatorSyntax.value w n h v) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxRenameOperatorSyntax.value w n h v) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameStateSyntax.state w R S a b c d q p) := .hyp (Or.inl rfl)
  exact SyntaxRenameOperatorMembership.at_state hZ w n h v p R S a b c d q h0 h1 h2

theorem valueAtState_kernel_certificate {m} (w n h v p R S a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (valueAtStateSentence w n h v p R S a b c d q)) := TheoryTransport.sentence (source_valueAtState w n h v p R S a b c d q)

theorem native_valueAtState {m} (w n h v p R S a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (valueAtStateSentence w n h v p R S a b c d q)) := ZFReplay.replay (valueAtState_kernel_certificate w n h v p R S a b c d q)

def offNaturalSentence {m} (w n h v : Fin m) : Source.Sentence := (((Formula.mem n w).neg).imp ((SyntaxRenameOperatorSyntax.value w n h v).imp ((OmegaSyntax.empty v)))).close

theorem source_offNatural {m} (w n h v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (offNaturalSentence w n h v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameOperatorSyntax.value w n h v) (Context.add ((Formula.mem n w).neg) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ ((Formula.mem n w).neg) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameOperatorSyntax.value w n h v) := .hyp (Or.inl rfl)
  exact SyntaxRenameOperatorMembership.off_natural w n h v h0 h1

theorem offNatural_kernel_certificate {m} (w n h v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (offNaturalSentence w n h v)) := TheoryTransport.sentence (source_offNatural w n h v)

theorem native_offNatural {m} (w n h v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (offNaturalSentence w n h v)) := ZFReplay.replay (offNatural_kernel_certificate w n h v)

def operatorTotalSentence {m} (w : Fin m) : Source.Sentence := ((OrdinalRecursionTotal.total SyntaxRenameRecursionSyntax.matrix (SyntaxRenameRecursionSyntax.one w))).close

theorem source_operatorTotal {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (operatorTotalSentence w) := by
  apply close_derives
  have hZ : ZFContext.Evidence (Source.SetLanguage.ZF.at m) := by
    exact ZFContext.source_ZF m
  exact SyntaxRenameRecursionStep.total hZ (SyntaxRenameRecursionSyntax.one w)

theorem operatorTotal_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (operatorTotalSentence w)) := TheoryTransport.sentence (source_operatorTotal w)

theorem native_operatorTotal {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (operatorTotalSentence w)) := ZFReplay.replay (operatorTotal_kernel_certificate w)

def operatorDeterministicSentence {m} (w : Fin m) : Source.Sentence := ((OrdinalRecursionDeterminism.deterministic SyntaxRenameRecursionSyntax.matrix (SyntaxRenameRecursionSyntax.one w))).close

theorem source_operatorDeterministic {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (operatorDeterministicSentence w) := by
  apply close_derives
  have hZ : ZFContext.Evidence (Source.SetLanguage.ZF.at m) := by
    exact ZFContext.source_ZF m
  exact SyntaxRenameRecursionStep.deterministic hZ (SyntaxRenameRecursionSyntax.one w)

theorem operatorDeterministic_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (operatorDeterministicSentence w)) := TheoryTransport.sentence (source_operatorDeterministic w)

theorem native_operatorDeterministic {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (operatorDeterministicSentence w)) := ZFReplay.replay (operatorDeterministic_kernel_certificate w)

def recursorsSentence {m} (w : Fin m) : Source.Sentence := ((SyntaxRenameRecursionSyntax.recursors w)).close

theorem source_recursors {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (recursorsSentence w) := by
  apply close_derives
  have hZ : ZFContext.Evidence (Source.SetLanguage.ZF.at m) := by
    exact ZFContext.source_ZF m
  exact SyntaxRenameRecursors.all_unique hZ w

theorem recursors_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (recursorsSentence w)) := TheoryTransport.sentence (source_recursors w)

theorem native_recursors {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (recursorsSentence w)) := ZFReplay.replay (recursors_kernel_certificate w)

def graphFiberSentence {m} (w d : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal d).imp ((OrdinalRecursionExistenceSyntax.fiber SyntaxRenameRecursionSyntax.matrix (SyntaxRenameRecursionSyntax.one w) d))).close

theorem source_graphFiber {m} (w d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphFiberSentence w d) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (OrdinalSyntax.ordinal d) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal d) := .hyp (Or.inl rfl)
  exact SyntaxRenameRecursors.at_ordinal hZ w d h0

theorem graphFiber_kernel_certificate {m} (w d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphFiberSentence w d)) := TheoryTransport.sentence (source_graphFiber w d)

theorem native_graphFiber {m} (w d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphFiberSentence w d)) := ZFReplay.replay (graphFiber_kernel_certificate w d)

def carrierRecursorsSentence {m} (w : Fin m) : Source.Sentence := ((SyntaxRenameRecursionSyntax.actualRecursors w)).close

theorem source_carrierRecursors {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (carrierRecursorsSentence w) := by
  apply close_derives
  have hZ : ZFContext.Evidence (Source.SetLanguage.ZF.at m) := by
    exact ZFContext.source_ZF m
  exact SyntaxRenameRecursors.actual_carrier_recursors hZ w

theorem carrierRecursors_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (carrierRecursorsSentence w)) := TheoryTransport.sentence (source_carrierRecursors w)

theorem native_carrierRecursors {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (carrierRecursorsSentence w)) := ZFReplay.replay (carrierRecursors_kernel_certificate w)

def evaluationExistsSentence {m} (w n : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal n).imp ((SyntaxRenameEvaluationSyntax.existsValue w n))).close

theorem source_evaluationExists {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (evaluationExistsSentence w n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (OrdinalSyntax.ordinal n) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inl rfl)
  exact SyntaxRenameEvaluationExistence.exists_value hZ w n h0

theorem evaluationExists_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (evaluationExistsSentence w n)) := TheoryTransport.sentence (source_evaluationExists w n)

theorem native_evaluationExists {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (evaluationExistsSentence w n)) := ZFReplay.replay (evaluationExists_kernel_certificate w n)

def naturalEvaluationExistsSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((SyntaxRenameEvaluationSyntax.existsValue w n)))).close

theorem source_naturalEvaluationExists {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (naturalEvaluationExistsSentence w n) := by
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
  exact SyntaxRenameEvaluationExistence.at_natural hZ w n h0 h1

theorem naturalEvaluationExists_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (naturalEvaluationExistsSentence w n)) := TheoryTransport.sentence (source_naturalEvaluationExists w n)

theorem native_naturalEvaluationExists {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (naturalEvaluationExistsSentence w n)) := ZFReplay.replay (naturalEvaluationExists_kernel_certificate w n)

def evaluationUniqueSentence {m} (w n y u : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal n).imp ((SyntaxRenameEvaluationSyntax.evaluation w n y).imp ((SyntaxRenameEvaluationSyntax.evaluation w n u).imp ((Formula.equal y u))))).close

theorem source_evaluationUnique {m} (w n y u : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (evaluationUniqueSentence w n y u) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameEvaluationSyntax.evaluation w n u) (Context.add (SyntaxRenameEvaluationSyntax.evaluation w n y) (Context.add (OrdinalSyntax.ordinal n) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxRenameEvaluationSyntax.evaluation w n y) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameEvaluationSyntax.evaluation w n u) := .hyp (Or.inl rfl)
  exact SyntaxRenameEvaluationUnique.unique hZ w n y u h0 h1 h2

theorem evaluationUnique_kernel_certificate {m} (w n y u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (evaluationUniqueSentence w n y u)) := TheoryTransport.sentence (source_evaluationUnique w n y u)

theorem native_evaluationUnique {m} (w n y u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (evaluationUniqueSentence w n y u)) := ZFReplay.replay (evaluationUnique_kernel_certificate w n y u)

def evaluationFiberSentence {m} (w n : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal n).imp ((SyntaxRenameEvaluationSyntax.fiber w n))).close

theorem source_evaluationFiber {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (evaluationFiberSentence w n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (OrdinalSyntax.ordinal n) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inl rfl)
  exact SyntaxRenameEvaluationUnique.exists_unique hZ w n h0

theorem evaluationFiber_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (evaluationFiberSentence w n)) := TheoryTransport.sentence (source_evaluationFiber w n)

theorem native_evaluationFiber {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (evaluationFiberSentence w n)) := ZFReplay.replay (evaluationFiber_kernel_certificate w n)

def naturalEvaluationFiberSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((SyntaxRenameEvaluationSyntax.fiber w n)))).close

theorem source_naturalEvaluationFiber {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (naturalEvaluationFiberSentence w n) := by
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
  exact SyntaxRenameEvaluationUnique.exists_unique hZ w n (NaturalOrderBasic.ordinal hZ w n h0 h1)

theorem naturalEvaluationFiber_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (naturalEvaluationFiberSentence w n)) := TheoryTransport.sentence (source_naturalEvaluationFiber w n)

theorem native_naturalEvaluationFiber {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (naturalEvaluationFiberSentence w n)) := ZFReplay.replay (naturalEvaluationFiber_kernel_certificate w n)

def graphAgreementSentence {m} (w f g d t : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal d).imp ((OrdinalSyntax.ordinal t).imp ((SyntaxRenameRecursionSyntax.graph w f d).imp ((SyntaxRenameRecursionSyntax.graph w g t).imp ((GraphFamilySyntax.agrees f g)))))).close

theorem source_graphAgreement {m} (w f g d t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphAgreementSentence w f g d t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursionSyntax.graph w g t) (Context.add (SyntaxRenameRecursionSyntax.graph w f d) (Context.add (OrdinalSyntax.ordinal t) (Context.add (OrdinalSyntax.ordinal d) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (OrdinalSyntax.ordinal t) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxRenameRecursionSyntax.graph w f d) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxRenameRecursionSyntax.graph w g t) := .hyp (Or.inl rfl)
  exact SyntaxRenameEvaluationUnique.graphs_agree hZ w f g d t h0 h1 h2 h3

theorem graphAgreement_kernel_certificate {m} (w f g d t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphAgreementSentence w f g d t)) := TheoryTransport.sentence (source_graphAgreement w f g d t)

theorem native_graphAgreement {m} (w f g d t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphAgreementSentence w f g d t)) := ZFReplay.replay (graphAgreement_kernel_certificate w f g d t)

def graphEdgeValueSentence {m} (w f d n y : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal d).imp ((Formula.mem n d).imp ((SyntaxRenameRecursionSyntax.graph w f d).imp (((GraphSyntax.edge f n y).iff (SyntaxRenameEvaluationSyntax.evaluation w n y)))))).close

theorem source_graphEdgeValue {m} (w f d n y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphEdgeValueSentence w f d n y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursionSyntax.graph w f d) (Context.add (Formula.mem n d) (Context.add (OrdinalSyntax.ordinal d) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem n d) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameRecursionSyntax.graph w f d) := .hyp (Or.inl rfl)
  exact SyntaxRenameGraphValues.edge_iff_value hZ w f d n y h0 h1 h2

theorem graphEdgeValue_kernel_certificate {m} (w f d n y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphEdgeValueSentence w f d n y)) := TheoryTransport.sentence (source_graphEdgeValue w f d n y)

theorem native_graphEdgeValue {m} (w f d n y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphEdgeValueSentence w f d n y)) := ZFReplay.replay (graphEdgeValue_kernel_certificate w f d n y)

def prefixSentence {m} (w n y : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal n).imp ((SyntaxRenameEvaluationSyntax.evaluation w n y).imp ((SyntaxRenameHistory.stepHistory w n y)))).close

theorem source_prefix {m} (w n y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (prefixSentence w n y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameEvaluationSyntax.evaluation w n y) (Context.add (OrdinalSyntax.ordinal n) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameEvaluationSyntax.evaluation w n y) := .hyp (Or.inl rfl)
  exact SyntaxRenameHistory.from_value hZ w n y h0 h1

theorem prefix_kernel_certificate {m} (w n y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (prefixSentence w n y)) := TheoryTransport.sentence (source_prefix w n y)

theorem native_prefix {m} (w n y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (prefixSentence w n y)) := ZFReplay.replay (prefix_kernel_certificate w n y)

def evaluationSubsetSentence {m} (w n y : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal n).imp ((SyntaxRenameEvaluationSyntax.evaluation w n y).imp ((RestrictionSyntax.subset y w)))).close

theorem source_evaluationSubset {m} (w n y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (evaluationSubsetSentence w n y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameEvaluationSyntax.evaluation w n y) (Context.add (OrdinalSyntax.ordinal n) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameEvaluationSyntax.evaluation w n y) := .hyp (Or.inl rfl)
  exact SyntaxRenameHistory.range_subset hZ w n y h0 h1

theorem evaluationSubset_kernel_certificate {m} (w n y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (evaluationSubsetSentence w n y)) := TheoryTransport.sentence (source_evaluationSubset w n y)

theorem native_evaluationSubset {m} (w n y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (evaluationSubsetSentence w n y)) := ZFReplay.replay (evaluationSubset_kernel_certificate w n y)

def evaluationUniverseSentence {m} (w u n y : Fin m) : Source.Sentence := ((PowerSetSyntax.powerOf u w).imp ((OrdinalSyntax.ordinal n).imp ((SyntaxRenameEvaluationSyntax.evaluation w n y).imp ((Formula.mem y u))))).close

theorem source_evaluationUniverse {m} (w u n y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (evaluationUniverseSentence w u n y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameEvaluationSyntax.evaluation w n y) (Context.add (OrdinalSyntax.ordinal n) (Context.add (PowerSetSyntax.powerOf u w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (PowerSetSyntax.powerOf u w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameEvaluationSyntax.evaluation w n y) := .hyp (Or.inl rfl)
  exact SyntaxRenameHistory.range_member hZ w u n y h0 h1 h2

theorem evaluationUniverse_kernel_certificate {m} (w u n y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (evaluationUniverseSentence w u n y)) := TheoryTransport.sentence (source_evaluationUniverse w u n y)

theorem native_evaluationUniverse {m} (w u n y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (evaluationUniverseSentence w u n y)) := ZFReplay.replay (evaluationUniverse_kernel_certificate w u n y)

def evaluationOffNaturalSentence {m} (w n y : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal n).imp (((Formula.mem n w).neg).imp ((SyntaxRenameEvaluationSyntax.evaluation w n y).imp ((OmegaSyntax.empty y))))).close

theorem source_evaluationOffNatural {m} (w n y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (evaluationOffNaturalSentence w n y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameEvaluationSyntax.evaluation w n y) (Context.add ((Formula.mem n w).neg) (Context.add (OrdinalSyntax.ordinal n) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ ((Formula.mem n w).neg) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameEvaluationSyntax.evaluation w n y) := .hyp (Or.inl rfl)
  exact SyntaxRenameHistory.off_natural hZ w n y h0 h1 h2

theorem evaluationOffNatural_kernel_certificate {m} (w n y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (evaluationOffNaturalSentence w n y)) := TheoryTransport.sentence (source_evaluationOffNatural w n y)

theorem native_evaluationOffNatural {m} (w n y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (evaluationOffNaturalSentence w n y)) := ZFReplay.replay (evaluationOffNatural_kernel_certificate w n y)

def existenceSentence : Source.Sentence := SyntaxRenameRecursionSyntax.existsSystem

theorem source_existence : Derives (Source.SetLanguage.ZF.at 0) existenceSentence := by
  have hh := SyntaxRenameRecursors.existence (ZFContext.source_ZF 0)
  have hId : (Fin.elim0 : Fin 0 → Fin 0) = id := by funext i; exact Fin.elim0 i
  simpa only [existenceSentence, hId, Reverse.source_rename_id] using hh

theorem existence_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence existenceSentence) := TheoryTransport.sentence source_existence

theorem native_existence : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence existenceSentence) := ZFReplay.replay existence_kernel_certificate
end PPAC.Migration.Internal.ObjectSyntaxRenameOperator
