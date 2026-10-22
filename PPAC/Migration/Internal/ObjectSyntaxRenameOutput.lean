import PPAC.Migration.Internal.SyntaxRenameNullary

/-! 实际量词提升参数对齐、输出纤维合同和两个空原子实际唯一输出的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxRenameOutput
open Source SourceAlgebra SourceLogic OmegaSyntax

def liftSuccessorsSentence {m} (w a c k u v l : Fin m) : Source.Sentence := ((SyntaxMapLiftSyntax.codedLift w a c k u v l).imp ((successor u a).conj (successor v c))).close

theorem source_liftSuccessors {m} (w a c k u v l : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftSuccessorsSentence w a c k u v l) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapLiftSyntax.codedLift w a c k u v l) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxMapLiftSyntax.codedLift w a c k u v l) := .hyp (Or.inl rfl)
  exact SyntaxMapLiftParameters.successors w a c k u v l h0

theorem liftSuccessors_kernel_certificate {m} (w a c k u v l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftSuccessorsSentence w a c k u v l)) := TheoryTransport.sentence (source_liftSuccessors w a c k u v l)

theorem native_liftSuccessors {m} (w a c k u v l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftSuccessorsSentence w a c k u v l)) := ZFReplay.replay (liftSuccessors_kernel_certificate w a c k u v l)

def liftParametersSentence {m} (w a c k u v l U V L : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapLiftSyntax.codedLift w a c k u v l).imp ((SyntaxMapLiftSyntax.codedLift w a c k U V L).imp ((Formula.equal u U).conj ((Formula.equal v V).conj (.equal l L)))))).close

theorem source_liftParameters {m} (w a c k u v l U V L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftParametersSentence w a c k u v l U V L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapLiftSyntax.codedLift w a c k U V L) (Context.add (SyntaxMapLiftSyntax.codedLift w a c k u v l) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMapLiftSyntax.codedLift w a c k u v l) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMapLiftSyntax.codedLift w a c k U V L) := .hyp (Or.inl rfl)
  exact SyntaxMapLiftParameters.unique hZ w a c k u v l U V L h0 h1 h2

theorem liftParameters_kernel_certificate {m} (w a c k u v l U V L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftParametersSentence w a c k u v l U V L)) := TheoryTransport.sentence (source_liftParameters w a c k u v l U V L)

theorem native_liftParameters {m} (w a c k u v l U V L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftParametersSentence w a c k u v l U V L)) := ZFReplay.replay (liftParameters_kernel_certificate w a c k u v l U V L)

def advancedAtLiftSentence {m} (w x r s a b c d q u v l : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapLiftSyntax.codedLift w a c r u v l).imp ((SyntaxRenameRecursiveSyntax.advanced w x r s a b c d q).iff (SyntaxRenameJudgmentSyntax.renamed w l s u b v d x q)))).close

theorem source_advancedAtLift {m} (w x r s a b c d q u v l : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (advancedAtLiftSentence w x r s a b c d q u v l) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapLiftSyntax.codedLift w a c r u v l) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMapLiftSyntax.codedLift w a c r u v l) := .hyp (Or.inl rfl)
  exact SyntaxRenameAdvancedKnown.at_lift hZ w x r s a b c d q u v l h0 h1

theorem advancedAtLift_kernel_certificate {m} (w x r s a b c d q u v l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (advancedAtLiftSentence w x r s a b c d q u v l)) := TheoryTransport.sentence (source_advancedAtLift w x r s a b c d q u v l)

theorem native_advancedAtLift {m} (w x r s a b c d q u v l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (advancedAtLiftSentence w x r s a b c d q u v l)) := ZFReplay.replay (advancedAtLift_kernel_certificate w x r s a b c d q u v l)

def renamedInputSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q).imp (SyntaxRenameOutputSyntax.input w r s a b c d n))).close

theorem source_renamedInput {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (renamedInputSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameOutput.input_of_renamed hZ w r s a b c d n q h0 h1

theorem renamedInput_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (renamedInputSentence w r s a b c d n q)) := TheoryTransport.sentence (source_renamedInput w r s a b c d n q)

theorem native_renamedInput {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (renamedInputSentence w r s a b c d n q)) := ZFReplay.replay (renamedInput_kernel_certificate w r s a b c d n q)

def renamedNaturalSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q).imp (Formula.mem q w)).close

theorem source_renamedNatural {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (renamedNaturalSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameOutput.output_natural w r s a b c d n q h0

theorem renamedNatural_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (renamedNaturalSentence w r s a b c d n q)) := TheoryTransport.sentence (source_renamedNatural w r s a b c d n q)

theorem native_renamedNatural {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (renamedNaturalSentence w r s a b c d n q)) := ZFReplay.replay (renamedNatural_kernel_certificate w r s a b c d n q)

def inputNaturalSentence {m} (w r s a b c d n : Fin m) : Source.Sentence := ((SyntaxRenameOutputSyntax.input w r s a b c d n).imp (Formula.mem n w)).close

theorem source_inputNatural {m} (w r s a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (inputNaturalSentence w r s a b c d n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameOutputSyntax.input w r s a b c d n) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxRenameOutputSyntax.input w r s a b c d n) := .hyp (Or.inl rfl)
  exact SyntaxRenameOutput.input_natural w r s a b c d n h0

theorem inputNatural_kernel_certificate {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (inputNaturalSentence w r s a b c d n)) := TheoryTransport.sentence (source_inputNatural w r s a b c d n)

theorem native_inputNatural {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (inputNaturalSentence w r s a b c d n)) := ZFReplay.replay (inputNatural_kernel_certificate w r s a b c d n)

def existsFromFiberSentence {m} (w r s a b c d n : Fin m) : Source.Sentence := ((SyntaxRenameOutputSyntax.fiber w r s a b c d n).imp (SyntaxRenameOutputSyntax.existsOutput w r s a b c d n)).close

theorem source_existsFromFiber {m} (w r s a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsFromFiberSentence w r s a b c d n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameOutputSyntax.fiber w r s a b c d n) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxRenameOutputSyntax.fiber w r s a b c d n) := .hyp (Or.inl rfl)
  exact SyntaxRenameOutput.exists_of_fiber w r s a b c d n h0

theorem existsFromFiber_kernel_certificate {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsFromFiberSentence w r s a b c d n)) := TheoryTransport.sentence (source_existsFromFiber w r s a b c d n)

theorem native_existsFromFiber {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsFromFiberSentence w r s a b c d n)) := ZFReplay.replay (existsFromFiber_kernel_certificate w r s a b c d n)

def existsFromRenamedSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q).imp (SyntaxRenameOutputSyntax.existsOutput w r s a b c d n)).close

theorem source_existsFromRenamed {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsFromRenamedSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameOutputSyntax.intro_exists w r s a b c d n q h0

theorem existsFromRenamed_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsFromRenamedSentence w r s a b c d n q)) := TheoryTransport.sentence (source_existsFromRenamed w r s a b c d n q)

theorem native_existsFromRenamed {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsFromRenamedSentence w r s a b c d n q)) := ZFReplay.replay (existsFromRenamed_kernel_certificate w r s a b c d n q)

def fiberIntroSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q).imp ((SyntaxRenameOutputSyntax.uniqueOutput w r s a b c d n q).imp (SyntaxRenameOutputSyntax.fiber w r s a b c d n))).close

theorem source_fiberIntro {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fiberIntroSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameOutputSyntax.uniqueOutput w r s a b c d n q) (Context.add (SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q) ((Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.uniqueOutput w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameOutputSyntax.intro_fiber w r s a b c d n q h0 h1

theorem fiberIntro_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fiberIntroSentence w r s a b c d n q)) := TheoryTransport.sentence (source_fiberIntro w r s a b c d n q)

theorem native_fiberIntro {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fiberIntroSentence w r s a b c d n q)) := ZFReplay.replay (fiberIntro_kernel_certificate w r s a b c d n q)

def propertyAtSentence {m} (w n r s a b c d : Fin m) : Source.Sentence := ((SyntaxRenameOutputSyntax.property w n).imp ((SyntaxRenameOutputSyntax.input w r s a b c d n).imp (SyntaxRenameOutputSyntax.fiber w r s a b c d n))).close

theorem source_propertyAt {m} (w n r s a b c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (propertyAtSentence w n r s a b c d) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameOutputSyntax.property w n) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxRenameOutputSyntax.property w n) := .hyp (Or.inl rfl)
  exact SyntaxRenameOutputSyntax.property_at w n r s a b c d h0

theorem propertyAt_kernel_certificate {m} (w n r s a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (propertyAtSentence w n r s a b c d)) := TheoryTransport.sentence (source_propertyAt w n r s a b c d)

theorem native_propertyAt {m} (w n r s a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (propertyAtSentence w n r s a b c d)) := ZFReplay.replay (propertyAt_kernel_certificate w n r s a b c d)

def earlierAtSentence {m} (w n x : Fin m) : Source.Sentence := ((SyntaxRenameOutputSyntax.earlier w n).imp ((Formula.mem x w).imp ((Formula.mem x n).imp (SyntaxRenameOutputSyntax.property w x)))).close

theorem source_earlierAt {m} (w n x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (earlierAtSentence w n x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem x n) (Context.add (Formula.mem x w) (Context.add (SyntaxRenameOutputSyntax.earlier w n) ((Source.SetLanguage.ZF.at m))))
  have h0 : Derives Δ (SyntaxRenameOutputSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem x w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem x n) := .hyp (Or.inl rfl)
  exact SyntaxRenameOutputSyntax.earlier_at w n x h0 h1 h2

theorem earlierAt_kernel_certificate {m} (w n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (earlierAtSentence w n x)) := TheoryTransport.sentence (source_earlierAt w n x)

theorem native_earlierAt {m} (w n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (earlierAtSentence w n x)) := ZFReplay.replay (earlierAt_kernel_certificate w n x)

def atomicFilterSentence {m} (kind : Fin 4) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor arity kind.val w xs n).imp ((SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q).imp (SyntaxRenameAtomicCases.atomicCase kind w r s a b c d n q)))).close

theorem source_atomicFilter {m} (kind : Fin 4) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atomicFilterSentence kind arity w R S r s a b c d n q xs) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q) (Context.add (SyntaxNodeSyntax.constructor arity kind.val w xs n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor arity kind.val w xs n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameAtomicCases.filter hZ kind arity w R S r s a b c d n q xs h0 h1 h2

theorem atomicFilter_kernel_certificate {m} (kind : Fin 4) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atomicFilterSentence kind arity w R S r s a b c d n q xs)) := TheoryTransport.sentence (source_atomicFilter kind arity w R S r s a b c d n q xs)

theorem native_atomicFilter {m} (kind : Fin 4) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atomicFilterSentence kind arity w R S r s a b c d n q xs)) := ZFReplay.replay (atomicFilter_kernel_certificate kind arity w R S r s a b c d n q xs)

def nullaryLocalSentence {m} (truth : Bool) (w r s a b c d n q : Fin m) : Source.Sentence := ((SyntaxMapCodeSyntax.mapCode w a c r).imp ((SyntaxMapCodeSyntax.mapCode w b d s).imp ((SyntaxRenameAtomSyntax.nullary truth w a b c d n q).imp (SyntaxRenameRecursiveSyntax.localRename w r s a b c d n q)))).close

theorem source_nullaryLocal {m} (truth : Bool) (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nullaryLocalSentence truth w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameAtomSyntax.nullary truth w a b c d n q) (Context.add (SyntaxMapCodeSyntax.mapCode w b d s) (Context.add (SyntaxMapCodeSyntax.mapCode w a c r) ((Source.SetLanguage.ZF.at m))))
  have h0 : Derives Δ (SyntaxMapCodeSyntax.mapCode w a c r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.mapCode w b d s) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameAtomSyntax.nullary truth w a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameNullary.local_nullary truth w r s a b c d n q h0 h1 h2

theorem nullaryLocal_kernel_certificate {m} (truth : Bool) (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nullaryLocalSentence truth w r s a b c d n q)) := TheoryTransport.sentence (source_nullaryLocal truth w r s a b c d n q)

theorem native_nullaryLocal {m} (truth : Bool) (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nullaryLocalSentence truth w r s a b c d n q)) := ZFReplay.replay (nullaryLocal_kernel_certificate truth w r s a b c d n q)

def nullarySelfSentence {m} (truth : Bool) (w r s a b c d n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.input w r s a b c d n).imp ((SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n).imp (SyntaxRenameJudgmentSyntax.renamed w r s a b c d n n)))).close

theorem source_nullarySelf {m} (truth : Bool) (w r s a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nullarySelfSentence truth w r s a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) (Context.add (SyntaxRenameOutputSyntax.input w r s a b c d n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.input w r s a b c d n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) := .hyp (Or.inl rfl)
  exact SyntaxRenameNullary.intro_self hZ truth w r s a b c d n h0 h1 h2

theorem nullarySelf_kernel_certificate {m} (truth : Bool) (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nullarySelfSentence truth w r s a b c d n)) := TheoryTransport.sentence (source_nullarySelf truth w r s a b c d n)

theorem native_nullarySelf {m} (truth : Bool) (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nullarySelfSentence truth w r s a b c d n)) := ZFReplay.replay (nullarySelf_kernel_certificate truth w r s a b c d n)

def nullaryUniqueSentence {m} (truth : Bool) (w r s a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n).imp ((SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q).imp (Formula.equal q n)))).close

theorem source_nullaryUnique {m} (truth : Bool) (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nullaryUniqueSentence truth w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q) (Context.add (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameNullary.unique hZ truth w r s a b c d n q h0 h1 h2

theorem nullaryUnique_kernel_certificate {m} (truth : Bool) (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nullaryUniqueSentence truth w r s a b c d n q)) := TheoryTransport.sentence (source_nullaryUnique truth w r s a b c d n q)

theorem native_nullaryUnique {m} (truth : Bool) (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nullaryUniqueSentence truth w r s a b c d n q)) := ZFReplay.replay (nullaryUnique_kernel_certificate truth w r s a b c d n q)

def nullaryFiberSentence {m} (truth : Bool) (w r s a b c d n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.input w r s a b c d n).imp ((SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n).imp (SyntaxRenameOutputSyntax.fiber w r s a b c d n)))).close

theorem source_nullaryFiber {m} (truth : Bool) (w r s a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nullaryFiberSentence truth w r s a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) (Context.add (SyntaxRenameOutputSyntax.input w r s a b c d n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.input w r s a b c d n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) := .hyp (Or.inl rfl)
  exact SyntaxRenameNullary.actual_fiber hZ truth w r s a b c d n h0 h1 h2

theorem nullaryFiber_kernel_certificate {m} (truth : Bool) (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nullaryFiberSentence truth w r s a b c d n)) := TheoryTransport.sentence (source_nullaryFiber truth w r s a b c d n)

theorem native_nullaryFiber {m} (truth : Bool) (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nullaryFiberSentence truth w r s a b c d n)) := ZFReplay.replay (nullaryFiber_kernel_certificate truth w r s a b c d n)

def nullaryAllParametersSentence {m} (truth : Bool) (w n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n).imp (SyntaxRenameOutputSyntax.property w n))).close

theorem source_nullaryAllParameters {m} (truth : Bool) (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nullaryAllParametersSentence truth w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) := .hyp (Or.inl rfl)
  exact SyntaxRenameNullary.property_all_parameters hZ truth w n h0 h1

theorem nullaryAllParameters_kernel_certificate {m} (truth : Bool) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nullaryAllParametersSentence truth w n)) := TheoryTransport.sentence (source_nullaryAllParameters truth w n)

theorem native_nullaryAllParameters {m} (truth : Bool) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nullaryAllParametersSentence truth w n)) := ZFReplay.replay (nullaryAllParameters_kernel_certificate truth w n)

end PPAC.Migration.Internal.ObjectSyntaxRenameOutput
