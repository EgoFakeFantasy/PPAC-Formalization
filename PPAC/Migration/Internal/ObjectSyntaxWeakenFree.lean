import PPAC.Migration.Internal.SyntaxWeakenFreeAtoms
import PPAC.Migration.Internal.SyntaxWeakenFreeLogical
import PPAC.Migration.Internal.SyntaxWeakenFreeTerm
import PPAC.Migration.Internal.SyntaxWeakenFreeLogicalInternal

/-! 全内部 free 头槽弱化、唯一输出和11构造子的 YesMetaZFC 原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxWeakenFree
open Source SourceAlgebra SourceLogic OmegaSyntax

def identityUniqueSentence {m} (w a R T : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w a R).imp ((SyntaxIdentityMapSyntax.identityCode w a T).imp ((Formula.equal R T))))).close

theorem source_identityUnique {m} (w a R T : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (identityUniqueSentence w a R T) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIdentityMapSyntax.identityCode w a T) (Context.add (SyntaxIdentityMapSyntax.identityCode w a R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a R) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a T) := .hyp (Or.inl rfl)
  exact SyntaxIdentityUnique.code_unique hZ w a R T h0 h1 h2

theorem identityUnique_kernel_certificate {m} (w a R T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (identityUniqueSentence w a R T)) := TheoryTransport.sentence (source_identityUnique w a R T)

theorem native_identityUnique {m} (w a R T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (identityUniqueSentence w a R T)) := ZFReplay.replay (identityUnique_kernel_certificate w a R T)

def identityLiftSentence {m} (w a R u L : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w a R).imp ((successor u a).imp ((SyntaxIdentityMapSyntax.identityCode w u L).imp ((SyntaxMapLiftSyntax.codedLift w a a R u u L)))))).close

theorem source_identityLift {m} (w a R u L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (identityLiftSentence w a R u L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIdentityMapSyntax.identityCode w u L) (Context.add (successor u a) (Context.add (SyntaxIdentityMapSyntax.identityCode w a R) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor u a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w u L) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeLift.identity_lift hZ w a R u L h0 h1 h2 h3

theorem identityLift_kernel_certificate {m} (w a R u L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (identityLiftSentence w a R u L)) := TheoryTransport.sentence (source_identityLift w a R u L)

theorem native_identityLift {m} (w a R u L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (identityLiftSentence w a R u L)) := ZFReplay.replay (identityLift_kernel_certificate w a R u L)

def inputSentence {m} (w a b B n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxWeakenFreeSyntax.weakened w a b B n q).imp ((SyntaxWeakenFreeSyntax.input w a b B n)))).close

theorem source_input {m} (w a b B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (inputSentence w a b B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxWeakenFreeSyntax.weakened w a b B n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxWeakenFreeSyntax.weakened w a b B n q) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeOutput.input_of_weakened hZ w a b B n q h0 h1

theorem input_kernel_certificate {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (inputSentence w a b B n q)) := TheoryTransport.sentence (source_input w a b B n q)

theorem native_input {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (inputSentence w a b B n q)) := ZFReplay.replay (input_kernel_certificate w a b B n q)

def sourceTypeSentence {m} (w a b B n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxWeakenFreeSyntax.weakened w a b B n q).imp ((FormulaCodeSyntax.formulaCode w n a b)))).close

theorem source_sourceType {m} (w a b B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (sourceTypeSentence w a b B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxWeakenFreeSyntax.weakened w a b B n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxWeakenFreeSyntax.weakened w a b B n q) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeOutput.source_type hZ w a b B n q h0 h1

theorem sourceType_kernel_certificate {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (sourceTypeSentence w a b B n q)) := TheoryTransport.sentence (source_sourceType w a b B n q)

theorem native_sourceType {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (sourceTypeSentence w a b B n q)) := ZFReplay.replay (sourceType_kernel_certificate w a b B n q)

def targetTypeSentence {m} (w a b B n q : Fin m) : Source.Sentence := ((SyntaxWeakenFreeSyntax.weakened w a b B n q).imp ((FormulaCodeSyntax.formulaCode w q a B))).close

theorem source_targetType {m} (w a b B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (targetTypeSentence w a b B n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxWeakenFreeSyntax.weakened w a b B n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxWeakenFreeSyntax.weakened w a b B n q) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeOutput.target_type w a b B n q h0

theorem targetType_kernel_certificate {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (targetTypeSentence w a b B n q)) := TheoryTransport.sentence (source_targetType w a b B n q)

theorem native_targetType {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (targetTypeSentence w a b B n q)) := ZFReplay.replay (targetType_kernel_certificate w a b B n q)

def outputNaturalSentence {m} (w a b B n q : Fin m) : Source.Sentence := ((SyntaxWeakenFreeSyntax.weakened w a b B n q).imp ((Formula.mem q w))).close

theorem source_outputNatural {m} (w a b B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (outputNaturalSentence w a b B n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxWeakenFreeSyntax.weakened w a b B n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxWeakenFreeSyntax.weakened w a b B n q) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeOutput.output_natural w a b B n q h0

theorem outputNatural_kernel_certificate {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (outputNaturalSentence w a b B n q)) := TheoryTransport.sentence (source_outputNatural w a b B n q)

theorem native_outputNatural {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (outputNaturalSentence w a b B n q)) := ZFReplay.replay (outputNatural_kernel_certificate w a b B n q)

def existsOutputSentence {m} (w a b B n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxWeakenFreeSyntax.input w a b B n).imp ((SyntaxWeakenFreeSyntax.existsOutput w a b B n)))).close

theorem source_existsOutput {m} (w a b B n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsOutputSentence w a b B n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxWeakenFreeSyntax.input w a b B n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxWeakenFreeSyntax.input w a b B n) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeOutput.exists_output hZ w a b B n h0 h1

theorem existsOutput_kernel_certificate {m} (w a b B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsOutputSentence w a b B n)) := TheoryTransport.sentence (source_existsOutput w a b B n)

theorem native_existsOutput {m} (w a b B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsOutputSentence w a b B n)) := ZFReplay.replay (existsOutput_kernel_certificate w a b B n)

def atCodesSentence {m} (w a b B n q R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w a R).imp ((SyntaxFreeShiftSyntax.shiftCode w b B S).imp (((SyntaxWeakenFreeSyntax.weakened w a b B n q).iff (SyntaxRenameJudgmentSyntax.renamed w R S a b a B n q)))))).close

theorem source_atCodes {m} (w a b B n q R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atCodesSentence w a b B n q R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeShiftSyntax.shiftCode w b B S) (Context.add (SyntaxIdentityMapSyntax.identityCode w a R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a R) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B S) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeUnique.at_codes_iff hZ w a b B n q R S h0 h1 h2

theorem atCodes_kernel_certificate {m} (w a b B n q R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atCodesSentence w a b B n q R S)) := TheoryTransport.sentence (source_atCodes w a b B n q R S)

theorem native_atCodes {m} (w a b B n q R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atCodesSentence w a b B n q R S)) := ZFReplay.replay (atCodes_kernel_certificate w a b B n q R S)

def outputUniqueSentence {m} (w a b B n q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxWeakenFreeSyntax.weakened w a b B n q).imp ((SyntaxWeakenFreeSyntax.weakened w a b B n v).imp ((Formula.equal q v))))).close

theorem source_outputUnique {m} (w a b B n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (outputUniqueSentence w a b B n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxWeakenFreeSyntax.weakened w a b B n v) (Context.add (SyntaxWeakenFreeSyntax.weakened w a b B n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxWeakenFreeSyntax.weakened w a b B n q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxWeakenFreeSyntax.weakened w a b B n v) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeUnique.unique hZ w a b B n q v h0 h1 h2

theorem outputUnique_kernel_certificate {m} (w a b B n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (outputUniqueSentence w a b B n q v)) := TheoryTransport.sentence (source_outputUnique w a b B n q v)

theorem native_outputUnique {m} (w a b B n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (outputUniqueSentence w a b B n q v)) := ZFReplay.replay (outputUnique_kernel_certificate w a b B n q v)

def uniqueOutputSentence {m} (w a b B n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxWeakenFreeSyntax.weakened w a b B n q).imp ((SyntaxWeakenFreeSyntax.uniqueOutput w a b B n q)))).close

theorem source_uniqueOutput {m} (w a b B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniqueOutputSentence w a b B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxWeakenFreeSyntax.weakened w a b B n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxWeakenFreeSyntax.weakened w a b B n q) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeUnique.unique_output hZ w a b B n q h0 h1

theorem uniqueOutput_kernel_certificate {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniqueOutputSentence w a b B n q)) := TheoryTransport.sentence (source_uniqueOutput w a b B n q)

theorem native_uniqueOutput {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniqueOutputSentence w a b B n q)) := ZFReplay.replay (uniqueOutput_kernel_certificate w a b B n q)

def actualFiberSentence {m} (w a b B n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxWeakenFreeSyntax.input w a b B n).imp ((SyntaxWeakenFreeSyntax.fiber w a b B n)))).close

theorem source_actualFiber {m} (w a b B n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualFiberSentence w a b B n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxWeakenFreeSyntax.input w a b B n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxWeakenFreeSyntax.input w a b B n) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeUnique.actual_fiber hZ w a b B n h0 h1

theorem actualFiber_kernel_certificate {m} (w a b B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualFiberSentence w a b B n)) := TheoryTransport.sentence (source_actualFiber w a b B n)

theorem native_actualFiber {m} (w a b B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualFiberSentence w a b B n)) := ZFReplay.replay (actualFiber_kernel_certificate w a b B n)

def existsInputIffSentence {m} (w a b B n : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxWeakenFreeSyntax.existsOutput w a b B n).iff (SyntaxWeakenFreeSyntax.input w a b B n)))).close

theorem source_existsInputIff {m} (w a b B n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsInputIffSentence w a b B n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeUnique.exists_iff_input hZ w a b B n h0

theorem existsInputIff_kernel_certificate {m} (w a b B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsInputIffSentence w a b B n)) := TheoryTransport.sentence (source_existsInputIff w a b B n)

theorem native_existsInputIff {m} (w a b B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsInputIffSentence w a b B n)) := ZFReplay.replay (existsInputIff_kernel_certificate w a b B n)

def fiberInputIffSentence {m} (w a b B n : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxWeakenFreeSyntax.fiber w a b B n).iff (SyntaxWeakenFreeSyntax.input w a b B n)))).close

theorem source_fiberInputIff {m} (w a b B n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fiberInputIffSentence w a b B n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeUnique.fiber_iff_input hZ w a b B n h0

theorem fiberInputIff_kernel_certificate {m} (w a b B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fiberInputIffSentence w a b B n)) := TheoryTransport.sentence (source_fiberInputIff w a b B n)

theorem native_fiberInputIff {m} (w a b B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fiberInputIffSentence w a b B n)) := ZFReplay.replay (fiberInputIff_kernel_certificate w a b B n)

def actualStateSentence {m} (w a b n : Fin m) : Source.Sentence := ((omega w).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((SyntaxWeakenFreeSyntax.actualState w a b n)))).close

theorem source_actualState {m} (w a b n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualStateSentence w a b n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeUnique.actual_state hZ w a b n h0 h1

theorem actualState_kernel_certificate {m} (w a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualStateSentence w a b n)) := TheoryTransport.sentence (source_actualState w a b n)

theorem native_actualState {m} (w a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualStateSentence w a b n)) := ZFReplay.replay (actualState_kernel_certificate w a b n)

def negationSentence {m} (w a b B n q x X R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w a R).imp ((SyntaxFreeShiftSyntax.shiftCode w b B S).imp ((SyntaxLogicalSyntax.singleCode 4 w x n).imp ((SyntaxLogicalSyntax.singleCode 4 w X q).imp (((SyntaxWeakenFreeSyntax.weakened w a b B n q).iff (SyntaxWeakenFreeSyntax.weakened w a b B x X)))))))).close

theorem source_negation {m} (w a b B n q x X R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationSentence w a b B n q x X R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 4 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 4 w x n) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B S) (Context.add (SyntaxIdentityMapSyntax.identityCode w a R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w X q) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeLogical.negation_iff hZ w a b B n q x X R S h0 h1 h2 h3 h4

theorem negation_kernel_certificate {m} (w a b B n q x X R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationSentence w a b B n q x X R S)) := TheoryTransport.sentence (source_negation w a b B n q x X R S)

theorem native_negation {m} (w a b B n q x X R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationSentence w a b B n q x X R S)) := ZFReplay.replay (negation_kernel_certificate w a b B n q x X R S)

def binarySentence {m} (kind : Fin 4) (w a b B n q x y X Y R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w a R).imp ((SyntaxFreeShiftSyntax.shiftCode w b B S).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp ((SyntaxLogicalSyntax.binaryCode kind w X Y q).imp (((SyntaxWeakenFreeSyntax.weakened w a b B n q).iff ((SyntaxWeakenFreeSyntax.weakened w a b B x X).conj (SyntaxWeakenFreeSyntax.weakened w a b B y Y))))))))).close

theorem source_binary {m} (kind : Fin 4) (w a b B n q x y X Y R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binarySentence kind w a b B n q x y X Y R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binaryCode kind w X Y q) (Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B S) (Context.add (SyntaxIdentityMapSyntax.identityCode w a R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w X Y q) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeLogical.binary_iff hZ kind w a b B n q x y X Y R S h0 h1 h2 h3 h4

theorem binary_kernel_certificate {m} (kind : Fin 4) (w a b B n q x y X Y R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binarySentence kind w a b B n q x y X Y R S)) := TheoryTransport.sentence (source_binary kind w a b B n q x y X Y R S)

theorem native_binary {m} (kind : Fin 4) (w a b B n q x y X Y R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binarySentence kind w a b B n q x y X Y R S)) := ZFReplay.replay (binary_kernel_certificate kind w a b B n q x y X Y R S)

def quantifiedSentence {m} (universal : Bool) (w a b B n q x X R S u L : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w a R).imp ((SyntaxFreeShiftSyntax.shiftCode w b B S).imp ((successor u a).imp ((SyntaxIdentityMapSyntax.identityCode w u L).imp ((SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n).imp ((SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q).imp (((SyntaxWeakenFreeSyntax.weakened w a b B n q).iff (SyntaxWeakenFreeSyntax.weakened w u b B x X)))))))))).close

theorem source_quantified {m} (universal : Bool) (w a b B n q x X R S u L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (quantifiedSentence universal w a b B n q x X R S u L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q) (Context.add (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n) (Context.add (SyntaxIdentityMapSyntax.identityCode w u L) (Context.add (successor u a) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B S) (Context.add (SyntaxIdentityMapSyntax.identityCode w a R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (successor u a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w u L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeLogical.quantified_iff hZ universal w a b B n q x X R S u L h0 h1 h2 h3 h4 h5 h6

theorem quantified_kernel_certificate {m} (universal : Bool) (w a b B n q x X R S u L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (quantifiedSentence universal w a b B n q x X R S u L)) := TheoryTransport.sentence (source_quantified universal w a b B n q x X R S u L)

theorem native_quantified {m} (universal : Bool) (w a b B n q x X R S u L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (quantifiedSentence universal w a b B n q x X R S u L)) := ZFReplay.replay (quantified_kernel_certificate universal w a b B n q x X R S u L)

def forallSentence {m} (w a b B n q x X R S u L : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w a R).imp ((SyntaxFreeShiftSyntax.shiftCode w b B S).imp ((successor u a).imp ((SyntaxIdentityMapSyntax.identityCode w u L).imp ((SyntaxLogicalSyntax.singleCode 9 w x n).imp ((SyntaxLogicalSyntax.singleCode 9 w X q).imp (((SyntaxWeakenFreeSyntax.weakened w a b B n q).iff (SyntaxWeakenFreeSyntax.weakened w u b B x X)))))))))).close

theorem source_forall {m} (w a b B n q x X R S u L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallSentence w a b B n q x X R S u L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 9 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 9 w x n) (Context.add (SyntaxIdentityMapSyntax.identityCode w u L) (Context.add (successor u a) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B S) (Context.add (SyntaxIdentityMapSyntax.identityCode w a R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (successor u a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w u L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxLogicalSyntax.singleCode 9 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxLogicalSyntax.singleCode 9 w X q) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeLogical.forall_iff hZ w a b B n q x X R S u L h0 h1 h2 h3 h4 h5 h6

theorem forall_kernel_certificate {m} (w a b B n q x X R S u L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallSentence w a b B n q x X R S u L)) := TheoryTransport.sentence (source_forall w a b B n q x X R S u L)

theorem native_forall {m} (w a b B n q x X R S u L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallSentence w a b B n q x X R S u L)) := ZFReplay.replay (forall_kernel_certificate w a b B n q x X R S u L)

def existsSentence {m} (w a b B n q x X R S u L : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w a R).imp ((SyntaxFreeShiftSyntax.shiftCode w b B S).imp ((successor u a).imp ((SyntaxIdentityMapSyntax.identityCode w u L).imp ((SyntaxLogicalSyntax.singleCode 10 w x n).imp ((SyntaxLogicalSyntax.singleCode 10 w X q).imp (((SyntaxWeakenFreeSyntax.weakened w a b B n q).iff (SyntaxWeakenFreeSyntax.weakened w u b B x X)))))))))).close

theorem source_exists {m} (w a b B n q x X R S u L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsSentence w a b B n q x X R S u L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 10 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 10 w x n) (Context.add (SyntaxIdentityMapSyntax.identityCode w u L) (Context.add (successor u a) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B S) (Context.add (SyntaxIdentityMapSyntax.identityCode w a R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (successor u a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w u L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxLogicalSyntax.singleCode 10 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxLogicalSyntax.singleCode 10 w X q) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeLogical.exists_iff hZ w a b B n q x X R S u L h0 h1 h2 h3 h4 h5 h6

theorem exists_kernel_certificate {m} (w a b B n q x X R S u L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsSentence w a b B n q x X R S u L)) := TheoryTransport.sentence (source_exists w a b B n q x X R S u L)

theorem native_exists {m} (w a b B n q x X R S u L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsSentence w a b B n q x X R S u L)) := ZFReplay.replay (exists_kernel_certificate w a b B n q x X R S u L)

def nullarySentence {m} (truth : Bool) (w a b B n q R S r s : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w a R).imp ((SyntaxFreeShiftSyntax.shiftCode w b B S).imp ((SyntaxMapCodeSyntax.encoded w r a a R).imp ((SyntaxMapCodeSyntax.encoded w s b B S).imp ((SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n).imp (((SyntaxWeakenFreeSyntax.weakened w a b B n q).iff (Formula.equal n q))))))))).close

theorem source_nullary {m} (truth : Bool) (w a b B n q R S r s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nullarySentence truth w a b B n q R S r s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) (Context.add (SyntaxMapCodeSyntax.encoded w s b B S) (Context.add (SyntaxMapCodeSyntax.encoded w r a a R) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B S) (Context.add (SyntaxIdentityMapSyntax.identityCode w a R) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a a R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b B S) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeAtoms.nullary_iff hZ truth w a b B n q R S r s h0 h1 h2 h3 h4 h5

theorem nullary_kernel_certificate {m} (truth : Bool) (w a b B n q R S r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nullarySentence truth w a b B n q R S r s)) := TheoryTransport.sentence (source_nullary truth w a b B n q R S r s)

theorem native_nullary {m} (truth : Bool) (w a b B n q R S r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nullarySentence truth w a b B n q R S r s)) := ZFReplay.replay (nullary_kernel_certificate truth w a b B n q R S r s)

def equalitySentence {m} (w a b B n q R S r s x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w a R).imp ((SyntaxFreeShiftSyntax.shiftCode w b B S).imp ((SyntaxMapCodeSyntax.encoded w r a a R).imp ((SyntaxMapCodeSyntax.encoded w s b B S).imp ((SyntaxAtomSyntax.equalCode w x y n).imp ((SyntaxAtomSyntax.equalCode w X Y q).imp (((SyntaxWeakenFreeSyntax.weakened w a b B n q).iff (SyntaxRenameKnownFieldsSyntax.equalOperands w r s a b a B x y X Y)))))))))).close

theorem source_equality {m} (w a b B n q R S r s x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalitySentence w a b B n q R S r s x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.equalCode w X Y q) (Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (SyntaxMapCodeSyntax.encoded w s b B S) (Context.add (SyntaxMapCodeSyntax.encoded w r a a R) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B S) (Context.add (SyntaxIdentityMapSyntax.identityCode w a R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a a R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b B S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxAtomSyntax.equalCode w X Y q) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeAtoms.equality_iff hZ w a b B n q R S r s x y X Y h0 h1 h2 h3 h4 h5 h6

theorem equality_kernel_certificate {m} (w a b B n q R S r s x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalitySentence w a b B n q R S r s x y X Y)) := TheoryTransport.sentence (source_equality w a b B n q R S r s x y X Y)

theorem native_equality {m} (w a b B n q R S r s x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalitySentence w a b B n q R S r s x y X Y)) := ZFReplay.replay (equality_kernel_certificate w a b B n q R S r s x y X Y)

def membershipSentence {m} (w a b B n q R S r s z Z x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w a R).imp ((SyntaxFreeShiftSyntax.shiftCode w b B S).imp ((SyntaxMapCodeSyntax.encoded w r a a R).imp ((SyntaxMapCodeSyntax.encoded w s b B S).imp ((SyntaxAtomSyntax.memberCode w z x y n).imp ((SyntaxAtomSyntax.memberCode w Z X Y q).imp (((SyntaxWeakenFreeSyntax.weakened w a b B n q).iff (SyntaxRenameKnownFieldsSyntax.memberOperands w r s a b a B z Z x y X Y)))))))))).close

theorem source_membership {m} (w a b B n q R S r s z Z x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (membershipSentence w a b B n q R S r s z Z x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.memberCode w Z X Y q) (Context.add (SyntaxAtomSyntax.memberCode w z x y n) (Context.add (SyntaxMapCodeSyntax.encoded w s b B S) (Context.add (SyntaxMapCodeSyntax.encoded w r a a R) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B S) (Context.add (SyntaxIdentityMapSyntax.identityCode w a R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a a R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b B S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxAtomSyntax.memberCode w z x y n) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxAtomSyntax.memberCode w Z X Y q) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeAtoms.membership_iff hZ w a b B n q R S r s z Z x y X Y h0 h1 h2 h3 h4 h5 h6

theorem membership_kernel_certificate {m} (w a b B n q R S r s z Z x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (membershipSentence w a b B n q R S r s z Z x y X Y)) := TheoryTransport.sentence (source_membership w a b B n q R S r s z Z x y X Y)

theorem native_membership {m} (w a b B n q R S r s z Z x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (membershipSentence w a b B n q R S r s z Z x y X Y)) := ZFReplay.replay (membership_kernel_certificate w a b B n q R S r s z Z x y X Y)

def boundTermSentence {m} (w a b B R S r s n q i j : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w a R).imp ((SyntaxMapCodeSyntax.encoded w r a a R).imp ((SyntaxMapCodeSyntax.encoded w s b B S).imp ((SyntaxVariableSyntax.code true w i n).imp ((SyntaxVariableSyntax.code true w j q).imp (((SyntaxRenameTermSyntax.renamed w r s a b a B n q).iff ((Formula.mem i a).conj (Formula.equal i j)))))))))).close

theorem source_boundTerm {m} (w a b B R S r s n q i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (boundTermSentence w a b B R S r s n q i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code true w j q) (Context.add (SyntaxVariableSyntax.code true w i n) (Context.add (SyntaxMapCodeSyntax.encoded w s b B S) (Context.add (SyntaxMapCodeSyntax.encoded w r a a R) (Context.add (SyntaxIdentityMapSyntax.identityCode w a R) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a a R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b B S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxVariableSyntax.code true w i n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxVariableSyntax.code true w j q) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeTerm.bound_iff hZ w a b B R S r s n q i j h0 h1 h2 h3 h4 h5

theorem boundTerm_kernel_certificate {m} (w a b B R S r s n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (boundTermSentence w a b B R S r s n q i j)) := TheoryTransport.sentence (source_boundTerm w a b B R S r s n q i j)

theorem native_boundTerm {m} (w a b B R S r s n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (boundTermSentence w a b B R S r s n q i j)) := ZFReplay.replay (boundTerm_kernel_certificate w a b B R S r s n q i j)

def freeTermSentence {m} (w a b B R S r s n q i j : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeShiftSyntax.shiftCode w b B S).imp ((SyntaxMapCodeSyntax.encoded w r a a R).imp ((SyntaxMapCodeSyntax.encoded w s b B S).imp ((SyntaxVariableSyntax.code false w i n).imp ((SyntaxVariableSyntax.code false w j q).imp (((SyntaxRenameTermSyntax.renamed w r s a b a B n q).iff ((Formula.mem i b).conj (successor j i)))))))))).close

theorem source_freeTerm {m} (w a b B R S r s n q i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeTermSentence w a b B R S r s n q i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code false w j q) (Context.add (SyntaxVariableSyntax.code false w i n) (Context.add (SyntaxMapCodeSyntax.encoded w s b B S) (Context.add (SyntaxMapCodeSyntax.encoded w r a a R) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a a R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b B S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxVariableSyntax.code false w i n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxVariableSyntax.code false w j q) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeTerm.free_iff hZ w a b B R S r s n q i j h0 h1 h2 h3 h4 h5

theorem freeTerm_kernel_certificate {m} (w a b B R S r s n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeTermSentence w a b B R S r s n q i j)) := TheoryTransport.sentence (source_freeTerm w a b B R S r s n q i j)

theorem native_freeTerm {m} (w a b B R S r s n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeTermSentence w a b B R S r s n q i j)) := ZFReplay.replay (freeTerm_kernel_certificate w a b B R S r s n q i j)

def freshFreeAbsentSentence {m} (w a b B R S r s n q i j : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeShiftSyntax.shiftCode w b B S).imp ((SyntaxMapCodeSyntax.encoded w r a a R).imp ((SyntaxMapCodeSyntax.encoded w s b B S).imp ((SyntaxVariableSyntax.code false w i n).imp ((SyntaxVariableSyntax.code false w j q).imp ((empty j).imp (((SyntaxRenameTermSyntax.renamed w r s a b a B n q).neg))))))))).close

theorem source_freshFreeAbsent {m} (w a b B R S r s n q i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freshFreeAbsentSentence w a b B R S r s n q i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty j) (Context.add (SyntaxVariableSyntax.code false w j q) (Context.add (SyntaxVariableSyntax.code false w i n) (Context.add (SyntaxMapCodeSyntax.encoded w s b B S) (Context.add (SyntaxMapCodeSyntax.encoded w r a a R) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a a R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b B S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxVariableSyntax.code false w i n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxVariableSyntax.code false w j q) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (empty j) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeTerm.fresh_free_absent hZ w a b B R S r s n q i j h0 h1 h2 h3 h4 h5 h6

theorem freshFreeAbsent_kernel_certificate {m} (w a b B R S r s n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freshFreeAbsentSentence w a b B R S r s n q i j)) := TheoryTransport.sentence (source_freshFreeAbsent w a b B R S r s n q i j)

theorem native_freshFreeAbsent {m} (w a b B R S r s n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freshFreeAbsentSentence w a b B R S r s n q i j)) := ZFReplay.replay (freshFreeAbsent_kernel_certificate w a b B R S r s n q i j)

def emptyFreeAbsentSentence {m} (w a b B R S r s n q i j : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeShiftSyntax.shiftCode w b B S).imp ((SyntaxMapCodeSyntax.encoded w r a a R).imp ((SyntaxMapCodeSyntax.encoded w s b B S).imp ((SyntaxVariableSyntax.code false w i n).imp ((SyntaxVariableSyntax.code false w j q).imp ((empty b).imp (((SyntaxRenameTermSyntax.renamed w r s a b a B n q).neg))))))))).close

theorem source_emptyFreeAbsent {m} (w a b B R S r s n q i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (emptyFreeAbsentSentence w a b B R S r s n q i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty b) (Context.add (SyntaxVariableSyntax.code false w j q) (Context.add (SyntaxVariableSyntax.code false w i n) (Context.add (SyntaxMapCodeSyntax.encoded w s b B S) (Context.add (SyntaxMapCodeSyntax.encoded w r a a R) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a a R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b B S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxVariableSyntax.code false w i n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxVariableSyntax.code false w j q) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (empty b) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeTerm.empty_free_absent hZ w a b B R S r s n q i j h0 h1 h2 h3 h4 h5 h6

theorem emptyFreeAbsent_kernel_certificate {m} (w a b B R S r s n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (emptyFreeAbsentSentence w a b B R S r s n q i j)) := TheoryTransport.sentence (source_emptyFreeAbsent w a b B R S r s n q i j)

theorem native_emptyFreeAbsent {m} (w a b B R S r s n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (emptyFreeAbsentSentence w a b B R S r s n q i j)) := ZFReplay.replay (emptyFreeAbsent_kernel_certificate w a b B R S r s n q i j)

def actualCodesSentence {m} (w a b B : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp ((Formula.mem b w).imp ((successor B b).imp ((SyntaxWeakenFreeLogicalInternal.actualCodes w a b B)))))).close

theorem source_actualCodes {m} (w a b B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualCodesSentence w a b B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor B b) (Context.add (Formula.mem b w) (Context.add (Formula.mem a w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem a w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor B b) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeLogicalInternal.actual_codes_exists hZ w a b B h0 h1 h2 h3

theorem actualCodes_kernel_certificate {m} (w a b B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualCodesSentence w a b B)) := TheoryTransport.sentence (source_actualCodes w a b B)

theorem native_actualCodes {m} (w a b B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualCodesSentence w a b B)) := ZFReplay.replay (actualCodes_kernel_certificate w a b B)

def internalNegationSentence {m} (w a b B n q x X : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp ((Formula.mem b w).imp ((successor B b).imp ((SyntaxLogicalSyntax.singleCode 4 w x n).imp ((SyntaxLogicalSyntax.singleCode 4 w X q).imp (((SyntaxWeakenFreeSyntax.weakened w a b B n q).iff (SyntaxWeakenFreeSyntax.weakened w a b B x X))))))))).close

theorem source_internalNegation {m} (w a b B n q x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (internalNegationSentence w a b B n q x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 4 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 4 w x n) (Context.add (successor B b) (Context.add (Formula.mem b w) (Context.add (Formula.mem a w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (Formula.mem a w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (successor B b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w X q) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeLogicalInternal.negation_iff hZ w a b B n q x X h0 h1 h2 h3 h4 h5

theorem internalNegation_kernel_certificate {m} (w a b B n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (internalNegationSentence w a b B n q x X)) := TheoryTransport.sentence (source_internalNegation w a b B n q x X)

theorem native_internalNegation {m} (w a b B n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (internalNegationSentence w a b B n q x X)) := ZFReplay.replay (internalNegation_kernel_certificate w a b B n q x X)

def internalBinarySentence {m} (kind : Fin 4) (w a b B n q x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp ((Formula.mem b w).imp ((successor B b).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp ((SyntaxLogicalSyntax.binaryCode kind w X Y q).imp (((SyntaxWeakenFreeSyntax.weakened w a b B n q).iff ((SyntaxWeakenFreeSyntax.weakened w a b B x X).conj (SyntaxWeakenFreeSyntax.weakened w a b B y Y)))))))))).close

theorem source_internalBinary {m} (kind : Fin 4) (w a b B n q x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (internalBinarySentence kind w a b B n q x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binaryCode kind w X Y q) (Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (successor B b) (Context.add (Formula.mem b w) (Context.add (Formula.mem a w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (Formula.mem a w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (successor B b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w X Y q) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeLogicalInternal.binary_iff hZ kind w a b B n q x y X Y h0 h1 h2 h3 h4 h5

theorem internalBinary_kernel_certificate {m} (kind : Fin 4) (w a b B n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (internalBinarySentence kind w a b B n q x y X Y)) := TheoryTransport.sentence (source_internalBinary kind w a b B n q x y X Y)

theorem native_internalBinary {m} (kind : Fin 4) (w a b B n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (internalBinarySentence kind w a b B n q x y X Y)) := ZFReplay.replay (internalBinary_kernel_certificate kind w a b B n q x y X Y)

def internalQuantifiedSentence {m} (universal : Bool) (w a b B n q x X u : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp ((Formula.mem b w).imp ((successor B b).imp ((successor u a).imp ((SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n).imp ((SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q).imp (((SyntaxWeakenFreeSyntax.weakened w a b B n q).iff (SyntaxWeakenFreeSyntax.weakened w u b B x X)))))))))).close

theorem source_internalQuantified {m} (universal : Bool) (w a b B n q x X u : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (internalQuantifiedSentence universal w a b B n q x X u) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q) (Context.add (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n) (Context.add (successor u a) (Context.add (successor B b) (Context.add (Formula.mem b w) (Context.add (Formula.mem a w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (Formula.mem a w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (successor B b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (successor u a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q) := .hyp (Or.inl rfl)
  exact SyntaxWeakenFreeLogicalInternal.quantified_iff hZ universal w a b B n q x X u h0 h1 h2 h3 h4 h5 h6

theorem internalQuantified_kernel_certificate {m} (universal : Bool) (w a b B n q x X u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (internalQuantifiedSentence universal w a b B n q x X u)) := TheoryTransport.sentence (source_internalQuantified universal w a b B n q x X u)

theorem native_internalQuantified {m} (universal : Bool) (w a b B n q x X u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (internalQuantifiedSentence universal w a b B n q x X u)) := ZFReplay.replay (internalQuantified_kernel_certificate universal w a b B n q x X u)

end PPAC.Migration.Internal.ObjectSyntaxWeakenFree
