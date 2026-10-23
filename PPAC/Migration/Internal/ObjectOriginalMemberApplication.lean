import PPAC.Migration.Internal.OriginalFormulaMemberCase

/-! 原App与纯成员原子之内部编号0和两参数森林精确对应的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectOriginalMemberApplication
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def originalAppHeadForestConstructorIffSentence {m} (k : Nat) (xs : Fin k → Fin m) (w symbol s args n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.scalar w symbol s).imp ((SyntaxForestSyntax.forest k w xs args).imp (((OriginalFormulaApplicationSyntax.application w symbol args n).iff (SyntaxNodeSyntax.constructor (k+1) 2 w (OriginalFormulaApplicationNodes.prepend k s xs) n)))))).close

theorem source_originalAppHeadForestConstructorIff {m} (k : Nat) (xs : Fin k → Fin m) (w symbol s args n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalAppHeadForestConstructorIffSentence k xs w symbol s args n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxForestSyntax.forest k w xs args) (Context.add (SyntaxNodeSyntax.scalar w symbol s) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNodeSyntax.scalar w symbol s) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxForestSyntax.forest k w xs args) := .hyp (Or.inl rfl)
  exact OriginalFormulaApplicationNodes.application_iff_constructor hZ k w symbol s args n xs h0 h1 h2

theorem originalAppHeadForestConstructorIff_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (w symbol s args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalAppHeadForestConstructorIffSentence k xs w symbol s args n)) := TheoryTransport.sentence (source_originalAppHeadForestConstructorIff k xs w symbol s args n)

theorem native_originalAppHeadForestConstructorIff {m} (k : Nat) (xs : Fin k → Fin m) (w symbol s args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalAppHeadForestConstructorIffSentence k xs w symbol s args n)) := ZFReplay.replay (originalAppHeadForestConstructorIff_kernel_certificate k xs w symbol s args n)

def originalAppHeadForestRecoveredSentence {m} (k : Nat) (xs : Fin k → Fin m) (w symbol s args n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem args w).imp ((SyntaxNodeSyntax.constructor (k+1) 2 w (OriginalFormulaApplicationNodes.prepend k s xs) n).imp ((OriginalFormulaApplicationSyntax.application w symbol args n).imp (((SyntaxNodeSyntax.scalar w symbol s).conj (SyntaxForestSyntax.forest k w xs args))))))).close

theorem source_originalAppHeadForestRecovered {m} (k : Nat) (xs : Fin k → Fin m) (w symbol s args n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalAppHeadForestRecoveredSentence k xs w symbol s args n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalFormulaApplicationSyntax.application w symbol args n) (Context.add (SyntaxNodeSyntax.constructor (k+1) 2 w (OriginalFormulaApplicationNodes.prepend k s xs) n) (Context.add (Formula.mem args w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem args w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNodeSyntax.constructor (k+1) 2 w (OriginalFormulaApplicationNodes.prepend k s xs) n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (OriginalFormulaApplicationSyntax.application w symbol args n) := .hyp (Or.inl rfl)
  exact OriginalFormulaApplicationRecover.recover_application hZ k w symbol s args n xs h0 h1 h2 h3

theorem originalAppHeadForestRecovered_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (w symbol s args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalAppHeadForestRecoveredSentence k xs w symbol s args n)) := TheoryTransport.sentence (source_originalAppHeadForestRecovered k xs w symbol s args n)

theorem native_originalAppHeadForestRecovered {m} (k : Nat) (xs : Fin k → Fin m) (w symbol s args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalAppHeadForestRecoveredSentence k xs w symbol s args n)) := ZFReplay.replay (originalAppHeadForestRecovered_kernel_certificate k xs w symbol s args n)

def originalMemberScalarAtZeroIndexSentence {m} (w z s : Fin m) : Source.Sentence := ((SyntaxNumeralSyntax.numeral 0 z).imp ((SyntaxAtomSyntax.zeroScalar w s).imp ((SyntaxNodeSyntax.scalar w z s)))).close

theorem source_originalMemberScalarAtZeroIndex {m} (w z s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalMemberScalarAtZeroIndexSentence w z s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.zeroScalar w s) (Context.add (SyntaxNumeralSyntax.numeral 0 z) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxNumeralSyntax.numeral 0 z) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxAtomSyntax.zeroScalar w s) := .hyp (Or.inl rfl)
  exact OriginalFormulaMemberApplication.scalar_at_zero hZ w z s h0 h1

theorem originalMemberScalarAtZeroIndex_kernel_certificate {m} (w z s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalMemberScalarAtZeroIndexSentence w z s)) := TheoryTransport.sentence (source_originalMemberScalarAtZeroIndex w z s)

theorem native_originalMemberScalarAtZeroIndex {m} (w z s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalMemberScalarAtZeroIndexSentence w z s)) := ZFReplay.replay (originalMemberScalarAtZeroIndex_kernel_certificate w z s)

def originalMemberAtTwoArgumentForestIffSentence {m} (w z s x y args n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 z).imp ((SyntaxAtomSyntax.zeroScalar w s).imp ((SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) args).imp (((OriginalFormulaApplicationSyntax.application w z args n).iff (SyntaxAtomSyntax.memberCode w s x y n))))))).close

theorem source_originalMemberAtTwoArgumentForestIff {m} (w z s x y args n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalMemberAtTwoArgumentForestIffSentence w z s x y args n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) args) (Context.add (SyntaxAtomSyntax.zeroScalar w s) (Context.add (SyntaxNumeralSyntax.numeral 0 z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxAtomSyntax.zeroScalar w s) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) args) := .hyp (Or.inl rfl)
  exact OriginalFormulaMemberApplication.member_at_forest_iff hZ w z s x y args n h0 h1 h2 h3

theorem originalMemberAtTwoArgumentForestIff_kernel_certificate {m} (w z s x y args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalMemberAtTwoArgumentForestIffSentence w z s x y args n)) := TheoryTransport.sentence (source_originalMemberAtTwoArgumentForestIff w z s x y args n)

theorem native_originalMemberAtTwoArgumentForestIff {m} (w z s x y args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalMemberAtTwoArgumentForestIffSentence w z s x y args n)) := ZFReplay.replay (originalMemberAtTwoArgumentForestIff_kernel_certificate w z s x y args n)

def originalMemberAppZeroAndTwoArgumentsRecoveredSentence {m} (w symbol s x y args n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.zeroScalar w s).imp ((SyntaxAtomSyntax.memberCode w s x y n).imp ((Formula.mem args w).imp ((OriginalFormulaApplicationSyntax.application w symbol args n).imp (((SyntaxNumeralSyntax.numeral 0 symbol).conj (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) args)))))))).close

theorem source_originalMemberAppZeroAndTwoArgumentsRecovered {m} (w symbol s x y args n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalMemberAppZeroAndTwoArgumentsRecoveredSentence w symbol s x y args n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalFormulaApplicationSyntax.application w symbol args n) (Context.add (Formula.mem args w) (Context.add (SyntaxAtomSyntax.memberCode w s x y n) (Context.add (SyntaxAtomSyntax.zeroScalar w s) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxAtomSyntax.zeroScalar w s) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxAtomSyntax.memberCode w s x y n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem args w) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (OriginalFormulaApplicationSyntax.application w symbol args n) := .hyp (Or.inl rfl)
  exact OriginalFormulaMemberApplication.recover_at_member hZ w symbol s x y args n h0 h1 h2 h3 h4

theorem originalMemberAppZeroAndTwoArgumentsRecovered_kernel_certificate {m} (w symbol s x y args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalMemberAppZeroAndTwoArgumentsRecoveredSentence w symbol s x y args n)) := TheoryTransport.sentence (source_originalMemberAppZeroAndTwoArgumentsRecovered w symbol s x y args n)

theorem native_originalMemberAppZeroAndTwoArgumentsRecovered {m} (w symbol s x y args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalMemberAppZeroAndTwoArgumentsRecoveredSentence w symbol s x y args n)) := ZFReplay.replay (originalMemberAppZeroAndTwoArgumentsRecovered_kernel_certificate w symbol s x y args n)

def originalMemberAppAtNaturalArgumentsIffSentence {m} (w symbol s x y args n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.zeroScalar w s).imp ((SyntaxAtomSyntax.memberCode w s x y n).imp ((Formula.mem args w).imp (((OriginalFormulaApplicationSyntax.application w symbol args n).iff ((SyntaxNumeralSyntax.numeral 0 symbol).conj (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) args)))))))).close

theorem source_originalMemberAppAtNaturalArgumentsIff {m} (w symbol s x y args n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalMemberAppAtNaturalArgumentsIffSentence w symbol s x y args n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem args w) (Context.add (SyntaxAtomSyntax.memberCode w s x y n) (Context.add (SyntaxAtomSyntax.zeroScalar w s) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxAtomSyntax.zeroScalar w s) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxAtomSyntax.memberCode w s x y n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem args w) := .hyp (Or.inl rfl)
  exact OriginalFormulaMemberApplication.application_at_member_iff hZ w symbol s x y args n h0 h1 h2 h3

theorem originalMemberAppAtNaturalArgumentsIff_kernel_certificate {m} (w symbol s x y args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalMemberAppAtNaturalArgumentsIffSentence w symbol s x y args n)) := TheoryTransport.sentence (source_originalMemberAppAtNaturalArgumentsIff w symbol s x y args n)

theorem native_originalMemberAppAtNaturalArgumentsIff {m} (w symbol s x y args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalMemberAppAtNaturalArgumentsIffSentence w symbol s x y args n)) := ZFReplay.replay (originalMemberAppAtNaturalArgumentsIff_kernel_certificate w symbol s x y args n)

def originalMemberCheckedAppIffSentence {m} (w symbol s x y args n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.zeroScalar w s).imp ((SyntaxAtomSyntax.memberCode w s x y n).imp ((((Formula.mem args w).conj (OriginalFormulaApplicationSyntax.application w symbol args n)).iff ((SyntaxNumeralSyntax.numeral 0 symbol).conj (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) args))))))).close

theorem source_originalMemberCheckedAppIff {m} (w symbol s x y args n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalMemberCheckedAppIffSentence w symbol s x y args n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.memberCode w s x y n) (Context.add (SyntaxAtomSyntax.zeroScalar w s) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxAtomSyntax.zeroScalar w s) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxAtomSyntax.memberCode w s x y n) := .hyp (Or.inl rfl)
  exact OriginalFormulaMemberApplication.checked_at_member_iff hZ w symbol s x y args n h0 h1 h2

theorem originalMemberCheckedAppIff_kernel_certificate {m} (w symbol s x y args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalMemberCheckedAppIffSentence w symbol s x y args n)) := TheoryTransport.sentence (source_originalMemberCheckedAppIff w symbol s x y args n)

theorem native_originalMemberCheckedAppIff {m} (w symbol s x y args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalMemberCheckedAppIffSentence w symbol s x y args n)) := ZFReplay.replay (originalMemberCheckedAppIff_kernel_certificate w symbol s x y args n)

def originalMemberApplicationCaseIffSentence {m} (w mode depth parameter s x y n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.zeroScalar w s).imp ((SyntaxAtomSyntax.memberCode w s x y n).imp (((OriginalFormulaCaseSyntax.applicationCase w mode depth parameter n q).iff (OriginalFormulaMemberCaseSyntax.membershipCase w mode depth parameter x y q)))))).close

theorem source_originalMemberApplicationCaseIff {m} (w mode depth parameter s x y n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalMemberApplicationCaseIffSentence w mode depth parameter s x y n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.memberCode w s x y n) (Context.add (SyntaxAtomSyntax.zeroScalar w s) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxAtomSyntax.zeroScalar w s) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxAtomSyntax.memberCode w s x y n) := .hyp (Or.inl rfl)
  exact OriginalFormulaMemberCase.case_iff hZ w mode depth parameter s x y n q h0 h1 h2

theorem originalMemberApplicationCaseIff_kernel_certificate {m} (w mode depth parameter s x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalMemberApplicationCaseIffSentence w mode depth parameter s x y n q)) := TheoryTransport.sentence (source_originalMemberApplicationCaseIff w mode depth parameter s x y n q)

theorem native_originalMemberApplicationCaseIff {m} (w mode depth parameter s x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalMemberApplicationCaseIffSentence w mode depth parameter s x y n q)) := ZFReplay.replay (originalMemberApplicationCaseIff_kernel_certificate w mode depth parameter s x y n q)

end PPAC.Migration.Internal.ObjectOriginalMemberApplication
