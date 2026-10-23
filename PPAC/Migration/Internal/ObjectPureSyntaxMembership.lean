import PPAC.Migration.Internal.PureSyntaxAtomicComplete

/-! 成员关系实际规则及四种Source原子查询构造；全公式查询双条件尚未完成。 -/
namespace PPAC.Migration.Internal.ObjectPureSyntaxMembership
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def membershipInputDataIffSentence {m} (w b f args n : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w (SyntaxAtomSyntax.three b f args)).imp (((HornExprSyntax.graph PureSyntaxMembershipInput.input w (SyntaxAtomSyntax.three b f args) n).iff (PureSyntaxMembershipInput.data w args n))))).close

theorem source_membershipInputDataIff {m} (w b f args n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (membershipInputDataIffSentence w b f args n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 3 w (SyntaxAtomSyntax.three b f args)) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w (SyntaxAtomSyntax.three b f args)) := .hyp (Or.inl rfl)
  exact PureSyntaxMembershipInput.data_iff hZ w n (SyntaxAtomSyntax.three b f args) h0 h1

theorem membershipInputDataIff_kernel_certificate {m} (w b f args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (membershipInputDataIffSentence w b f args n)) := TheoryTransport.sentence (source_membershipInputDataIff w b f args n)

theorem native_membershipInputDataIff {m} (w b f args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (membershipInputDataIffSentence w b f args n)) := ZFReplay.replay (membershipInputDataIff_kernel_certificate w b f args n)

def membershipAtForestIffSentence {m} (w s x y args n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.zeroScalar w s).imp ((SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) args).imp (((PureSyntaxMembershipInput.data w args n).iff (SyntaxAtomSyntax.memberCode w s x y n)))))).close

theorem source_membershipAtForestIff {m} (w s x y args n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (membershipAtForestIffSentence w s x y args n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) args) (Context.add (SyntaxAtomSyntax.zeroScalar w s) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxAtomSyntax.zeroScalar w s) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) args) := .hyp (Or.inl rfl)
  exact PureSyntaxMembershipType.at_forest_iff hZ w s x y args n h0 h1 h2

theorem membershipAtForestIff_kernel_certificate {m} (w s x y args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (membershipAtForestIffSentence w s x y args n)) := TheoryTransport.sentence (source_membershipAtForestIff w s x y args n)

theorem native_membershipAtForestIff {m} (w s x y args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (membershipAtForestIffSentence w s x y args n)) := ZFReplay.replay (membershipAtForestIff_kernel_certificate w s x y args n)

def membershipTypedListSoundSentence {m} (w b f args n len : Fin m) : Source.Sentence := ((omega w).imp ((PureSyntaxMembershipInput.data w args n).imp ((SyntaxNumeralSyntax.numeral 2 len).imp ((SyntaxMixedImageCodeSyntax.termList w len b f args).imp ((FormulaCodeSyntax.formulaCode w n b f)))))).close

theorem source_membershipTypedListSound {m} (w b f args n len : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (membershipTypedListSoundSentence w b f args n len) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w len b f args) (Context.add (SyntaxNumeralSyntax.numeral 2 len) (Context.add (PureSyntaxMembershipInput.data w args n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PureSyntaxMembershipInput.data w args n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 2 len) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w len b f args) := .hyp (Or.inl rfl)
  exact PureSyntaxMembershipType.from_typed_list hZ w b f args n len h0 h1 h2 h3

theorem membershipTypedListSound_kernel_certificate {m} (w b f args n len : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (membershipTypedListSoundSentence w b f args n len)) := TheoryTransport.sentence (source_membershipTypedListSound w b f args n len)

theorem native_membershipTypedListSound {m} (w b f args n len : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (membershipTypedListSoundSentence w b f args n len)) := ZFReplay.replay (membershipTypedListSound_kernel_certificate w b f args n len)

def membershipActualPremiseAtTwoSentence {m} (w b f args R len : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w (SyntaxAtomSyntax.three b f args)).imp ((SyntaxNumeralSyntax.numeral 2 len).imp ((RestrictionSyntax.subset R w).imp ((PureSyntaxTrace.closed w R).imp ((HornRuleSyntax.premise PureSyntaxMembershipPremise.head w R (SyntaxAtomSyntax.three b f args)).imp ((SyntaxMixedImageCodeSyntax.termList w len b f args)))))))).close

theorem source_membershipActualPremiseAtTwo {m} (w b f args R len : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (membershipActualPremiseAtTwoSentence w b f args R len) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornRuleSyntax.premise PureSyntaxMembershipPremise.head w R (SyntaxAtomSyntax.three b f args)) (Context.add (PureSyntaxTrace.closed w R) (Context.add (RestrictionSyntax.subset R w) (Context.add (SyntaxNumeralSyntax.numeral 2 len) (Context.add (HornExprSyntax.environmentNat 3 w (SyntaxAtomSyntax.three b f args)) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w (SyntaxAtomSyntax.three b f args)) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 2 len) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (RestrictionSyntax.subset R w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (PureSyntaxTrace.closed w R) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (HornRuleSyntax.premise PureSyntaxMembershipPremise.head w R (SyntaxAtomSyntax.three b f args)) := .hyp (Or.inl rfl)
  exact PureSyntaxMembershipPremise.at_numeral hZ w R len (SyntaxAtomSyntax.three b f args) h0 h1 h2 h3 h4 h5

theorem membershipActualPremiseAtTwo_kernel_certificate {m} (w b f args R len : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (membershipActualPremiseAtTwoSentence w b f args R len)) := TheoryTransport.sentence (source_membershipActualPremiseAtTwo w b f args R len)

theorem native_membershipActualPremiseAtTwo {m} (w b f args R len : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (membershipActualPremiseAtTwoSentence w b f args R len)) := ZFReplay.replay (membershipActualPremiseAtTwo_kernel_certificate w b f args R len)

def membershipApplicationSoundSentence {m} (w b f n r R : Fin m) : Source.Sentence := ((omega w).imp ((RestrictionSyntax.subset R w).imp ((PureSyntaxTrace.closed w R).imp ((PureSyntaxTrace.formulaRow w b f n r).imp ((HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectFormulaSyntax.relationRule .membership) w r R).imp ((FormulaCodeSyntax.formulaCode w n b f))))))).close

theorem source_membershipApplicationSound {m} (w b f n r R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (membershipApplicationSoundSentence w b f n r R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectFormulaSyntax.relationRule .membership) w r R) (Context.add (PureSyntaxTrace.formulaRow w b f n r) (Context.add (PureSyntaxTrace.closed w R) (Context.add (RestrictionSyntax.subset R w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (RestrictionSyntax.subset R w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (PureSyntaxTrace.closed w R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (PureSyntaxTrace.formulaRow w b f n r) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectFormulaSyntax.relationRule .membership) w r R) := .hyp (Or.inl rfl)
  exact PureSyntaxMembershipRule.application_sound hZ w b f n r R h0 h1 h2 h3 h4

theorem membershipApplicationSound_kernel_certificate {m} (w b f n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (membershipApplicationSoundSentence w b f n r R)) := TheoryTransport.sentence (source_membershipApplicationSound w b f n r R)

theorem native_membershipApplicationSound {m} (w b f n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (membershipApplicationSoundSentence w b f n r R)) := ZFReplay.replay (membershipApplicationSound_kernel_certificate w b f n r R)

def membershipQueryFromListSentence {m} (w b f args n len : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 2 len).imp ((SyntaxMixedImageCodeSyntax.termList w len b f args).imp ((PureSyntaxMembershipInput.data w args n).imp ((PureSyntaxTrace.formula w b f n)))))).close

theorem source_membershipQueryFromList {m} (w b f args n len : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (membershipQueryFromListSentence w b f args n len) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureSyntaxMembershipInput.data w args n) (Context.add (SyntaxMixedImageCodeSyntax.termList w len b f args) (Context.add (SyntaxNumeralSyntax.numeral 2 len) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 2 len) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w len b f args) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PureSyntaxMembershipInput.data w args n) := .hyp (Or.inl rfl)
  exact PureSyntaxMembershipQuery.checked_from_list hZ w b f args n len h0 h1 h2 h3

theorem membershipQueryFromList_kernel_certificate {m} (w b f args n len : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (membershipQueryFromListSentence w b f args n len)) := TheoryTransport.sentence (source_membershipQueryFromList w b f args n len)

theorem native_membershipQueryFromList {m} (w b f args n len : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (membershipQueryFromListSentence w b f args n len)) := ZFReplay.replay (membershipQueryFromList_kernel_certificate w b f args n len)

def membershipQueryAtSentence {m} (w b f s x y n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.zeroScalar w s).imp ((SyntaxTermSyntax.term w b f x).imp ((SyntaxTermSyntax.term w b f y).imp ((SyntaxAtomSyntax.memberCode w s x y n).imp ((PureSyntaxTrace.formula w b f n))))))).close

theorem source_membershipQueryAt {m} (w b f s x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (membershipQueryAtSentence w b f s x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.memberCode w s x y n) (Context.add (SyntaxTermSyntax.term w b f y) (Context.add (SyntaxTermSyntax.term w b f x) (Context.add (SyntaxAtomSyntax.zeroScalar w s) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxAtomSyntax.zeroScalar w s) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxTermSyntax.term w b f x) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxTermSyntax.term w b f y) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxAtomSyntax.memberCode w s x y n) := .hyp (Or.inl rfl)
  exact PureSyntaxMembershipComplete.checked_at hZ w b f s x y n h0 h1 h2 h3 h4

theorem membershipQueryAt_kernel_certificate {m} (w b f s x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (membershipQueryAtSentence w b f s x y n)) := TheoryTransport.sentence (source_membershipQueryAt w b f s x y n)

theorem native_membershipQueryAt {m} (w b f s x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (membershipQueryAtSentence w b f s x y n)) := ZFReplay.replay (membershipQueryAt_kernel_certificate w b f s x y n)

def typedMembershipQuerySentence {m} (w b f s x y n : Fin m) : Source.Sentence := ((omega w).imp ((FormulaCodeSyntax.formulaCode w n b f).imp ((SyntaxAtomSyntax.zeroScalar w s).imp ((SyntaxAtomSyntax.memberCode w s x y n).imp ((PureSyntaxTrace.formula w b f n)))))).close

theorem source_typedMembershipQuery {m} (w b f s x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (typedMembershipQuerySentence w b f s x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.memberCode w s x y n) (Context.add (SyntaxAtomSyntax.zeroScalar w s) (Context.add (FormulaCodeSyntax.formulaCode w n b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (FormulaCodeSyntax.formulaCode w n b f) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxAtomSyntax.zeroScalar w s) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxAtomSyntax.memberCode w s x y n) := .hyp (Or.inl rfl)
  exact PureSyntaxMembershipComplete.typed_membership_checked hZ w b f s x y n h0 h1 h2 h3

theorem typedMembershipQuery_kernel_certificate {m} (w b f s x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (typedMembershipQuerySentence w b f s x y n)) := TheoryTransport.sentence (source_typedMembershipQuery w b f s x y n)

theorem native_typedMembershipQuery {m} (w b f s x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (typedMembershipQuerySentence w b f s x y n)) := ZFReplay.replay (typedMembershipQuery_kernel_certificate w b f s x y n)

def fullMembershipQuerySentence {m} (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.membership w b f n).imp ((PureSyntaxTrace.formula w b f n)))).close

theorem source_fullMembershipQuery {m} (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fullMembershipQuerySentence w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.membership w b f n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxAtomSyntax.membership w b f n) := .hyp (Or.inl rfl)
  exact PureSyntaxMembershipComplete.checked_membership hZ w b f n h0 h1

theorem fullMembershipQuery_kernel_certificate {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fullMembershipQuerySentence w b f n)) := TheoryTransport.sentence (source_fullMembershipQuery w b f n)

theorem native_fullMembershipQuery {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fullMembershipQuerySentence w b f n)) := ZFReplay.replay (fullMembershipQuery_kernel_certificate w b f n)

def allFourAtomicQueriesSentence {m} (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.atomic w b f n).imp ((PureSyntaxTrace.formula w b f n)))).close

theorem source_allFourAtomicQueries {m} (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allFourAtomicQueriesSentence w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.atomic w b f n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxAtomSyntax.atomic w b f n) := .hyp (Or.inl rfl)
  exact PureSyntaxAtomicComplete.checked_atomic hZ w b f n h0 h1

theorem allFourAtomicQueries_kernel_certificate {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allFourAtomicQueriesSentence w b f n)) := TheoryTransport.sentence (source_allFourAtomicQueries w b f n)

theorem native_allFourAtomicQueries {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allFourAtomicQueriesSentence w b f n)) := ZFReplay.replay (allFourAtomicQueries_kernel_certificate w b f n)

end PPAC.Migration.Internal.ObjectPureSyntaxMembership
