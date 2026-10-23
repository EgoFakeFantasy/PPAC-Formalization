import PPAC.Migration.Internal.OriginalArgumentModeFiber

/-! 原参数列表的全内部成员归纳与实际唯一有类型输出之原核证书。 -/
namespace PPAC.Migration.Internal.ObjectOriginalArgumentFiber
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def originalRunInputSubstitutionSentence {m} (kind : Nat) (w mode depth parameter input output replacement : Fin m) : Source.Sentence := ((Formula.equal input replacement).imp ((OriginalTransformRowSyntax.run kind w mode depth parameter input output).imp ((OriginalTransformRowSyntax.run kind w mode depth parameter replacement output)))).close

theorem source_originalRunInputSubstitution {m} (kind : Nat) (w mode depth parameter input output replacement : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalRunInputSubstitutionSentence kind w mode depth parameter input output replacement) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.run kind w mode depth parameter input output) (Context.add (Formula.equal input replacement) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (Formula.equal input replacement) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (OriginalTransformRowSyntax.run kind w mode depth parameter input output) := .hyp (Or.inl rfl)
  exact OriginalRunValueSubstitution.run_input kind w mode depth parameter input output replacement h0 h1

theorem originalRunInputSubstitution_kernel_certificate {m} (kind : Nat) (w mode depth parameter input output replacement : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalRunInputSubstitutionSentence kind w mode depth parameter input output replacement)) := TheoryTransport.sentence (source_originalRunInputSubstitution kind w mode depth parameter input output replacement)

theorem native_originalRunInputSubstitution {m} (kind : Nat) (w mode depth parameter input output replacement : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalRunInputSubstitutionSentence kind w mode depth parameter input output replacement)) := ZFReplay.replay (originalRunInputSubstitution_kernel_certificate kind w mode depth parameter input output replacement)

def originalRunOutputSubstitutionSentence {m} (kind : Nat) (w mode depth parameter input output replacement : Fin m) : Source.Sentence := ((Formula.equal output replacement).imp ((OriginalTransformRowSyntax.run kind w mode depth parameter input output).imp ((OriginalTransformRowSyntax.run kind w mode depth parameter input replacement)))).close

theorem source_originalRunOutputSubstitution {m} (kind : Nat) (w mode depth parameter input output replacement : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalRunOutputSubstitutionSentence kind w mode depth parameter input output replacement) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.run kind w mode depth parameter input output) (Context.add (Formula.equal output replacement) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (Formula.equal output replacement) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (OriginalTransformRowSyntax.run kind w mode depth parameter input output) := .hyp (Or.inl rfl)
  exact OriginalRunValueSubstitution.run_output kind w mode depth parameter input output replacement h0 h1

theorem originalRunOutputSubstitution_kernel_certificate {m} (kind : Nat) (w mode depth parameter input output replacement : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalRunOutputSubstitutionSentence kind w mode depth parameter input output replacement)) := TheoryTransport.sentence (source_originalRunOutputSubstitution kind w mode depth parameter input output replacement)

theorem native_originalRunOutputSubstitution {m} (kind : Nat) (w mode depth parameter input output replacement : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalRunOutputSubstitutionSentence kind w mode depth parameter input output replacement)) := ZFReplay.replay (originalRunOutputSubstitution_kernel_certificate kind w mode depth parameter input output replacement)

def originalListValueTargetTypeSentence {m} (w mode depth parameter k c d n q : Fin m) : Source.Sentence := ((OriginalArgumentValueSyntax.value w mode depth parameter k c d n q).imp ((SyntaxMixedImageCodeSyntax.termList w k c d q))).close

theorem source_originalListValueTargetType {m} (w mode depth parameter k c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalListValueTargetTypeSentence w mode depth parameter k c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalArgumentValueSyntax.value w mode depth parameter k c d n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (OriginalArgumentValueSyntax.value w mode depth parameter k c d n q) := .hyp (Or.inl rfl)
  exact OriginalArgumentValueSyntax.target_type w mode depth parameter k c d n q h0

theorem originalListValueTargetType_kernel_certificate {m} (w mode depth parameter k c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalListValueTargetTypeSentence w mode depth parameter k c d n q)) := TheoryTransport.sentence (source_originalListValueTargetType w mode depth parameter k c d n q)

theorem native_originalListValueTargetType {m} (w mode depth parameter k c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalListValueTargetTypeSentence w mode depth parameter k c d n q)) := ZFReplay.replay (originalListValueTargetType_kernel_certificate w mode depth parameter k c d n q)

def originalListAllCandidateUniqueSentence {m} (w mode depth parameter k c d n q v : Fin m) : Source.Sentence := ((OriginalArgumentValueSyntax.value w mode depth parameter k c d n q).imp ((OriginalTransformRowSyntax.run 2 w mode depth parameter n v).imp ((Formula.equal v q)))).close

theorem source_originalListAllCandidateUnique {m} (w mode depth parameter k c d n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalListAllCandidateUniqueSentence w mode depth parameter k c d n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.run 2 w mode depth parameter n v) (Context.add (OriginalArgumentValueSyntax.value w mode depth parameter k c d n q) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (OriginalArgumentValueSyntax.value w mode depth parameter k c d n q) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (OriginalTransformRowSyntax.run 2 w mode depth parameter n v) := .hyp (Or.inl rfl)
  exact OriginalArgumentValueSyntax.unique w mode depth parameter k c d n q v h0 h1

theorem originalListAllCandidateUnique_kernel_certificate {m} (w mode depth parameter k c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalListAllCandidateUniqueSentence w mode depth parameter k c d n q v)) := TheoryTransport.sentence (source_originalListAllCandidateUnique w mode depth parameter k c d n q v)

theorem native_originalListAllCandidateUnique {m} (w mode depth parameter k c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalListAllCandidateUniqueSentence w mode depth parameter k c d n q v)) := ZFReplay.replay (originalListAllCandidateUnique_kernel_certificate w mode depth parameter k c d n q v)

def originalNilListActualValueSentence {m} (three : Bool) (w mode depth parameter k c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((Formula.mem depth w).imp ((Formula.mem parameter w).imp ((empty k).imp ((SyntaxTermSyntax.contexts w c d).imp ((StructuralListSyntax.nilCode w n).imp ((StructuralListSyntax.nilCode w q).imp ((OriginalArgumentValueSyntax.value w mode depth parameter k c d n q)))))))))).close

theorem source_originalNilListActualValue {m} (three : Bool) (w mode depth parameter k c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalNilListActualValueSentence three w mode depth parameter k c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.nilCode w q) (Context.add (StructuralListSyntax.nilCode w n) (Context.add (SyntaxTermSyntax.contexts w c d) (Context.add (empty k) (Context.add (Formula.mem parameter w) (Context.add (Formula.mem depth w) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (Formula.mem depth w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (Formula.mem parameter w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (empty k) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (SyntaxTermSyntax.contexts w c d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (StructuralListSyntax.nilCode w n) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (StructuralListSyntax.nilCode w q) := .hyp (Or.inl rfl)
  exact OriginalArgumentValueConstruct.nil_value hZ three w mode depth parameter k c d n q h0 h1 h2 h3 h4 h5 h6 h7

theorem originalNilListActualValue_kernel_certificate {m} (three : Bool) (w mode depth parameter k c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalNilListActualValueSentence three w mode depth parameter k c d n q)) := TheoryTransport.sentence (source_originalNilListActualValue three w mode depth parameter k c d n q)

theorem native_originalNilListActualValue {m} (three : Bool) (w mode depth parameter k c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalNilListActualValueSentence three w mode depth parameter k c d n q)) := ZFReplay.replay (originalNilListActualValue_kernel_certificate three w mode depth parameter k c d n q)

def originalConsListActualValueSentence {m} (three : Bool) (w mode depth parameter ell k c d n q h t H T : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((Formula.mem depth w).imp ((Formula.mem parameter w).imp ((successor k ell).imp ((StructuralListSyntax.consCode w h t n).imp ((StructuralListSyntax.consCode w H T q).imp ((OriginalNumericTermValueSyntax.value w mode depth parameter c d h H).imp ((OriginalArgumentValueSyntax.value w mode depth parameter ell c d t T).imp ((OriginalArgumentValueSyntax.value w mode depth parameter k c d n q))))))))))).close

theorem source_originalConsListActualValue {m} (three : Bool) (w mode depth parameter ell k c d n q h t H T : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalConsListActualValueSentence three w mode depth parameter ell k c d n q h t H T) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalArgumentValueSyntax.value w mode depth parameter ell c d t T) (Context.add (OriginalNumericTermValueSyntax.value w mode depth parameter c d h H) (Context.add (StructuralListSyntax.consCode w H T q) (Context.add (StructuralListSyntax.consCode w h t n) (Context.add (successor k ell) (Context.add (Formula.mem parameter w) (Context.add (Formula.mem depth w) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h2 : Derives Δ (Formula.mem depth w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h3 : Derives Δ (Formula.mem parameter w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h4 : Derives Δ (successor k ell) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : Derives Δ (StructuralListSyntax.consCode w h t n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h6 : Derives Δ (StructuralListSyntax.consCode w H T q) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h7 : Derives Δ (OriginalNumericTermValueSyntax.value w mode depth parameter c d h H) := .hyp (Or.inr (Or.inl rfl))
  have h8 : Derives Δ (OriginalArgumentValueSyntax.value w mode depth parameter ell c d t T) := .hyp (Or.inl rfl)
  exact OriginalArgumentValueConstruct.cons_value hZ three w mode depth parameter ell k c d n q h t H T h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem originalConsListActualValue_kernel_certificate {m} (three : Bool) (w mode depth parameter ell k c d n q h t H T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalConsListActualValueSentence three w mode depth parameter ell k c d n q h t H T)) := TheoryTransport.sentence (source_originalConsListActualValue three w mode depth parameter ell k c d n q h t H T)

theorem native_originalConsListActualValue {m} (three : Bool) (w mode depth parameter ell k c d n q h t H T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalConsListActualValueSentence three w mode depth parameter ell k c d n q h t H T)) := ZFReplay.replay (originalConsListActualValue_kernel_certificate three w mode depth parameter ell k c d n q h t H T)

def originalAllInternalTypedListFiberSentence {m} (three : Bool) (w mode depth parameter a b c d n k : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((Formula.mem depth w).imp ((Formula.mem parameter w).imp ((SyntaxTermSyntax.contexts w c d).imp ((OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d).imp ((SyntaxMixedImageCodeSyntax.termList w k a b n).imp ((OriginalArgumentValueSyntax.fiber w mode depth parameter k c d n))))))))).close

theorem source_originalAllInternalTypedListFiber {m} (three : Bool) (w mode depth parameter a b c d n k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalAllInternalTypedListFiberSentence three w mode depth parameter a b c d n k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w k a b n) (Context.add (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d) (Context.add (SyntaxTermSyntax.contexts w c d) (Context.add (Formula.mem parameter w) (Context.add (Formula.mem depth w) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (Formula.mem depth w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (Formula.mem parameter w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxTermSyntax.contexts w c d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a b n) := .hyp (Or.inl rfl)
  exact OriginalArgumentValueInduction.actual_fiber hZ three w mode depth parameter a b c d n k h0 h1 h2 h3 h4 h5 h6

theorem originalAllInternalTypedListFiber_kernel_certificate {m} (three : Bool) (w mode depth parameter a b c d n k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalAllInternalTypedListFiberSentence three w mode depth parameter a b c d n k)) := TheoryTransport.sentence (source_originalAllInternalTypedListFiber three w mode depth parameter a b c d n k)

theorem native_originalAllInternalTypedListFiber {m} (three : Bool) (w mode depth parameter a b c d n k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalAllInternalTypedListFiberSentence three w mode depth parameter a b c d n k)) := ZFReplay.replay (originalAllInternalTypedListFiber_kernel_certificate three w mode depth parameter a b c d n k)

def originalAllInternalListCodePropertiesSentence {m} (three : Bool) (w mode depth parameter a b c d : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((Formula.mem depth w).imp ((Formula.mem parameter w).imp ((SyntaxTermSyntax.contexts w c d).imp ((OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d).imp ((Formula.all ((Formula.mem (Fin.last m) w.castSucc).imp (OriginalArgumentValueSyntax.property w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc c.castSucc d.castSucc (Fin.last m))))))))))).close

theorem source_originalAllInternalListCodeProperties {m} (three : Bool) (w mode depth parameter a b c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalAllInternalListCodePropertiesSentence three w mode depth parameter a b c d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d) (Context.add (SyntaxTermSyntax.contexts w c d) (Context.add (Formula.mem parameter w) (Context.add (Formula.mem depth w) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (Formula.mem depth w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (Formula.mem parameter w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxTermSyntax.contexts w c d) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d) := .hyp (Or.inl rfl)
  exact OriginalArgumentValueInduction.all_properties hZ three w mode depth parameter a b c d h0 h1 h2 h3 h4 h5

theorem originalAllInternalListCodeProperties_kernel_certificate {m} (three : Bool) (w mode depth parameter a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalAllInternalListCodePropertiesSentence three w mode depth parameter a b c d)) := TheoryTransport.sentence (source_originalAllInternalListCodeProperties three w mode depth parameter a b c d)

theorem native_originalAllInternalListCodeProperties {m} (three : Bool) (w mode depth parameter a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalAllInternalListCodePropertiesSentence three w mode depth parameter a b c d)) := ZFReplay.replay (originalAllInternalListCodeProperties_kernel_certificate three w mode depth parameter a b c d)

def replaceAllInternalOriginalListFiberSentence {m} (w mode depth a b c L I R n k : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((IndexTermImageCodeSyntax.converted true w I R a a c).imp ((SyntaxMixedImageCodeSyntax.termList w b a c L).imp ((SyntaxMixedImageCodeSyntax.termList w k a b n).imp ((OriginalArgumentValueSyntax.fiber w mode depth L k a c n))))))))).close

theorem source_replaceAllInternalOriginalListFiber {m} (w mode depth a b c L I R n k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (replaceAllInternalOriginalListFiberSentence w mode depth a b c L I R n k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w k a b n) (Context.add (SyntaxMixedImageCodeSyntax.termList w b a c L) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a c) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth L) (Context.add (SyntaxNumeralSyntax.numeral 3 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 3 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth L) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a c) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w b a c L) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a b n) := .hyp (Or.inl rfl)
  exact OriginalArgumentModeFiber.replace_fiber hZ w mode depth a b c L I R n k h0 h1 h2 h3 h4 h5 h6

theorem replaceAllInternalOriginalListFiber_kernel_certificate {m} (w mode depth a b c L I R n k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (replaceAllInternalOriginalListFiberSentence w mode depth a b c L I R n k)) := TheoryTransport.sentence (source_replaceAllInternalOriginalListFiber w mode depth a b c L I R n k)

theorem native_replaceAllInternalOriginalListFiber {m} (w mode depth a b c L I R n k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (replaceAllInternalOriginalListFiberSentence w mode depth a b c L I R n k)) := ZFReplay.replay (replaceAllInternalOriginalListFiber_kernel_certificate w mode depth a b c L I R n k)

def weakenAllInternalOriginalListFiberSentence {m} (w mode depth parameter a b B I J R S n k : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeShiftSyntax.shiftCode w b B J).imp ((IndexTermImageCodeSyntax.converted true w I R a a B).imp ((IndexTermImageCodeSyntax.converted false w J S b a B).imp ((SyntaxMixedImageCodeSyntax.termList w k a b n).imp ((OriginalArgumentValueSyntax.fiber w mode depth parameter k a B n)))))))))).close

theorem source_weakenAllInternalOriginalListFiber {m} (w mode depth parameter a b B I J R S n k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakenAllInternalOriginalListFiberSentence w mode depth parameter a b B I J R S n k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w k a b n) (Context.add (IndexTermImageCodeSyntax.converted false w J S b a B) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a B) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B J) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral 0 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth parameter) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B J) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (IndexTermImageCodeSyntax.converted false w J S b a B) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a b n) := .hyp (Or.inl rfl)
  exact OriginalArgumentModeFiber.weaken_fiber hZ w mode depth parameter a b B I J R S n k h0 h1 h2 h3 h4 h5 h6 h7

theorem weakenAllInternalOriginalListFiber_kernel_certificate {m} (w mode depth parameter a b B I J R S n k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakenAllInternalOriginalListFiberSentence w mode depth parameter a b B I J R S n k)) := TheoryTransport.sentence (source_weakenAllInternalOriginalListFiber w mode depth parameter a b B I J R S n k)

theorem native_weakenAllInternalOriginalListFiber {m} (w mode depth parameter a b B I J R S n k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakenAllInternalOriginalListFiberSentence w mode depth parameter a b B I J R S n k)) := ZFReplay.replay (weakenAllInternalOriginalListFiber_kernel_certificate w mode depth parameter a b B I J R S n k)

end PPAC.Migration.Internal.ObjectOriginalArgumentFiber
