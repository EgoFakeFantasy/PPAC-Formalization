import PPAC.Migration.Internal.AbstractOperationFrameBinder

/-! 任意内部深度的实际抽象frame、变量协变及原binder闭包原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectAbstractOperationFrame
open Source SourceAlgebra SourceLogic OmegaSyntax

def arbitraryDepthBoundShiftedIffSentence {m} (w d i j x y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem d w).imp ((successor j i).imp ((Formula.mem d j).imp (((AbstractVariableValueSyntax.boundValue w d i x y).iff (SyntaxVariableSyntax.code true w j y))))))).close

theorem source_arbitraryDepthBoundShiftedIff {m} (w d i j x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (arbitraryDepthBoundShiftedIffSentence w d i j x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem d j) (Context.add (successor j i) (Context.add (Formula.mem d w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem d w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor j i) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem d j) := .hyp (Or.inl rfl)
  exact AbstractBoundOrder.above_iff hZ w d i j x y h0 h1 h2 h3

theorem arbitraryDepthBoundShiftedIff_kernel_certificate {m} (w d i j x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (arbitraryDepthBoundShiftedIffSentence w d i j x y)) := TheoryTransport.sentence (source_arbitraryDepthBoundShiftedIff w d i j x y)

theorem native_arbitraryDepthBoundShiftedIff {m} (w d i j x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (arbitraryDepthBoundShiftedIffSentence w d i j x y)) := ZFReplay.replay (arbitraryDepthBoundShiftedIff_kernel_certificate w d i j x y)

def internalSuccessorThresholdIffSentence {m} (w d i D I : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem d w).imp ((Formula.mem i w).imp ((successor D d).imp ((successor I i).imp (((Formula.mem I D).iff (Formula.mem i d)))))))).close

theorem source_internalSuccessorThresholdIff {m} (w d i D I : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (internalSuccessorThresholdIffSentence w d i D I) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor I i) (Context.add (successor D d) (Context.add (Formula.mem i w) (Context.add (Formula.mem d w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem d w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem i w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (successor D d) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (successor I i) := .hyp (Or.inl rfl)
  exact AbstractBoundOrder.successor_threshold_iff hZ w d i D I h0 h1 h2 h3 h4

theorem internalSuccessorThresholdIff_kernel_certificate {m} (w d i D I : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (internalSuccessorThresholdIffSentence w d i D I)) := TheoryTransport.sentence (source_internalSuccessorThresholdIff w d i D I)

theorem native_internalSuccessorThresholdIff {m} (w d i D I : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (internalSuccessorThresholdIffSentence w d i D I)) := ZFReplay.replay (internalSuccessorThresholdIff_kernel_certificate w d i D I)

def knownActualIndexVariableRenameIffSentence {m} (bound : Bool) (w r t a b c e n q i j : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIndexMapSyntax.maps w r t a b c e).imp ((Formula.mem i (SyntaxTermSyntax.limit bound a b)).imp ((GraphSyntax.edge (SyntaxIndexMapSyntax.selectMap bound r t) i j).imp ((SyntaxVariableSyntax.code bound w i n).imp (((SyntaxRenameTermSyntax.renamed w r t a b c e n q).iff (SyntaxVariableSyntax.code bound w j q)))))))).close

theorem source_knownActualIndexVariableRenameIff {m} (bound : Bool) (w r t a b c e n q i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (knownActualIndexVariableRenameIffSentence bound w r t a b c e n q i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w i n) (Context.add (GraphSyntax.edge (SyntaxIndexMapSyntax.selectMap bound r t) i j) (Context.add (Formula.mem i (SyntaxTermSyntax.limit bound a b)) (Context.add (SyntaxIndexMapSyntax.maps w r t a b c e) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxIndexMapSyntax.maps w r t a b c e) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem i (SyntaxTermSyntax.limit bound a b)) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (GraphSyntax.edge (SyntaxIndexMapSyntax.selectMap bound r t) i j) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxVariableSyntax.code bound w i n) := .hyp (Or.inl rfl)
  exact SyntaxRenameTermAtIndex.renamed_at hZ bound w r t a b c e n q i j h0 h1 h2 h3 h4

theorem knownActualIndexVariableRenameIff_kernel_certificate {m} (bound : Bool) (w r t a b c e n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (knownActualIndexVariableRenameIffSentence bound w r t a b c e n q i j)) := TheoryTransport.sentence (source_knownActualIndexVariableRenameIff bound w r t a b c e n q i j)

theorem native_knownActualIndexVariableRenameIff {m} (bound : Bool) (w r t a b c e n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (knownActualIndexVariableRenameIffSentence bound w r t a b c e n q i j)) := ZFReplay.replay (knownActualIndexVariableRenameIff_kernel_certificate bound w r t a b c e n q i j)

def actualBinderBoundRenameIffSentence {m} (w U V c e C t q i j : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w e V).imp ((SyntaxTermSyntax.term w c e t).imp ((SyntaxVariableSyntax.code true w i t).imp ((successor j i).imp (((SyntaxRenameTermSyntax.renamed w U V c e C e t q).iff (SyntaxVariableSyntax.code true w j q))))))))).close

theorem source_actualBinderBoundRenameIff {m} (w U V c e C t q i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualBinderBoundRenameIffSentence w U V c e C t q i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor j i) (Context.add (SyntaxVariableSyntax.code true w i t) (Context.add (SyntaxTermSyntax.term w c e t) (Context.add (SyntaxIdentityMapSyntax.identityMap w e V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w e V) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxTermSyntax.term w c e t) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxVariableSyntax.code true w i t) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (successor j i) := .hyp (Or.inl rfl)
  exact AbstractBinderRename.bound_at hZ w U V c e C t q i j h0 h1 h2 h3 h4 h5

theorem actualBinderBoundRenameIff_kernel_certificate {m} (w U V c e C t q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualBinderBoundRenameIffSentence w U V c e C t q i j)) := TheoryTransport.sentence (source_actualBinderBoundRenameIff w U V c e C t q i j)

theorem native_actualBinderBoundRenameIff {m} (w U V c e C t q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualBinderBoundRenameIffSentence w U V c e C t q i j)) := ZFReplay.replay (actualBinderBoundRenameIff_kernel_certificate w U V c e C t q i j)

def actualBinderFreeRenameIffSentence {m} (w U V c e C t q i : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w e V).imp ((SyntaxTermSyntax.term w c e t).imp ((SyntaxVariableSyntax.code false w i t).imp (((SyntaxRenameTermSyntax.renamed w U V c e C e t q).iff (SyntaxVariableSyntax.code false w i q)))))))).close

theorem source_actualBinderFreeRenameIff {m} (w U V c e C t q i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualBinderFreeRenameIffSentence w U V c e C t q i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code false w i t) (Context.add (SyntaxTermSyntax.term w c e t) (Context.add (SyntaxIdentityMapSyntax.identityMap w e V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w e V) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxTermSyntax.term w c e t) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxVariableSyntax.code false w i t) := .hyp (Or.inl rfl)
  exact AbstractBinderRename.free_at hZ w U V c e C t q i h0 h1 h2 h3 h4

theorem actualBinderFreeRenameIff_kernel_certificate {m} (w U V c e C t q i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualBinderFreeRenameIffSentence w U V c e C t q i)) := TheoryTransport.sentence (source_actualBinderFreeRenameIff w U V c e C t q i)

theorem native_actualBinderFreeRenameIff {m} (w U V c e C t q i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualBinderFreeRenameIffSentence w U V c e C t q i)) := ZFReplay.replay (actualBinderFreeRenameIff_kernel_certificate w U V c e C t q i)

def arbitraryDepthBoundBinderCovarianceIffSentence {m} (w d i D I U V c e C x X t q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem d w).imp ((successor D d).imp ((successor I i).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w e V).imp ((SyntaxTermSyntax.term w c e t).imp ((SyntaxVariableSyntax.code true w i x).imp ((SyntaxVariableSyntax.code true w I X).imp ((AbstractVariableValueSyntax.boundValue w d i x t).imp (((AbstractVariableValueSyntax.boundValue w D I X q).iff (SyntaxRenameTermSyntax.renamed w U V c e C e t q))))))))))))).close

theorem source_arbitraryDepthBoundBinderCovarianceIff {m} (w d i D I U V c e C x X t q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (arbitraryDepthBoundBinderCovarianceIffSentence w d i D I U V c e C x X t q) := by
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
  apply Derives.impI
  let Δ : Context m := Context.add (AbstractVariableValueSyntax.boundValue w d i x t) (Context.add (SyntaxVariableSyntax.code true w I X) (Context.add (SyntaxVariableSyntax.code true w i x) (Context.add (SyntaxTermSyntax.term w c e t) (Context.add (SyntaxIdentityMapSyntax.identityMap w e V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (successor I i) (Context.add (successor D d) (Context.add (Formula.mem d w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))))
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
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  have h1 : Derives Δ (Formula.mem d w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h2 : Derives Δ (successor D d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h3 : Derives Δ (successor I i) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h4 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h5 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w e V) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h6 : Derives Δ (SyntaxTermSyntax.term w c e t) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h7 : Derives Δ (SyntaxVariableSyntax.code true w i x) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h8 : Derives Δ (SyntaxVariableSyntax.code true w I X) := .hyp (Or.inr (Or.inl rfl))
  have h9 : Derives Δ (AbstractVariableValueSyntax.boundValue w d i x t) := .hyp (Or.inl rfl)
  exact AbstractBinderVariable.bound_iff hZ w d i D I U V c e C x X t q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem arbitraryDepthBoundBinderCovarianceIff_kernel_certificate {m} (w d i D I U V c e C x X t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (arbitraryDepthBoundBinderCovarianceIffSentence w d i D I U V c e C x X t q)) := TheoryTransport.sentence (source_arbitraryDepthBoundBinderCovarianceIff w d i D I U V c e C x X t q)

theorem native_arbitraryDepthBoundBinderCovarianceIff {m} (w d i D I U V c e C x X t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (arbitraryDepthBoundBinderCovarianceIffSentence w d i D I U V c e C x X t q)) := ZFReplay.replay (arbitraryDepthBoundBinderCovarianceIff_kernel_certificate w d i D I U V c e C x X t q)

def arbitraryDepthFreeBinderCovarianceIffSentence {m} (w d i D U V c e C t q : Fin m) : Source.Sentence := ((omega w).imp ((successor D d).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w e V).imp ((SyntaxTermSyntax.term w c e t).imp ((AbstractVariableValueSyntax.freeValue w d i t).imp (((AbstractVariableValueSyntax.freeValue w D i q).iff (SyntaxRenameTermSyntax.renamed w U V c e C e t q))))))))).close

theorem source_arbitraryDepthFreeBinderCovarianceIff {m} (w d i D U V c e C t q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (arbitraryDepthFreeBinderCovarianceIffSentence w d i D U V c e C t q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (AbstractVariableValueSyntax.freeValue w d i t) (Context.add (SyntaxTermSyntax.term w c e t) (Context.add (SyntaxIdentityMapSyntax.identityMap w e V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (successor D d) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (successor D d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w e V) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxTermSyntax.term w c e t) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (AbstractVariableValueSyntax.freeValue w d i t) := .hyp (Or.inl rfl)
  exact AbstractBinderVariable.free_iff hZ w d i D U V c e C t q h0 h1 h2 h3 h4 h5

theorem arbitraryDepthFreeBinderCovarianceIff_kernel_certificate {m} (w d i D U V c e C t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (arbitraryDepthFreeBinderCovarianceIffSentence w d i D U V c e C t q)) := TheoryTransport.sentence (source_arbitraryDepthFreeBinderCovarianceIff w d i D U V c e C t q)

theorem native_arbitraryDepthFreeBinderCovarianceIff {m} (w d i D U V c e C t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (arbitraryDepthFreeBinderCovarianceIffSentence w d i D U V c e C t q)) := ZFReplay.replay (arbitraryDepthFreeBinderCovarianceIff_kernel_certificate w d i D U V c e C t q)

def actualAbstractRootCompatibleFrameSentence {m} (w mode z P a b A B R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w z P).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((AbstractOperationFrameSyntax.frame w mode z P a B A b R S))))))).close

theorem source_actualAbstractRootCompatibleFrame {m} (w mode z P a b A B R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualAbstractRootCompatibleFrameSentence w mode z P a b A B R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (empty z) (Context.add (OriginalTermTraceSyntax.metadata w z P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 1 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w z P) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inl rfl)
  exact AbstractOperationFrameRoot.from_actual hZ w mode z P a b A B R S h0 h1 h2 h3 h4

theorem actualAbstractRootCompatibleFrame_kernel_certificate {m} (w mode z P a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualAbstractRootCompatibleFrameSentence w mode z P a b A B R S)) := TheoryTransport.sentence (source_actualAbstractRootCompatibleFrame w mode z P a b A B R S)

theorem native_actualAbstractRootCompatibleFrame {m} (w mode z P a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualAbstractRootCompatibleFrameSentence w mode z P a b A B R S)) := ZFReplay.replay (actualAbstractRootCompatibleFrame_kernel_certificate w mode z P a b A B R S)

def actualLiftedBoundFieldsIffSentence {m} (w mode depth P D R S a b c e A C K H U V z n i j X q : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((successor D depth).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w e V).imp ((SyntaxMixedImageHead.head w C e z n).imp ((Formula.mem i A).imp ((Formula.mem j a).imp ((successor i j).imp ((SyntaxVariableSyntax.code true w i X).imp (((AbstractVariableValueSyntax.boundValue w D i X q).iff (StructuralListFieldSyntax.field w K i q)))))))))))))).close

theorem source_actualLiftedBoundFieldsIff {m} (w mode depth P D R S a b c e A C K H U V z n i j X q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualLiftedBoundFieldsIffSentence w mode depth P D R S a b c e A C K H U V z n i j X q) := by
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
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code true w i X) (Context.add (successor i j) (Context.add (Formula.mem j a) (Context.add (Formula.mem i A) (Context.add (SyntaxMixedImageHead.head w C e z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w e V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) (Context.add (successor D depth) (Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))))
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
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  have h2 : Derives Δ (successor D depth) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h3 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h4 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h5 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w e V) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h6 : Derives Δ (SyntaxMixedImageHead.head w C e z n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h7 : Derives Δ (Formula.mem i A) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h8 : Derives Δ (Formula.mem j a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h9 : Derives Δ (successor i j) := .hyp (Or.inr (Or.inl rfl))
  have h10 : Derives Δ (SyntaxVariableSyntax.code true w i X) := .hyp (Or.inl rfl)
  exact AbstractFrameLiftValues.bound_successor hZ w mode depth P D R S a b c e A C K H U V z n i j X q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem actualLiftedBoundFieldsIff_kernel_certificate {m} (w mode depth P D R S a b c e A C K H U V z n i j X q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualLiftedBoundFieldsIffSentence w mode depth P D R S a b c e A C K H U V z n i j X q)) := TheoryTransport.sentence (source_actualLiftedBoundFieldsIff w mode depth P D R S a b c e A C K H U V z n i j X q)

theorem native_actualLiftedBoundFieldsIff {m} (w mode depth P D R S a b c e A C K H U V z n i j X q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualLiftedBoundFieldsIffSentence w mode depth P D R S a b c e A C K H U V z n i j X q)) := ZFReplay.replay (actualLiftedBoundFieldsIff_kernel_certificate w mode depth P D R S a b c e A C K H U V z n i j X q)

def actualLiftedFreeFieldsIffSentence {m} (w mode depth P D R S a b c e A C K H U V z n i X q : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((successor D depth).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w e V).imp ((SyntaxMixedImageHead.head w C e z n).imp ((Formula.mem i b).imp ((SyntaxVariableSyntax.code false w i X).imp (((AbstractVariableValueSyntax.freeValue w D i q).iff (StructuralListFieldSyntax.field w H i q)))))))))))).close

theorem source_actualLiftedFreeFieldsIff {m} (w mode depth P D R S a b c e A C K H U V z n i X q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualLiftedFreeFieldsIffSentence w mode depth P D R S a b c e A C K H U V z n i X q) := by
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
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code false w i X) (Context.add (Formula.mem i b) (Context.add (SyntaxMixedImageHead.head w C e z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w e V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) (Context.add (successor D depth) (Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))
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
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h2 : Derives Δ (successor D depth) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h3 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h4 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w e V) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h6 : Derives Δ (SyntaxMixedImageHead.head w C e z n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h7 : Derives Δ (Formula.mem i b) := .hyp (Or.inr (Or.inl rfl))
  have h8 : Derives Δ (SyntaxVariableSyntax.code false w i X) := .hyp (Or.inl rfl)
  exact AbstractFrameLiftValues.free hZ w mode depth P D R S a b c e A C K H U V z n i X q h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem actualLiftedFreeFieldsIff_kernel_certificate {m} (w mode depth P D R S a b c e A C K H U V z n i X q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualLiftedFreeFieldsIffSentence w mode depth P D R S a b c e A C K H U V z n i X q)) := TheoryTransport.sentence (source_actualLiftedFreeFieldsIff w mode depth P D R S a b c e A C K H U V z n i X q)

theorem native_actualLiftedFreeFieldsIff {m} (w mode depth P D R S a b c e A C K H U V z n i X q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualLiftedFreeFieldsIffSentence w mode depth P D R S a b c e A C K H U V z n i X q)) := ZFReplay.replay (actualLiftedFreeFieldsIff_kernel_certificate w mode depth P D R S a b c e A C K H U V z n i X q)

def allInternalLiftedBoundFieldsIffSentence {m} (w mode depth P D R S a b c e A C K H U V z n i X q : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((successor D depth).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w e V).imp ((SyntaxMixedImageHead.head w C e z n).imp ((Formula.mem i A).imp ((SyntaxVariableSyntax.code true w i X).imp (((AbstractVariableValueSyntax.boundValue w D i X q).iff (StructuralListFieldSyntax.field w K i q)))))))))))).close

theorem source_allInternalLiftedBoundFieldsIff {m} (w mode depth P D R S a b c e A C K H U V z n i X q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalLiftedBoundFieldsIffSentence w mode depth P D R S a b c e A C K H U V z n i X q) := by
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
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code true w i X) (Context.add (Formula.mem i A) (Context.add (SyntaxMixedImageHead.head w C e z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w e V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) (Context.add (successor D depth) (Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))
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
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h2 : Derives Δ (successor D depth) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h3 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h4 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w e V) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h6 : Derives Δ (SyntaxMixedImageHead.head w C e z n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h7 : Derives Δ (Formula.mem i A) := .hyp (Or.inr (Or.inl rfl))
  have h8 : Derives Δ (SyntaxVariableSyntax.code true w i X) := .hyp (Or.inl rfl)
  exact AbstractFrameLiftCompatibility.bound hZ w mode depth P D R S a b c e A C K H U V z n i X q h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem allInternalLiftedBoundFieldsIff_kernel_certificate {m} (w mode depth P D R S a b c e A C K H U V z n i X q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalLiftedBoundFieldsIffSentence w mode depth P D R S a b c e A C K H U V z n i X q)) := TheoryTransport.sentence (source_allInternalLiftedBoundFieldsIff w mode depth P D R S a b c e A C K H U V z n i X q)

theorem native_allInternalLiftedBoundFieldsIff {m} (w mode depth P D R S a b c e A C K H U V z n i X q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalLiftedBoundFieldsIffSentence w mode depth P D R S a b c e A C K H U V z n i X q)) := ZFReplay.replay (allInternalLiftedBoundFieldsIff_kernel_certificate w mode depth P D R S a b c e A C K H U V z n i X q)

def allInternalLiftedFrameCompatibilitySentence {m} (bound : Bool) (w mode depth P D R S a b c e A C K H U V z n : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((successor D depth).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w e V).imp ((SyntaxMixedImageHead.head w C e z n).imp ((AbstractOperationFrameSyntax.compatible bound w D A b K H))))))))).close

theorem source_allInternalLiftedFrameCompatibility {m} (bound : Bool) (w mode depth P D R S a b c e A C K H U V z n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalLiftedFrameCompatibilitySentence bound w mode depth P D R S a b c e A C K H U V z n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageHead.head w C e z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w e V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) (Context.add (successor D depth) (Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (successor D depth) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w e V) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxMixedImageHead.head w C e z n) := .hyp (Or.inl rfl)
  exact AbstractFrameLiftCompatibility.compatible hZ bound w mode depth P D R S a b c e A C K H U V z n h0 h1 h2 h3 h4 h5 h6

theorem allInternalLiftedFrameCompatibility_kernel_certificate {m} (bound : Bool) (w mode depth P D R S a b c e A C K H U V z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalLiftedFrameCompatibilitySentence bound w mode depth P D R S a b c e A C K H U V z n)) := TheoryTransport.sentence (source_allInternalLiftedFrameCompatibility bound w mode depth P D R S a b c e A C K H U V z n)

theorem native_allInternalLiftedFrameCompatibility {m} (bound : Bool) (w mode depth P D R S a b c e A C K H U V z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalLiftedFrameCompatibilitySentence bound w mode depth P D R S a b c e A C K H U V z n)) := ZFReplay.replay (allInternalLiftedFrameCompatibility_kernel_certificate bound w mode depth P D R S a b c e A C K H U V z n)

def actualBinderCompatibleFrameWitnessesDischargedSentence {m} (w mode depth P D R S a b c e A C K H : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((successor D depth).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H).imp ((AbstractOperationFrameSyntax.frame w mode D P A b C e K H)))))).close

theorem source_actualBinderCompatibleFrameWitnessesDischarged {m} (w mode depth P D R S a b c e A C K H : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualBinderCompatibleFrameWitnessesDischargedSentence w mode depth P D R S a b c e A C K H) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) (Context.add (successor D depth) (Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor D depth) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) := .hyp (Or.inl rfl)
  exact AbstractOperationFrameBinder.lifted hZ w mode depth P D R S a b c e A C K H h0 h1 h2 h3

theorem actualBinderCompatibleFrameWitnessesDischarged_kernel_certificate {m} (w mode depth P D R S a b c e A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualBinderCompatibleFrameWitnessesDischargedSentence w mode depth P D R S a b c e A C K H)) := TheoryTransport.sentence (source_actualBinderCompatibleFrameWitnessesDischarged w mode depth P D R S a b c e A C K H)

theorem native_actualBinderCompatibleFrameWitnessesDischarged {m} (w mode depth P D R S a b c e A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualBinderCompatibleFrameWitnessesDischargedSentence w mode depth P D R S a b c e A C K H)) := ZFReplay.replay (actualBinderCompatibleFrameWitnessesDischarged_kernel_certificate w mode depth P D R S a b c e A C K H)

end PPAC.Migration.Internal.ObjectAbstractOperationFrame
