import PPAC.Migration.Internal.InstantiateOperationFrameBinder

/-! mode2真实binder框架闭包、全内部变量兼容及独立后继几何的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectInstantiateBinder
open Source SourceAlgebra SourceLogic OmegaSyntax InstantiateOperationFrameSyntax InstantiateVariableValueSyntax

def modeTwoBinderSuccessorPointSentence {m} (d i D I : Fin m) : Source.Sentence := ((Formula.equal i d).imp ((successor D d).imp ((successor I i).imp ((Formula.equal I D))))).close

theorem source_modeTwoBinderSuccessorPoint {m} (d i D I : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoBinderSuccessorPointSentence d i D I) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor I i) (Context.add (successor D d) (Context.add (Formula.equal i d) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (Formula.equal i d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (successor D d) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor I i) := .hyp (Or.inl rfl)
  exact InstantiateBinderGeometry.successor_point hZ d i D I h0 h1 h2

theorem modeTwoBinderSuccessorPoint_kernel_certificate {m} (d i D I : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoBinderSuccessorPointSentence d i D I)) := TheoryTransport.sentence (source_modeTwoBinderSuccessorPoint d i D I)

theorem native_modeTwoBinderSuccessorPoint {m} (d i D I : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoBinderSuccessorPointSentence d i D I)) := ZFReplay.replay (modeTwoBinderSuccessorPoint_kernel_certificate d i D I)

def modeTwoBinderContextGeometrySentence {m} (d a b c e D A C : Fin m) : Source.Sentence := ((InstantiateOperationFrameSyntax.contextsAtDepth d a b c e).imp ((successor D d).imp ((successor A a).imp ((successor C c).imp ((InstantiateOperationFrameSyntax.contextsAtDepth D A b C e)))))).close

theorem source_modeTwoBinderContextGeometry {m} (d a b c e D A C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoBinderContextGeometrySentence d a b c e D A C) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor C c) (Context.add (successor A a) (Context.add (successor D d) (Context.add (InstantiateOperationFrameSyntax.contextsAtDepth d a b c e) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (InstantiateOperationFrameSyntax.contextsAtDepth d a b c e) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (successor D d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor A a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor C c) := .hyp (Or.inl rfl)
  exact InstantiateBinderGeometry.lifted_contexts hZ d a b c e D A C h0 h1 h2 h3

theorem modeTwoBinderContextGeometry_kernel_certificate {m} (d a b c e D A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoBinderContextGeometrySentence d a b c e D A C)) := TheoryTransport.sentence (source_modeTwoBinderContextGeometry d a b c e D A C)

theorem native_modeTwoBinderContextGeometry {m} (d a b c e D A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoBinderContextGeometrySentence d a b c e D A C)) := ZFReplay.replay (modeTwoBinderContextGeometry_kernel_certificate d a b c e D A C)

def modeTwoBinderBelowCaseIffSentence {m} (w d P i D I U V c e C X t q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem d w).imp ((successor D d).imp ((successor I i).imp ((Formula.mem i d).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w e V).imp ((SyntaxTermSyntax.term w c e t).imp ((SyntaxVariableSyntax.code true w i t).imp ((SyntaxVariableSyntax.code true w I X).imp (((boundValue w D P I X q).iff (SyntaxRenameTermSyntax.renamed w U V c e C e t q))))))))))))).close

theorem source_modeTwoBinderBelowCaseIff {m} (w d P i D I U V c e C X t q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoBinderBelowCaseIffSentence w d P i D I U V c e C X t q) := by
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
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code true w I X) (Context.add (SyntaxVariableSyntax.code true w i t) (Context.add (SyntaxTermSyntax.term w c e t) (Context.add (SyntaxIdentityMapSyntax.identityMap w e V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (Formula.mem i d) (Context.add (successor I i) (Context.add (successor D d) (Context.add (Formula.mem d w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))))
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
  have h4 : Derives Δ (Formula.mem i d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h5 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h6 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w e V) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h7 : Derives Δ (SyntaxTermSyntax.term w c e t) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h8 : Derives Δ (SyntaxVariableSyntax.code true w i t) := .hyp (Or.inr (Or.inl rfl))
  have h9 : Derives Δ (SyntaxVariableSyntax.code true w I X) := .hyp (Or.inl rfl)
  exact InstantiateBinderVariablePoint.preserved hZ w d P i D I U V c e C X t q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem modeTwoBinderBelowCaseIff_kernel_certificate {m} (w d P i D I U V c e C X t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoBinderBelowCaseIffSentence w d P i D I U V c e C X t q)) := TheoryTransport.sentence (source_modeTwoBinderBelowCaseIff w d P i D I U V c e C X t q)

theorem native_modeTwoBinderBelowCaseIff {m} (w d P i D I U V c e C X t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoBinderBelowCaseIffSentence w d P i D I U V c e C X t q)) := ZFReplay.replay (modeTwoBinderBelowCaseIff_kernel_certificate w d P i D I U V c e C X t q)

def modeTwoBinderPointCaseIffSentence {m} (w d P i D I U V c e C X t q : Fin m) : Source.Sentence := ((omega w).imp ((successor D d).imp ((successor I i).imp ((Formula.equal i d).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w e V).imp ((InstantiateOperationFrameSyntax.closedParameter w e P).imp ((Formula.equal t P).imp (((boundValue w D P I X q).iff (SyntaxRenameTermSyntax.renamed w U V c e C e t q))))))))))).close

theorem source_modeTwoBinderPointCaseIff {m} (w d P i D I U V c e C X t q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoBinderPointCaseIffSentence w d P i D I U V c e C X t q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.equal t P) (Context.add (InstantiateOperationFrameSyntax.closedParameter w e P) (Context.add (SyntaxIdentityMapSyntax.identityMap w e V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (Formula.equal i d) (Context.add (successor I i) (Context.add (successor D d) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
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
  have h1 : Derives Δ (successor D d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (successor I i) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (Formula.equal i d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w e V) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (InstantiateOperationFrameSyntax.closedParameter w e P) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (Formula.equal t P) := .hyp (Or.inl rfl)
  exact InstantiateBinderVariablePoint.at_point hZ w d P i D I U V c e C X t q h0 h1 h2 h3 h4 h5 h6 h7

theorem modeTwoBinderPointCaseIff_kernel_certificate {m} (w d P i D I U V c e C X t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoBinderPointCaseIffSentence w d P i D I U V c e C X t q)) := TheoryTransport.sentence (source_modeTwoBinderPointCaseIff w d P i D I U V c e C X t q)

theorem native_modeTwoBinderPointCaseIff {m} (w d P i D I U V c e C X t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoBinderPointCaseIffSentence w d P i D I U V c e C X t q)) := ZFReplay.replay (modeTwoBinderPointCaseIff_kernel_certificate w d P i D I U V c e C X t q)

def modeTwoBinderBoundCovarianceIffSentence {m} (w d P a i D I U V c e C x X t q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem d w).imp ((successor a d).imp ((Formula.mem i a).imp ((successor D d).imp ((successor I i).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w e V).imp ((SyntaxTermSyntax.term w c e t).imp ((SyntaxVariableSyntax.code true w i x).imp ((SyntaxVariableSyntax.code true w I X).imp ((InstantiateOperationFrameSyntax.closedParameter w e P).imp ((boundValue w d P i x t).imp (((boundValue w D P I X q).iff (SyntaxRenameTermSyntax.renamed w U V c e C e t q)))))))))))))))).close

theorem source_modeTwoBinderBoundCovarianceIff {m} (w d P a i D I U V c e C x X t q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoBinderBoundCovarianceIffSentence w d P a i D I U V c e C x X t q) := by
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
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (boundValue w d P i x t) (Context.add (InstantiateOperationFrameSyntax.closedParameter w e P) (Context.add (SyntaxVariableSyntax.code true w I X) (Context.add (SyntaxVariableSyntax.code true w i x) (Context.add (SyntaxTermSyntax.term w c e t) (Context.add (SyntaxIdentityMapSyntax.identityMap w e V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (successor I i) (Context.add (successor D d) (Context.add (Formula.mem i a) (Context.add (successor a d) (Context.add (Formula.mem d w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))))))
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
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))
  have h1 : Derives Δ (Formula.mem d w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))
  have h2 : Derives Δ (successor a d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))
  have h3 : Derives Δ (Formula.mem i a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  have h4 : Derives Δ (successor D d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h5 : Derives Δ (successor I i) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h6 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h7 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w e V) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h8 : Derives Δ (SyntaxTermSyntax.term w c e t) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h9 : Derives Δ (SyntaxVariableSyntax.code true w i x) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h10 : Derives Δ (SyntaxVariableSyntax.code true w I X) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h11 : Derives Δ (InstantiateOperationFrameSyntax.closedParameter w e P) := .hyp (Or.inr (Or.inl rfl))
  have h12 : Derives Δ (boundValue w d P i x t) := .hyp (Or.inl rfl)
  exact InstantiateBinderVariable.bound_iff hZ w d P a i D I U V c e C x X t q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

theorem modeTwoBinderBoundCovarianceIff_kernel_certificate {m} (w d P a i D I U V c e C x X t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoBinderBoundCovarianceIffSentence w d P a i D I U V c e C x X t q)) := TheoryTransport.sentence (source_modeTwoBinderBoundCovarianceIff w d P a i D I U V c e C x X t q)

theorem native_modeTwoBinderBoundCovarianceIff {m} (w d P a i D I U V c e C x X t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoBinderBoundCovarianceIffSentence w d P a i D I U V c e C x X t q)) := ZFReplay.replay (modeTwoBinderBoundCovarianceIff_kernel_certificate w d P a i D I U V c e C x X t q)

def modeTwoBinderFreeCovarianceIffSentence {m} (w i U V c e C X t q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w e V).imp ((SyntaxTermSyntax.term w c e t).imp ((SyntaxVariableSyntax.code false w i X).imp ((Formula.equal t X).imp (((Formula.equal q X).iff (SyntaxRenameTermSyntax.renamed w U V c e C e t q))))))))).close

theorem source_modeTwoBinderFreeCovarianceIff {m} (w i U V c e C X t q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoBinderFreeCovarianceIffSentence w i U V c e C X t q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.equal t X) (Context.add (SyntaxVariableSyntax.code false w i X) (Context.add (SyntaxTermSyntax.term w c e t) (Context.add (SyntaxIdentityMapSyntax.identityMap w e V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h4 : Derives Δ (SyntaxVariableSyntax.code false w i X) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (Formula.equal t X) := .hyp (Or.inl rfl)
  exact InstantiateBinderVariable.free_iff hZ w i U V c e C X t q h0 h1 h2 h3 h4 h5

theorem modeTwoBinderFreeCovarianceIff_kernel_certificate {m} (w i U V c e C X t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoBinderFreeCovarianceIffSentence w i U V c e C X t q)) := TheoryTransport.sentence (source_modeTwoBinderFreeCovarianceIff w i U V c e C X t q)

theorem native_modeTwoBinderFreeCovarianceIff {m} (w i U V c e C X t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoBinderFreeCovarianceIffSentence w i U V c e C X t q)) := ZFReplay.replay (modeTwoBinderFreeCovarianceIff_kernel_certificate w i U V c e C X t q)

def modeTwoBinderFreshZeroFieldIffSentence {m} (w depth P D R S a b c e A C K H U V z n i X q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem depth w).imp ((successor D depth).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w e V).imp ((SyntaxMixedImageHead.head w C e z n).imp ((Formula.mem i A).imp ((empty i).imp ((SyntaxVariableSyntax.code true w i X).imp (((boundValue w D P i X q).iff (StructuralListFieldSyntax.field w K i q))))))))))))).close

theorem source_modeTwoBinderFreshZeroFieldIff {m} (w depth P D R S a b c e A C K H U V z n i X q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoBinderFreshZeroFieldIffSentence w depth P D R S a b c e A C K H U V z n i X q) := by
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
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code true w i X) (Context.add (empty i) (Context.add (Formula.mem i A) (Context.add (SyntaxMixedImageHead.head w C e z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w e V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) (Context.add (successor D depth) (Context.add (Formula.mem depth w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))))
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
  have h1 : Derives Δ (Formula.mem depth w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h2 : Derives Δ (successor D depth) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h3 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h4 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h5 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w e V) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h6 : Derives Δ (SyntaxMixedImageHead.head w C e z n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h7 : Derives Δ (Formula.mem i A) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h8 : Derives Δ (empty i) := .hyp (Or.inr (Or.inl rfl))
  have h9 : Derives Δ (SyntaxVariableSyntax.code true w i X) := .hyp (Or.inl rfl)
  exact InstantiateFrameLiftPoint.fresh hZ w depth P D R S a b c e A C K H U V z n i X q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem modeTwoBinderFreshZeroFieldIff_kernel_certificate {m} (w depth P D R S a b c e A C K H U V z n i X q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoBinderFreshZeroFieldIffSentence w depth P D R S a b c e A C K H U V z n i X q)) := TheoryTransport.sentence (source_modeTwoBinderFreshZeroFieldIff w depth P D R S a b c e A C K H U V z n i X q)

theorem native_modeTwoBinderFreshZeroFieldIff {m} (w depth P D R S a b c e A C K H U V z n i X q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoBinderFreshZeroFieldIffSentence w depth P D R S a b c e A C K H U V z n i X q)) := ZFReplay.replay (modeTwoBinderFreshZeroFieldIff_kernel_certificate w depth P D R S a b c e A C K H U V z n i X q)

def modeTwoBinderBoundSuccessorFieldIffSentence {m} (w mode depth P D R S a b c e A C K H U V z n i j X q : Fin m) : Source.Sentence := ((omega w).imp ((frame w mode depth P a b c e R S).imp ((successor D depth).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w e V).imp ((SyntaxMixedImageHead.head w C e z n).imp ((Formula.mem i A).imp ((Formula.mem j a).imp ((successor i j).imp ((SyntaxVariableSyntax.code true w i X).imp (((boundValue w D P i X q).iff (StructuralListFieldSyntax.field w K i q)))))))))))))).close

theorem source_modeTwoBinderBoundSuccessorFieldIff {m} (w mode depth P D R S a b c e A C K H U V z n i j X q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoBinderBoundSuccessorFieldIffSentence w mode depth P D R S a b c e A C K H U V z n i j X q) := by
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
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code true w i X) (Context.add (successor i j) (Context.add (Formula.mem j a) (Context.add (Formula.mem i A) (Context.add (SyntaxMixedImageHead.head w C e z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w e V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) (Context.add (successor D depth) (Context.add (frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))))
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
  have h1 : Derives Δ (frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  have h2 : Derives Δ (successor D depth) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h3 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h4 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h5 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w e V) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h6 : Derives Δ (SyntaxMixedImageHead.head w C e z n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h7 : Derives Δ (Formula.mem i A) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h8 : Derives Δ (Formula.mem j a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h9 : Derives Δ (successor i j) := .hyp (Or.inr (Or.inl rfl))
  have h10 : Derives Δ (SyntaxVariableSyntax.code true w i X) := .hyp (Or.inl rfl)
  exact InstantiateFrameLiftValues.bound_successor hZ w mode depth P D R S a b c e A C K H U V z n i j X q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem modeTwoBinderBoundSuccessorFieldIff_kernel_certificate {m} (w mode depth P D R S a b c e A C K H U V z n i j X q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoBinderBoundSuccessorFieldIffSentence w mode depth P D R S a b c e A C K H U V z n i j X q)) := TheoryTransport.sentence (source_modeTwoBinderBoundSuccessorFieldIff w mode depth P D R S a b c e A C K H U V z n i j X q)

theorem native_modeTwoBinderBoundSuccessorFieldIff {m} (w mode depth P D R S a b c e A C K H U V z n i j X q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoBinderBoundSuccessorFieldIffSentence w mode depth P D R S a b c e A C K H U V z n i j X q)) := ZFReplay.replay (modeTwoBinderBoundSuccessorFieldIff_kernel_certificate w mode depth P D R S a b c e A C K H U V z n i j X q)

def modeTwoBinderFreeFieldIffSentence {m} (w mode depth P D R S a b c e A C K H U V z n i X q : Fin m) : Source.Sentence := ((omega w).imp ((frame w mode depth P a b c e R S).imp ((successor D depth).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w e V).imp ((SyntaxMixedImageHead.head w C e z n).imp ((Formula.mem i b).imp ((SyntaxVariableSyntax.code false w i X).imp (((Formula.equal q X).iff (StructuralListFieldSyntax.field w H i q)))))))))))).close

theorem source_modeTwoBinderFreeFieldIff {m} (w mode depth P D R S a b c e A C K H U V z n i X q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoBinderFreeFieldIffSentence w mode depth P D R S a b c e A C K H U V z n i X q) := by
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
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code false w i X) (Context.add (Formula.mem i b) (Context.add (SyntaxMixedImageHead.head w C e z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w e V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) (Context.add (successor D depth) (Context.add (frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))
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
  have h1 : Derives Δ (frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h2 : Derives Δ (successor D depth) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h3 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h4 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w e V) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h6 : Derives Δ (SyntaxMixedImageHead.head w C e z n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h7 : Derives Δ (Formula.mem i b) := .hyp (Or.inr (Or.inl rfl))
  have h8 : Derives Δ (SyntaxVariableSyntax.code false w i X) := .hyp (Or.inl rfl)
  exact InstantiateFrameLiftValues.free hZ w mode depth P D R S a b c e A C K H U V z n i X q h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem modeTwoBinderFreeFieldIff_kernel_certificate {m} (w mode depth P D R S a b c e A C K H U V z n i X q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoBinderFreeFieldIffSentence w mode depth P D R S a b c e A C K H U V z n i X q)) := TheoryTransport.sentence (source_modeTwoBinderFreeFieldIff w mode depth P D R S a b c e A C K H U V z n i X q)

theorem native_modeTwoBinderFreeFieldIff {m} (w mode depth P D R S a b c e A C K H U V z n i X q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoBinderFreeFieldIffSentence w mode depth P D R S a b c e A C K H U V z n i X q)) := ZFReplay.replay (modeTwoBinderFreeFieldIff_kernel_certificate w mode depth P D R S a b c e A C K H U V z n i X q)

def modeTwoBinderVariableCompatibilitySentence {m} (boundTag : Bool) (w mode depth P D R S a b c e A C K H U V z n : Fin m) : Source.Sentence := ((omega w).imp ((frame w mode depth P a b c e R S).imp ((successor D depth).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w e V).imp ((SyntaxMixedImageHead.head w C e z n).imp ((InstantiateOperationFrameSyntax.compatible boundTag w D P A b K H))))))))).close

theorem source_modeTwoBinderVariableCompatibility {m} (boundTag : Bool) (w mode depth P D R S a b c e A C K H U V z n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoBinderVariableCompatibilitySentence boundTag w mode depth P D R S a b c e A C K H U V z n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageHead.head w C e z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w e V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) (Context.add (successor D depth) (Context.add (frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (successor D depth) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w e V) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxMixedImageHead.head w C e z n) := .hyp (Or.inl rfl)
  exact InstantiateFrameLiftCompatibility.compatible hZ boundTag w mode depth P D R S a b c e A C K H U V z n h0 h1 h2 h3 h4 h5 h6

theorem modeTwoBinderVariableCompatibility_kernel_certificate {m} (boundTag : Bool) (w mode depth P D R S a b c e A C K H U V z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoBinderVariableCompatibilitySentence boundTag w mode depth P D R S a b c e A C K H U V z n)) := TheoryTransport.sentence (source_modeTwoBinderVariableCompatibility boundTag w mode depth P D R S a b c e A C K H U V z n)

theorem native_modeTwoBinderVariableCompatibility {m} (boundTag : Bool) (w mode depth P D R S a b c e A C K H U V z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoBinderVariableCompatibilitySentence boundTag w mode depth P D R S a b c e A C K H U V z n)) := ZFReplay.replay (modeTwoBinderVariableCompatibility_kernel_certificate boundTag w mode depth P D R S a b c e A C K H U V z n)

def modeTwoBinderFrameAtWitnessesSentence {m} (w mode depth P D R S a b c e A C K H U V z n : Fin m) : Source.Sentence := ((omega w).imp ((frame w mode depth P a b c e R S).imp ((successor D depth).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w e V).imp ((SyntaxMixedImageHead.head w C e z n).imp ((frame w mode D P A b C e K H))))))))).close

theorem source_modeTwoBinderFrameAtWitnesses {m} (w mode depth P D R S a b c e A C K H U V z n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoBinderFrameAtWitnessesSentence w mode depth P D R S a b c e A C K H U V z n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageHead.head w C e z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w e V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) (Context.add (successor D depth) (Context.add (frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (successor D depth) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w e V) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxMixedImageHead.head w C e z n) := .hyp (Or.inl rfl)
  exact InstantiateFrameLiftCompatibility.at_witnesses hZ w mode depth P D R S a b c e A C K H U V z n h0 h1 h2 h3 h4 h5 h6

theorem modeTwoBinderFrameAtWitnesses_kernel_certificate {m} (w mode depth P D R S a b c e A C K H U V z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoBinderFrameAtWitnessesSentence w mode depth P D R S a b c e A C K H U V z n)) := TheoryTransport.sentence (source_modeTwoBinderFrameAtWitnesses w mode depth P D R S a b c e A C K H U V z n)

theorem native_modeTwoBinderFrameAtWitnesses {m} (w mode depth P D R S a b c e A C K H U V z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoBinderFrameAtWitnessesSentence w mode depth P D R S a b c e A C K H U V z n)) := ZFReplay.replay (modeTwoBinderFrameAtWitnesses_kernel_certificate w mode depth P D R S a b c e A C K H U V z n)

def modeTwoActualBinderFrameSentence {m} (w mode depth P D R S a b c e A C K H : Fin m) : Source.Sentence := ((omega w).imp ((frame w mode depth P a b c e R S).imp ((successor D depth).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H).imp ((frame w mode D P A b C e K H)))))).close

theorem source_modeTwoActualBinderFrame {m} (w mode depth P D R S a b c e A C K H : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoActualBinderFrameSentence w mode depth P D R S a b c e A C K H) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) (Context.add (successor D depth) (Context.add (frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor D depth) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) := .hyp (Or.inl rfl)
  exact InstantiateOperationFrameBinder.lifted hZ w mode depth P D R S a b c e A C K H h0 h1 h2 h3

theorem modeTwoActualBinderFrame_kernel_certificate {m} (w mode depth P D R S a b c e A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoActualBinderFrameSentence w mode depth P D R S a b c e A C K H)) := TheoryTransport.sentence (source_modeTwoActualBinderFrame w mode depth P D R S a b c e A C K H)

theorem native_modeTwoActualBinderFrame {m} (w mode depth P D R S a b c e A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoActualBinderFrameSentence w mode depth P D R S a b c e A C K H)) := ZFReplay.replay (modeTwoActualBinderFrame_kernel_certificate w mode depth P D R S a b c e A C K H)

end PPAC.Migration.Internal.ObjectInstantiateBinder
