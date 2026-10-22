import PPAC.Migration.Internal.SyntaxMixedImageBinderFields

/-! 完全内部化的混合binder提升、完整头槽扩展及原YesMetaZFC核证书。 -/
namespace PPAC.Migration.Internal.ObjectMixedBinder
open Source SourceAlgebra SourceLogic OmegaSyntax

def prefixExistsSentence {m} (w f a c d z A : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermImageSyntax.imageMap w f a c d).imp ((SyntaxTermSyntax.term w c d z).imp ((successor A a).imp ((SyntaxTermImagePrefixSyntax.existsPrefix w f a c d z A)))))).close

theorem source_prefixExists {m} (w f a c d z A : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (prefixExistsSentence w f a c d z A) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor A a) (Context.add (SyntaxTermSyntax.term w c d z) (Context.add (SyntaxTermImageSyntax.imageMap w f a c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxTermImageSyntax.imageMap w f a c d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxTermSyntax.term w c d z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor A a) := .hyp (Or.inl rfl)
  exact SyntaxTermImagePrefixGraph.exists_prefix hZ w f a c d z A h0 h1 h2 h3

theorem prefixExists_kernel_certificate {m} (w f a c d z A : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (prefixExistsSentence w f a c d z A)) := TheoryTransport.sentence (source_prefixExists w f a c d z A)

theorem native_prefixExists {m} (w f a c d z A : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (prefixExistsSentence w f a c d z A)) := ZFReplay.replay (prefixExists_kernel_certificate w f a c d z A)

def prefixUniqueSentence {m} (w f a c d z A g h : Fin m) : Source.Sentence := ((SyntaxTermImagePrefixSyntax.prefixed w f a c d z A g).imp ((SyntaxTermImagePrefixSyntax.prefixed w f a c d z A h).imp ((Formula.equal g h)))).close

theorem source_prefixUnique {m} (w f a c d z A g h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (prefixUniqueSentence w f a c d z A g h) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermImagePrefixSyntax.prefixed w f a c d z A h) (Context.add (SyntaxTermImagePrefixSyntax.prefixed w f a c d z A g) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxTermImagePrefixSyntax.prefixed w f a c d z A g) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTermImagePrefixSyntax.prefixed w f a c d z A h) := .hyp (Or.inl rfl)
  exact SyntaxTermImagePrefixGraph.unique hZ w f a c d z A g h h0 h1

theorem prefixUnique_kernel_certificate {m} (w f a c d z A g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (prefixUniqueSentence w f a c d z A g h)) := TheoryTransport.sentence (source_prefixUnique w f a c d z A g h)

theorem native_prefixUnique {m} (w f a c d z A g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (prefixUniqueSentence w f a c d z A g h)) := ZFReplay.replay (prefixUnique_kernel_certificate w f a c d z A g h)

def prefixEdgesSentence {m} (w f a c d z A g i q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermImagePrefixSyntax.prefixed w f a c d z A g).imp (((GraphSyntax.edge g i q).iff (SyntaxTermImagePrefixSyntax.value f a z i q))))).close

theorem source_prefixEdges {m} (w f a c d z A g i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (prefixEdgesSentence w f a c d z A g i q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermImagePrefixSyntax.prefixed w f a c d z A g) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTermImagePrefixSyntax.prefixed w f a c d z A g) := .hyp (Or.inl rfl)
  exact SyntaxTermImagePrefixGraph.edge_iff hZ w f a c d z A g i q h0 h1

theorem prefixEdges_kernel_certificate {m} (w f a c d z A g i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (prefixEdgesSentence w f a c d z A g i q)) := TheoryTransport.sentence (source_prefixEdges w f a c d z A g i q)

theorem native_prefixEdges {m} (w f a c d z A g i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (prefixEdgesSentence w f a c d z A g i q)) := ZFReplay.replay (prefixEdges_kernel_certificate w f a c d z A g i q)

def prefixZeroSentence {m} (w f a c d z A g i q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermImagePrefixSyntax.prefixed w f a c d z A g).imp ((empty i).imp (((GraphSyntax.edge g i q).iff (Formula.equal q z)))))).close

theorem source_prefixZero {m} (w f a c d z A g i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (prefixZeroSentence w f a c d z A g i q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty i) (Context.add (SyntaxTermImagePrefixSyntax.prefixed w f a c d z A g) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxTermImagePrefixSyntax.prefixed w f a c d z A g) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty i) := .hyp (Or.inl rfl)
  exact SyntaxTermImagePrefixGraph.zero_iff hZ w f a c d z A g i q h0 h1 h2

theorem prefixZero_kernel_certificate {m} (w f a c d z A g i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (prefixZeroSentence w f a c d z A g i q)) := TheoryTransport.sentence (source_prefixZero w f a c d z A g i q)

theorem native_prefixZero {m} (w f a c d z A g i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (prefixZeroSentence w f a c d z A g i q)) := ZFReplay.replay (prefixZero_kernel_certificate w f a c d z A g i q)

def prefixSuccessorSentence {m} (w f a c d z A g i q k : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermImagePrefixSyntax.prefixed w f a c d z A g).imp ((Formula.mem k a).imp ((successor i k).imp (((GraphSyntax.edge g i q).iff (GraphSyntax.edge f k q))))))).close

theorem source_prefixSuccessor {m} (w f a c d z A g i q k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (prefixSuccessorSentence w f a c d z A g i q k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor i k) (Context.add (Formula.mem k a) (Context.add (SyntaxTermImagePrefixSyntax.prefixed w f a c d z A g) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxTermImagePrefixSyntax.prefixed w f a c d z A g) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem k a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor i k) := .hyp (Or.inl rfl)
  exact SyntaxTermImagePrefixGraph.successor_iff hZ w f a c d z A g i q k h0 h1 h2 h3

theorem prefixSuccessor_kernel_certificate {m} (w f a c d z A g i q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (prefixSuccessorSentence w f a c d z A g i q k)) := TheoryTransport.sentence (source_prefixSuccessor w f a c d z A g i q k)

theorem native_prefixSuccessor {m} (w f a c d z A g i q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (prefixSuccessorSentence w f a c d z A g i q k)) := ZFReplay.replay (prefixSuccessor_kernel_certificate w f a c d z A g i q k)

def valueUniqueSentence {m} (w f a c d z i q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermImageSyntax.imageMap w f a c d).imp ((SyntaxTermImagePrefixSyntax.value f a z i q).imp ((SyntaxTermImagePrefixSyntax.value f a z i v).imp ((Formula.equal q v)))))).close

theorem source_valueUnique {m} (w f a c d z i q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (valueUniqueSentence w f a c d z i q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermImagePrefixSyntax.value f a z i v) (Context.add (SyntaxTermImagePrefixSyntax.value f a z i q) (Context.add (SyntaxTermImageSyntax.imageMap w f a c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxTermImageSyntax.imageMap w f a c d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxTermImagePrefixSyntax.value f a z i q) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxTermImagePrefixSyntax.value f a z i v) := .hyp (Or.inl rfl)
  exact SyntaxTermImagePrefixUnique.unique hZ w f a c d z i q v h0 h1 h2 h3

theorem valueUnique_kernel_certificate {m} (w f a c d z i q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (valueUniqueSentence w f a c d z i q v)) := TheoryTransport.sentence (source_valueUnique w f a c d z i q v)

theorem native_valueUnique {m} (w f a c d z i q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (valueUniqueSentence w f a c d z i q v)) := ZFReplay.replay (valueUnique_kernel_certificate w f a c d z i q v)

def valueZeroSentence {m} (f a z i q : Fin m) : Source.Sentence := ((empty i).imp (((SyntaxTermImagePrefixSyntax.value f a z i q).iff (Formula.equal q z)))).close

theorem source_valueZero {m} (f a z i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (valueZeroSentence f a z i q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (empty i) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (empty i) := .hyp (Or.inl rfl)
  exact SyntaxTermImagePrefixPoint.zero_iff f a z i q h0

theorem valueZero_kernel_certificate {m} (f a z i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (valueZeroSentence f a z i q)) := TheoryTransport.sentence (source_valueZero f a z i q)

theorem native_valueZero {m} (f a z i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (valueZeroSentence f a z i q)) := ZFReplay.replay (valueZero_kernel_certificate f a z i q)

def valueSuccessorSentence {m} (w f a z i q k : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem k w).imp ((successor i k).imp (((SyntaxTermImagePrefixSyntax.value f a z i q).iff ((Formula.mem k a).conj (GraphSyntax.edge f k q))))))).close

theorem source_valueSuccessor {m} (w f a z i q k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (valueSuccessorSentence w f a z i q k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor i k) (Context.add (Formula.mem k w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem k w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor i k) := .hyp (Or.inl rfl)
  exact SyntaxTermImagePrefixPoint.successor_iff hZ w f a z i q k h0 h1 h2

theorem valueSuccessor_kernel_certificate {m} (w f a z i q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (valueSuccessorSentence w f a z i q k)) := TheoryTransport.sentence (source_valueSuccessor w f a z i q k)

theorem native_valueSuccessor {m} (w f a z i q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (valueSuccessorSentence w f a z i q k)) := ZFReplay.replay (valueSuccessor_kernel_certificate w f a z i q k)

def valueTargetSentence {m} (w f a c d z i q : Fin m) : Source.Sentence := ((SyntaxTermImageSyntax.imageMap w f a c d).imp ((SyntaxTermSyntax.term w c d z).imp ((SyntaxTermImagePrefixSyntax.value f a z i q).imp ((SyntaxTermSyntax.term w c d q))))).close

theorem source_valueTarget {m} (w f a c d z i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (valueTargetSentence w f a c d z i q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermImagePrefixSyntax.value f a z i q) (Context.add (SyntaxTermSyntax.term w c d z) (Context.add (SyntaxTermImageSyntax.imageMap w f a c d) (Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (SyntaxTermImageSyntax.imageMap w f a c d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxTermSyntax.term w c d z) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxTermImagePrefixSyntax.value f a z i q) := .hyp (Or.inl rfl)
  exact SyntaxTermImagePrefixPoint.target_type w f a c d z i q h0 h1 h2

theorem valueTarget_kernel_certificate {m} (w f a c d z i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (valueTargetSentence w f a c d z i q)) := TheoryTransport.sentence (source_valueTarget w f a c d z i q)

theorem native_valueTarget {m} (w f a c d z i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (valueTargetSentence w f a c d z i q)) := ZFReplay.replay (valueTarget_kernel_certificate w f a c d z i q)

def valueSourceSentence {m} (w f a z A i q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp ((successor A a).imp ((SyntaxTermImagePrefixSyntax.value f a z i q).imp ((Formula.mem i A)))))).close

theorem source_valueSource {m} (w f a z A i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (valueSourceSentence w f a z A i q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermImagePrefixSyntax.value f a z i q) (Context.add (successor A a) (Context.add (Formula.mem a w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem a w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor A a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxTermImagePrefixSyntax.value f a z i q) := .hyp (Or.inl rfl)
  exact SyntaxTermImagePrefixPoint.source_member hZ w f a z A i q h0 h1 h2 h3

theorem valueSource_kernel_certificate {m} (w f a z A i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (valueSourceSentence w f a z A i q)) := TheoryTransport.sentence (source_valueSource w f a z A i q)

theorem native_valueSource {m} (w f a z A i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (valueSourceSentence w f a z A i q)) := ZFReplay.replay (valueSource_kernel_certificate w f a z A i q)

def headTermSentence {m} (w c C d z n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem c w).imp ((Formula.mem d w).imp ((successor C c).imp ((empty z).imp ((SyntaxVariableSyntax.code true w z n).imp ((SyntaxTermSyntax.term w C d n)))))))).close

theorem source_headTerm {m} (w c C d z n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (headTermSentence w c C d z n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code true w z n) (Context.add (empty z) (Context.add (successor C c) (Context.add (Formula.mem d w) (Context.add (Formula.mem c w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (Formula.mem c w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (Formula.mem d w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (successor C c) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxVariableSyntax.code true w z n) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageHead.term_at_zero hZ w c C d z n h0 h1 h2 h3 h4 h5

theorem headTerm_kernel_certificate {m} (w c C d z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (headTermSentence w c C d z n)) := TheoryTransport.sentence (source_headTerm w c C d z n)

theorem native_headTerm {m} (w c C d z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (headTermSentence w c C d z n)) := ZFReplay.replay (headTerm_kernel_certificate w c C d z n)

def headCodeSentence {m} (w c C d z : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem c w).imp ((Formula.mem d w).imp ((successor C c).imp ((empty z).imp ((SyntaxMixedImageHead.codeExists w C d z))))))).close

theorem source_headCode {m} (w c C d z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (headCodeSentence w c C d z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (successor C c) (Context.add (Formula.mem d w) (Context.add (Formula.mem c w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem c w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem d w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (successor C c) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageHead.code_exists hZ w c C d z h0 h1 h2 h3 h4

theorem headCode_kernel_certificate {m} (w c C d z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (headCodeSentence w c C d z)) := TheoryTransport.sentence (source_headCode w c C d z)

theorem native_headCode {m} (w c C d z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (headCodeSentence w c C d z)) := ZFReplay.replay (headCode_kernel_certificate w c C d z)

def headExistsSentence {m} (w c C d : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem c w).imp ((Formula.mem d w).imp ((successor C c).imp ((SyntaxMixedImageHead.existsHead w C d)))))).close

theorem source_headExists {m} (w c C d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (headExistsSentence w c C d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor C c) (Context.add (Formula.mem d w) (Context.add (Formula.mem c w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem c w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem d w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor C c) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageHead.exists_head hZ w c C d h0 h1 h2 h3

theorem headExists_kernel_certificate {m} (w c C d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (headExistsSentence w c C d)) := TheoryTransport.sentence (source_headExists w c C d)

theorem native_headExists {m} (w c C d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (headExistsSentence w c C d)) := ZFReplay.replay (headExists_kernel_certificate w c C d)

def headUniqueSentence {m} (w C d z n Z N : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedImageHead.head w C d z n).imp ((SyntaxMixedImageHead.head w C d Z N).imp (((Formula.equal z Z).conj (Formula.equal n N)))))).close

theorem source_headUnique {m} (w C d z n Z N : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (headUniqueSentence w C d z n Z N) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageHead.head w C d Z N) (Context.add (SyntaxMixedImageHead.head w C d z n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMixedImageHead.head w C d z n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMixedImageHead.head w C d Z N) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageBinderAlign.head_unique hZ w C d z n Z N h0 h1 h2

theorem headUnique_kernel_certificate {m} (w C d z n Z N : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (headUniqueSentence w C d z n Z N)) := TheoryTransport.sentence (source_headUnique w C d z n Z N)

theorem native_headUnique {m} (w C d z n Z N : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (headUniqueSentence w C d z n Z N)) := ZFReplay.replay (headUnique_kernel_certificate w C d z n Z N)

def preparedExistsSentence {m} (w R S r s a b c d A C n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermImageSyntax.maps w r s a b c d).imp ((SyntaxIndexMapSyntax.maps w R S c d C d).imp ((SyntaxTermSyntax.term w C d n).imp ((successor A a).imp ((SyntaxMixedImageLiftSyntax.existsPair w R S r s a b c d A C n))))))).close

theorem source_preparedExists {m} (w R S r s a b c d A C n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (preparedExistsSentence w R S r s a b c d A C n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor A a) (Context.add (SyntaxTermSyntax.term w C d n) (Context.add (SyntaxIndexMapSyntax.maps w R S c d C d) (Context.add (SyntaxTermImageSyntax.maps w r s a b c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxTermImageSyntax.maps w r s a b c d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxIndexMapSyntax.maps w R S c d C d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxTermSyntax.term w C d n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (successor A a) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageLiftExistence.exists_pair hZ w R S r s a b c d A C n h0 h1 h2 h3 h4

theorem preparedExists_kernel_certificate {m} (w R S r s a b c d A C n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (preparedExistsSentence w R S r s a b c d A C n)) := TheoryTransport.sentence (source_preparedExists w R S r s a b c d A C n)

theorem native_preparedExists {m} (w R S r s a b c d A C n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (preparedExistsSentence w R S r s a b c d A C n)) := ZFReplay.replay (preparedExists_kernel_certificate w R S r s a b c d A C n)

def preparedUniqueSentence {m} (w R S r s a b c d A C n k h K H : Fin m) : Source.Sentence := ((SyntaxMixedImageLiftSyntax.lifted w R S r s a b c d A C n k h).imp ((SyntaxMixedImageLiftSyntax.lifted w R S r s a b c d A C n K H).imp (((Formula.equal k K).conj (Formula.equal h H))))).close

theorem source_preparedUnique {m} (w R S r s a b c d A C n k h K H : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (preparedUniqueSentence w R S r s a b c d A C n k h K H) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageLiftSyntax.lifted w R S r s a b c d A C n K H) (Context.add (SyntaxMixedImageLiftSyntax.lifted w R S r s a b c d A C n k h) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxMixedImageLiftSyntax.lifted w R S r s a b c d A C n k h) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedImageLiftSyntax.lifted w R S r s a b c d A C n K H) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageLiftUnique.unique_pair hZ w R S r s a b c d A C n k h K H h0 h1

theorem preparedUnique_kernel_certificate {m} (w R S r s a b c d A C n k h K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (preparedUniqueSentence w R S r s a b c d A C n k h K H)) := TheoryTransport.sentence (source_preparedUnique w R S r s a b c d A C n k h K H)

theorem native_preparedUnique {m} (w R S r s a b c d A C n k h K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (preparedUniqueSentence w R S r s a b c d A C n k h K H)) := ZFReplay.replay (preparedUnique_kernel_certificate w R S r s a b c d A C n k h K H)

def preparedTargetSentence {m} (w R S r s a b c d A C n k h : Fin m) : Source.Sentence := ((SyntaxMixedImageLiftSyntax.lifted w R S r s a b c d A C n k h).imp ((SyntaxTermImageSyntax.maps w k h A b C d))).close

theorem source_preparedTarget {m} (w R S r s a b c d A C n k h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (preparedTargetSentence w R S r s a b c d A C n k h) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageLiftSyntax.lifted w R S r s a b c d A C n k h) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxMixedImageLiftSyntax.lifted w R S r s a b c d A C n k h) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageLiftFields.target_maps w R S r s a b c d A C n k h h0

theorem preparedTarget_kernel_certificate {m} (w R S r s a b c d A C n k h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (preparedTargetSentence w R S r s a b c d A C n k h)) := TheoryTransport.sentence (source_preparedTarget w R S r s a b c d A C n k h)

theorem native_preparedTarget {m} (w R S r s a b c d A C n k h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (preparedTargetSentence w R S r s a b c d A C n k h)) := ZFReplay.replay (preparedTarget_kernel_certificate w R S r s a b c d A C n k h)

def actualStateSentence {m} (w r s a b c d A C : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermImageSyntax.maps w r s a b c d).imp ((successor A a).imp ((successor C c).imp ((SyntaxMixedImageLiftState.existsState w r s a b c d A C)))))).close

theorem source_actualState {m} (w r s a b c d A C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualStateSentence w r s a b c d A C) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor C c) (Context.add (successor A a) (Context.add (SyntaxTermImageSyntax.maps w r s a b c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxTermImageSyntax.maps w r s a b c d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor A a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor C c) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageLiftState.exists_state hZ w r s a b c d A C h0 h1 h2 h3

theorem actualState_kernel_certificate {m} (w r s a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualStateSentence w r s a b c d A C)) := TheoryTransport.sentence (source_actualState w r s a b c d A C)

theorem native_actualState {m} (w r s a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualStateSentence w r s a b c d A C)) := ZFReplay.replay (actualState_kernel_certificate w r s a b c d A C)

def binderExistsSentence {m} (w r s a b c d A C : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermImageSyntax.maps w r s a b c d).imp ((successor A a).imp ((successor C c).imp ((SyntaxMixedImageBinderSyntax.existsPair w r s a b c d A C)))))).close

theorem source_binderExists {m} (w r s a b c d A C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderExistsSentence w r s a b c d A C) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor C c) (Context.add (successor A a) (Context.add (SyntaxTermImageSyntax.maps w r s a b c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxTermImageSyntax.maps w r s a b c d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor A a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor C c) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageBinderOutput.exists_pair hZ w r s a b c d A C h0 h1 h2 h3

theorem binderExists_kernel_certificate {m} (w r s a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderExistsSentence w r s a b c d A C)) := TheoryTransport.sentence (source_binderExists w r s a b c d A C)

theorem native_binderExists {m} (w r s a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderExistsSentence w r s a b c d A C)) := ZFReplay.replay (binderExists_kernel_certificate w r s a b c d A C)

def binderUniqueSentence {m} (w r s a b c d A C k h K H : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h).imp ((SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C K H).imp (((Formula.equal k K).conj (Formula.equal h H)))))).close

theorem source_binderUnique {m} (w r s a b c d A C k h K H : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderUniqueSentence w r s a b c d A C k h K H) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C K H) (Context.add (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C K H) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageBinderOutput.unique_pair hZ w r s a b c d A C k h K H h0 h1 h2

theorem binderUnique_kernel_certificate {m} (w r s a b c d A C k h K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderUniqueSentence w r s a b c d A C k h K H)) := TheoryTransport.sentence (source_binderUnique w r s a b c d A C k h K H)

theorem native_binderUnique {m} (w r s a b c d A C k h K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderUniqueSentence w r s a b c d A C k h K H)) := ZFReplay.replay (binderUnique_kernel_certificate w r s a b c d A C k h K H)

def binderTargetSentence {m} (w r s a b c d A C k h : Fin m) : Source.Sentence := ((SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h).imp ((SyntaxTermImageSyntax.maps w k h A b C d))).close

theorem source_binderTarget {m} (w r s a b c d A C k h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderTargetSentence w r s a b c d A C k h) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageBinderOutput.target_maps w r s a b c d A C k h h0

theorem binderTarget_kernel_certificate {m} (w r s a b c d A C k h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderTargetSentence w r s a b c d A C k h)) := TheoryTransport.sentence (source_binderTarget w r s a b c d A C k h)

theorem native_binderTarget {m} (w r s a b c d A C k h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderTargetSentence w r s a b c d A C k h)) := ZFReplay.replay (binderTarget_kernel_certificate w r s a b c d A C k h)

def binderAtWitnessesSentence {m} (w r s a b c d A C k h R S z n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeShiftSyntax.shiftMap w c C R).imp ((SyntaxIdentityMapSyntax.identityMap w d S).imp ((SyntaxMixedImageHead.head w C d z n).imp ((SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h).imp ((SyntaxMixedImageLiftSyntax.lifted w R S r s a b c d A C n k h))))))).close

theorem source_binderAtWitnesses {m} (w r s a b c d A C k h R S z n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderAtWitnessesSentence w r s a b c d A C k h R S z n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h) (Context.add (SyntaxMixedImageHead.head w C d z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w d S) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w d S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxMixedImageHead.head w C d z n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageBinderOutput.at_witnesses hZ w r s a b c d A C k h R S z n h0 h1 h2 h3 h4

theorem binderAtWitnesses_kernel_certificate {m} (w r s a b c d A C k h R S z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderAtWitnessesSentence w r s a b c d A C k h R S z n)) := TheoryTransport.sentence (source_binderAtWitnesses w r s a b c d A C k h R S z n)

theorem native_binderAtWitnesses {m} (w r s a b c d A C k h R S z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderAtWitnessesSentence w r s a b c d A C k h R S z n)) := ZFReplay.replay (binderAtWitnesses_kernel_certificate w r s a b c d A C k h R S z n)

def binderInputSentence {m} (w r s a b c d A C k h : Fin m) : Source.Sentence := ((SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h).imp ((SyntaxMixedImageBinderFiber.input w r s a b c d A C))).close

theorem source_binderInput {m} (w r s a b c d A C k h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderInputSentence w r s a b c d A C k h) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageBinderFiber.input_of_lifted w r s a b c d A C k h h0

theorem binderInput_kernel_certificate {m} (w r s a b c d A C k h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderInputSentence w r s a b c d A C k h)) := TheoryTransport.sentence (source_binderInput w r s a b c d A C k h)

theorem native_binderInput {m} (w r s a b c d A C k h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderInputSentence w r s a b c d A C k h)) := ZFReplay.replay (binderInput_kernel_certificate w r s a b c d A C k h)

def binderUniquePairSentence {m} (w r s a b c d A C k h : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h).imp ((SyntaxMixedImageBinderFiber.uniquePair w r s a b c d A C k h)))).close

theorem source_binderUniquePair {m} (w r s a b c d A C k h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderUniquePairSentence w r s a b c d A C k h) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageBinderFiber.unique_pair hZ w r s a b c d A C k h h0 h1

theorem binderUniquePair_kernel_certificate {m} (w r s a b c d A C k h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderUniquePairSentence w r s a b c d A C k h)) := TheoryTransport.sentence (source_binderUniquePair w r s a b c d A C k h)

theorem native_binderUniquePair {m} (w r s a b c d A C k h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderUniquePairSentence w r s a b c d A C k h)) := ZFReplay.replay (binderUniquePair_kernel_certificate w r s a b c d A C k h)

def binderFiberSentence {m} (w r s a b c d A C : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedImageBinderFiber.input w r s a b c d A C).imp ((SyntaxMixedImageBinderFiber.fiber w r s a b c d A C)))).close

theorem source_binderFiber {m} (w r s a b c d A C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderFiberSentence w r s a b c d A C) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageBinderFiber.input w r s a b c d A C) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedImageBinderFiber.input w r s a b c d A C) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageBinderFiber.actual_fiber hZ w r s a b c d A C h0 h1

theorem binderFiber_kernel_certificate {m} (w r s a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderFiberSentence w r s a b c d A C)) := TheoryTransport.sentence (source_binderFiber w r s a b c d A C)

theorem native_binderFiber {m} (w r s a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderFiberSentence w r s a b c d A C)) := ZFReplay.replay (binderFiber_kernel_certificate w r s a b c d A C)

def binderExistsIffSentence {m} (w r s a b c d A C : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxMixedImageBinderSyntax.existsPair w r s a b c d A C).iff (SyntaxMixedImageBinderFiber.input w r s a b c d A C)))).close

theorem source_binderExistsIff {m} (w r s a b c d A C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderExistsIffSentence w r s a b c d A C) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageBinderFiber.exists_iff_input hZ w r s a b c d A C h0

theorem binderExistsIff_kernel_certificate {m} (w r s a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderExistsIffSentence w r s a b c d A C)) := TheoryTransport.sentence (source_binderExistsIff w r s a b c d A C)

theorem native_binderExistsIff {m} (w r s a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderExistsIffSentence w r s a b c d A C)) := ZFReplay.replay (binderExistsIff_kernel_certificate w r s a b c d A C)

def binderFiberIffSentence {m} (w r s a b c d A C : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxMixedImageBinderFiber.fiber w r s a b c d A C).iff (SyntaxMixedImageBinderFiber.input w r s a b c d A C)))).close

theorem source_binderFiberIff {m} (w r s a b c d A C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderFiberIffSentence w r s a b c d A C) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageBinderFiber.fiber_iff_input hZ w r s a b c d A C h0

theorem binderFiberIff_kernel_certificate {m} (w r s a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderFiberIffSentence w r s a b c d A C)) := TheoryTransport.sentence (source_binderFiberIff w r s a b c d A C)

theorem native_binderFiberIff {m} (w r s a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderFiberIffSentence w r s a b c d A C)) := ZFReplay.replay (binderFiberIff_kernel_certificate w r s a b c d A C)

def binderZeroSentence {m} (w r s a b c d A C k h R S z n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeShiftSyntax.shiftMap w c C R).imp ((SyntaxIdentityMapSyntax.identityMap w d S).imp ((SyntaxMixedImageHead.head w C d z n).imp ((SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h).imp (((GraphSyntax.edge k z q).iff (Formula.equal q n)))))))).close

theorem source_binderZero {m} (w r s a b c d A C k h R S z n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderZeroSentence w r s a b c d A C k h R S z n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h) (Context.add (SyntaxMixedImageHead.head w C d z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w d S) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w d S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxMixedImageHead.head w C d z n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageBinderFields.zero_iff hZ w r s a b c d A C k h R S z n q h0 h1 h2 h3 h4

theorem binderZero_kernel_certificate {m} (w r s a b c d A C k h R S z n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderZeroSentence w r s a b c d A C k h R S z n q)) := TheoryTransport.sentence (source_binderZero w r s a b c d A C k h R S z n q)

theorem native_binderZero {m} (w r s a b c d A C k h R S z n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderZeroSentence w r s a b c d A C k h R S z n q)) := ZFReplay.replay (binderZero_kernel_certificate w r s a b c d A C k h R S z n q)

def binderBoundSentence {m} (w r s a b c d A C k h R S z n i j t q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeShiftSyntax.shiftMap w c C R).imp ((SyntaxIdentityMapSyntax.identityMap w d S).imp ((SyntaxMixedImageHead.head w C d z n).imp ((SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h).imp ((Formula.mem j a).imp ((successor i j).imp ((GraphSyntax.edge r j t).imp (((GraphSyntax.edge k i q).iff (SyntaxRenameTermSyntax.renamed w R S c d C d t q))))))))))).close

theorem source_binderBound {m} (w r s a b c d A C k h R S z n i j t q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderBoundSentence w r s a b c d A C k h R S z n i j t q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (GraphSyntax.edge r j t) (Context.add (successor i j) (Context.add (Formula.mem j a) (Context.add (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h) (Context.add (SyntaxMixedImageHead.head w C d z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w d S) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C R) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
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
  have h1 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w d S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (SyntaxMixedImageHead.head w C d z n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (Formula.mem j a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (successor i j) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (GraphSyntax.edge r j t) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageBinderFields.bound_iff hZ w r s a b c d A C k h R S z n i j t q h0 h1 h2 h3 h4 h5 h6 h7

theorem binderBound_kernel_certificate {m} (w r s a b c d A C k h R S z n i j t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderBoundSentence w r s a b c d A C k h R S z n i j t q)) := TheoryTransport.sentence (source_binderBound w r s a b c d A C k h R S z n i j t q)

theorem native_binderBound {m} (w r s a b c d A C k h R S z n i j t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderBoundSentence w r s a b c d A C k h R S z n i j t q)) := ZFReplay.replay (binderBound_kernel_certificate w r s a b c d A C k h R S z n i j t q)

def binderFreeSentence {m} (w r s a b c d A C k h R S z n j t q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeShiftSyntax.shiftMap w c C R).imp ((SyntaxIdentityMapSyntax.identityMap w d S).imp ((SyntaxMixedImageHead.head w C d z n).imp ((SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h).imp ((GraphSyntax.edge s j t).imp (((GraphSyntax.edge h j q).iff (SyntaxRenameTermSyntax.renamed w R S c d C d t q))))))))).close

theorem source_binderFree {m} (w r s a b c d A C k h R S z n j t q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderFreeSentence w r s a b c d A C k h R S z n j t q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (GraphSyntax.edge s j t) (Context.add (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h) (Context.add (SyntaxMixedImageHead.head w C d z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w d S) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C R) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w d S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxMixedImageHead.head w C d z n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (GraphSyntax.edge s j t) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageBinderFields.free_iff hZ w r s a b c d A C k h R S z n j t q h0 h1 h2 h3 h4 h5

theorem binderFree_kernel_certificate {m} (w r s a b c d A C k h R S z n j t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderFreeSentence w r s a b c d A C k h R S z n j t q)) := TheoryTransport.sentence (source_binderFree w r s a b c d A C k h R S z n j t q)

theorem native_binderFree {m} (w r s a b c d A C k h R S z n j t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderFreeSentence w r s a b c d A C k h R S z n j t q)) := ZFReplay.replay (binderFree_kernel_certificate w r s a b c d A C k h R S z n j t q)

end PPAC.Migration.Internal.ObjectMixedBinder
