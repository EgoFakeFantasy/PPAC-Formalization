import PPAC.Migration.Internal.SyntaxAtomReject

/-! 原常量/membership/equal的闭句模式、原源ZF证书及原nativeZF推导证书。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxAtoms
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxTermSyntax SyntaxAtomSyntax SyntaxAtomDecode

def zeroTwoSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((zeroScalar w n).iff (SyntaxNumeralSyntax.numeral 2 n))).close

theorem source_zeroTwo {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (zeroTwoSentence w n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxZeroScalar.two_iff hZ w n h0

theorem zeroTwo_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (zeroTwoSentence w n)) := TheoryTransport.sentence (source_zeroTwo w n)

theorem native_zeroTwo {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (zeroTwoSentence w n)) := ZFReplay.replay (zeroTwo_kernel_certificate w n)

def zeroIndexSentence {m} (w i s : Fin m) : Source.Sentence := ((omega w).imp ((scalar w i s).imp ((zeroScalar w s).iff (SyntaxNumeralSyntax.numeral 0 i)))).close

theorem source_zeroIndex {m} (w i s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (zeroIndexSentence w i s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (scalar w i s) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (scalar w i s) := .hyp (Or.inl rfl)
  exact SyntaxZeroScalar.index_iff hZ w i s h0 h1

theorem zeroIndex_kernel_certificate {m} (w i s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (zeroIndexSentence w i s)) := TheoryTransport.sentence (source_zeroIndex w i s)

theorem native_zeroIndex {m} (w i s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (zeroIndexSentence w i s)) := ZFReplay.replay (zeroIndex_kernel_certificate w i s)

def nullaryContextsSentence {m} (truth : Bool) (w b f n : Fin m) : Source.Sentence := ((constructor 0 (nullaryTag truth) w Fin.elim0 n).imp ((nullary truth w b f n).iff (contexts w b f))).close

theorem source_nullaryContexts {m} (truth : Bool) (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nullaryContextsSentence truth w b f n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (constructor 0 (nullaryTag truth) w Fin.elim0 n) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (constructor 0 (nullaryTag truth) w Fin.elim0 n) := .hyp (Or.inl rfl)
  exact SyntaxAtomTyping.nullary_iff_contexts truth w b f n h0

theorem nullaryContexts_kernel_certificate {m} (truth : Bool) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nullaryContextsSentence truth w b f n)) := TheoryTransport.sentence (source_nullaryContexts truth w b f n)

theorem native_nullaryContexts {m} (truth : Bool) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nullaryContextsSentence truth w b f n)) := ZFReplay.replay (nullaryContexts_kernel_certificate truth w b f n)

def falseTwoSentence {m} (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((nullary false w b f n).iff ((contexts w b f).conj (SyntaxNumeralSyntax.numeral 2 n)))).close

theorem source_falseTwo {m} (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (falseTwoSentence w b f n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxAtomTyping.false_iff_two hZ w b f n h0

theorem falseTwo_kernel_certificate {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (falseTwoSentence w b f n)) := TheoryTransport.sentence (source_falseTwo w b f n)

theorem native_falseTwo {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (falseTwoSentence w b f n)) := ZFReplay.replay (falseTwo_kernel_certificate w b f n)

def memberTypesSentence {m} (w b f s x y n : Fin m) : Source.Sentence := ((omega w).imp ((memberCode w s x y n).imp ((membership w b f n).iff (memberTypes w b f s x y)))).close

theorem source_memberTypes {m} (w b f s x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberTypesSentence w b f s x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (memberCode w s x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (memberCode w s x y n) := .hyp (Or.inl rfl)
  exact SyntaxAtomTyping.member_iff_types hZ w b f s x y n h0 h1

theorem memberTypes_kernel_certificate {m} (w b f s x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberTypesSentence w b f s x y n)) := TheoryTransport.sentence (source_memberTypes w b f s x y n)

theorem native_memberTypes {m} (w b f s x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberTypesSentence w b f s x y n)) := ZFReplay.replay (memberTypes_kernel_certificate w b f s x y n)

def equalTypesSentence {m} (w b f x y n : Fin m) : Source.Sentence := ((omega w).imp ((equalCode w x y n).imp ((equality w b f n).iff (equalTypes w b f x y)))).close

theorem source_equalTypes {m} (w b f x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalTypesSentence w b f x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (equalCode w x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (equalCode w x y n) := .hyp (Or.inl rfl)
  exact SyntaxAtomTyping.equal_iff_types hZ w b f x y n h0 h1

theorem equalTypes_kernel_certificate {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalTypesSentence w b f x y n)) := TheoryTransport.sentence (source_equalTypes w b f x y n)

theorem native_equalTypes {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalTypesSentence w b f x y n)) := ZFReplay.replay (equalTypes_kernel_certificate w b f x y n)

def nullaryExistsSentence {m} (truth : Bool) (w b f : Fin m) : Source.Sentence := ((omega w).imp ((contexts w b f).imp (existsNullary truth w b f))).close

theorem source_nullaryExists {m} (truth : Bool) (w b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nullaryExistsSentence truth w b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (contexts w b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (contexts w b f) := .hyp (Or.inl rfl)
  exact SyntaxAtomExistence.nullary_exists hZ truth w b f h0 h1

theorem nullaryExists_kernel_certificate {m} (truth : Bool) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nullaryExistsSentence truth w b f)) := TheoryTransport.sentence (source_nullaryExists truth w b f)

theorem native_nullaryExists {m} (truth : Bool) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nullaryExistsSentence truth w b f)) := ZFReplay.replay (nullaryExists_kernel_certificate truth w b f)

def memberExistsSentence {m} (w b f x y : Fin m) : Source.Sentence := ((omega w).imp ((term w b f x).imp ((term w b f y).imp (existsMembership w b f x y)))).close

theorem source_memberExists {m} (w b f x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberExistsSentence w b f x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (term w b f y) (Context.add (term w b f x) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (term w b f x) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (term w b f y) := .hyp (Or.inl rfl)
  exact SyntaxAtomExistence.membership_exists hZ w b f x y h0 h1 h2

theorem memberExists_kernel_certificate {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberExistsSentence w b f x y)) := TheoryTransport.sentence (source_memberExists w b f x y)

theorem native_memberExists {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberExistsSentence w b f x y)) := ZFReplay.replay (memberExists_kernel_certificate w b f x y)

def equalExistsSentence {m} (w b f x y : Fin m) : Source.Sentence := ((omega w).imp ((term w b f x).imp ((term w b f y).imp (existsEquality w b f x y)))).close

theorem source_equalExists {m} (w b f x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalExistsSentence w b f x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (term w b f y) (Context.add (term w b f x) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (term w b f x) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (term w b f y) := .hyp (Or.inl rfl)
  exact SyntaxAtomExistence.equality_exists hZ w b f x y h0 h1 h2

theorem equalExists_kernel_certificate {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalExistsSentence w b f x y)) := TheoryTransport.sentence (source_equalExists w b f x y)

theorem native_equalExists {m} (w b f x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalExistsSentence w b f x y)) := ZFReplay.replay (equalExists_kernel_certificate w b f x y)

def memberFieldsSentence {m} (w s x y t u v n : Fin m) : Source.Sentence := ((omega w).imp ((memberCode w s x y n).imp ((memberCode w t u v n).imp ((Formula.equal s t).conj ((Formula.equal x u).conj (.equal y v)))))).close

theorem source_memberFields {m} (w s x y t u v n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberFieldsSentence w s x y t u v n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (memberCode w t u v n) (Context.add (memberCode w s x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (memberCode w s x y n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (memberCode w t u v n) := .hyp (Or.inl rfl)
  exact SyntaxAtomUnique.member_fields hZ w s x y t u v n h0 h1 h2

theorem memberFields_kernel_certificate {m} (w s x y t u v n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberFieldsSentence w s x y t u v n)) := TheoryTransport.sentence (source_memberFields w s x y t u v n)

theorem native_memberFields {m} (w s x y t u v n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberFieldsSentence w s x y t u v n)) := ZFReplay.replay (memberFields_kernel_certificate w s x y t u v n)

def equalFieldsSentence {m} (w x y u v n : Fin m) : Source.Sentence := ((omega w).imp ((equalCode w x y n).imp ((equalCode w u v n).imp ((Formula.equal x u).conj (.equal y v))))).close

theorem source_equalFields {m} (w x y u v n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalFieldsSentence w x y u v n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (equalCode w u v n) (Context.add (equalCode w x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (equalCode w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (equalCode w u v n) := .hyp (Or.inl rfl)
  exact SyntaxAtomUnique.equal_fields hZ w x y u v n h0 h1 h2

theorem equalFields_kernel_certificate {m} (w x y u v n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalFieldsSentence w x y u v n)) := TheoryTransport.sentence (source_equalFields w x y u v n)

theorem native_equalFields {m} (w x y u v n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalFieldsSentence w x y u v n)) := ZFReplay.replay (equalFields_kernel_certificate w x y u v n)

def memberValueUniqueSentence {m} (w b f s t x y n r : Fin m) : Source.Sentence := ((omega w).imp ((memberAt w b f s x y n).imp ((memberAt w b f t x y r).imp (Formula.equal n r)))).close

theorem source_memberValueUnique {m} (w b f s t x y n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberValueUniqueSentence w b f s t x y n r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (memberAt w b f t x y r) (Context.add (memberAt w b f s x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (memberAt w b f s x y n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (memberAt w b f t x y r) := .hyp (Or.inl rfl)
  exact SyntaxAtomUnique.member_same_inputs hZ w b f s t x y n r h0 h1 h2

theorem memberValueUnique_kernel_certificate {m} (w b f s t x y n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberValueUniqueSentence w b f s t x y n r)) := TheoryTransport.sentence (source_memberValueUnique w b f s t x y n r)

theorem native_memberValueUnique {m} (w b f s t x y n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberValueUniqueSentence w b f s t x y n r)) := ZFReplay.replay (memberValueUnique_kernel_certificate w b f s t x y n r)

def equalValueUniqueSentence {m} (w b f x y n r : Fin m) : Source.Sentence := ((omega w).imp ((equalAt w b f x y n).imp ((equalAt w b f x y r).imp (Formula.equal n r)))).close

theorem source_equalValueUnique {m} (w b f x y n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalValueUniqueSentence w b f x y n r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (equalAt w b f x y r) (Context.add (equalAt w b f x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (equalAt w b f x y n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (equalAt w b f x y r) := .hyp (Or.inl rfl)
  exact SyntaxAtomUnique.equal_same_inputs hZ w b f x y n r h0 h1 h2

theorem equalValueUnique_kernel_certificate {m} (w b f x y n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalValueUniqueSentence w b f x y n r)) := TheoryTransport.sentence (source_equalValueUnique w b f x y n r)

theorem native_equalValueUnique {m} (w b f x y n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalValueUniqueSentence w b f x y n r)) := ZFReplay.replay (equalValueUnique_kernel_certificate w b f x y n r)

def memberDecodeSentence {m} (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((membership w b f n).iff (memberDecoded w b f n))).close

theorem source_memberDecode {m} (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberDecodeSentence w b f n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxAtomDecode.member_decode_iff hZ w b f n h0

theorem memberDecode_kernel_certificate {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberDecodeSentence w b f n)) := TheoryTransport.sentence (source_memberDecode w b f n)

theorem native_memberDecode {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberDecodeSentence w b f n)) := ZFReplay.replay (memberDecode_kernel_certificate w b f n)

def memberFiberSentence {m} (w n s x y : Fin m) : Source.Sentence := ((omega w).imp ((memberCode w s x y n).imp (memberUnique w n s x y))).close

theorem source_memberFiber {m} (w n s x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberFiberSentence w n s x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (memberCode w s x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (memberCode w s x y n) := .hyp (Or.inl rfl)
  exact SyntaxAtomDecode.member_unique hZ w n s x y h0 h1

theorem memberFiber_kernel_certificate {m} (w n s x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberFiberSentence w n s x y)) := TheoryTransport.sentence (source_memberFiber w n s x y)

theorem native_memberFiber {m} (w n s x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberFiberSentence w n s x y)) := ZFReplay.replay (memberFiber_kernel_certificate w n s x y)

def equalDecodeSentence {m} (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((equality w b f n).iff (equalDecoded w b f n))).close

theorem source_equalDecode {m} (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalDecodeSentence w b f n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxAtomDecode.equal_decode_iff hZ w b f n h0

theorem equalDecode_kernel_certificate {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalDecodeSentence w b f n)) := TheoryTransport.sentence (source_equalDecode w b f n)

theorem native_equalDecode {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalDecodeSentence w b f n)) := ZFReplay.replay (equalDecode_kernel_certificate w b f n)

def equalFiberSentence {m} (w n x y : Fin m) : Source.Sentence := ((omega w).imp ((equalCode w x y n).imp (equalUnique w n x y))).close

theorem source_equalFiber {m} (w n x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalFiberSentence w n x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (equalCode w x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (equalCode w x y n) := .hyp (Or.inl rfl)
  exact SyntaxAtomDecode.equal_unique hZ w n x y h0 h1

theorem equalFiber_kernel_certificate {m} (w n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalFiberSentence w n x y)) := TheoryTransport.sentence (source_equalFiber w n x y)

theorem native_equalFiber {m} (w n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalFiberSentence w n x y)) := ZFReplay.replay (equalFiber_kernel_certificate w n x y)

def atomicContextsSentence {m} (w b f n : Fin m) : Source.Sentence := ((atomic w b f n).imp (contexts w b f)).close

theorem source_atomicContexts {m} (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atomicContextsSentence w b f n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (atomic w b f n) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (atomic w b f n) := .hyp (Or.inl rfl)
  exact SyntaxAtomCases.context w b f n h0

theorem atomicContexts_kernel_certificate {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atomicContextsSentence w b f n)) := TheoryTransport.sentence (source_atomicContexts w b f n)

theorem native_atomicContexts {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atomicContextsSentence w b f n)) := ZFReplay.replay (atomicContexts_kernel_certificate w b f n)

def atomicRangeSentence {m} (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((atomic w b f n).imp (Formula.mem n w))).close

theorem source_atomicRange {m} (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atomicRangeSentence w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (atomic w b f n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (atomic w b f n) := .hyp (Or.inl rfl)
  exact SyntaxAtomCases.range hZ w b f n h0 h1

theorem atomicRange_kernel_certificate {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atomicRangeSentence w b f n)) := TheoryTransport.sentence (source_atomicRange w b f n)

theorem native_atomicRange {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atomicRangeSentence w b f n)) := ZFReplay.replay (atomicRange_kernel_certificate w b f n)

def nullaryAtomicSentence {m} (truth : Bool) (w b f n : Fin m) : Source.Sentence := ((constructor 0 (nullaryTag truth) w Fin.elim0 n).imp ((atomic w b f n).iff (contexts w b f))).close

theorem source_nullaryAtomic {m} (truth : Bool) (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nullaryAtomicSentence truth w b f n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (constructor 0 (nullaryTag truth) w Fin.elim0 n) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (constructor 0 (nullaryTag truth) w Fin.elim0 n) := .hyp (Or.inl rfl)
  exact SyntaxAtomCases.nullary_atomic_iff truth w b f n h0

theorem nullaryAtomic_kernel_certificate {m} (truth : Bool) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nullaryAtomicSentence truth w b f n)) := TheoryTransport.sentence (source_nullaryAtomic truth w b f n)

theorem native_nullaryAtomic {m} (truth : Bool) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nullaryAtomicSentence truth w b f n)) := ZFReplay.replay (nullaryAtomic_kernel_certificate truth w b f n)

def memberAtomicSentence {m} (w b f s x y n : Fin m) : Source.Sentence := ((omega w).imp ((memberCode w s x y n).imp ((atomic w b f n).iff (memberTypes w b f s x y)))).close

theorem source_memberAtomic {m} (w b f s x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberAtomicSentence w b f s x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (memberCode w s x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (memberCode w s x y n) := .hyp (Or.inl rfl)
  exact SyntaxAtomCases.member_atomic_iff hZ w b f s x y n h0 h1

theorem memberAtomic_kernel_certificate {m} (w b f s x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberAtomicSentence w b f s x y n)) := TheoryTransport.sentence (source_memberAtomic w b f s x y n)

theorem native_memberAtomic {m} (w b f s x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberAtomicSentence w b f s x y n)) := ZFReplay.replay (memberAtomic_kernel_certificate w b f s x y n)

def equalAtomicSentence {m} (w b f x y n : Fin m) : Source.Sentence := ((omega w).imp ((equalCode w x y n).imp ((atomic w b f n).iff (equalTypes w b f x y)))).close

theorem source_equalAtomic {m} (w b f x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalAtomicSentence w b f x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (equalCode w x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (equalCode w x y n) := .hyp (Or.inl rfl)
  exact SyntaxAtomCases.equal_atomic_iff hZ w b f x y n h0 h1

theorem equalAtomic_kernel_certificate {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalAtomicSentence w b f x y n)) := TheoryTransport.sentence (source_equalAtomic w b f x y n)

theorem native_equalAtomic {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalAtomicSentence w b f x y n)) := ZFReplay.replay (equalAtomic_kernel_certificate w b f x y n)

def symbolCheckSentence {m} (w b f i s x y n : Fin m) : Source.Sentence := ((omega w).imp ((scalar w i s).imp ((memberCode w s x y n).imp ((membership w b f n).iff ((SyntaxNumeralSyntax.numeral 0 i).conj ((term w b f x).conj (term w b f y))))))).close

theorem source_symbolCheck {m} (w b f i s x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (symbolCheckSentence w b f i s x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (memberCode w s x y n) (Context.add (scalar w i s) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (scalar w i s) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (memberCode w s x y n) := .hyp (Or.inl rfl)
  exact SyntaxAtomReject.symbol_iff hZ w b f i s x y n h0 h1 h2

theorem symbolCheck_kernel_certificate {m} (w b f i s x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (symbolCheckSentence w b f i s x y n)) := TheoryTransport.sentence (source_symbolCheck w b f i s x y n)

theorem native_symbolCheck {m} (w b f i s x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (symbolCheckSentence w b f i s x y n)) := ZFReplay.replay (symbolCheck_kernel_certificate w b f i s x y n)

def badSymbolSentence {m} (w b f i s x y n : Fin m) : Source.Sentence := ((omega w).imp ((scalar w i s).imp ((memberCode w s x y n).imp (((SyntaxNumeralSyntax.numeral 0 i).neg).imp ((membership w b f n).neg))))).close

theorem source_badSymbol {m} (w b f i s x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (badSymbolSentence w b f i s x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((SyntaxNumeralSyntax.numeral 0 i).neg) (Context.add (memberCode w s x y n) (Context.add (scalar w i s) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (scalar w i s) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (memberCode w s x y n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ ((SyntaxNumeralSyntax.numeral 0 i).neg) := .hyp (Or.inl rfl)
  exact SyntaxAtomReject.bad_symbol hZ w b f i s x y n h0 h1 h2 h3

theorem badSymbol_kernel_certificate {m} (w b f i s x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (badSymbolSentence w b f i s x y n)) := TheoryTransport.sentence (source_badSymbol w b f i s x y n)

theorem native_badSymbol {m} (w b f i s x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (badSymbolSentence w b f i s x y n)) := ZFReplay.replay (badSymbol_kernel_certificate w b f i s x y n)

def unknownAtomicTagSentence {m} (w b f t p n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem t w).imp ((Formula.mem p w).imp (((SyntaxNumeralSyntax.numeral 0 t).neg).imp (((SyntaxNumeralSyntax.numeral 1 t).neg).imp (((SyntaxNumeralSyntax.numeral 2 t).neg).imp (((SyntaxNumeralSyntax.numeral 3 t).neg).imp ((StructuralNodeSyntax.raw w t p n).imp ((atomic w b f n).neg))))))))).close

theorem source_unknownAtomicTag {m} (w b f t p n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (unknownAtomicTagSentence w b f t p n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralNodeSyntax.raw w t p n) (Context.add ((SyntaxNumeralSyntax.numeral 3 t).neg) (Context.add ((SyntaxNumeralSyntax.numeral 2 t).neg) (Context.add ((SyntaxNumeralSyntax.numeral 1 t).neg) (Context.add ((SyntaxNumeralSyntax.numeral 0 t).neg) (Context.add (Formula.mem p w) (Context.add (Formula.mem t w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
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
  have h1 : Derives Δ (Formula.mem t w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (Formula.mem p w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ ((SyntaxNumeralSyntax.numeral 0 t).neg) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ ((SyntaxNumeralSyntax.numeral 1 t).neg) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ ((SyntaxNumeralSyntax.numeral 2 t).neg) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ ((SyntaxNumeralSyntax.numeral 3 t).neg) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (StructuralNodeSyntax.raw w t p n) := .hyp (Or.inl rfl)
  exact SyntaxAtomReject.atomic_unknown_tag hZ w b f t p n h0 h1 h2 h3 h4 h5 h6 h7

theorem unknownAtomicTag_kernel_certificate {m} (w b f t p n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (unknownAtomicTagSentence w b f t p n)) := TheoryTransport.sentence (source_unknownAtomicTag w b f t p n)

theorem native_unknownAtomicTag {m} (w b f t p n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (unknownAtomicTagSentence w b f t p n)) := ZFReplay.replay (unknownAtomicTag_kernel_certificate w b f t p n)
end PPAC.Migration.Internal.ObjectSyntaxAtoms
