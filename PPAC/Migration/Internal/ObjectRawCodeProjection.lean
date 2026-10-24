import PPAC.Migration.Internal.RawCodeGetLaws

/-! 原任意外壳投影、全内部get值及递归方程的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectRawCodeProjection
open Source SourceAlgebra SourceLogic OmegaSyntax

def pairingComponentExistsSentence {m} (raw head : Bool) (w x : Fin m) : Source.Sentence := ((omega w).imp ((PairingProjectionSyntax.hasStep raw head w x))).close

theorem source_pairingComponentExists {m} (raw head : Bool) (w x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pairingComponentExistsSentence raw head w x) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PairingProjection.exists_step raw head w x h0

theorem pairingComponentExists_kernel_certificate {m} (raw head : Bool) (w x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pairingComponentExistsSentence raw head w x)) := TheoryTransport.sentence (source_pairingComponentExists raw head w x)

theorem native_pairingComponentExists {m} (raw head : Bool) (w x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pairingComponentExistsSentence raw head w x)) := ZFReplay.replay (pairingComponentExists_kernel_certificate raw head w x)

def pairingComponentUniqueSentence {m} (raw head : Bool) (w x y z : Fin m) : Source.Sentence := ((omega w).imp ((PairingProjectionSyntax.step raw head w x y).imp ((PairingProjectionSyntax.step raw head w x z).imp ((Formula.equal y z))))).close

theorem source_pairingComponentUnique {m} (raw head : Bool) (w x y z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pairingComponentUniqueSentence raw head w x y z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PairingProjectionSyntax.step raw head w x z) (Context.add (PairingProjectionSyntax.step raw head w x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PairingProjectionSyntax.step raw head w x y) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PairingProjectionSyntax.step raw head w x z) := .hyp (Or.inl rfl)
  exact PairingProjection.functional_point hZ raw head w x y z h0 h1 h2

theorem pairingComponentUnique_kernel_certificate {m} (raw head : Bool) (w x y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pairingComponentUniqueSentence raw head w x y z)) := TheoryTransport.sentence (source_pairingComponentUnique raw head w x y z)

theorem native_pairingComponentUnique {m} (raw head : Bool) (w x y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pairingComponentUniqueSentence raw head w x y z)) := ZFReplay.replay (pairingComponentUnique_kernel_certificate raw head w x y z)

def barePairEveryNaturalDecodesSentence {m} (head : Bool) (w x : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem x w).imp ((PairingProjectionSyntax.hasSelected false head w x)))).close

theorem source_barePairEveryNaturalDecodes {m} (head : Bool) (w x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (barePairEveryNaturalDecodesSentence head w x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem x w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem x w) := .hyp (Or.inl rfl)
  exact PairingProjectionNatural.bare_selected hZ head w x h0 h1

theorem barePairEveryNaturalDecodes_kernel_certificate {m} (head : Bool) (w x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (barePairEveryNaturalDecodesSentence head w x)) := TheoryTransport.sentence (source_barePairEveryNaturalDecodes head w x)

theorem native_barePairEveryNaturalDecodes {m} (head : Bool) (w x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (barePairEveryNaturalDecodesSentence head w x)) := ZFReplay.replay (barePairEveryNaturalDecodes_kernel_certificate head w x)

def rawEveryPositiveNaturalDecodesSentence {m} (head : Bool) (w x : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem x w).imp (((empty x).neg).imp ((PairingProjectionSyntax.hasSelected true head w x))))).close

theorem source_rawEveryPositiveNaturalDecodes {m} (head : Bool) (w x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawEveryPositiveNaturalDecodesSentence head w x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((empty x).neg) (Context.add (Formula.mem x w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem x w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ ((empty x).neg) := .hyp (Or.inl rfl)
  exact PairingProjectionNatural.raw_selected hZ head w x h0 h1 h2

theorem rawEveryPositiveNaturalDecodes_kernel_certificate {m} (head : Bool) (w x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawEveryPositiveNaturalDecodesSentence head w x)) := TheoryTransport.sentence (source_rawEveryPositiveNaturalDecodes head w x)

theorem native_rawEveryPositiveNaturalDecodes {m} (head : Bool) (w x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawEveryPositiveNaturalDecodesSentence head w x)) := ZFReplay.replay (rawEveryPositiveNaturalDecodes_kernel_certificate head w x)

def rawZeroComponentSentence {m} (head : Bool) (w x y : Fin m) : Source.Sentence := ((empty x).imp ((PairingProjectionSyntax.step true head w x y).imp ((empty y)))).close

theorem source_rawZeroComponent {m} (head : Bool) (w x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawZeroComponentSentence head w x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PairingProjectionSyntax.step true head w x y) (Context.add (empty x) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (empty x) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PairingProjectionSyntax.step true head w x y) := .hyp (Or.inl rfl)
  exact PairingProjectionNatural.raw_zero head w x y h0 h1

theorem rawZeroComponent_kernel_certificate {m} (head : Bool) (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawZeroComponentSentence head w x y)) := TheoryTransport.sentence (source_rawZeroComponent head w x y)

theorem native_rawZeroComponent {m} (head : Bool) (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawZeroComponentSentence head w x y)) := ZFReplay.replay (rawZeroComponent_kernel_certificate head w x y)

def rawUnselectedNaturalIsZeroSentence {m} (head : Bool) (w x : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem x w).imp (((PairingProjectionSyntax.hasSelected true head w x).neg).imp ((empty x))))).close

theorem source_rawUnselectedNaturalIsZero {m} (head : Bool) (w x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawUnselectedNaturalIsZeroSentence head w x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((PairingProjectionSyntax.hasSelected true head w x).neg) (Context.add (Formula.mem x w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem x w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ ((PairingProjectionSyntax.hasSelected true head w x).neg) := .hyp (Or.inl rfl)
  exact PairingProjectionNatural.natural_raw_unselected_zero hZ head w x h0 h1 h2

theorem rawUnselectedNaturalIsZero_kernel_certificate {m} (head : Bool) (w x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawUnselectedNaturalIsZeroSentence head w x)) := TheoryTransport.sentence (source_rawUnselectedNaturalIsZero head w x)

theorem native_rawUnselectedNaturalIsZero {m} (head : Bool) (w x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawUnselectedNaturalIsZeroSentence head w x)) := ZFReplay.replay (rawUnselectedNaturalIsZero_kernel_certificate head w x)

def rawHeadTailExistsSentence {m} (head : Bool) (w x : Fin m) : Source.Sentence := ((omega w).imp ((RawCodeProjectionSyntax.hasStep head w x))).close

theorem source_rawHeadTailExists {m} (head : Bool) (w x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawHeadTailExistsSentence head w x) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact RawCodeProjection.exists_step head w x h0

theorem rawHeadTailExists_kernel_certificate {m} (head : Bool) (w x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawHeadTailExistsSentence head w x)) := TheoryTransport.sentence (source_rawHeadTailExists head w x)

theorem native_rawHeadTailExists {m} (head : Bool) (w x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawHeadTailExistsSentence head w x)) := ZFReplay.replay (rawHeadTailExists_kernel_certificate head w x)

def rawHeadTailUniqueSentence {m} (head : Bool) (w x y z : Fin m) : Source.Sentence := ((omega w).imp ((RawCodeProjectionSyntax.step head w x y).imp ((RawCodeProjectionSyntax.step head w x z).imp ((Formula.equal y z))))).close

theorem source_rawHeadTailUnique {m} (head : Bool) (w x y z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawHeadTailUniqueSentence head w x y z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (RawCodeProjectionSyntax.step head w x z) (Context.add (RawCodeProjectionSyntax.step head w x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (RawCodeProjectionSyntax.step head w x y) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (RawCodeProjectionSyntax.step head w x z) := .hyp (Or.inl rfl)
  exact RawCodeProjection.functional_point hZ head w x y z h0 h1 h2

theorem rawHeadTailUnique_kernel_certificate {m} (head : Bool) (w x y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawHeadTailUniqueSentence head w x y z)) := TheoryTransport.sentence (source_rawHeadTailUnique head w x y z)

theorem native_rawHeadTailUnique {m} (head : Bool) (w x y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawHeadTailUniqueSentence head w x y z)) := ZFReplay.replay (rawHeadTailUnique_kernel_certificate head w x y z)

def rawHeadTailRangeSentence {m} (head : Bool) (w x y : Fin m) : Source.Sentence := ((omega w).imp ((RawCodeProjectionSyntax.step head w x y).imp ((Formula.mem y w)))).close

theorem source_rawHeadTailRange {m} (head : Bool) (w x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawHeadTailRangeSentence head w x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (RawCodeProjectionSyntax.step head w x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (RawCodeProjectionSyntax.step head w x y) := .hyp (Or.inl rfl)
  exact RawCodeProjection.range_point hZ head w x y h0 h1

theorem rawHeadTailRange_kernel_certificate {m} (head : Bool) (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawHeadTailRangeSentence head w x y)) := TheoryTransport.sentence (source_rawHeadTailRange head w x y)

theorem native_rawHeadTailRange {m} (head : Bool) (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawHeadTailRangeSentence head w x y)) := ZFReplay.replay (rawHeadTailRange_kernel_certificate head w x y)

def rawHeadTailZeroIffSentence {m} (head : Bool) (w x y : Fin m) : Source.Sentence := ((omega w).imp ((empty x).imp (((RawCodeProjectionSyntax.step head w x y).iff (empty y))))).close

theorem source_rawHeadTailZeroIff {m} (head : Bool) (w x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawHeadTailZeroIffSentence head w x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty x) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty x) := .hyp (Or.inl rfl)
  exact RawCodeProjection.zero_iff hZ head w x y h0 h1

theorem rawHeadTailZeroIff_kernel_certificate {m} (head : Bool) (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawHeadTailZeroIffSentence head w x y)) := TheoryTransport.sentence (source_rawHeadTailZeroIff head w x y)

theorem native_rawHeadTailZeroIff {m} (head : Bool) (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawHeadTailZeroIffSentence head w x y)) := ZFReplay.replay (rawHeadTailZeroIff_kernel_certificate head w x y)

def arbitraryRawTagHeadTailIffSentence {m} (head : Bool) (w tag p a b x y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem tag w).imp ((Formula.mem p w).imp ((Formula.mem a w).imp ((Formula.mem b w).imp ((StructuralNodeSyntax.raw w tag p x).imp ((GodelPairSyntax.code w a b p).imp (((RawCodeProjectionSyntax.step head w x y).iff (Formula.equal y (if head then a else b))))))))))).close

theorem source_arbitraryRawTagHeadTailIff {m} (head : Bool) (w tag p a b x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (arbitraryRawTagHeadTailIffSentence head w tag p a b x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (GodelPairSyntax.code w a b p) (Context.add (StructuralNodeSyntax.raw w tag p x) (Context.add (Formula.mem b w) (Context.add (Formula.mem a w) (Context.add (Formula.mem p w) (Context.add (Formula.mem tag w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (Formula.mem tag w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (Formula.mem p w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (Formula.mem a w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (StructuralNodeSyntax.raw w tag p x) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (GodelPairSyntax.code w a b p) := .hyp (Or.inl rfl)
  exact RawCodeProjection.on_raw_pair_iff hZ head w tag p a b x y h0 h1 h2 h3 h4 h5 h6

theorem arbitraryRawTagHeadTailIff_kernel_certificate {m} (head : Bool) (w tag p a b x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (arbitraryRawTagHeadTailIffSentence head w tag p a b x y)) := TheoryTransport.sentence (source_arbitraryRawTagHeadTailIff head w tag p a b x y)

theorem native_arbitraryRawTagHeadTailIff {m} (head : Bool) (w tag p a b x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (arbitraryRawTagHeadTailIffSentence head w tag p a b x y)) := ZFReplay.replay (arbitraryRawTagHeadTailIff_kernel_certificate head w tag p a b x y)

def rawNaturalIterationFiberSentence {m} (head : Bool) (w x i : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem i w).imp ((RawCodeProjectionSyntax.iterationFiber head w x i)))).close

theorem source_rawNaturalIterationFiber {m} (head : Bool) (w x i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawNaturalIterationFiberSentence head w x i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem i w) := .hyp (Or.inl rfl)
  exact RawCodeProjectionRecursion.actual_fiber hZ head w x i h0 h1

theorem rawNaturalIterationFiber_kernel_certificate {m} (head : Bool) (w x i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawNaturalIterationFiberSentence head w x i)) := TheoryTransport.sentence (source_rawNaturalIterationFiber head w x i)

theorem native_rawNaturalIterationFiber {m} (head : Bool) (w x i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawNaturalIterationFiberSentence head w x i)) := ZFReplay.replay (rawNaturalIterationFiber_kernel_certificate head w x i)

def rawGetExistsSentence {m} (w x i : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem i w).imp ((RawCodeGetSyntax.existsGet w x i)))).close

theorem source_rawGetExists {m} (w x i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawGetExistsSentence w x i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem i w) := .hyp (Or.inl rfl)
  exact RawCodeGetValues.exists_value hZ w x i h0 h1

theorem rawGetExists_kernel_certificate {m} (w x i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawGetExistsSentence w x i)) := TheoryTransport.sentence (source_rawGetExists w x i)

theorem native_rawGetExists {m} (w x i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawGetExistsSentence w x i)) := ZFReplay.replay (rawGetExists_kernel_certificate w x i)

def rawGetUniqueSentence {m} (w x i y z : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem i w).imp ((RawCodeGetSyntax.get w x i y).imp ((RawCodeGetSyntax.get w x i z).imp ((Formula.equal y z)))))).close

theorem source_rawGetUnique {m} (w x i y z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawGetUniqueSentence w x i y z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (RawCodeGetSyntax.get w x i z) (Context.add (RawCodeGetSyntax.get w x i y) (Context.add (Formula.mem i w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem i w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (RawCodeGetSyntax.get w x i y) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (RawCodeGetSyntax.get w x i z) := .hyp (Or.inl rfl)
  exact RawCodeGetValues.unique hZ w x i y z h0 h1 h2 h3

theorem rawGetUnique_kernel_certificate {m} (w x i y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawGetUniqueSentence w x i y z)) := TheoryTransport.sentence (source_rawGetUnique w x i y z)

theorem native_rawGetUnique {m} (w x i y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawGetUniqueSentence w x i y z)) := ZFReplay.replay (rawGetUnique_kernel_certificate w x i y z)

def rawGetFiberSentence {m} (w x i : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem i w).imp ((RawCodeGetSyntax.fiber w x i)))).close

theorem source_rawGetFiber {m} (w x i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawGetFiberSentence w x i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem i w) := .hyp (Or.inl rfl)
  exact RawCodeGetValues.exists_unique hZ w x i h0 h1

theorem rawGetFiber_kernel_certificate {m} (w x i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawGetFiberSentence w x i)) := TheoryTransport.sentence (source_rawGetFiber w x i)

theorem native_rawGetFiber {m} (w x i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawGetFiberSentence w x i)) := ZFReplay.replay (rawGetFiber_kernel_certificate w x i)

def rawGetRangeSentence {m} (w x i y : Fin m) : Source.Sentence := ((omega w).imp ((RawCodeGetSyntax.get w x i y).imp ((Formula.mem y w)))).close

theorem source_rawGetRange {m} (w x i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawGetRangeSentence w x i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (RawCodeGetSyntax.get w x i y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (RawCodeGetSyntax.get w x i y) := .hyp (Or.inl rfl)
  exact RawCodeGetValues.range hZ w x i y h0 h1

theorem rawGetRange_kernel_certificate {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawGetRangeSentence w x i y)) := TheoryTransport.sentence (source_rawGetRange w x i y)

theorem native_rawGetRange {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawGetRangeSentence w x i y)) := ZFReplay.replay (rawGetRange_kernel_certificate w x i y)

def rawGetZeroEquationSentence {m} (w x i y : Fin m) : Source.Sentence := ((omega w).imp ((empty i).imp (((RawCodeGetSyntax.get w x i y).iff (RawCodeProjectionSyntax.step true w x y))))).close

theorem source_rawGetZeroEquation {m} (w x i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawGetZeroEquationSentence w x i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty i) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty i) := .hyp (Or.inl rfl)
  exact RawCodeGetLaws.zero_iff hZ w x i y h0 h1

theorem rawGetZeroEquation_kernel_certificate {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawGetZeroEquationSentence w x i y)) := TheoryTransport.sentence (source_rawGetZeroEquation w x i y)

theorem native_rawGetZeroEquation {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawGetZeroEquationSentence w x i y)) := ZFReplay.replay (rawGetZeroEquation_kernel_certificate w x i y)

def rawGetSuccessorEquationSentence {m} (w x t r s y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem r w).imp ((successor s r).imp ((RawCodeProjectionSyntax.step false w x t).imp (((RawCodeGetSyntax.get w x s y).iff (RawCodeGetSyntax.get w t r y))))))).close

theorem source_rawGetSuccessorEquation {m} (w x t r s y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawGetSuccessorEquationSentence w x t r s y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (RawCodeProjectionSyntax.step false w x t) (Context.add (successor s r) (Context.add (Formula.mem r w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem r w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor s r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (RawCodeProjectionSyntax.step false w x t) := .hyp (Or.inl rfl)
  exact RawCodeGetLaws.successor_iff hZ w x t r s y h0 h1 h2 h3

theorem rawGetSuccessorEquation_kernel_certificate {m} (w x t r s y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawGetSuccessorEquationSentence w x t r s y)) := TheoryTransport.sentence (source_rawGetSuccessorEquation w x t r s y)

theorem native_rawGetSuccessorEquation {m} (w x t r s y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawGetSuccessorEquationSentence w x t r s y)) := ZFReplay.replay (rawGetSuccessorEquation_kernel_certificate w x t r s y)

end PPAC.Migration.Internal.ObjectRawCodeProjection
