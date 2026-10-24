import PPAC.Migration.Internal.PacketAffineLiteral

/-! All internal Packet radix-affine arithmetic, actual literal systems and recursive equations; full Packet Horn/byte bridge remains unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectPacketAffine
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetAffineExistsUniqueSentence {m} (w B d t : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((Formula.mem d B).imp ((Formula.mem t w).imp ((PacketAffineSyntax.fiber w B d t)))))).close

theorem source_packetAffineExistsUnique {m} (w B d t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineExistsUniqueSentence w B d t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem t w) (Context.add (Formula.mem d B) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem d B) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem t w) := .hyp (Or.inl rfl)
  exact PacketAffineFiber.exists_fiber hZ w B d t h0 h1 h2 h3

theorem packetAffineExistsUnique_kernel_certificate {m} (w B d t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineExistsUniqueSentence w B d t)) := TheoryTransport.sentence (source_packetAffineExistsUnique w B d t)

theorem native_packetAffineExistsUnique {m} (w B d t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineExistsUniqueSentence w B d t)) := ZFReplay.replay (packetAffineExistsUnique_kernel_certificate w B d t)

def packetAffineOutputsUniqueSentence {m} (w B d t n a : Fin m) : Source.Sentence := ((omega w).imp ((PacketAffineSyntax.affine w B d t n).imp ((PacketAffineSyntax.affine w B d t a).imp ((Formula.equal n a))))).close

theorem source_packetAffineOutputsUnique {m} (w B d t n a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineOutputsUniqueSentence w B d t n a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineSyntax.affine w B d t a) (Context.add (PacketAffineSyntax.affine w B d t n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketAffineSyntax.affine w B d t n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketAffineSyntax.affine w B d t a) := .hyp (Or.inl rfl)
  exact PacketAffineCore.unique hZ w B d t n a h0 h1 h2

theorem packetAffineOutputsUnique_kernel_certificate {m} (w B d t n a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineOutputsUniqueSentence w B d t n a)) := TheoryTransport.sentence (source_packetAffineOutputsUnique w B d t n a)

theorem native_packetAffineOutputsUnique {m} (w B d t n a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineOutputsUniqueSentence w B d t n a)) := ZFReplay.replay (packetAffineOutputsUnique_kernel_certificate w B d t n a)

def packetAffineZeroIffSentence {m} (w B d z n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp (((PacketAffineSyntax.affine w B d z n).iff ((Formula.mem d B).conj (.equal n d))))))).close

theorem source_packetAffineZeroIff {m} (w B d z n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineZeroIffSentence w B d z n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact PacketAffineZero.zero_iff hZ w B d z n h0 h1 h2

theorem packetAffineZeroIff_kernel_certificate {m} (w B d z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineZeroIffSentence w B d z n)) := TheoryTransport.sentence (source_packetAffineZeroIff w B d z n)

theorem native_packetAffineZeroIff {m} (w B d z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineZeroIffSentence w B d z n)) := ZFReplay.replay (packetAffineZeroIff_kernel_certificate w B d z n)

def packetAffineAdvanceSentence {m} (w B d t a s n : Fin m) : Source.Sentence := ((omega w).imp ((PacketAffineSyntax.affine w B d t a).imp ((successor s t).imp ((NaturalAdditionSyntax.sum w a B n).imp ((PacketAffineSyntax.affine w B d s n)))))).close

theorem source_packetAffineAdvance {m} (w B d t a s n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineAdvanceSentence w B d t a s n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (NaturalAdditionSyntax.sum w a B n) (Context.add (successor s t) (Context.add (PacketAffineSyntax.affine w B d t a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PacketAffineSyntax.affine w B d t a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor s t) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (NaturalAdditionSyntax.sum w a B n) := .hyp (Or.inl rfl)
  exact PacketAffineStep.advance hZ w B d t a s n h0 h1 h2 h3

theorem packetAffineAdvance_kernel_certificate {m} (w B d t a s n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineAdvanceSentence w B d t a s n)) := TheoryTransport.sentence (source_packetAffineAdvance w B d t a s n)

theorem native_packetAffineAdvance {m} (w B d t a s n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineAdvanceSentence w B d t a s n)) := ZFReplay.replay (packetAffineAdvance_kernel_certificate w B d t a s n)

def packetAffineRecursiveIffSentence {m} (w B d t n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp (((PacketAffineSyntax.affine w B d t n).iff (PacketAffineSyntax.criterion w B d t n))))).close

theorem source_packetAffineRecursiveIff {m} (w B d t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineRecursiveIffSentence w B d t n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inl rfl)
  exact PacketAffineRecursive.recursive_iff hZ w B d t n h0 h1

theorem packetAffineRecursiveIff_kernel_certificate {m} (w B d t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineRecursiveIffSentence w B d t n)) := TheoryTransport.sentence (source_packetAffineRecursiveIff w B d t n)

theorem native_packetAffineRecursiveIff {m} (w B d t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineRecursiveIffSentence w B d t n)) := ZFReplay.replay (packetAffineRecursiveIff_kernel_certificate w B d t n)

def packetAffineAllInternalRecursiveLawSentence {m} (w B : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketAffineRecursive.universalLaw w B)))).close

theorem source_packetAffineAllInternalRecursiveLaw {m} (w B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineAllInternalRecursiveLawSentence w B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inl rfl)
  exact PacketAffineRecursive.all_law hZ w B h0 h1

theorem packetAffineAllInternalRecursiveLaw_kernel_certificate {m} (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineAllInternalRecursiveLawSentence w B)) := TheoryTransport.sentence (source_packetAffineAllInternalRecursiveLaw w B)

theorem native_packetAffineAllInternalRecursiveLaw {m} (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineAllInternalRecursiveLawSentence w B)) := ZFReplay.replay (packetAffineAllInternalRecursiveLaw_kernel_certificate w B)

def packetAffineAllInternalFibersSentence {m} (w B : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketAffineLiteralSyntax.totalLaw w B)))).close

theorem source_packetAffineAllInternalFibers {m} (w B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineAllInternalFibersSentence w B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inl rfl)
  exact PacketAffineLiteral.all_fibers hZ w B h0 h1

theorem packetAffineAllInternalFibers_kernel_certificate {m} (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineAllInternalFibersSentence w B)) := TheoryTransport.sentence (source_packetAffineAllInternalFibers w B)

theorem native_packetAffineAllInternalFibers {m} (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineAllInternalFibersSentence w B)) := ZFReplay.replay (packetAffineAllInternalFibers_kernel_certificate w B)

def packetAffineLiteralSystemExistsSentence {m} (wide : Bool) (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketAffineLiteralSyntax.existsSystem wide w))).close

theorem source_packetAffineLiteralSystemExists {m} (wide : Bool) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineLiteralSystemExistsSentence wide w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketAffineLiteral.exists_system hZ wide w h0

theorem packetAffineLiteralSystemExists_kernel_certificate {m} (wide : Bool) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineLiteralSystemExistsSentence wide w)) := TheoryTransport.sentence (source_packetAffineLiteralSystemExists wide w)

theorem native_packetAffineLiteralSystemExists {m} (wide : Bool) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineLiteralSystemExistsSentence wide w)) := ZFReplay.replay (packetAffineLiteralSystemExists_kernel_certificate wide w)

def packetAffineLiteralFramesUniqueSentence {m} (wide : Bool) (w B C : Fin m) : Source.Sentence := ((PacketAffineLiteralSyntax.frame wide w B).imp ((PacketAffineLiteralSyntax.frame wide w C).imp ((Formula.equal B C)))).close

theorem source_packetAffineLiteralFramesUnique {m} (wide : Bool) (w B C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineLiteralFramesUniqueSentence wide w B C) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineLiteralSyntax.frame wide w C) (Context.add (PacketAffineLiteralSyntax.frame wide w B) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (PacketAffineLiteralSyntax.frame wide w B) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketAffineLiteralSyntax.frame wide w C) := .hyp (Or.inl rfl)
  exact PacketAffineLiteral.frame_unique hZ wide w B C h0 h1

theorem packetAffineLiteralFramesUnique_kernel_certificate {m} (wide : Bool) (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineLiteralFramesUniqueSentence wide w B C)) := TheoryTransport.sentence (source_packetAffineLiteralFramesUnique wide w B C)

theorem native_packetAffineLiteralFramesUnique {m} (wide : Bool) (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineLiteralFramesUniqueSentence wide w B C)) := ZFReplay.replay (packetAffineLiteralFramesUnique_kernel_certificate wide w B C)

def packetAffineZeroBelowLiteralBaseSentence {m} (wide : Bool) (w B z : Fin m) : Source.Sentence := ((PacketAffineLiteralSyntax.frame wide w B).imp ((empty z).imp ((Formula.mem z B)))).close

theorem source_packetAffineZeroBelowLiteralBase {m} (wide : Bool) (w B z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineZeroBelowLiteralBaseSentence wide w B z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (PacketAffineLiteralSyntax.frame wide w B) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (PacketAffineLiteralSyntax.frame wide w B) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact PacketAffineLiteral.zero_below hZ wide w B z h0 h1

theorem packetAffineZeroBelowLiteralBase_kernel_certificate {m} (wide : Bool) (w B z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineZeroBelowLiteralBaseSentence wide w B z)) := TheoryTransport.sentence (source_packetAffineZeroBelowLiteralBase wide w B z)

theorem native_packetAffineZeroBelowLiteralBase {m} (wide : Bool) (w B z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineZeroBelowLiteralBaseSentence wide w B z)) := ZFReplay.replay (packetAffineZeroBelowLiteralBase_kernel_certificate wide w B z)

def packetAffineTwoBelowLiteralBaseSentence {m} (wide : Bool) (w B e : Fin m) : Source.Sentence := ((PacketAffineLiteralSyntax.frame wide w B).imp ((SyntaxNumeralSyntax.numeral 2 e).imp ((Formula.mem e B)))).close

theorem source_packetAffineTwoBelowLiteralBase {m} (wide : Bool) (w B e : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineTwoBelowLiteralBaseSentence wide w B e) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 2 e) (Context.add (PacketAffineLiteralSyntax.frame wide w B) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (PacketAffineLiteralSyntax.frame wide w B) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 2 e) := .hyp (Or.inl rfl)
  exact PacketAffineLiteral.two_below hZ wide w B e h0 h1

theorem packetAffineTwoBelowLiteralBase_kernel_certificate {m} (wide : Bool) (w B e : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineTwoBelowLiteralBaseSentence wide w B e)) := TheoryTransport.sentence (source_packetAffineTwoBelowLiteralBase wide w B e)

theorem native_packetAffineTwoBelowLiteralBase {m} (wide : Bool) (w B e : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineTwoBelowLiteralBaseSentence wide w B e)) := ZFReplay.replay (packetAffineTwoBelowLiteralBase_kernel_certificate wide w B e)

def packetAffineRejectDigitSentence {m} (w B d t n : Fin m) : Source.Sentence := (((Formula.mem d B).neg).imp (((PacketAffineSyntax.affine w B d t n).neg))).close

theorem source_packetAffineRejectDigit {m} (w B d t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineRejectDigitSentence w B d t n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem d B).neg) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ ((Formula.mem d B).neg) := .hyp (Or.inl rfl)
  exact PacketAffineFiber.reject_digit w B d t n h0

theorem packetAffineRejectDigit_kernel_certificate {m} (w B d t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineRejectDigitSentence w B d t n)) := TheoryTransport.sentence (source_packetAffineRejectDigit w B d t n)

theorem native_packetAffineRejectDigit {m} (w B d t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineRejectDigitSentence w B d t n)) := ZFReplay.replay (packetAffineRejectDigit_kernel_certificate w B d t n)

def packetAffineRejectTailSentence {m} (w B d t n : Fin m) : Source.Sentence := (((Formula.mem t w).neg).imp (((PacketAffineSyntax.affine w B d t n).neg))).close

theorem source_packetAffineRejectTail {m} (w B d t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineRejectTailSentence w B d t n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem t w).neg) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ ((Formula.mem t w).neg) := .hyp (Or.inl rfl)
  exact PacketAffineFiber.reject_tail w B d t n h0

theorem packetAffineRejectTail_kernel_certificate {m} (w B d t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineRejectTailSentence w B d t n)) := TheoryTransport.sentence (source_packetAffineRejectTail w B d t n)

theorem native_packetAffineRejectTail {m} (w B d t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineRejectTailSentence w B d t n)) := ZFReplay.replay (packetAffineRejectTail_kernel_certificate w B d t n)

def packetAffineRejectOutputSentence {m} (w B d t n : Fin m) : Source.Sentence := (((Formula.mem n w).neg).imp (((PacketAffineSyntax.affine w B d t n).neg))).close

theorem source_packetAffineRejectOutput {m} (w B d t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineRejectOutputSentence w B d t n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem n w).neg) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ ((Formula.mem n w).neg) := .hyp (Or.inl rfl)
  exact PacketAffineFiber.reject_output w B d t n h0

theorem packetAffineRejectOutput_kernel_certificate {m} (w B d t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineRejectOutputSentence w B d t n)) := TheoryTransport.sentence (source_packetAffineRejectOutput w B d t n)

theorem native_packetAffineRejectOutput {m} (w B d t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineRejectOutputSentence w B d t n)) := ZFReplay.replay (packetAffineRejectOutput_kernel_certificate w B d t n)

end PPAC.Migration.Internal.ObjectPacketAffine
