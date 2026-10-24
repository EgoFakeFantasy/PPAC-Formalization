import PPAC.Migration.Internal.PacketDivisionValue

/-! All internal radix division, unique inverse fibers and actual relational Packet acceptance; full Basic AST and varint bridge remain unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectPacketDivision
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetDivisionIncrementSentence {m} (w B d q n s e : Fin m) : Source.Sentence := ((omega w).imp ((PacketAffineSyntax.affine w B d q n).imp ((successor s n).imp ((successor e d).imp ((Formula.mem e B).imp ((PacketAffineSyntax.affine w B e q s))))))).close

theorem source_packetDivisionIncrement {m} (w B d q n s e : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDivisionIncrementSentence w B d q n s e) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem e B) (Context.add (successor e d) (Context.add (successor s n) (Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (successor s n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (successor e d) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (Formula.mem e B) := .hyp (Or.inl rfl)
  exact PacketDivisionTransitions.increment hZ w B d q n s e h0 h1 h2 h3 h4

theorem packetDivisionIncrement_kernel_certificate {m} (w B d q n s e : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDivisionIncrementSentence w B d q n s e)) := TheoryTransport.sentence (source_packetDivisionIncrement w B d q n s e)

theorem native_packetDivisionIncrement {m} (w B d q n s e : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDivisionIncrementSentence w B d q n s e)) := ZFReplay.replay (packetDivisionIncrement_kernel_certificate w B d q n s e)

def packetDivisionCarrySentence {m} (w B d q n s Q z : Fin m) : Source.Sentence := ((omega w).imp ((PacketAffineSyntax.affine w B d q n).imp ((successor s n).imp ((successor B d).imp ((successor Q q).imp ((OmegaSyntax.empty z).imp ((Formula.mem z B).imp ((PacketAffineSyntax.affine w B z Q s))))))))).close

theorem source_packetDivisionCarry {m} (w B d q n s Q z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDivisionCarrySentence w B d q n s Q z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem z B) (Context.add (OmegaSyntax.empty z) (Context.add (successor Q q) (Context.add (successor B d) (Context.add (successor s n) (Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (successor s n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (successor B d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (successor Q q) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (OmegaSyntax.empty z) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (Formula.mem z B) := .hyp (Or.inl rfl)
  exact PacketDivisionTransitions.carry hZ w B d q n s Q z h0 h1 h2 h3 h4 h5 h6

theorem packetDivisionCarry_kernel_certificate {m} (w B d q n s Q z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDivisionCarrySentence w B d q n s Q z)) := TheoryTransport.sentence (source_packetDivisionCarry w B d q n s Q z)

theorem native_packetDivisionCarry {m} (w B d q n s Q z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDivisionCarrySentence w B d q n s Q z)) := ZFReplay.replay (packetDivisionCarry_kernel_certificate w B d q n s Q z)

def packetDivisionSuccessorExistsSentence {m} (wide : Bool) (w B n s : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketDivisionSyntax.decomposes w B n).imp ((successor s n).imp ((PacketDivisionSyntax.decomposes w B s)))))).close

theorem source_packetDivisionSuccessorExists {m} (wide : Bool) (w B n s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDivisionSuccessorExistsSentence wide w B n s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor s n) (Context.add (PacketDivisionSyntax.decomposes w B n) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketDivisionSyntax.decomposes w B n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor s n) := .hyp (Or.inl rfl)
  exact PacketDivisionStep.from_decomposition hZ wide w B n s h0 h1 h2 h3

theorem packetDivisionSuccessorExists_kernel_certificate {m} (wide : Bool) (w B n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDivisionSuccessorExistsSentence wide w B n s)) := TheoryTransport.sentence (source_packetDivisionSuccessorExists wide w B n s)

theorem native_packetDivisionSuccessorExists {m} (wide : Bool) (w B n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDivisionSuccessorExistsSentence wide w B n s)) := ZFReplay.replay (packetDivisionSuccessorExists_kernel_certificate wide w B n s)

def packetDivisionAllNaturalOutputsSentence {m} (wide : Bool) (w B : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((.all ((Formula.mem (Fin.last m) w.castSucc).imp (PacketDivisionSyntax.decomposes w.castSucc B.castSucc (Fin.last m))))))).close

theorem source_packetDivisionAllNaturalOutputs {m} (wide : Bool) (w B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDivisionAllNaturalOutputsSentence wide w B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inl rfl)
  exact PacketDivisionInduction.all_decomposes hZ wide w B h0 h1

theorem packetDivisionAllNaturalOutputs_kernel_certificate {m} (wide : Bool) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDivisionAllNaturalOutputsSentence wide w B)) := TheoryTransport.sentence (source_packetDivisionAllNaturalOutputs wide w B)

theorem native_packetDivisionAllNaturalOutputs {m} (wide : Bool) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDivisionAllNaturalOutputsSentence wide w B)) := ZFReplay.replay (packetDivisionAllNaturalOutputs_kernel_certificate wide w B)

def packetDivisionDecompositionExistsSentence {m} (wide : Bool) (w B n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((Formula.mem n w).imp ((PacketDivisionSyntax.decomposes w B n))))).close

theorem source_packetDivisionDecompositionExists {m} (wide : Bool) (w B n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDivisionDecompositionExistsSentence wide w B n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem n w) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem n w) := .hyp (Or.inl rfl)
  exact PacketDivisionInduction.exists_decomposition hZ wide w B n h0 h1 h2

theorem packetDivisionDecompositionExists_kernel_certificate {m} (wide : Bool) (w B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDivisionDecompositionExistsSentence wide w B n)) := TheoryTransport.sentence (source_packetDivisionDecompositionExists wide w B n)

theorem native_packetDivisionDecompositionExists {m} (wide : Bool) (w B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDivisionDecompositionExistsSentence wide w B n)) := ZFReplay.replay (packetDivisionDecompositionExists_kernel_certificate wide w B n)

def packetDivisionLowerBandSentence {m} (w B d q n p : Fin m) : Source.Sentence := ((omega w).imp ((PacketAffineSyntax.affine w B d q n).imp ((NaturalMultiplicationSyntax.product w B q p).imp ((NaturalAdditionBounds.below p n))))).close

theorem source_packetDivisionLowerBand {m} (w B d q n p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDivisionLowerBandSentence w B d q n p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (NaturalMultiplicationSyntax.product w B q p) (Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (NaturalMultiplicationSyntax.product w B q p) := .hyp (Or.inl rfl)
  exact PacketDivisionBand.lower hZ w B d q n p h0 h1 h2

theorem packetDivisionLowerBand_kernel_certificate {m} (w B d q n p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDivisionLowerBandSentence w B d q n p)) := TheoryTransport.sentence (source_packetDivisionLowerBand w B d q n p)

theorem native_packetDivisionLowerBand {m} (w B d q n p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDivisionLowerBandSentence w B d q n p)) := ZFReplay.replay (packetDivisionLowerBand_kernel_certificate w B d q n p)

def packetDivisionUpperBandSentence {m} (w B d q n Q y : Fin m) : Source.Sentence := ((omega w).imp ((PacketAffineSyntax.affine w B d q n).imp ((successor Q q).imp ((NaturalMultiplicationSyntax.product w B Q y).imp ((Formula.mem n y)))))).close

theorem source_packetDivisionUpperBand {m} (w B d q n Q y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDivisionUpperBandSentence w B d q n Q y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (NaturalMultiplicationSyntax.product w B Q y) (Context.add (successor Q q) (Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor Q q) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (NaturalMultiplicationSyntax.product w B Q y) := .hyp (Or.inl rfl)
  exact PacketDivisionBand.upper hZ w B d q n Q y h0 h1 h2 h3

theorem packetDivisionUpperBand_kernel_certificate {m} (w B d q n Q y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDivisionUpperBandSentence w B d q n Q y)) := TheoryTransport.sentence (source_packetDivisionUpperBand w B d q n Q y)

theorem native_packetDivisionUpperBand {m} (w B d q n Q y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDivisionUpperBandSentence w B d q n Q y)) := ZFReplay.replay (packetDivisionUpperBand_kernel_certificate w B d q n Q y)

def packetDivisionQuotientUniqueSentence {m} (w B d q e p n : Fin m) : Source.Sentence := ((omega w).imp ((PacketAffineSyntax.affine w B d q n).imp ((PacketAffineSyntax.affine w B e p n).imp ((Formula.equal q p))))).close

theorem source_packetDivisionQuotientUnique {m} (w B d q e p n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDivisionQuotientUniqueSentence w B d q e p n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineSyntax.affine w B e p n) (Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketAffineSyntax.affine w B e p n) := .hyp (Or.inl rfl)
  exact PacketDivisionUnique.quotient_equal hZ w B d q e p n h0 h1 h2

theorem packetDivisionQuotientUnique_kernel_certificate {m} (w B d q e p n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDivisionQuotientUniqueSentence w B d q e p n)) := TheoryTransport.sentence (source_packetDivisionQuotientUnique w B d q e p n)

theorem native_packetDivisionQuotientUnique {m} (w B d q e p n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDivisionQuotientUniqueSentence w B d q e p n)) := ZFReplay.replay (packetDivisionQuotientUnique_kernel_certificate w B d q e p n)

def packetDivisionRemainderUniqueSentence {m} (w B d e q n : Fin m) : Source.Sentence := ((omega w).imp ((PacketAffineSyntax.affine w B d q n).imp ((PacketAffineSyntax.affine w B e q n).imp ((Formula.equal d e))))).close

theorem source_packetDivisionRemainderUnique {m} (w B d e q n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDivisionRemainderUniqueSentence w B d e q n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineSyntax.affine w B e q n) (Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketAffineSyntax.affine w B e q n) := .hyp (Or.inl rfl)
  exact PacketDivisionUnique.digit_same_quotient hZ w B d e q n h0 h1 h2

theorem packetDivisionRemainderUnique_kernel_certificate {m} (w B d e q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDivisionRemainderUniqueSentence w B d e q n)) := TheoryTransport.sentence (source_packetDivisionRemainderUnique w B d e q n)

theorem native_packetDivisionRemainderUnique {m} (w B d e q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDivisionRemainderUniqueSentence w B d e q n)) := ZFReplay.replay (packetDivisionRemainderUnique_kernel_certificate w B d e q n)

def packetDivisionPairUniqueSentence {m} (w B d q e p n : Fin m) : Source.Sentence := ((omega w).imp ((PacketAffineSyntax.affine w B d q n).imp ((PacketAffineSyntax.affine w B e p n).imp (((Formula.equal d e).conj (.equal q p)))))).close

theorem source_packetDivisionPairUnique {m} (w B d q e p n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDivisionPairUniqueSentence w B d q e p n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineSyntax.affine w B e p n) (Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketAffineSyntax.affine w B e p n) := .hyp (Or.inl rfl)
  exact PacketDivisionUnique.unique hZ w B d q e p n h0 h1 h2

theorem packetDivisionPairUnique_kernel_certificate {m} (w B d q e p n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDivisionPairUniqueSentence w B d q e p n)) := TheoryTransport.sentence (source_packetDivisionPairUnique w B d q e p n)

theorem native_packetDivisionPairUnique {m} (w B d q e p n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDivisionPairUniqueSentence w B d q e p n)) := ZFReplay.replay (packetDivisionPairUnique_kernel_certificate w B d q e p n)

def packetDivisionExactDomainSentence {m} (wide : Bool) (w B n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp (((PacketDivisionSyntax.decomposes w B n).iff (.mem n w))))).close

theorem source_packetDivisionExactDomain {m} (wide : Bool) (w B n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDivisionExactDomainSentence wide w B n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inl rfl)
  exact PacketDivisionValue.decomposes_iff hZ wide w B n h0 h1

theorem packetDivisionExactDomain_kernel_certificate {m} (wide : Bool) (w B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDivisionExactDomainSentence wide w B n)) := TheoryTransport.sentence (source_packetDivisionExactDomain wide w B n)

theorem native_packetDivisionExactDomain {m} (wide : Bool) (w B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDivisionExactDomainSentence wide w B n)) := ZFReplay.replay (packetDivisionExactDomain_kernel_certificate wide w B n)

def packetDivisionQuantifiedPairUniqueSentence {m} (w B n d q : Fin m) : Source.Sentence := ((omega w).imp ((PacketAffineSyntax.affine w B d q n).imp ((PacketDivisionValueSyntax.uniquePair w B n d q)))).close

theorem source_packetDivisionQuantifiedPairUnique {m} (w B n d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDivisionQuantifiedPairUniqueSentence w B n d q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inl rfl)
  exact PacketDivisionValue.unique_pair hZ w B n d q h0 h1

theorem packetDivisionQuantifiedPairUnique_kernel_certificate {m} (w B n d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDivisionQuantifiedPairUniqueSentence w B n d q)) := TheoryTransport.sentence (source_packetDivisionQuantifiedPairUnique w B n d q)

theorem native_packetDivisionQuantifiedPairUnique {m} (w B n d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDivisionQuantifiedPairUniqueSentence w B n d q)) := ZFReplay.replay (packetDivisionQuantifiedPairUnique_kernel_certificate w B n d q)

def packetDivisionUniqueFiberExistsSentence {m} (wide : Bool) (w B n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((Formula.mem n w).imp ((PacketDivisionValueSyntax.fiber w B n))))).close

theorem source_packetDivisionUniqueFiberExists {m} (wide : Bool) (w B n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDivisionUniqueFiberExistsSentence wide w B n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem n w) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem n w) := .hyp (Or.inl rfl)
  exact PacketDivisionValue.exists_fiber hZ wide w B n h0 h1 h2

theorem packetDivisionUniqueFiberExists_kernel_certificate {m} (wide : Bool) (w B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDivisionUniqueFiberExistsSentence wide w B n)) := TheoryTransport.sentence (source_packetDivisionUniqueFiberExists wide w B n)

theorem native_packetDivisionUniqueFiberExists {m} (wide : Bool) (w B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDivisionUniqueFiberExistsSentence wide w B n)) := ZFReplay.replay (packetDivisionUniqueFiberExists_kernel_certificate wide w B n)

def packetDivisionUniqueFiberExactDomainSentence {m} (wide : Bool) (w B n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp (((PacketDivisionValueSyntax.fiber w B n).iff (.mem n w))))).close

theorem source_packetDivisionUniqueFiberExactDomain {m} (wide : Bool) (w B n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDivisionUniqueFiberExactDomainSentence wide w B n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inl rfl)
  exact PacketDivisionValue.fiber_iff hZ wide w B n h0 h1

theorem packetDivisionUniqueFiberExactDomain_kernel_certificate {m} (wide : Bool) (w B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDivisionUniqueFiberExactDomainSentence wide w B n)) := TheoryTransport.sentence (source_packetDivisionUniqueFiberExactDomain wide w B n)

theorem native_packetDivisionUniqueFiberExactDomain {m} (wide : Bool) (w B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDivisionUniqueFiberExactDomainSentence wide w B n)) := ZFReplay.replay (packetDivisionUniqueFiberExactDomain_kernel_certificate wide w B n)

def packetDivisionAcceptedInverseExistsSentence {m} (wide : Bool) (w B n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((Formula.mem n w).imp ((PacketDivisionValueSyntax.acceptedDecomposition wide w n))))).close

theorem source_packetDivisionAcceptedInverseExists {m} (wide : Bool) (w B n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDivisionAcceptedInverseExistsSentence wide w B n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem n w) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem n w) := .hyp (Or.inl rfl)
  exact PacketDivisionValue.accepted_exists hZ wide w B n h0 h1 h2

theorem packetDivisionAcceptedInverseExists_kernel_certificate {m} (wide : Bool) (w B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDivisionAcceptedInverseExistsSentence wide w B n)) := TheoryTransport.sentence (source_packetDivisionAcceptedInverseExists wide w B n)

theorem native_packetDivisionAcceptedInverseExists {m} (wide : Bool) (w B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDivisionAcceptedInverseExistsSentence wide w B n)) := ZFReplay.replay (packetDivisionAcceptedInverseExists_kernel_certificate wide w B n)

def packetDivisionAcceptedInverseExactDomainSentence {m} (wide : Bool) (w B n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp (((PacketDivisionValueSyntax.acceptedDecomposition wide w n).iff (.mem n w))))).close

theorem source_packetDivisionAcceptedInverseExactDomain {m} (wide : Bool) (w B n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDivisionAcceptedInverseExactDomainSentence wide w B n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inl rfl)
  exact PacketDivisionValue.accepted_iff hZ wide w B n h0 h1

theorem packetDivisionAcceptedInverseExactDomain_kernel_certificate {m} (wide : Bool) (w B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDivisionAcceptedInverseExactDomainSentence wide w B n)) := TheoryTransport.sentence (source_packetDivisionAcceptedInverseExactDomain wide w B n)

theorem native_packetDivisionAcceptedInverseExactDomain {m} (wide : Bool) (w B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDivisionAcceptedInverseExactDomainSentence wide w B n)) := ZFReplay.replay (packetDivisionAcceptedInverseExactDomain_kernel_certificate wide w B n)

def packetDivisionAcceptedInverseUniqueSentence {m} (wide : Bool) (w B d q e p n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketAffineAcceptedSyntax.accepted wide w d q n).imp ((PacketAffineAcceptedSyntax.accepted wide w e p n).imp (((Formula.equal d e).conj (.equal q p))))))).close

theorem source_packetDivisionAcceptedInverseUnique {m} (wide : Bool) (w B d q e p n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDivisionAcceptedInverseUniqueSentence wide w B d q e p n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineAcceptedSyntax.accepted wide w e p n) (Context.add (PacketAffineAcceptedSyntax.accepted wide w d q n) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketAffineAcceptedSyntax.accepted wide w d q n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketAffineAcceptedSyntax.accepted wide w e p n) := .hyp (Or.inl rfl)
  exact PacketDivisionValue.accepted_unique hZ wide w B d q e p n h0 h1 h2 h3

theorem packetDivisionAcceptedInverseUnique_kernel_certificate {m} (wide : Bool) (w B d q e p n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDivisionAcceptedInverseUniqueSentence wide w B d q e p n)) := TheoryTransport.sentence (source_packetDivisionAcceptedInverseUnique wide w B d q e p n)

theorem native_packetDivisionAcceptedInverseUnique {m} (wide : Bool) (w B d q e p n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDivisionAcceptedInverseUniqueSentence wide w B d q e p n)) := ZFReplay.replay (packetDivisionAcceptedInverseUnique_kernel_certificate wide w B d q e p n)

def packetDivisionAllInternalUniqueFibersSentence {m} (wide : Bool) (w B : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketDivisionValueSyntax.allLaw w B)))).close

theorem source_packetDivisionAllInternalUniqueFibers {m} (wide : Bool) (w B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDivisionAllInternalUniqueFibersSentence wide w B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inl rfl)
  exact PacketDivisionValue.all_law hZ wide w B h0 h1

theorem packetDivisionAllInternalUniqueFibers_kernel_certificate {m} (wide : Bool) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDivisionAllInternalUniqueFibersSentence wide w B)) := TheoryTransport.sentence (source_packetDivisionAllInternalUniqueFibers wide w B)

theorem native_packetDivisionAllInternalUniqueFibers {m} (wide : Bool) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDivisionAllInternalUniqueFibersSentence wide w B)) := ZFReplay.replay (packetDivisionAllInternalUniqueFibers_kernel_certificate wide w B)

def packetDivisionAllInternalAcceptedInverseSentence {m} (wide : Bool) (w B : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketDivisionValueSyntax.allAcceptedLaw wide w)))).close

theorem source_packetDivisionAllInternalAcceptedInverse {m} (wide : Bool) (w B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDivisionAllInternalAcceptedInverseSentence wide w B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inl rfl)
  exact PacketDivisionValue.all_accepted_law hZ wide w B h0 h1

theorem packetDivisionAllInternalAcceptedInverse_kernel_certificate {m} (wide : Bool) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDivisionAllInternalAcceptedInverseSentence wide w B)) := TheoryTransport.sentence (source_packetDivisionAllInternalAcceptedInverse wide w B)

theorem native_packetDivisionAllInternalAcceptedInverse {m} (wide : Bool) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDivisionAllInternalAcceptedInverseSentence wide w B)) := ZFReplay.replay (packetDivisionAllInternalAcceptedInverse_kernel_certificate wide w B)

def packetDivisionActualLiteralSystemExistsSentence {m} (wide : Bool) (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketDivisionValueSyntax.existsSystem wide w))).close

theorem source_packetDivisionActualLiteralSystemExists {m} (wide : Bool) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDivisionActualLiteralSystemExistsSentence wide w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketDivisionValue.exists_system hZ wide w h0

theorem packetDivisionActualLiteralSystemExists_kernel_certificate {m} (wide : Bool) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDivisionActualLiteralSystemExistsSentence wide w)) := TheoryTransport.sentence (source_packetDivisionActualLiteralSystemExists wide w)

theorem native_packetDivisionActualLiteralSystemExists {m} (wide : Bool) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDivisionActualLiteralSystemExistsSentence wide w)) := ZFReplay.replay (packetDivisionActualLiteralSystemExists_kernel_certificate wide w)

end PPAC.Migration.Internal.ObjectPacketDivision
