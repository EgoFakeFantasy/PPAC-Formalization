import PPAC.Migration.Internal.FixedAxiomTableExistence

/-! Fixed-axiom partial tests in the original nativeZF kernel; full schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectFixedAxiomTest
open Source SourceAlgebra SourceLogic OmegaSyntax

def fixedPacketExistsSentence {m} (tag : Nat) (w : Fin m) : Source.Sentence := ((omega w).imp ((FixedAxiomPacketSyntax.existsLeaf tag w))).close

theorem source_fixedPacketExists {m} (tag : Nat) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fixedPacketExistsSentence tag w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FixedAxiomPacketExistence.exists_packet hZ tag w h0

theorem fixedPacketExists_kernel_certificate {m} (tag : Nat) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fixedPacketExistsSentence tag w)) := TheoryTransport.sentence (source_fixedPacketExists tag w)

theorem native_fixedPacketExists {m} (tag : Nat) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fixedPacketExistsSentence tag w)) := ZFReplay.replay (fixedPacketExists_kernel_certificate tag w)

def fixedPacketNaturalSentence {m} (tag : Nat) (w p : Fin m) : Source.Sentence := ((omega w).imp ((FixedAxiomPacketSyntax.leaf tag w p).imp ((Formula.mem p w)))).close

theorem source_fixedPacketNatural {m} (tag : Nat) (w p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fixedPacketNaturalSentence tag w p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FixedAxiomPacketSyntax.leaf tag w p) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FixedAxiomPacketSyntax.leaf tag w p) := .hyp (Or.inl rfl)
  exact FixedAxiomPacketUnique.range hZ tag w p h0 h1

theorem fixedPacketNatural_kernel_certificate {m} (tag : Nat) (w p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fixedPacketNaturalSentence tag w p)) := TheoryTransport.sentence (source_fixedPacketNatural tag w p)

theorem native_fixedPacketNatural {m} (tag : Nat) (w p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fixedPacketNaturalSentence tag w p)) := ZFReplay.replay (fixedPacketNatural_kernel_certificate tag w p)

def fixedPacketUniqueSentence {m} (tag : Nat) (w p q : Fin m) : Source.Sentence := ((omega w).imp ((FixedAxiomPacketSyntax.leaf tag w p).imp ((FixedAxiomPacketSyntax.leaf tag w q).imp ((Formula.equal p q))))).close

theorem source_fixedPacketUnique {m} (tag : Nat) (w p q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fixedPacketUniqueSentence tag w p q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FixedAxiomPacketSyntax.leaf tag w q) (Context.add (FixedAxiomPacketSyntax.leaf tag w p) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (FixedAxiomPacketSyntax.leaf tag w p) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FixedAxiomPacketSyntax.leaf tag w q) := .hyp (Or.inl rfl)
  exact FixedAxiomPacketUnique.unique hZ tag w p q h0 h1 h2

theorem fixedPacketUnique_kernel_certificate {m} (tag : Nat) (w p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fixedPacketUniqueSentence tag w p q)) := TheoryTransport.sentence (source_fixedPacketUnique tag w p q)

theorem native_fixedPacketUnique {m} (tag : Nat) (w p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fixedPacketUniqueSentence tag w p q)) := ZFReplay.replay (fixedPacketUnique_kernel_certificate tag w p q)

def fixedPacketTagsDisjointSentence {m} (k l : Nat) (_hkl : k ≠ l) (w p : Fin m) : Source.Sentence := ((omega w).imp ((FixedAxiomPacketSyntax.leaf k w p).imp ((FixedAxiomPacketSyntax.leaf l w p).imp ((Formula.bot))))).close

theorem source_fixedPacketTagsDisjoint {m} (k l : Nat) (hkl : k ≠ l) (w p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fixedPacketTagsDisjointSentence k l hkl w p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FixedAxiomPacketSyntax.leaf l w p) (Context.add (FixedAxiomPacketSyntax.leaf k w p) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (FixedAxiomPacketSyntax.leaf k w p) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FixedAxiomPacketSyntax.leaf l w p) := .hyp (Or.inl rfl)
  exact FixedAxiomPacketUnique.disjoint hZ k l hkl w p h0 h1 h2

theorem fixedPacketTagsDisjoint_kernel_certificate {m} (k l : Nat) (hkl : k ≠ l) (w p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fixedPacketTagsDisjointSentence k l hkl w p)) := TheoryTransport.sentence (source_fixedPacketTagsDisjoint k l hkl w p)

theorem native_fixedPacketTagsDisjoint {m} (k l : Nat) (hkl : k ≠ l) (w p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fixedPacketTagsDisjointSentence k l hkl w p)) := ZFReplay.replay (fixedPacketTagsDisjoint_kernel_certificate k l hkl w p)

def fixedPacketAtValueSentence {m} (tag : Nat) (w p q : Fin m) : Source.Sentence := ((omega w).imp ((FixedAxiomPacketSyntax.leaf tag w p).imp (((FixedAxiomPacketSyntax.leaf tag w q).iff (.equal q p))))).close

theorem source_fixedPacketAtValue {m} (tag : Nat) (w p q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fixedPacketAtValueSentence tag w p q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FixedAxiomPacketSyntax.leaf tag w p) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FixedAxiomPacketSyntax.leaf tag w p) := .hyp (Or.inl rfl)
  exact FixedAxiomPacketUnique.at_value hZ tag w p q h0 h1

theorem fixedPacketAtValue_kernel_certificate {m} (tag : Nat) (w p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fixedPacketAtValueSentence tag w p q)) := TheoryTransport.sentence (source_fixedPacketAtValue tag w p q)

theorem native_fixedPacketAtValue {m} (tag : Nat) (w p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fixedPacketAtValueSentence tag w p q)) := ZFReplay.replay (fixedPacketAtValue_kernel_certificate tag w p q)

def fixedAxiomTableAtPacketSentence {m} (target : Bool) (kind : Fin 10) (_hk : kind ∈ FixedAxiomTableSyntax.kinds target) (w c f : Fin m) : Source.Sentence := ((omega w).imp ((FixedAxiomPacketSyntax.leaf (NativeAxiomCertificateData.fixedTag kind) w c).imp (((FixedAxiomTableSyntax.table target w c f).iff (PureQuotationSyntax.formula (NativeAxiomCertificateData.fixedFormula kind) w f))))).close

theorem source_fixedAxiomTableAtPacket {m} (target : Bool) (kind : Fin 10) (hk : kind ∈ FixedAxiomTableSyntax.kinds target) (w c f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fixedAxiomTableAtPacketSentence target kind hk w c f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FixedAxiomPacketSyntax.leaf (NativeAxiomCertificateData.fixedTag kind) w c) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FixedAxiomPacketSyntax.leaf (NativeAxiomCertificateData.fixedTag kind) w c) := .hyp (Or.inl rfl)
  exact FixedAxiomTableFacts.table_at hZ target kind hk w c f h0 h1

theorem fixedAxiomTableAtPacket_kernel_certificate {m} (target : Bool) (kind : Fin 10) (hk : kind ∈ FixedAxiomTableSyntax.kinds target) (w c f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fixedAxiomTableAtPacketSentence target kind hk w c f)) := TheoryTransport.sentence (source_fixedAxiomTableAtPacket target kind hk w c f)

theorem native_fixedAxiomTableAtPacket {m} (target : Bool) (kind : Fin 10) (hk : kind ∈ FixedAxiomTableSyntax.kinds target) (w c f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fixedAxiomTableAtPacketSentence target kind hk w c f)) := ZFReplay.replay (fixedAxiomTableAtPacket_kernel_certificate target kind hk w c f)

def fixedAxiomRowAtConstructorSentence {m} (target : Bool) (w row c f : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 2 0 w (Source.SetLanguage.args2 c f) row).imp (((FixedAxiomTableSyntax.rowTest target w row).iff (FixedAxiomTableSyntax.table target w c f))))).close

theorem source_fixedAxiomRowAtConstructor {m} (target : Bool) (w row c f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fixedAxiomRowAtConstructorSentence target w row c f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 2 0 w (Source.SetLanguage.args2 c f) row) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 2 0 w (Source.SetLanguage.args2 c f) row) := .hyp (Or.inl rfl)
  exact FixedAxiomTableFacts.row_at hZ target w row c f h0 h1

theorem fixedAxiomRowAtConstructor_kernel_certificate {m} (target : Bool) (w row c f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fixedAxiomRowAtConstructorSentence target w row c f)) := TheoryTransport.sentence (source_fixedAxiomRowAtConstructor target w row c f)

theorem native_fixedAxiomRowAtConstructor {m} (target : Bool) (w row c f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fixedAxiomRowAtConstructorSentence target w row c f)) := ZFReplay.replay (fixedAxiomRowAtConstructor_kernel_certificate target w row c f)

def fixedAxiomTestAtOmegaSentence {m} (target : Bool) (w row : Fin m) : Source.Sentence := ((omega w).imp (((AxiomTestSyntax.holds (FixedAxiomTableSyntax.test target) row).iff (FixedAxiomTableSyntax.rowTest target w row)))).close

theorem source_fixedAxiomTestAtOmega {m} (target : Bool) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fixedAxiomTestAtOmegaSentence target w row) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FixedAxiomTableFacts.test_iff_row hZ target w row h0

theorem fixedAxiomTestAtOmega_kernel_certificate {m} (target : Bool) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fixedAxiomTestAtOmegaSentence target w row)) := TheoryTransport.sentence (source_fixedAxiomTestAtOmega target w row)

theorem native_fixedAxiomTestAtOmega {m} (target : Bool) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fixedAxiomTestAtOmegaSentence target w row)) := ZFReplay.replay (fixedAxiomTestAtOmega_kernel_certificate target w row)

def fixedAxiomTestAtPacketRowSentence {m} (target : Bool) (kind : Fin 10) (_hk : kind ∈ FixedAxiomTableSyntax.kinds target) (w row c f : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 2 0 w (Source.SetLanguage.args2 c f) row).imp ((FixedAxiomPacketSyntax.leaf (NativeAxiomCertificateData.fixedTag kind) w c).imp (((AxiomTestSyntax.holds (FixedAxiomTableSyntax.test target) row).iff (PureQuotationSyntax.formula (NativeAxiomCertificateData.fixedFormula kind) w f)))))).close

theorem source_fixedAxiomTestAtPacketRow {m} (target : Bool) (kind : Fin 10) (hk : kind ∈ FixedAxiomTableSyntax.kinds target) (w row c f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fixedAxiomTestAtPacketRowSentence target kind hk w row c f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FixedAxiomPacketSyntax.leaf (NativeAxiomCertificateData.fixedTag kind) w c) (Context.add (SyntaxNodeSyntax.constructor 2 0 w (Source.SetLanguage.args2 c f) row) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 2 0 w (Source.SetLanguage.args2 c f) row) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FixedAxiomPacketSyntax.leaf (NativeAxiomCertificateData.fixedTag kind) w c) := .hyp (Or.inl rfl)
  exact FixedAxiomTableFacts.at_packet_row hZ target kind hk w row c f h0 h1 h2

theorem fixedAxiomTestAtPacketRow_kernel_certificate {m} (target : Bool) (kind : Fin 10) (hk : kind ∈ FixedAxiomTableSyntax.kinds target) (w row c f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fixedAxiomTestAtPacketRowSentence target kind hk w row c f)) := TheoryTransport.sentence (source_fixedAxiomTestAtPacketRow target kind hk w row c f)

theorem native_fixedAxiomTestAtPacketRow {m} (target : Bool) (kind : Fin 10) (hk : kind ∈ FixedAxiomTableSyntax.kinds target) (w row c f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fixedAxiomTestAtPacketRowSentence target kind hk w row c f)) := ZFReplay.replay (fixedAxiomTestAtPacketRow_kernel_certificate target kind hk w row c f)

def fixedAxiomChoicePacketRejectedSentence {m} (target : Bool) (w row c f : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 2 0 w (Source.SetLanguage.args2 c f) row).imp ((FixedAxiomPacketSyntax.leaf 7 w c).imp (((AxiomTestSyntax.holds (FixedAxiomTableSyntax.test target) row).neg))))).close

theorem source_fixedAxiomChoicePacketRejected {m} (target : Bool) (w row c f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fixedAxiomChoicePacketRejectedSentence target w row c f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FixedAxiomPacketSyntax.leaf 7 w c) (Context.add (SyntaxNodeSyntax.constructor 2 0 w (Source.SetLanguage.args2 c f) row) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 2 0 w (Source.SetLanguage.args2 c f) row) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FixedAxiomPacketSyntax.leaf 7 w c) := .hyp (Or.inl rfl)
  exact FixedAxiomTableFacts.reject_choice_row hZ target w row c f h0 h1 h2

theorem fixedAxiomChoicePacketRejected_kernel_certificate {m} (target : Bool) (w row c f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fixedAxiomChoicePacketRejectedSentence target w row c f)) := TheoryTransport.sentence (source_fixedAxiomChoicePacketRejected target w row c f)

theorem native_fixedAxiomChoicePacketRejected {m} (target : Bool) (w row c f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fixedAxiomChoicePacketRejectedSentence target w row c f)) := ZFReplay.replay (fixedAxiomChoicePacketRejected_kernel_certificate target w row c f)

def fixedAxiomAcceptedWitnessExistsSentence {m} (target : Bool) (kind : Fin 10) (_hk : kind ∈ FixedAxiomTableSyntax.kinds target) (w : Fin m) : Source.Sentence := ((omega w).imp ((FixedAxiomTableExistence.existsTest target w))).close

theorem source_fixedAxiomAcceptedWitnessExists {m} (target : Bool) (kind : Fin 10) (hk : kind ∈ FixedAxiomTableSyntax.kinds target) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fixedAxiomAcceptedWitnessExistsSentence target kind hk w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FixedAxiomTableExistence.exists_accepted hZ target kind hk w h0

theorem fixedAxiomAcceptedWitnessExists_kernel_certificate {m} (target : Bool) (kind : Fin 10) (hk : kind ∈ FixedAxiomTableSyntax.kinds target) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fixedAxiomAcceptedWitnessExistsSentence target kind hk w)) := TheoryTransport.sentence (source_fixedAxiomAcceptedWitnessExists target kind hk w)

theorem native_fixedAxiomAcceptedWitnessExists {m} (target : Bool) (kind : Fin 10) (hk : kind ∈ FixedAxiomTableSyntax.kinds target) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fixedAxiomAcceptedWitnessExistsSentence target kind hk w)) := ZFReplay.replay (fixedAxiomAcceptedWitnessExists_kernel_certificate target kind hk w)

end PPAC.Migration.Internal.ObjectFixedAxiomTest
