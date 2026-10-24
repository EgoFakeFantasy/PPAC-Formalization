import PPAC.Migration.Internal.ProofSubstitutionNode

/-! 原替换节点两投影、全部五查询、全部内部数值搜索界及完整纯关系式节点的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectProofSubstitutionNode
open Source SourceAlgebra SourceLogic OmegaSyntax

def substitutionFreeProjectionIffSentence {m} (env : Fin 6 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp ((empty z).imp (((ProjectionExprQuery.query ProofSubstitutionProjectionSyntax.freeProjection w env).iff (RawCodeFieldSyntax.field w (env 4) z (env 2))))))).close

theorem source_substitutionFreeProjectionIff {m} (env : Fin 6 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (substitutionFreeProjectionIffSentence env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofSubstitutionProjection.free_query_iff hZ w z env h0 h1 h2

theorem substitutionFreeProjectionIff_kernel_certificate {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (substitutionFreeProjectionIffSentence env w z)) := TheoryTransport.sentence (source_substitutionFreeProjectionIff env w z)

theorem native_substitutionFreeProjectionIff {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (substitutionFreeProjectionIffSentence env w z)) := ZFReplay.replay (substitutionFreeProjectionIff_kernel_certificate env w z)

def substitutionFormulaProjectionAtOneIffSentence {m} (env : Fin 6 → Fin m) (w one : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp ((SyntaxNumeralSyntax.numeral 1 one).imp (((ProjectionExprQuery.query ProofSubstitutionProjectionSyntax.formulaProjection w env).iff (RawCodeFieldSyntax.field w (env 4) one (env 5))))))).close

theorem source_substitutionFormulaProjectionAtOneIff {m} (env : Fin 6 → Fin m) (w one : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (substitutionFormulaProjectionAtOneIffSentence env w one) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 1 one) (Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 1 one) := .hyp (Or.inl rfl)
  exact ProofSubstitutionProjection.formula_query_at_one hZ w one env h0 h1 h2

theorem substitutionFormulaProjectionAtOneIff_kernel_certificate {m} (env : Fin 6 → Fin m) (w one : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (substitutionFormulaProjectionAtOneIffSentence env w one)) := TheoryTransport.sentence (source_substitutionFormulaProjectionAtOneIff env w one)

theorem native_substitutionFormulaProjectionAtOneIff {m} (env : Fin 6 → Fin m) (w one : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (substitutionFormulaProjectionAtOneIffSentence env w one)) := ZFReplay.replay (substitutionFormulaProjectionAtOneIff_kernel_certificate env w one)

def substitutionFormulaProjectionIffSentence {m} (env : Fin 6 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp (((ProjectionExprQuery.query ProofSubstitutionProjectionSyntax.formulaProjection w env).iff (ProofSubstitutionProjectionSyntax.atOne w (env 4) (env 5)))))).close

theorem source_substitutionFormulaProjectionIff {m} (env : Fin 6 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (substitutionFormulaProjectionIffSentence env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inl rfl)
  exact ProofSubstitutionProjection.formula_query_iff hZ w env h0 h1

theorem substitutionFormulaProjectionIff_kernel_certificate {m} (env : Fin 6 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (substitutionFormulaProjectionIffSentence env w)) := TheoryTransport.sentence (source_substitutionFormulaProjectionIff env w)

theorem native_substitutionFormulaProjectionIff {m} (env : Fin 6 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (substitutionFormulaProjectionIffSentence env w)) := ZFReplay.replay (substitutionFormulaProjectionIff_kernel_certificate env w)

def substitutionBothProjectionsIffSentence {m} (env : Fin 6 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp ((empty z).imp (((ProofSubstitutionProjectionSyntax.projections w env).iff (ProofSubstitutionProjectionSyntax.metadata w z env)))))).close

theorem source_substitutionBothProjectionsIff {m} (env : Fin 6 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (substitutionBothProjectionsIffSentence env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofSubstitutionProjection.projections_iff hZ w z env h0 h1 h2

theorem substitutionBothProjectionsIff_kernel_certificate {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (substitutionBothProjectionsIffSentence env w z)) := TheoryTransport.sentence (source_substitutionBothProjectionsIff env w z)

theorem native_substitutionBothProjectionsIff {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (substitutionBothProjectionsIffSentence env w z)) := ZFReplay.replay (substitutionBothProjectionsIff_kernel_certificate env w z)

def substitutionFreeProjectionAtConstructorSentence {m} (k tag : Nat) (xs : Fin (k+2) → Fin m) (env : Fin 6 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp ((empty z).imp ((SyntaxNodeSyntax.constructor (k+2) tag w xs (env 4)).imp (((ProjectionExprQuery.query ProofSubstitutionProjectionSyntax.freeProjection w env).iff (Formula.equal (env 2) (xs (ProofSubstitutionProjectionSlots.firstSlot k))))))))).close

theorem source_substitutionFreeProjectionAtConstructor {m} (k tag : Nat) (xs : Fin (k+2) → Fin m) (env : Fin 6 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (substitutionFreeProjectionAtConstructorSentence k tag xs env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor (k+2) tag w xs (env 4)) (Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxNodeSyntax.constructor (k+2) tag w xs (env 4)) := .hyp (Or.inl rfl)
  exact ProofSubstitutionProjectionSlots.free_at_constructor hZ (k+2) tag xs (ProofSubstitutionProjectionSlots.firstSlot k) rfl w z env h0 h1 h2 h3

theorem substitutionFreeProjectionAtConstructor_kernel_certificate {m} (k tag : Nat) (xs : Fin (k+2) → Fin m) (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (substitutionFreeProjectionAtConstructorSentence k tag xs env w z)) := TheoryTransport.sentence (source_substitutionFreeProjectionAtConstructor k tag xs env w z)

theorem native_substitutionFreeProjectionAtConstructor {m} (k tag : Nat) (xs : Fin (k+2) → Fin m) (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (substitutionFreeProjectionAtConstructorSentence k tag xs env w z)) := ZFReplay.replay (substitutionFreeProjectionAtConstructor_kernel_certificate k tag xs env w z)

def substitutionFormulaProjectionAtConstructorSentence {m} (k tag : Nat) (xs : Fin (k+2) → Fin m) (env : Fin 6 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp ((SyntaxNodeSyntax.constructor (k+2) tag w xs (env 4)).imp (((ProjectionExprQuery.query ProofSubstitutionProjectionSyntax.formulaProjection w env).iff (Formula.equal (env 5) (xs (ProofSubstitutionProjectionSlots.secondSlot k)))))))).close

theorem source_substitutionFormulaProjectionAtConstructor {m} (k tag : Nat) (xs : Fin (k+2) → Fin m) (env : Fin 6 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (substitutionFormulaProjectionAtConstructorSentence k tag xs env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor (k+2) tag w xs (env 4)) (Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNodeSyntax.constructor (k+2) tag w xs (env 4)) := .hyp (Or.inl rfl)
  exact ProofSubstitutionProjectionSlots.formula_at_constructor hZ (k+2) tag xs (ProofSubstitutionProjectionSlots.secondSlot k) rfl w env h0 h1 h2

theorem substitutionFormulaProjectionAtConstructor_kernel_certificate {m} (k tag : Nat) (xs : Fin (k+2) → Fin m) (env : Fin 6 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (substitutionFormulaProjectionAtConstructorSentence k tag xs env w)) := TheoryTransport.sentence (source_substitutionFormulaProjectionAtConstructor k tag xs env w)

theorem native_substitutionFormulaProjectionAtConstructor {m} (k tag : Nat) (xs : Fin (k+2) → Fin m) (env : Fin 6 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (substitutionFormulaProjectionAtConstructorSentence k tag xs env w)) := ZFReplay.replay (substitutionFormulaProjectionAtConstructor_kernel_certificate k tag xs env w)

def substitutionProjectionsAtConstructorSentence {m} (k tag : Nat) (xs : Fin (k+2) → Fin m) (env : Fin 6 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp ((empty z).imp ((SyntaxNodeSyntax.constructor (k+2) tag w xs (env 4)).imp (((ProofSubstitutionProjectionSyntax.projections w env).iff ((Formula.equal (env 2) (xs (ProofSubstitutionProjectionSlots.firstSlot k))).conj (Formula.equal (env 5) (xs (ProofSubstitutionProjectionSlots.secondSlot k)))))))))).close

theorem source_substitutionProjectionsAtConstructor {m} (k tag : Nat) (xs : Fin (k+2) → Fin m) (env : Fin 6 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (substitutionProjectionsAtConstructorSentence k tag xs env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor (k+2) tag w xs (env 4)) (Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxNodeSyntax.constructor (k+2) tag w xs (env 4)) := .hyp (Or.inl rfl)
  exact ProofSubstitutionProjectionSlots.projections_at_constructor hZ (k+2) tag xs (ProofSubstitutionProjectionSlots.firstSlot k) (ProofSubstitutionProjectionSlots.secondSlot k) rfl rfl w z env h0 h1 h2 h3

theorem substitutionProjectionsAtConstructor_kernel_certificate {m} (k tag : Nat) (xs : Fin (k+2) → Fin m) (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (substitutionProjectionsAtConstructorSentence k tag xs env w z)) := TheoryTransport.sentence (source_substitutionProjectionsAtConstructor k tag xs env w z)

theorem native_substitutionProjectionsAtConstructor {m} (k tag : Nat) (xs : Fin (k+2) → Fin m) (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (substitutionProjectionsAtConstructorSentence k tag xs env w z)) := ZFReplay.replay (substitutionProjectionsAtConstructor_kernel_certificate k tag xs env w z)

def substitutionAllFiveQueriesIffSentence {m} (env : Fin 6 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp ((empty z).imp (((ProofSubstitutionAllQueries.bundle w env).iff (ProofSubstitutionAllQueries.specification w z env)))))).close

theorem source_substitutionAllFiveQueriesIff {m} (env : Fin 6 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (substitutionAllFiveQueriesIffSentence env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofSubstitutionAllQueries.bundle_iff hZ w z env h0 h1 h2

theorem substitutionAllFiveQueriesIff_kernel_certificate {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (substitutionAllFiveQueriesIffSentence env w z)) := TheoryTransport.sentence (source_substitutionAllFiveQueriesIff env w z)

theorem native_substitutionAllFiveQueriesIff {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (substitutionAllFiveQueriesIffSentence env w z)) := ZFReplay.replay (substitutionAllFiveQueriesIff_kernel_certificate env w z)

def pairingProjectionNumericBoundSentence {m} (raw head : Bool) (w x y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem x w).imp ((PairingProjectionSyntax.step raw head w x y).imp ((NaturalAdditionBounds.below y x))))).close

theorem source_pairingProjectionNumericBound {m} (raw head : Bool) (w x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pairingProjectionNumericBoundSentence raw head w x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PairingProjectionSyntax.step raw head w x y) (Context.add (Formula.mem x w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem x w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PairingProjectionSyntax.step raw head w x y) := .hyp (Or.inl rfl)
  exact PairingProjectionBounds.step_bound hZ raw head w x y h0 h1 h2

theorem pairingProjectionNumericBound_kernel_certificate {m} (raw head : Bool) (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pairingProjectionNumericBoundSentence raw head w x y)) := TheoryTransport.sentence (source_pairingProjectionNumericBound raw head w x y)

theorem native_pairingProjectionNumericBound {m} (raw head : Bool) (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pairingProjectionNumericBoundSentence raw head w x y)) := ZFReplay.replay (pairingProjectionNumericBound_kernel_certificate raw head w x y)

def rawHeadTailNumericBoundSentence {m} (head : Bool) (w x y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem x w).imp ((RawCodeProjectionSyntax.step head w x y).imp ((NaturalAdditionBounds.below y x))))).close

theorem source_rawHeadTailNumericBound {m} (head : Bool) (w x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawHeadTailNumericBoundSentence head w x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (RawCodeProjectionSyntax.step head w x y) (Context.add (Formula.mem x w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem x w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (RawCodeProjectionSyntax.step head w x y) := .hyp (Or.inl rfl)
  exact RawCodeProjectionBounds.step_bound hZ head w x y h0 h1 h2

theorem rawHeadTailNumericBound_kernel_certificate {m} (head : Bool) (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawHeadTailNumericBoundSentence head w x y)) := TheoryTransport.sentence (source_rawHeadTailNumericBound head w x y)

theorem native_rawHeadTailNumericBound {m} (head : Bool) (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawHeadTailNumericBoundSentence head w x y)) := ZFReplay.replay (rawHeadTailNumericBound_kernel_certificate head w x y)

def rawGetAllInternalBoundsSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((.all ((Formula.mem (Fin.last m) w.castSucc).imp (RawCodeGetBoundsSyntax.correct w.castSucc (Fin.last m)))))).close

theorem source_rawGetAllInternalBounds {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawGetAllInternalBoundsSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact RawCodeGetBounds.all_correct hZ w h0

theorem rawGetAllInternalBounds_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawGetAllInternalBoundsSentence w)) := TheoryTransport.sentence (source_rawGetAllInternalBounds w)

theorem native_rawGetAllInternalBounds {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawGetAllInternalBoundsSentence w)) := ZFReplay.replay (rawGetAllInternalBounds_kernel_certificate w)

def rawGetNumericBoundSentence {m} (w x i y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem x w).imp ((Formula.mem i w).imp ((RawCodeGetSyntax.get w x i y).imp ((NaturalAdditionBounds.below y x)))))).close

theorem source_rawGetNumericBound {m} (w x i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawGetNumericBoundSentence w x i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (RawCodeGetSyntax.get w x i y) (Context.add (Formula.mem i w) (Context.add (Formula.mem x w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem x w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem i w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (RawCodeGetSyntax.get w x i y) := .hyp (Or.inl rfl)
  exact RawCodeGetBounds.bound hZ w x i y h0 h1 h2 h3

theorem rawGetNumericBound_kernel_certificate {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawGetNumericBoundSentence w x i y)) := TheoryTransport.sentence (source_rawGetNumericBound w x i y)

theorem native_rawGetNumericBound {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawGetNumericBoundSentence w x i y)) := ZFReplay.replay (rawGetNumericBound_kernel_certificate w x i y)

def rawFieldNumericBoundSentence {m} (w x i y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem x w).imp ((Formula.mem i w).imp ((RawCodeFieldSyntax.field w x i y).imp ((NaturalAdditionBounds.below y x)))))).close

theorem source_rawFieldNumericBound {m} (w x i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawFieldNumericBoundSentence w x i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (RawCodeFieldSyntax.field w x i y) (Context.add (Formula.mem i w) (Context.add (Formula.mem x w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem x w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem i w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (RawCodeFieldSyntax.field w x i y) := .hyp (Or.inl rfl)
  exact RawCodeFieldBounds.bound hZ w x i y h0 h1 h2 h3

theorem rawFieldNumericBound_kernel_certificate {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawFieldNumericBoundSentence w x i y)) := TheoryTransport.sentence (source_rawFieldNumericBound w x i y)

theorem native_rawFieldNumericBound {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawFieldNumericBoundSentence w x i y)) := ZFReplay.replay (rawFieldNumericBound_kernel_certificate w x i y)

def substitutionAtOneBoundSentence {m} (w p y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem p w).imp ((ProofSubstitutionProjectionSyntax.atOne w p y).imp ((NaturalAdditionBounds.below y p))))).close

theorem source_substitutionAtOneBound {m} (w p y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (substitutionAtOneBoundSentence w p y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProofSubstitutionProjectionSyntax.atOne w p y) (Context.add (Formula.mem p w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem p w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProofSubstitutionProjectionSyntax.atOne w p y) := .hyp (Or.inl rfl)
  exact ProofSubstitutionBounds.atOne_bound hZ w p y h0 h1 h2

theorem substitutionAtOneBound_kernel_certificate {m} (w p y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (substitutionAtOneBoundSentence w p y)) := TheoryTransport.sentence (source_substitutionAtOneBound w p y)

theorem native_substitutionAtOneBound {m} (w p y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (substitutionAtOneBoundSentence w p y)) := ZFReplay.replay (substitutionAtOneBound_kernel_certificate w p y)

def substitutionFormulaProjectionBoundSentence {m} (env : Fin 6 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp ((ProjectionExprQuery.query ProofSubstitutionProjectionSyntax.formulaProjection w env).imp ((NaturalAdditionBounds.below (env 5) (env 4)))))).close

theorem source_substitutionFormulaProjectionBound {m} (env : Fin 6 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (substitutionFormulaProjectionBoundSentence env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionExprQuery.query ProofSubstitutionProjectionSyntax.formulaProjection w env) (Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectionExprQuery.query ProofSubstitutionProjectionSyntax.formulaProjection w env) := .hyp (Or.inl rfl)
  exact ProofSubstitutionBounds.formula_projection_bound hZ w env h0 h1 h2

theorem substitutionFormulaProjectionBound_kernel_certificate {m} (env : Fin 6 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (substitutionFormulaProjectionBoundSentence env w)) := TheoryTransport.sentence (source_substitutionFormulaProjectionBound env w)

theorem native_substitutionFormulaProjectionBound {m} (env : Fin 6 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (substitutionFormulaProjectionBoundSentence env w)) := ZFReplay.replay (substitutionFormulaProjectionBound_kernel_certificate env w)

def substitutionAllAssignmentBoundsSentence {m} (env : Fin 6 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp ((HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.substitutionShape.head w env row).imp ((ProjectionExprQuery.query ProofSubstitutionProjectionSyntax.formulaProjection w env).imp ((HornExprBounds.environmentBound 6 row env)))))).close

theorem source_substitutionAllAssignmentBounds {m} (env : Fin 6 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (substitutionAllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionExprQuery.query ProofSubstitutionProjectionSyntax.formulaProjection w env) (Context.add (HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.substitutionShape.head w env row) (Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.substitutionShape.head w env row) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (ProjectionExprQuery.query ProofSubstitutionProjectionSyntax.formulaProjection w env) := .hyp (Or.inl rfl)
  exact ProofSubstitutionBounds.environment_bound hZ w row env h0 h1 h2 h3

theorem substitutionAllAssignmentBounds_kernel_certificate {m} (env : Fin 6 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (substitutionAllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_substitutionAllAssignmentBounds env w row)

theorem native_substitutionAllAssignmentBounds {m} (env : Fin 6 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (substitutionAllAssignmentBoundsSentence env w row)) := ZFReplay.replay (substitutionAllAssignmentBounds_kernel_certificate env w row)

def substitutionActualFiveFieldHeadIffSentence {m} (env : Fin 6 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp (((HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.substitutionShape.head w env row).iff (SyntaxNodeSyntax.constructor 5 5 w (fun j : Fin 5 => env j.castSucc) row))))).close

theorem source_substitutionActualFiveFieldHeadIff {m} (env : Fin 6 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (substitutionActualFiveFieldHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inl rfl)
  exact ProofSubstitutionBounds.head_constructor_iff hZ w row env h0 h1

theorem substitutionActualFiveFieldHeadIff_kernel_certificate {m} (env : Fin 6 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (substitutionActualFiveFieldHeadIffSentence env w row)) := TheoryTransport.sentence (source_substitutionActualFiveFieldHeadIff env w row)

theorem native_substitutionActualFiveFieldHeadIff {m} (env : Fin 6 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (substitutionActualFiveFieldHeadIffSentence env w row)) := ZFReplay.replay (substitutionActualFiveFieldHeadIff_kernel_certificate env w row)

def substitutionBoundedMatrixIffSentence {m} (env : Fin 6 → Fin m) (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((ProofSubstitutionNodeSyntax.boundedMatrix w row env).iff (ProofSubstitutionNodeSyntax.specificationMatrix w z row env))))).close

theorem source_substitutionBoundedMatrixIff {m} (env : Fin 6 → Fin m) (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (substitutionBoundedMatrixIffSentence env w z row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofSubstitutionNode.matrix_iff hZ w z row env h0 h1

theorem substitutionBoundedMatrixIff_kernel_certificate {m} (env : Fin 6 → Fin m) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (substitutionBoundedMatrixIffSentence env w z row)) := TheoryTransport.sentence (source_substitutionBoundedMatrixIff env w z row)

theorem native_substitutionBoundedMatrixIff {m} (env : Fin 6 → Fin m) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (substitutionBoundedMatrixIffSentence env w z row)) := ZFReplay.replay (substitutionBoundedMatrixIff_kernel_certificate env w z row)

def substitutionFullPureRelationalNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((ProofSubstitutionNodeSyntax.node w row).iff (ProofSubstitutionNodeSyntax.specification w z row))))).close

theorem source_substitutionFullPureRelationalNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (substitutionFullPureRelationalNodeIffSentence w z row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofSubstitutionNode.node_iff hZ w z row h0 h1

theorem substitutionFullPureRelationalNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (substitutionFullPureRelationalNodeIffSentence w z row)) := TheoryTransport.sentence (source_substitutionFullPureRelationalNodeIff w z row)

theorem native_substitutionFullPureRelationalNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (substitutionFullPureRelationalNodeIffSentence w z row)) := ZFReplay.replay (substitutionFullPureRelationalNodeIff_kernel_certificate w z row)

end PPAC.Migration.Internal.ObjectProofSubstitutionNode
