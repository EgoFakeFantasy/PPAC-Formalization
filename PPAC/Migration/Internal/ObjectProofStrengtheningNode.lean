import PPAC.Migration.Internal.ProofStrengtheningNode

/-! 原mode0全公式及strengthening完整纯关系式节点的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectProofStrengtheningNode
open Source SourceAlgebra SourceLogic OmegaSyntax

def modeZeroFormulaAtCodesIffSentence {m} (w mode depth P a b B n q I J R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth P).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeShiftSyntax.shiftCode w b B J).imp ((IndexTermImageCodeSyntax.environment w I J R S a b a B).imp (((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (SyntaxWeakenFreeSyntax.weakened w a b B n q)))))))))).close

theorem source_modeZeroFormulaAtCodesIff {m} (w mode depth P a b B n q I J R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeZeroFormulaAtCodesIffSentence w mode depth P a b B n q I J R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (IndexTermImageCodeSyntax.environment w I J R S a b a B) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B J) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (OriginalTermTraceSyntax.metadata w depth P) (Context.add (SyntaxNumeralSyntax.numeral 0 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth P) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B J) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (IndexTermImageCodeSyntax.environment w I J R S a b a B) := .hyp (Or.inl rfl)
  exact OriginalWeakenFormulaRun.at_codes_iff hZ w mode depth P a b B n q I J R S h0 h1 h2 h3 h4 h5 h6

theorem modeZeroFormulaAtCodesIff_kernel_certificate {m} (w mode depth P a b B n q I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeZeroFormulaAtCodesIffSentence w mode depth P a b B n q I J R S)) := TheoryTransport.sentence (source_modeZeroFormulaAtCodesIff w mode depth P a b B n q I J R S)

theorem native_modeZeroFormulaAtCodesIff {m} (w mode depth P a b B n q I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeZeroFormulaAtCodesIffSentence w mode depth P a b B n q I J R S)) := ZFReplay.replay (modeZeroFormulaAtCodesIff_kernel_certificate w mode depth P a b B n q I J R S)

def modeZeroFullFormulaWeakenIffSentence {m} (w mode depth P a b B n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth P).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((successor B b).imp (((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (SyntaxWeakenFreeSyntax.weakened w a b B n q)))))))).close

theorem source_modeZeroFullFormulaWeakenIff {m} (w mode depth P a b B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeZeroFullFormulaWeakenIffSentence w mode depth P a b B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor B b) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (OriginalTermTraceSyntax.metadata w depth P) (Context.add (SyntaxNumeralSyntax.numeral 0 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth P) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (successor B b) := .hyp (Or.inl rfl)
  exact OriginalWeakenFormulaRun.typed_iff hZ w mode depth P a b B n q h0 h1 h2 h3 h4

theorem modeZeroFullFormulaWeakenIff_kernel_certificate {m} (w mode depth P a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeZeroFullFormulaWeakenIffSentence w mode depth P a b B n q)) := TheoryTransport.sentence (source_modeZeroFullFormulaWeakenIff w mode depth P a b B n q)

theorem native_modeZeroFullFormulaWeakenIff {m} (w mode depth P a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeZeroFullFormulaWeakenIffSentence w mode depth P a b B n q)) := ZFReplay.replay (modeZeroFullFormulaWeakenIff_kernel_certificate w mode depth P a b B n q)

def modeZeroFullFormulaProgramIffSentence {m} (w mode depth P a b B n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth P).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((successor B b).imp (((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (WeakenFreeProgramSyntax.executed w a b B n q)))))))).close

theorem source_modeZeroFullFormulaProgramIff {m} (w mode depth P a b B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeZeroFullFormulaProgramIffSentence w mode depth P a b B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor B b) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (OriginalTermTraceSyntax.metadata w depth P) (Context.add (SyntaxNumeralSyntax.numeral 0 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth P) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (successor B b) := .hyp (Or.inl rfl)
  exact OriginalWeakenFormulaRun.program_iff hZ w mode depth P a b B n q h0 h1 h2 h3 h4

theorem modeZeroFullFormulaProgramIff_kernel_certificate {m} (w mode depth P a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeZeroFullFormulaProgramIffSentence w mode depth P a b B n q)) := TheoryTransport.sentence (source_modeZeroFullFormulaProgramIff w mode depth P a b B n q)

theorem native_modeZeroFullFormulaProgramIff {m} (w mode depth P a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeZeroFullFormulaProgramIffSentence w mode depth P a b B n q)) := ZFReplay.replay (modeZeroFullFormulaProgramIff_kernel_certificate w mode depth P a b B n q)

def modeZeroFullFormulaOutputTypeSentence {m} (w mode depth P a b B n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth P).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((successor B b).imp ((OriginalTransformRowSyntax.run 3 w mode depth P n q).imp ((FormulaCodeSyntax.formulaCode w q a B)))))))).close

theorem source_modeZeroFullFormulaOutputType {m} (w mode depth P a b B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeZeroFullFormulaOutputTypeSentence w mode depth P a b B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.run 3 w mode depth P n q) (Context.add (successor B b) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (OriginalTermTraceSyntax.metadata w depth P) (Context.add (SyntaxNumeralSyntax.numeral 0 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth P) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (successor B b) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (OriginalTransformRowSyntax.run 3 w mode depth P n q) := .hyp (Or.inl rfl)
  exact OriginalWeakenFormulaRun.output_type hZ w mode depth P a b B n q h0 h1 h2 h3 h4 h5

theorem modeZeroFullFormulaOutputType_kernel_certificate {m} (w mode depth P a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeZeroFullFormulaOutputTypeSentence w mode depth P a b B n q)) := TheoryTransport.sentence (source_modeZeroFullFormulaOutputType w mode depth P a b B n q)

theorem native_modeZeroFullFormulaOutputType {m} (w mode depth P a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeZeroFullFormulaOutputTypeSentence w mode depth P a b B n q)) := ZFReplay.replay (modeZeroFullFormulaOutputType_kernel_certificate w mode depth P a b B n q)

def strengtheningFormulaQueryIffSentence {m} (env : Fin 4 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((empty z).imp (((PureSyntaxExprQuery.query ProofStrengtheningSyntax.formulaQuery w env).iff (FormulaCodeSyntax.formulaCode w (env 1) z (env 0))))))).close

theorem source_strengtheningFormulaQueryIff {m} (env : Fin 4 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (strengtheningFormulaQueryIffSentence env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofStrengtheningQueries.formula_iff hZ w z env h0 h1 h2

theorem strengtheningFormulaQueryIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (strengtheningFormulaQueryIffSentence env w z)) := TheoryTransport.sentence (source_strengtheningFormulaQueryIff env w z)

theorem native_strengtheningFormulaQueryIff {m} (env : Fin 4 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (strengtheningFormulaQueryIffSentence env w z)) := ZFReplay.replay (strengtheningFormulaQueryIff_kernel_certificate env w z)

def strengtheningFreeProjectionAtSuccessorIffSentence {m} (env : Fin 4 → Fin m) (w z B : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((empty z).imp ((successor B (env 0)).imp (((ProjectionExprQuery.query ProofStrengtheningSyntax.freeQuery w env).iff (RawCodeFieldSyntax.field w (env 2) z B))))))).close

theorem source_strengtheningFreeProjectionAtSuccessorIff {m} (env : Fin 4 → Fin m) (w z B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (strengtheningFreeProjectionAtSuccessorIffSentence env w z B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor B (env 0)) (Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor B (env 0)) := .hyp (Or.inl rfl)
  exact ProofStrengtheningQueries.free_iff_at_successor hZ w z B env h0 h1 h2 h3

theorem strengtheningFreeProjectionAtSuccessorIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w z B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (strengtheningFreeProjectionAtSuccessorIffSentence env w z B)) := TheoryTransport.sentence (source_strengtheningFreeProjectionAtSuccessorIff env w z B)

theorem native_strengtheningFreeProjectionAtSuccessorIff {m} (env : Fin 4 → Fin m) (w z B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (strengtheningFreeProjectionAtSuccessorIffSentence env w z B)) := ZFReplay.replay (strengtheningFreeProjectionAtSuccessorIff_kernel_certificate env w z B)

def strengtheningPredecessorFormulaIffSentence {m} (env : Fin 4 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp (((ProjectionExprQuery.query ProofStrengtheningSyntax.predecessorFormulaQuery w env).iff (ProofSubstitutionProjectionSyntax.atOne w (env 2) (env 3)))))).close

theorem source_strengtheningPredecessorFormulaIff {m} (env : Fin 4 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (strengtheningPredecessorFormulaIffSentence env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inl rfl)
  exact ProofStrengtheningQueries.predecessorFormula_iff hZ w env h0 h1

theorem strengtheningPredecessorFormulaIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (strengtheningPredecessorFormulaIffSentence env w)) := TheoryTransport.sentence (source_strengtheningPredecessorFormulaIff env w)

theorem native_strengtheningPredecessorFormulaIff {m} (env : Fin 4 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (strengtheningPredecessorFormulaIffSentence env w)) := ZFReplay.replay (strengtheningPredecessorFormulaIff_kernel_certificate env w)

def strengtheningActualModeZeroQueryIffSentence {m} (env : Fin 4 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((empty z).imp (((OriginalTransformExprQuery.query ProofStrengtheningSyntax.transformQuery w env).iff (OriginalTransformRowSyntax.run 3 w z z z (env 1) (env 3))))))).close

theorem source_strengtheningActualModeZeroQueryIff {m} (env : Fin 4 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (strengtheningActualModeZeroQueryIffSentence env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofStrengtheningQueries.transform_at_zero hZ w z env h0 h1 h2

theorem strengtheningActualModeZeroQueryIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (strengtheningActualModeZeroQueryIffSentence env w z)) := TheoryTransport.sentence (source_strengtheningActualModeZeroQueryIff env w z)

theorem native_strengtheningActualModeZeroQueryIff {m} (env : Fin 4 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (strengtheningActualModeZeroQueryIffSentence env w z)) := ZFReplay.replay (strengtheningActualModeZeroQueryIff_kernel_certificate env w z)

def strengtheningGuardedModeZeroProgramIffSentence {m} (env : Fin 4 → Fin m) (w z B : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((empty z).imp ((successor B (env 0)).imp ((PureSyntaxExprQuery.query ProofStrengtheningSyntax.formulaQuery w env).imp (((OriginalTransformExprQuery.query ProofStrengtheningSyntax.transformQuery w env).iff (WeakenFreeProgramSyntax.executed w z (env 0) B (env 1) (env 3))))))))).close

theorem source_strengtheningGuardedModeZeroProgramIff {m} (env : Fin 4 → Fin m) (w z B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (strengtheningGuardedModeZeroProgramIffSentence env w z B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureSyntaxExprQuery.query ProofStrengtheningSyntax.formulaQuery w env) (Context.add (successor B (env 0)) (Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (successor B (env 0)) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PureSyntaxExprQuery.query ProofStrengtheningSyntax.formulaQuery w env) := .hyp (Or.inl rfl)
  exact ProofStrengtheningQueries.guarded_transform_iff hZ w z B env h0 h1 h2 h3 h4

theorem strengtheningGuardedModeZeroProgramIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w z B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (strengtheningGuardedModeZeroProgramIffSentence env w z B)) := TheoryTransport.sentence (source_strengtheningGuardedModeZeroProgramIff env w z B)

theorem native_strengtheningGuardedModeZeroProgramIff {m} (env : Fin 4 → Fin m) (w z B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (strengtheningGuardedModeZeroProgramIffSentence env w z B)) := ZFReplay.replay (strengtheningGuardedModeZeroProgramIff_kernel_certificate env w z B)

def strengtheningAllFourQueriesAtSuccessorIffSentence {m} (env : Fin 4 → Fin m) (w z B : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((empty z).imp ((successor B (env 0)).imp (((ProofStrengtheningSyntax.bundle w env).iff (ProofStrengtheningSyntax.atSuccessor w z B env))))))).close

theorem source_strengtheningAllFourQueriesAtSuccessorIff {m} (env : Fin 4 → Fin m) (w z B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (strengtheningAllFourQueriesAtSuccessorIffSentence env w z B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor B (env 0)) (Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor B (env 0)) := .hyp (Or.inl rfl)
  exact ProofStrengtheningAllQueries.at_successor_iff hZ w z B env h0 h1 h2 h3

theorem strengtheningAllFourQueriesAtSuccessorIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w z B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (strengtheningAllFourQueriesAtSuccessorIffSentence env w z B)) := TheoryTransport.sentence (source_strengtheningAllFourQueriesAtSuccessorIff env w z B)

theorem native_strengtheningAllFourQueriesAtSuccessorIff {m} (env : Fin 4 → Fin m) (w z B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (strengtheningAllFourQueriesAtSuccessorIffSentence env w z B)) := ZFReplay.replay (strengtheningAllFourQueriesAtSuccessorIff_kernel_certificate env w z B)

def strengtheningAllFourQueriesIffSentence {m} (env : Fin 4 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((empty z).imp (((ProofStrengtheningSyntax.bundle w env).iff (ProofStrengtheningSyntax.specification w z env)))))).close

theorem source_strengtheningAllFourQueriesIff {m} (env : Fin 4 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (strengtheningAllFourQueriesIffSentence env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofStrengtheningAllQueries.bundle_iff hZ w z env h0 h1 h2

theorem strengtheningAllFourQueriesIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (strengtheningAllFourQueriesIffSentence env w z)) := TheoryTransport.sentence (source_strengtheningAllFourQueriesIff env w z)

theorem native_strengtheningAllFourQueriesIff {m} (env : Fin 4 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (strengtheningAllFourQueriesIffSentence env w z)) := ZFReplay.replay (strengtheningAllFourQueriesIff_kernel_certificate env w z)

def strengtheningPredecessorFormulaBoundSentence {m} (env : Fin 4 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((ProjectionExprQuery.query ProofStrengtheningSyntax.predecessorFormulaQuery w env).imp ((NaturalAdditionBounds.below (env 3) (env 2)))))).close

theorem source_strengtheningPredecessorFormulaBound {m} (env : Fin 4 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (strengtheningPredecessorFormulaBoundSentence env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionExprQuery.query ProofStrengtheningSyntax.predecessorFormulaQuery w env) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectionExprQuery.query ProofStrengtheningSyntax.predecessorFormulaQuery w env) := .hyp (Or.inl rfl)
  exact ProofStrengtheningBounds.predecessorFormula_bound hZ w env h0 h1 h2

theorem strengtheningPredecessorFormulaBound_kernel_certificate {m} (env : Fin 4 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (strengtheningPredecessorFormulaBoundSentence env w)) := TheoryTransport.sentence (source_strengtheningPredecessorFormulaBound env w)

theorem native_strengtheningPredecessorFormulaBound {m} (env : Fin 4 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (strengtheningPredecessorFormulaBoundSentence env w)) := ZFReplay.replay (strengtheningPredecessorFormulaBound_kernel_certificate env w)

def strengtheningAllAssignmentBoundsSentence {m} (env : Fin 4 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.strengtheningShape.head w env row).imp ((ProjectionExprQuery.query ProofStrengtheningSyntax.predecessorFormulaQuery w env).imp ((HornExprBounds.environmentBound 4 row env)))))).close

theorem source_strengtheningAllAssignmentBounds {m} (env : Fin 4 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (strengtheningAllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionExprQuery.query ProofStrengtheningSyntax.predecessorFormulaQuery w env) (Context.add (HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.strengtheningShape.head w env row) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.strengtheningShape.head w env row) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (ProjectionExprQuery.query ProofStrengtheningSyntax.predecessorFormulaQuery w env) := .hyp (Or.inl rfl)
  exact ProofStrengtheningBounds.environment_bound hZ w row env h0 h1 h2 h3

theorem strengtheningAllAssignmentBounds_kernel_certificate {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (strengtheningAllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_strengtheningAllAssignmentBounds env w row)

theorem native_strengtheningAllAssignmentBounds {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (strengtheningAllAssignmentBoundsSentence env w row)) := ZFReplay.replay (strengtheningAllAssignmentBounds_kernel_certificate env w row)

def strengtheningActualThreeFieldHeadIffSentence {m} (env : Fin 4 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp (((HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.strengtheningShape.head w env row).iff (SyntaxNodeSyntax.constructor 3 4 w (fun j : Fin 3 => env j.castSucc) row))))).close

theorem source_strengtheningActualThreeFieldHeadIff {m} (env : Fin 4 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (strengtheningActualThreeFieldHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inl rfl)
  exact ProofStrengtheningBounds.head_constructor_iff hZ w row env h0 h1

theorem strengtheningActualThreeFieldHeadIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (strengtheningActualThreeFieldHeadIffSentence env w row)) := TheoryTransport.sentence (source_strengtheningActualThreeFieldHeadIff env w row)

theorem native_strengtheningActualThreeFieldHeadIff {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (strengtheningActualThreeFieldHeadIffSentence env w row)) := ZFReplay.replay (strengtheningActualThreeFieldHeadIff_kernel_certificate env w row)

def strengtheningBoundedMatrixIffSentence {m} (env : Fin 4 → Fin m) (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((ProofStrengtheningNodeSyntax.boundedMatrix w row env).iff (ProofStrengtheningNodeSyntax.specificationMatrix w z row env))))).close

theorem source_strengtheningBoundedMatrixIff {m} (env : Fin 4 → Fin m) (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (strengtheningBoundedMatrixIffSentence env w z row) := by
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
  exact ProofStrengtheningNode.matrix_iff hZ w z row env h0 h1

theorem strengtheningBoundedMatrixIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (strengtheningBoundedMatrixIffSentence env w z row)) := TheoryTransport.sentence (source_strengtheningBoundedMatrixIff env w z row)

theorem native_strengtheningBoundedMatrixIff {m} (env : Fin 4 → Fin m) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (strengtheningBoundedMatrixIffSentence env w z row)) := ZFReplay.replay (strengtheningBoundedMatrixIff_kernel_certificate env w z row)

def strengtheningFullPureRelationalNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((ProofStrengtheningNodeSyntax.node w row).iff (ProofStrengtheningNodeSyntax.specification w z row))))).close

theorem source_strengtheningFullPureRelationalNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (strengtheningFullPureRelationalNodeIffSentence w z row) := by
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
  exact ProofStrengtheningNode.node_iff hZ w z row h0 h1

theorem strengtheningFullPureRelationalNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (strengtheningFullPureRelationalNodeIffSentence w z row)) := TheoryTransport.sentence (source_strengtheningFullPureRelationalNodeIff w z row)

theorem native_strengtheningFullPureRelationalNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (strengtheningFullPureRelationalNodeIffSentence w z row)) := ZFReplay.replay (strengtheningFullPureRelationalNodeIff_kernel_certificate w z row)

end PPAC.Migration.Internal.ObjectProofStrengtheningNode
