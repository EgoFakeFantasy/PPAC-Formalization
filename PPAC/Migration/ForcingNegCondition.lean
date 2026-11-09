import PPAC.Migration.ForcingNegNormalization
import PPAC.Migration.ForcingConditionOpening

/-! The ACTUAL complete negative compiler at an arbitrary condition.
Reuse the original shell/head/guard data and both original mixed substitutions.
The operand property is derived from actual original rebind/open/mode2,
not assumed. Guard validity and monotonicity remain separate obligations. -/
namespace PPAC.Migration.ForcingNegCondition
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ForcingNegNormalization (compiled compiledData compiledData_rename compiledBody compiled_rename shellResult shellResultBody shellResultData_rename shellResult_rename)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

def operations {m} (w mode z a f T A C R S K H j n P r s L D : Fin m) : Formula m :=
  (omega w).conj ((SyntaxNumeralSyntax.numeral 2 mode).conj ((empty z).conj ((ForcingOpenLayout.environment w z a f T R S).conj ((SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H).conj ((Formula.mem j f).conj ((SyntaxTermSyntax.term w z T P).conj ((ForcingReflexiveImages.replacement w f z T S j P L).conj ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z T C P r s).conj (SyntaxMixedFormulaJudgmentSyntax.substituted w R L a f z T n D)))))))))

theorem operations_rename {m l} (w mode z a f T A C R S K H j n P r s L D : Fin m) (ρ : Fin m → Fin l) :
    (operations w mode z a f T A C R S K H j n P r s L D).rename ρ = operations (ρ w) (ρ mode) (ρ z) (ρ a) (ρ f) (ρ T) (ρ A) (ρ C) (ρ R) (ρ S) (ρ K) (ρ H) (ρ j) (ρ n) (ρ P) (ρ r) (ρ s) (ρ L) (ρ D) := by
  simp only [operations, Formula.rename, omega_rename, SyntaxNumeralSyntax.numeral_rename, empty_rename, ForcingOpenLayout.environment_rename, SyntaxCodedMixedBinderSyntax.lifted_rename, SyntaxTermSyntax.term_rename, ForcingReflexiveImages.replacement_rename, SyntaxTopCodedEnvironmentSyntax.instantiateCoded_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

private theorem cancellation {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z a f T A C R S K H j n P r s L D q : Fin m) (hop : Derives Γ (operations w mode z a f T A C R S K H j n P r s L D))
    (hc : Derives Γ (ForcingConditionRebind.compiled w a f A j n q)) :
    Derives Γ (ForcingNegShell.operandCancellation w K H A f C T q r s z D) := by
  apply OriginalUniversalBlock.intro_many 2
  apply Derives.impI
  let E := (SyntaxMixedFormulaJudgmentSyntax.substituted (old 2 w) (old 2 K) (old 2 H) (old 2 A) (old 2 f) (old 2 C) (old 2 T) (old 2 q) (slot 2 0)).conj
    (SyntaxMixedFormulaJudgmentSyntax.substituted (old 2 w) (old 2 r) (old 2 s) (old 2 C) (old 2 T) (old 2 z) (old 2 T) (slot 2 0) (slot 2 1))
  let Δ := Context.add E (raisedContext 2 Γ)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ E
  have hop2 := of_eq (operations_rename w mode z a f T A C R S K H j n P r s L D (old 2)) (HornBinderRules.under_body 2 hop E)
  have hc2 := of_eq (ForcingConditionRebind.compiled_rename w a f A j n q (old 2)) (HornBinderRules.under_body 2 hc E)
  have h0 := (Derives.conjL hop2)
  have h1 := (Derives.conjL (Derives.conjR hop2))
  have h2 := (Derives.conjL (Derives.conjR (Derives.conjR hop2)))
  have h3 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hop2))))
  have h4 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hop2)))))
  have h5 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hop2))))))
  have h6 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hop2)))))))
  have h7 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hop2))))))))
  have h8 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hop2)))))))))
  have h9 := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hop2)))))))))
  have ht := SyntaxMixedFormulaJudgment.target_type (old 2 w) (old 2 K) (old 2 H) (old 2 A) (old 2 f) (old 2 C) (old 2 T) (old 2 q) (slot 2 0) (Derives.conjL hE)
  have htop := Derives.impE (Derives.conjR (SyntaxTopFormulaCodes.instantiate_at_codes hZ2 (old 2 w) (old 2 z) (old 2 T) (old 2 C) (old 2 P) (slot 2 0) (slot 2 1) (old 2 r) (old 2 s) h0 h8)) (Derives.conjR hE)
  have hrun := Derives.impE (Derives.conjR (InstantiateTopFormulaOperation.at_codes_iff hZ2 (old 2 w) (old 2 mode) (old 2 z) (old 2 P) (old 2 T) (old 2 C) (old 2 r) (old 2 s) (slot 2 0) (slot 2 1) h0 h1 h2 h8 ht)) htop
  exact ForcingConditionOpening.from_compiled hZ2 (old 2 w) (old 2 mode) (old 2 z) (old 2 a) (old 2 f) (old 2 T) (old 2 A) (old 2 C) (old 2 R) (old 2 S) (old 2 L) (old 2 K) (old 2 H) (old 2 j) (old 2 n) (old 2 q) (slot 2 0) (slot 2 1) (old 2 D) (old 2 P) (old 2 r) (old 2 s)
    h0 h1 h2 h3 h4 hc2 h5 h6 h7 h8 (Derives.conjL hE) hrun h9

private theorem normalize_shell {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f T A C K H r s D q M O Q J F Y : Fin m) (v : Fin 4 → Fin m)
    (hw : Derives Γ (omega w))
    (hc : Derives Γ (ForcingNegShell.operandCancellation w K H A f C T q r s z D))
    (hs : Derives Γ (ForcingNegCode.shellData w a A f M O q Q v))
    (hJ : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w J Q))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T J F))
    (hi : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s C T z T F Y)) :
    Derives Γ (ForcingNegShell.normalized w K H A f C T M O q (v 0) F r s z Y D) := by
  have hAll : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w (v 3) Q) := .conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hs))))
  have eqJ := SyntaxLogicalFields.single_fields hZ 9 w J (v 3) Q hw hJ hAll
  have hOpen := SyntaxMixedFormulaJudgmentSubst.subst_n w K H A f C T J F (v 3) eqJ ho
  exact ForcingNegShell.normalize_with_cancellation hZ w z f T A C K H q r s D M O (v 0) (v 1) (v 2) (v 3) F Y hw hc
    (Derives.conjL (Derives.conjL hs)) (Derives.conjL (Derives.conjL (Derives.conjR hs)))
    (Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjR hs)))) (Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hs))))) hOpen hi

private theorem from_data {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (relation : Source.Formula (k+2)) (w mode z a f T A C R S K H j n P r s L D Q J F Y : Fin m) (v : Fin 5 → Fin m)
    (hop : Derives Γ (operations w mode z a f T A C R S K H j n P r s L D))
    (hd : Derives Γ (ForcingNegCode.data relation w a A f j n Q v))
    (hJ : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w J Q))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T J F))
    (hi : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s C T z T F Y)) :
    Derives Γ (compiledData relation w a A f j n Q K H C T F r s z Y D v) := by
  have hb := cancellation hZ w mode z a f T A C R S K H j n P r s L D (v 2) hop (Derives.conjL (Derives.conjR hd))
  let E := ForcingNegCode.shellBody w a A f (v 3) (v 4) (v 2) Q
  let Δ := Context.add E (raisedContext 4 Γ)
  have hShell : Derives Γ (shellResult w a A f (v 3) (v 4) (v 2) Q K H C T F r s z Y D) := by
    apply HornBinderRules.eliminate_many 4 E _ (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hd))))
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    have hb4 := of_eq (ForcingNegShell.operandCancellation_rename w K H A f C T (v 2) r s z D (old 4)) (HornBinderRules.under_body 4 hb E)
    have hJ4 := of_eq (SyntaxLogicalSyntax.singleCode_rename 9 w J Q (old 4)) (HornBinderRules.under_body 4 hJ E)
    have ho4 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w K H A f C T J F (old 4)) (HornBinderRules.under_body 4 ho E)
    have hi4 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w r s C T z T F Y (old 4)) (HornBinderRules.under_body 4 hi E)
    have hn := normalize_shell (HornBinderRules.zf_body 4 hZ E) (old 4 w) (old 4 z) (old 4 a) (old 4 f) (old 4 T) (old 4 A) (old 4 C) (old 4 K) (old 4 H) (old 4 r) (old 4 s) (old 4 D)
      (old 4 (v 2)) (old 4 (v 3)) (old 4 (v 4)) (old 4 Q) (old 4 J) (old 4 F) (old 4 Y) (slot 4)
      (of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 (Derives.conjL hop) E)) hb4 hE hJ4 ho4 hi4
    have hout : Derives Δ (shellResult (old 4 w) (old 4 a) (old 4 A) (old 4 f) (old 4 (v 3)) (old 4 (v 4))
        (old 4 (v 2)) (old 4 Q) (old 4 K) (old 4 H) (old 4 C) (old 4 T) (old 4 F) (old 4 r) (old 4 s) (old 4 z) (old 4 Y) (old 4 D)) := by
      apply HornBinderRules.intro_many 4 _ (slot 4)
      exact of_eq (by simp only [shellResultBody, shellResultData_rename, assign_old, assign_slot]; rfl) (.conjI hE hn)
    exact of_eq (shellResult_rename w a A f (v 3) (v 4) (v 2) Q K H C T F r s z Y D (old 4)).symm hout
  exact .conjI (Derives.conjL hd) (.conjI (Derives.conjL (Derives.conjR hd))
    (.conjI (Derives.conjL (Derives.conjR (Derives.conjR hd))) (.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hd)))) hShell)))

/-- Consume the actual complete compiler directly. All original five compiler
and four shell witnesses are eliminated by original object existence rules. -/
theorem from_compiled {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (relation : Source.Formula (k+2)) (w mode z a f T A C R S K H j n P r s L D Q J F Y : Fin m)
    (hop : Derives Γ (operations w mode z a f T A C R S K H j n P r s L D))
    (hc : Derives Γ (ForcingNegCode.compiled relation w a A f j n Q))
    (hJ : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w J Q))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T J F))
    (hi : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s C T z T F Y)) :
    Derives Γ (compiled relation w a A f j n Q K H C T F r s z Y D) := by
  let E := ForcingNegCode.body relation w a A f j n Q
  let Δ := Context.add E (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 E _ (Derives.conjR hc)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hop5 := of_eq (operations_rename w mode z a f T A C R S K H j n P r s L D (old 5)) (HornBinderRules.under_body 5 hop E)
  have hJ5 := of_eq (SyntaxLogicalSyntax.singleCode_rename 9 w J Q (old 5)) (HornBinderRules.under_body 5 hJ E)
  have ho5 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w K H A f C T J F (old 5)) (HornBinderRules.under_body 5 ho E)
  have hi5 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w r s C T z T F Y (old 5)) (HornBinderRules.under_body 5 hi E)
  have hn := from_data (HornBinderRules.zf_body 5 hZ E) relation (old 5 w) (old 5 mode) (old 5 z) (old 5 a) (old 5 f) (old 5 T) (old 5 A) (old 5 C) (old 5 R) (old 5 S) (old 5 K) (old 5 H) (old 5 j) (old 5 n) (old 5 P) (old 5 r) (old 5 s) (old 5 L) (old 5 D) (old 5 Q) (old 5 J) (old 5 F) (old 5 Y) (slot 5) hop5 hE hJ5 ho5 hi5
  have hout : Derives Δ (compiled relation (old 5 w) (old 5 a) (old 5 A) (old 5 f) (old 5 j) (old 5 n) (old 5 Q) (old 5 K) (old 5 H) (old 5 C) (old 5 T) (old 5 F) (old 5 r) (old 5 s) (old 5 z) (old 5 Y) (old 5 D)) := by
    apply HornBinderRules.intro_many 5 _ (slot 5)
    exact of_eq (by simp only [compiledBody, compiledData_rename, assign_old, assign_slot]) hn
  exact of_eq (compiled_rename relation w a A f j n Q K H C T F r s z Y D (old 5)).symm hout

/-- The same actual native InstantiateTop instance produced by rule20 suffices;
its coded environment is already one of the genuine root operations. -/
theorem from_instance {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (relation : Source.Formula (k+2)) (w mode z a f T A C R S K H j n P r s L D Q J F Y : Fin m)
    (hop : Derives Γ (operations w mode z a f T A C R S K H j n P r s L D))
    (hc : Derives Γ (ForcingNegCode.compiled relation w a A f j n Q))
    (hJ : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w J Q))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T J F))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C P F Y)) :
    Derives Γ (compiled relation w a A f j n Q K H C T F r s z Y D) := by
  have ht := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hop)))))))))
  have hcode := Derives.impE (Derives.conjL (SyntaxTopFormulaCodes.instantiate_at_codes hZ w z T C P F Y r s (Derives.conjL hop) ht)) hi
  exact from_compiled hZ relation w mode z a f T A C R S K H j n P r s L D Q J F Y hop hc hJ ho hcode

def input {k m} (relation : Source.Formula (k+2)) (w mode z a f T A C R S K H j n P r s L D Q J F Y : Fin m) : Formula m :=
  (operations w mode z a f T A C R S K H j n P r s L D).conj ((ForcingNegCode.compiled relation w a A f j n Q).conj
    ((SyntaxLogicalSyntax.singleCode 9 w J Q).conj
      ((SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T J F).conj
        (SyntaxTopFormulaSyntax.instantiated w z T C P F Y))))
def sentence {k m} (relation : Source.Formula (k+2)) (w mode z a f T A C R S K H j n P r s L D Q J F Y : Fin m) : Source.Sentence :=
  ((input relation w mode z a f T A C R S K H j n P r s L D Q J F Y).imp (compiled relation w a A f j n Q K H C T F r s z Y D)).close

theorem kernel_certificate {k m} (relation : Source.Formula (k+2)) (w mode z a f T A C R S K H j n P r s L D Q J F Y : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence relation w mode z a f T A C R S K H j n P r s L D Q J F Y)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input relation w mode z a f T A C R S K H j n P r s L D Q J F Y
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact from_instance (ZFContext.add (ZFContext.source_ZF m) E) relation w mode z a f T A C R S K H j n P r s L D Q J F Y
    (Derives.conjL h) (Derives.conjL (Derives.conjR h)) (Derives.conjL (Derives.conjR (Derives.conjR h)))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR h)))) (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h))))
def common {m} (w mode z a f T A C R S K H j n P r s : Fin m) : Formula m :=
  (omega w).conj ((SyntaxNumeralSyntax.numeral 2 mode).conj ((empty z).conj ((ForcingOpenLayout.environment w z a f T R S).conj ((SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H).conj ((Formula.mem j f).conj ((SyntaxTermSyntax.term w z T P).conj ((FormulaCodeSyntax.formulaCode w n a f).conj (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z T C P r s))))))))

theorem common_rename {m l} (w mode z a f T A C R S K H j n P r s : Fin m) (ρ : Fin m → Fin l) :
    (common w mode z a f T A C R S K H j n P r s).rename ρ = common (ρ w) (ρ mode) (ρ z) (ρ a) (ρ f) (ρ T) (ρ A) (ρ C) (ρ R) (ρ S) (ρ K) (ρ H) (ρ j) (ρ n) (ρ P) (ρ r) (ρ s) := by
  simp only [common, Formula.rename, omega_rename, SyntaxNumeralSyntax.numeral_rename, empty_rename, ForcingOpenLayout.environment_rename, SyntaxCodedMixedBinderSyntax.lifted_rename, SyntaxTermSyntax.term_rename, FormulaCodeSyntax.formulaCode_rename, SyntaxTopCodedEnvironmentSyntax.instantiateCoded_rename]

def generatedData {k m} (relation : Source.Formula (k+2)) (w z a f T A C R S K H j n P r s Q F Y L D : Fin m) : Formula m :=
  (ForcingReflexiveImages.replacement w f z T S j P L).conj
    ((SyntaxMixedFormulaJudgmentSyntax.substituted w R L a f z T n D).conj
      (compiled relation w a A f j n Q K H C T F r s z Y D))

theorem generatedData_rename {k m l} (relation : Source.Formula (k+2)) (w z a f T A C R S K H j n P r s Q F Y L D : Fin m) (ρ : Fin m → Fin l) :
    (generatedData relation w z a f T A C R S K H j n P r s Q F Y L D).rename ρ = generatedData relation (ρ w) (ρ z) (ρ a) (ρ f) (ρ T) (ρ A) (ρ C) (ρ R) (ρ S) (ρ K) (ρ H) (ρ j) (ρ n) (ρ P) (ρ r) (ρ s) (ρ Q) (ρ F) (ρ Y) (ρ L) (ρ D) := by
  simp only [generatedData, Formula.rename, ForcingReflexiveImages.replacement_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, compiled_rename]

def generatedBody {k m} (relation : Source.Formula (k+2)) (w z a f T A C R S K H j n P r s Q F Y : Fin m) : Formula (m+2) :=
  generatedData relation (old 2 w) (old 2 z) (old 2 a) (old 2 f) (old 2 T) (old 2 A) (old 2 C) (old 2 R) (old 2 S) (old 2 K) (old 2 H) (old 2 j) (old 2 n) (old 2 P) (old 2 r) (old 2 s) (old 2 Q) (old 2 F) (old 2 Y) (slot 2 0) (slot 2 1)
def generated {k m} (relation : Source.Formula (k+2)) (w z a f T A C R S K H j n P r s Q F Y : Fin m) : Formula m := existsMany 2 (generatedBody relation w z a f T A C R S K H j n P r s Q F Y)

theorem generated_rename {k m l} (relation : Source.Formula (k+2)) (w z a f T A C R S K H j n P r s Q F Y : Fin m) (ρ : Fin m → Fin l) :
    (generated relation w z a f T A C R S K H j n P r s Q F Y).rename ρ = generated relation (ρ w) (ρ z) (ρ a) (ρ f) (ρ T) (ρ A) (ρ C) (ρ R) (ρ S) (ρ K) (ρ H) (ρ j) (ρ n) (ρ P) (ρ r) (ρ s) (ρ Q) (ρ F) (ρ Y) := by
  simp only [generated, existsMany_rename, generatedBody, generatedData_rename, lift_old, lift_slot]

/-- Construct the update table and direct operand internally, then consume the
ACTUAL whole negative compiler and original native instance. No supplied table,
operand output, guard truth, operand-equality answer or proof is required. -/
theorem produce {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (relation : Source.Formula (k+2)) (w mode z a f T A C R S K H j n P r s Q J F Y : Fin m)
    (hb : Derives Γ (common w mode z a f T A C R S K H j n P r s))
    (hc : Derives Γ (ForcingNegCode.compiled relation w a A f j n Q))
    (hJ : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w J Q))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T J F))
    (hInst : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C P F Y)) :
    Derives Γ (generated relation w z a f T A C R S K H j n P r s Q F Y) := by
  have hw := (Derives.conjL hb)
  have he := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hb))))
  have hp := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hb)))))))
  have hn := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hb))))))))
  have hLists := ForcingOpenLayout.environment_types w z a f T R S he
  let B := ForcingReflexiveImages.replacement w.castSucc f.castSucc z.castSucc T.castSucc S.castSucc j.castSucc P.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (ForcingReflexiveImages.exists_replacement hZ w f z T S j P hw (Derives.conjR hLists) hp)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 := of_eq (FormulaCodeSyntax.formulaCode_rename w n a f Fin.castSucc) (under hn B)
  have hl1 := of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w a f z T R S Fin.castSucc) (under hLists B)
  have hNew := Derives.conjI (Derives.conjL hl1) (ForcingReflexiveImages.target_type w.castSucc f.castSucc z.castSucc T.castSucc S.castSucc j.castSucc P.castSucc (Fin.last m) hB)
  let E := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc.castSucc R.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc f.castSucc.castSucc z.castSucc.castSucc T.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))
  let Ξ := Context.add E (Context.image Formula.raise Δ)
  apply Derives.exE (p := E) (SyntaxMixedFormulaOutputInduction.actual_exists hZ1 w.castSucc R.castSucc (Fin.last m) a.castSucc f.castSucc z.castSucc T.castSucc n.castSucc hw1 (.conjI hn1 hNew))
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  have hUpdate := of_eq (ForcingReflexiveImages.replacement_rename w.castSucc f.castSucc z.castSucc T.castSucc S.castSucc j.castSucc P.castSucc (Fin.last m) Fin.castSucc) (under hB E)
  have hb2 : Derives Ξ (common w.castSucc.castSucc mode.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc f.castSucc.castSucc T.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc j.castSucc.castSucc n.castSucc.castSucc P.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc) := of_eq (by simp only [Formula.raise, common_rename]) (under (under hb B) E)
  have b0 := (Derives.conjL hb2)
  have b1 := (Derives.conjL (Derives.conjR hb2))
  have b2 := (Derives.conjL (Derives.conjR (Derives.conjR hb2)))
  have b3 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hb2))))
  have b4 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hb2)))))
  have b5 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hb2))))))
  have b6 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hb2)))))))
  have b7 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hb2))))))))
  have b8 := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hb2))))))))
  have hc2 : Derives Ξ (ForcingNegCode.compiled relation w.castSucc.castSucc a.castSucc.castSucc A.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc n.castSucc.castSucc Q.castSucc.castSucc) := of_eq (by simp only [Formula.raise, ForcingNegCode.compiled_rename]) (under (under hc B) E)
  have hJ2 : Derives Ξ (SyntaxLogicalSyntax.singleCode 9 w.castSucc.castSucc J.castSucc.castSucc Q.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.singleCode_rename]) (under (under hJ B) E)
  have ho2 : Derives Ξ (SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc A.castSucc.castSucc f.castSucc.castSucc C.castSucc.castSucc T.castSucc.castSucc J.castSucc.castSucc F.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]) (under (under ho B) E)
  have hInst2 : Derives Ξ (SyntaxTopFormulaSyntax.instantiated w.castSucc.castSucc z.castSucc.castSucc T.castSucc.castSucc C.castSucc.castSucc P.castSucc.castSucc F.castSucc.castSucc Y.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTopFormulaSyntax.instantiated_rename]) (under (under hInst B) E)
  have hop2 : Derives Ξ (operations w.castSucc.castSucc mode.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc f.castSucc.castSucc T.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc j.castSucc.castSucc n.castSucc.castSucc P.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))) := (.conjI b0 (.conjI b1 (.conjI b2 (.conjI b3 (.conjI b4 (.conjI b5 (.conjI b6 (.conjI hUpdate (.conjI b8 hE)))))))))
  have hResult := from_instance (ZFContext.under hZ1 E) relation w.castSucc.castSucc mode.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc f.castSucc.castSucc T.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc j.castSucc.castSucc n.castSucc.castSucc P.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) Q.castSucc.castSucc J.castSucc.castSucc F.castSucc.castSucc Y.castSucc.castSucc hop2 hc2 hJ2 ho2 hInst2
  have hout : Derives Ξ (generated relation w.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc f.castSucc.castSucc T.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc j.castSucc.castSucc n.castSucc.castSucc P.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc Q.castSucc.castSucc F.castSucc.castSucc Y.castSucc.castSucc) := by
    apply HornBinderRules.intro_many 2 _ (SetLanguage.args2 (Fin.last m).castSucc (Fin.last (m+1)))
    exact of_eq (by simp only [generatedBody, generatedData_rename, assign_old, assign_slot]; rfl) (.conjI hUpdate (.conjI hE hResult))
  exact of_eq (by simp only [Formula.raise, generated_rename]) hout

def generatedInput {k m} (relation : Source.Formula (k+2)) (w mode z a f T A C R S K H j n P r s Q J F Y : Fin m) : Formula m :=
  (common w mode z a f T A C R S K H j n P r s).conj ((ForcingNegCode.compiled relation w a A f j n Q).conj ((SyntaxLogicalSyntax.singleCode 9 w J Q).conj ((SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T J F).conj (SyntaxTopFormulaSyntax.instantiated w z T C P F Y))))

def generatedSentence {k m} (relation : Source.Formula (k+2)) (w mode z a f T A C R S K H j n P r s Q J F Y : Fin m) : Source.Sentence :=
  ((generatedInput relation w mode z a f T A C R S K H j n P r s Q J F Y).imp (generated relation w z a f T A C R S K H j n P r s Q F Y)).close

theorem generated_kernel_certificate {k m} (relation : Source.Formula (k+2)) (w mode z a f T A C R S K H j n P r s Q J F Y : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (generatedSentence relation w mode z a f T A C R S K H j n P r s Q J F Y)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := generatedInput relation w mode z a f T A C R S K H j n P r s Q J F Y
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact produce (ZFContext.add (ZFContext.source_ZF m) E) relation w mode z a f T A C R S K H j n P r s Q J F Y
    (Derives.conjL h)
    (Derives.conjL (Derives.conjR h))
    (Derives.conjL (Derives.conjR (Derives.conjR h)))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR h))))
    (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h))))

end PPAC.Migration.ForcingNegCondition
