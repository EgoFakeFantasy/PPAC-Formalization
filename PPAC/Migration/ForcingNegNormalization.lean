import PPAC.Migration.ForcingNegShell

/-! Normalize the ACTUAL complete negative compiler, keeping its head, both
original guards and same output code. This consumes the completed full-formula
body cancellation, not a substituted compiler or a supplied equality answer.
Guard validity/regularity and forcing MP remain separate unproved obligations. -/
namespace PPAC.Migration.ForcingNegNormalization
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

def operations {m} (w mode z a f T A C R S K H j n P r s D : Fin m) : Formula m :=
  (omega w).conj ((SyntaxNumeralSyntax.numeral 2 mode).conj ((empty z).conj ((ForcingOpenLayout.environment w z a f T R S).conj ((SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H).conj ((Formula.mem j f).conj ((StructuralListFieldSyntax.field w S j P).conj ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z T C P r s).conj (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a f z T n D))))))))
theorem operations_rename {m l} (w mode z a f T A C R S K H j n P r s D : Fin m) (ρ : Fin m → Fin l) :
    (operations w mode z a f T A C R S K H j n P r s D).rename ρ = operations (ρ w) (ρ mode) (ρ z) (ρ a) (ρ f) (ρ T) (ρ A) (ρ C) (ρ R) (ρ S) (ρ K) (ρ H) (ρ j) (ρ n) (ρ P) (ρ r) (ρ s) (ρ D) := by
  simp only [operations, Formula.rename, omega_rename, SyntaxNumeralSyntax.numeral_rename, empty_rename, ForcingOpenLayout.environment_rename, SyntaxCodedMixedBinderSyntax.lifted_rename, StructuralListFieldSyntax.field_rename, SyntaxTopCodedEnvironmentSyntax.instantiateCoded_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

private theorem with_rebind {m} {Γ : Context m} (w mode z a f T A C R S K H j n P r s D q : Fin m)
    (ho : Derives Γ (operations w mode z a f T A C R S K H j n P r s D))
    (hc : Derives Γ (ForcingConditionRebind.compiled w a f A j n q)) :
    Derives Γ (ForcingNegShell.cancellationBase w mode z a f T A C R S K H j n q P r s D) := by
  exact (.conjI (Derives.conjL ho) (.conjI (Derives.conjL (Derives.conjR ho)) (.conjI (Derives.conjL (Derives.conjR (Derives.conjR ho))) (.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR ho)))) (.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR ho))))) (.conjI hc (.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR ho)))))) (.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR ho))))))) (.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR ho)))))))) (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR ho)))))))))))))))))

def shellResultData {m} (w a A f M O q Q K H C T F r s z Y D : Fin m) (v : Fin 4 → Fin m) : Formula m :=
  (ForcingNegCode.shellData w a A f M O q Q v).conj
    (ForcingNegShell.normalized w K H A f C T M O q (v 0) F r s z Y D)
theorem shellResultData_rename {m l} (w a A f M O q Q K H C T F r s z Y D : Fin m) (v : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (shellResultData w a A f M O q Q K H C T F r s z Y D v).rename ρ = shellResultData (ρ w) (ρ a) (ρ A) (ρ f) (ρ M) (ρ O) (ρ q) (ρ Q) (ρ K) (ρ H) (ρ C) (ρ T) (ρ F) (ρ r) (ρ s) (ρ z) (ρ Y) (ρ D) (fun i => ρ (v i)) := by
  simp only [shellResultData, Formula.rename, ForcingNegCode.shellData_rename, ForcingNegShell.normalized_rename]
def shellResultBody {m} (w a A f M O q Q K H C T F r s z Y D : Fin m) : Formula (m+4) :=
  shellResultData (old 4 w) (old 4 a) (old 4 A) (old 4 f) (old 4 M) (old 4 O) (old 4 q) (old 4 Q) (old 4 K) (old 4 H) (old 4 C) (old 4 T) (old 4 F) (old 4 r) (old 4 s) (old 4 z) (old 4 Y) (old 4 D) (slot 4)
def shellResult {m} (w a A f M O q Q K H C T F r s z Y D : Fin m) : Formula m := existsMany 4 (shellResultBody w a A f M O q Q K H C T F r s z Y D)
theorem shellResult_rename {m l} (w a A f M O q Q K H C T F r s z Y D : Fin m) (ρ : Fin m → Fin l) :
    (shellResult w a A f M O q Q K H C T F r s z Y D).rename ρ = shellResult (ρ w) (ρ a) (ρ A) (ρ f) (ρ M) (ρ O) (ρ q) (ρ Q) (ρ K) (ρ H) (ρ C) (ρ T) (ρ F) (ρ r) (ρ s) (ρ z) (ρ Y) (ρ D) := by
  simp only [shellResult, existsMany_rename, shellResultBody, shellResultData_rename, lift_old, lift_slot]

private theorem normalize_shell {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z a f T A C R S K H j n P r s D q M O Q J F Y : Fin m) (v : Fin 4 → Fin m)
    (hb : Derives Γ (ForcingNegShell.cancellationBase w mode z a f T A C R S K H j n q P r s D))
    (hs : Derives Γ (ForcingNegCode.shellData w a A f M O q Q v))
    (hJ : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w J Q))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T J F))
    (hi : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s C T z T F Y)) :
    Derives Γ (ForcingNegShell.normalized w K H A f C T M O q (v 0) F r s z Y D) := by
  have hAll : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w (v 3) Q) := .conjL (.conjR (.conjR (.conjR (.conjR hs))))
  have eqJ := SyntaxLogicalFields.single_fields hZ 9 w J (v 3) Q (.conjL hb) hJ hAll
  have hOpen := SyntaxMixedFormulaJudgmentSubst.subst_n w K H A f C T J F (v 3) eqJ ho
  exact ForcingNegShell.normalize hZ w mode z a f T A C R S K H j n q P r s D M O (v 0) (v 1) (v 2) (v 3) F Y hb
    (.conjL (.conjL hs)) (.conjL (.conjL (.conjR hs)))
    (.conjL (.conjL (.conjR (.conjR hs)))) (.conjL (.conjL (.conjR (.conjR (.conjR hs))))) hOpen hi

/-- Original head and both guard compilations are retained, together with all
actual shell/target fields; the compiler's five witnesses stay object-bound. -/
def compiledData {k m} (relation : Source.Formula (k+2)) (w a A f j n Q K H C T F r s z Y D : Fin m) (v : Fin 5 → Fin m) : Formula m :=
  (SyntaxMixedImageHead.head w A f (v 0) (v 1)).conj
    ((ForcingConditionRebind.compiled w a f A j n (v 2)).conj
      ((ForcingGuardCode.compiled false relation w A f (v 1) (v 3)).conj
        ((ForcingGuardCode.compiled true relation w A f (v 1) (v 4)).conj
          (shellResult w a A f (v 3) (v 4) (v 2) Q K H C T F r s z Y D))))
theorem compiledData_rename {k m l} (relation : Source.Formula (k+2)) (w a A f j n Q K H C T F r s z Y D : Fin m) (v : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (compiledData relation w a A f j n Q K H C T F r s z Y D v).rename ρ = compiledData relation (ρ w) (ρ a) (ρ A) (ρ f) (ρ j) (ρ n) (ρ Q) (ρ K) (ρ H) (ρ C) (ρ T) (ρ F) (ρ r) (ρ s) (ρ z) (ρ Y) (ρ D) (fun i => ρ (v i)) := by
  simp only [compiledData, Formula.rename, SyntaxMixedImageHead.head_rename, ForcingConditionRebind.compiled_rename,
    ForcingGuardCode.compiled_rename, shellResult_rename]
def compiledBody {k m} (relation : Source.Formula (k+2)) (w a A f j n Q K H C T F r s z Y D : Fin m) : Formula (m+5) :=
  compiledData relation (old 5 w) (old 5 a) (old 5 A) (old 5 f) (old 5 j) (old 5 n) (old 5 Q) (old 5 K) (old 5 H) (old 5 C) (old 5 T) (old 5 F) (old 5 r) (old 5 s) (old 5 z) (old 5 Y) (old 5 D) (slot 5)
def compiled {k m} (relation : Source.Formula (k+2)) (w a A f j n Q K H C T F r s z Y D : Fin m) : Formula m := existsMany 5 (compiledBody relation w a A f j n Q K H C T F r s z Y D)
theorem compiled_rename {k m l} (relation : Source.Formula (k+2)) (w a A f j n Q K H C T F r s z Y D : Fin m) (ρ : Fin m → Fin l) :
    (compiled relation w a A f j n Q K H C T F r s z Y D).rename ρ = compiled relation (ρ w) (ρ a) (ρ A) (ρ f) (ρ j) (ρ n) (ρ Q) (ρ K) (ρ H) (ρ C) (ρ T) (ρ F) (ρ r) (ρ s) (ρ z) (ρ Y) (ρ D) := by
  simp only [compiled, existsMany_rename, compiledBody, compiledData_rename, lift_old, lift_slot]

private theorem from_data {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (relation : Source.Formula (k+2)) (w mode z a f T A C R S K H j n P r s D Q J F Y : Fin m) (v : Fin 5 → Fin m)
    (hop : Derives Γ (operations w mode z a f T A C R S K H j n P r s D))
    (hd : Derives Γ (ForcingNegCode.data relation w a A f j n Q v))
    (hJ : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w J Q))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T J F))
    (hi : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s C T z T F Y)) :
    Derives Γ (compiledData relation w a A f j n Q K H C T F r s z Y D v) := by
  have hb := with_rebind w mode z a f T A C R S K H j n P r s D (v 2) hop (.conjL (.conjR hd))
  let E := ForcingNegCode.shellBody w a A f (v 3) (v 4) (v 2) Q
  let Δ := Context.add E (raisedContext 4 Γ)
  have hShell : Derives Γ (shellResult w a A f (v 3) (v 4) (v 2) Q K H C T F r s z Y D) := by
    apply HornBinderRules.eliminate_many 4 E _ (.conjR (.conjR (.conjR (.conjR hd))))
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    have hb4 := of_eq (ForcingNegShell.cancellationBase_rename w mode z a f T A C R S K H j n (v 2) P r s D (old 4)) (HornBinderRules.under_body 4 hb E)
    have hJ4 := of_eq (SyntaxLogicalSyntax.singleCode_rename 9 w J Q (old 4)) (HornBinderRules.under_body 4 hJ E)
    have ho4 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w K H A f C T J F (old 4)) (HornBinderRules.under_body 4 ho E)
    have hi4 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w r s C T z T F Y (old 4)) (HornBinderRules.under_body 4 hi E)
    have hn := normalize_shell (HornBinderRules.zf_body 4 hZ E) (old 4 w) (old 4 mode) (old 4 z) (old 4 a) (old 4 f) (old 4 T) (old 4 A) (old 4 C) (old 4 R) (old 4 S) (old 4 K) (old 4 H) (old 4 j) (old 4 n) (old 4 P) (old 4 r) (old 4 s) (old 4 D)
      (old 4 (v 2)) (old 4 (v 3)) (old 4 (v 4)) (old 4 Q) (old 4 J) (old 4 F) (old 4 Y) (slot 4) hb4 hE hJ4 ho4 hi4
    have hout : Derives Δ (shellResult (old 4 w) (old 4 a) (old 4 A) (old 4 f) (old 4 (v 3)) (old 4 (v 4))
        (old 4 (v 2)) (old 4 Q) (old 4 K) (old 4 H) (old 4 C) (old 4 T) (old 4 F) (old 4 r) (old 4 s) (old 4 z) (old 4 Y) (old 4 D)) := by
      apply HornBinderRules.intro_many 4 _ (slot 4)
      exact of_eq (by simp only [shellResultBody, shellResultData_rename, assign_old, assign_slot]; rfl) (.conjI hE hn)
    exact of_eq (shellResult_rename w a A f (v 3) (v 4) (v 2) Q K H C T F r s z Y D (old 4)).symm hout
  exact .conjI (.conjL hd) (.conjI (.conjL (.conjR hd))
    (.conjI (.conjL (.conjR (.conjR hd))) (.conjI (.conjL (.conjR (.conjR (.conjR hd)))) hShell)))

/-- Consume the actual complete compiler directly. All original five compiler
and four shell witnesses are eliminated by original object existence rules. -/
theorem from_compiled {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (relation : Source.Formula (k+2)) (w mode z a f T A C R S K H j n P r s D Q J F Y : Fin m)
    (hop : Derives Γ (operations w mode z a f T A C R S K H j n P r s D))
    (hc : Derives Γ (ForcingNegCode.compiled relation w a A f j n Q))
    (hJ : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w J Q))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T J F))
    (hi : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s C T z T F Y)) :
    Derives Γ (compiled relation w a A f j n Q K H C T F r s z Y D) := by
  let E := ForcingNegCode.body relation w a A f j n Q
  let Δ := Context.add E (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 E _ (.conjR hc)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hop5 := of_eq (operations_rename w mode z a f T A C R S K H j n P r s D (old 5)) (HornBinderRules.under_body 5 hop E)
  have hJ5 := of_eq (SyntaxLogicalSyntax.singleCode_rename 9 w J Q (old 5)) (HornBinderRules.under_body 5 hJ E)
  have ho5 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w K H A f C T J F (old 5)) (HornBinderRules.under_body 5 ho E)
  have hi5 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w r s C T z T F Y (old 5)) (HornBinderRules.under_body 5 hi E)
  have hn := from_data (HornBinderRules.zf_body 5 hZ E) relation (old 5 w) (old 5 mode) (old 5 z) (old 5 a) (old 5 f) (old 5 T) (old 5 A) (old 5 C) (old 5 R) (old 5 S) (old 5 K) (old 5 H) (old 5 j) (old 5 n) (old 5 P) (old 5 r) (old 5 s) (old 5 D) (old 5 Q) (old 5 J) (old 5 F) (old 5 Y) (slot 5) hop5 hE hJ5 ho5 hi5
  have hout : Derives Δ (compiled relation (old 5 w) (old 5 a) (old 5 A) (old 5 f) (old 5 j) (old 5 n) (old 5 Q) (old 5 K) (old 5 H) (old 5 C) (old 5 T) (old 5 F) (old 5 r) (old 5 s) (old 5 z) (old 5 Y) (old 5 D)) := by
    apply HornBinderRules.intro_many 5 _ (slot 5)
    exact of_eq (by simp only [compiledBody, compiledData_rename, assign_old, assign_slot]) hn
  exact of_eq (compiled_rename relation w a A f j n Q K H C T F r s z Y D (old 5)).symm hout

/-- The same actual native InstantiateTop instance produced by rule20 suffices;
its coded environment is already one of the genuine root operations. -/
theorem from_instance {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (relation : Source.Formula (k+2)) (w mode z a f T A C R S K H j n P r s D Q J F Y : Fin m)
    (hop : Derives Γ (operations w mode z a f T A C R S K H j n P r s D))
    (hc : Derives Γ (ForcingNegCode.compiled relation w a A f j n Q))
    (hJ : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w J Q))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T J F))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C P F Y)) :
    Derives Γ (compiled relation w a A f j n Q K H C T F r s z Y D) := by
  have ht := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hop))))))))
  have hcode := Derives.impE (.conjL (SyntaxTopFormulaCodes.instantiate_at_codes hZ w z T C P F Y r s (.conjL hop) ht)) hi
  exact from_compiled hZ relation w mode z a f T A C R S K H j n P r s D Q J F Y hop hc hJ ho hcode

def input {k m} (relation : Source.Formula (k+2)) (w mode z a f T A C R S K H j n P r s D Q J F Y : Fin m) : Formula m :=
  (operations w mode z a f T A C R S K H j n P r s D).conj ((ForcingNegCode.compiled relation w a A f j n Q).conj
    ((SyntaxLogicalSyntax.singleCode 9 w J Q).conj
      ((SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T J F).conj
        (SyntaxTopFormulaSyntax.instantiated w z T C P F Y))))
def sentence {k m} (relation : Source.Formula (k+2)) (w mode z a f T A C R S K H j n P r s D Q J F Y : Fin m) : Source.Sentence :=
  ((input relation w mode z a f T A C R S K H j n P r s D Q J F Y).imp (compiled relation w a A f j n Q K H C T F r s z Y D)).close

theorem kernel_certificate {k m} (relation : Source.Formula (k+2)) (w mode z a f T A C R S K H j n P r s D Q J F Y : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence relation w mode z a f T A C R S K H j n P r s D Q J F Y)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input relation w mode z a f T A C R S K H j n P r s D Q J F Y
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact from_instance (ZFContext.add (ZFContext.source_ZF m) E) relation w mode z a f T A C R S K H j n P r s D Q J F Y
    (.conjL h) (.conjL (.conjR h)) (.conjL (.conjR (.conjR h)))
    (.conjL (.conjR (.conjR (.conjR h)))) (.conjR (.conjR (.conjR (.conjR h))))

end PPAC.Migration.ForcingNegNormalization
