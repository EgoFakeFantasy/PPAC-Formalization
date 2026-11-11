import PPAC.Migration.InternalProofOperations
import PPAC.Migration.InternalProofConjunction
import PPAC.Migration.Internal.WeakenFreeProgramCorrectness
import PPAC.Migration.Internal.SyntaxRenameNullary
import PPAC.Migration.OmegaInduction
import PPAC.Migration.InternalConsistency
import PPAC.Migration.ForcingPointwiseCode

/-! Project an actual open falsum proof to the unchanged original closed Root.
Existing constant weakening and strengthening are consumed. The number of free
slots is an INTERNAL omega value; closure uses existing object omega induction,
not an external Lean Nat iteration. No new proof kernel or evaluator. -/
namespace PPAC.Migration.InternalFalseRoot
open Internal Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ReplacementPredicates (paramsUp)
set_option maxRecDepth 16384
attribute [local irreducible] NaturalRecursionSyntax.matrix

private theorem weaken_at_maps {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b B F I J : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (FormulaCodeSyntax.formulaCode w F z b))
    (hf : Derives Γ (SyntaxAtomSyntax.zeroScalar w F))
    (hi : Derives Γ (SyntaxIdentityMapSyntax.identityCode w z I)) (hj : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J)) :
    Derives Γ (WeakenFreeProgramSyntax.executed w z b B F F) := by
  have hinput : Derives Γ (SyntaxRenameOutputSyntax.input w I J z b z B F) :=
    .conjI hc (.conjI (SyntaxIdentityCode.map_code w z I hi) (SyntaxFreeShiftCode.map_code w b B J hj))
  have hr := SyntaxRenameNullary.intro_self hZ false w I J z b z B F hw hinput hf
  exact WeakenFreeProgramCorrectness.forward hZ w z b B F F hw
    (SyntaxWeakenFreeSyntax.intro_weakened w z b B F F I J hi hj hr)

/-- The ORIGINAL free weakening really executes on the same falsum code, for
all internal scope lengths. All identity/shift code witnesses are constructed. -/
theorem weaken_falsum {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b B F : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hb : Derives Γ (.mem b w))
    (hB : Derives Γ (successor B b)) (hf : Derives Γ (SyntaxAtomSyntax.zeroScalar w F)) :
    Derives Γ (WeakenFreeProgramSyntax.executed w z b B F F) := by
  have hzN := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have hc := Derives.impE (.conjR (FormulaCodeKnownAtomic.nullary_iff hZ false w z b F hw hf)) (.conjI hzN hb)
  let I := SyntaxIdentityMapSyntax.identityCode w.castSucc z.castSucc (Fin.last m)
  let Δ := Context.add I (Context.image Formula.raise Γ)
  apply Derives.exE (p := I) (SyntaxIdentityCode.exists_code hZ w z hw hzN)
  have hI : Derives Δ I := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw I)
  let J := SyntaxFreeShiftSyntax.shiftCode w.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc (Fin.last (m+1))
  let Ξ := Context.add J (Context.image Formula.raise Δ)
  apply Derives.exE (p := J) (SyntaxFreeShiftCode.exists_code (ZFContext.under hZ I) w.castSucc b.castSucc B.castSucc hw1
    (under hb I) (of_eq (successor_rename B b Fin.castSucc) (under hB I)))
  have hJ : Derives Ξ J := .hyp (Or.inl rfl)
  have hI2 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w.castSucc z.castSucc (Fin.last m) Fin.castSucc) (under hI J)
  have out := weaken_at_maps (ZFContext.under (ZFContext.under hZ I) J) w.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc F.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) (of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 J))
    (of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) (under (under hc I) J))
    (of_eq (by simp only [Formula.raise, SyntaxAtomSyntax.zeroScalar_rename]) (under (under hf I) J)) hI2 hJ
  exact of_eq (by simp only [Formula.raise, WeakenFreeProgramSyntax.executed_rename]) out

private theorem from_result {m} {Γ : Context m} (test : Formula 1) (w z b F p : Fin m)
    (hr : Derives Γ (InternalProofOperations.existsResult test 4 w z (SetLanguage.args3 b F p))) :
    Derives Γ (InternalProofConjunction.proved test w z b F) := by
  let E := InternalProofOperations.result test 4 w.castSucc z.castSucc (Fin.last m) (fun i => (SetLanguage.args3 b F p i).castSucc)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hr
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have out : Derives Δ (InternalProofConjunction.proved test w.castSucc z.castSucc b.castSucc F.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, InternalMPProof.annotated_rename, empty_rename, ProofTreeEntryFacts.root_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]; rfl) (.conjI (.conjL hE) (.conjR (.conjR hE)))
  exact of_eq (InternalProofConjunction.proved_rename test w z b F Fin.castSucc).symm out

/-- One actual original strengthening node, using a genuine child proof;
its scope is removed in the original direction B=b+1 -> b. -/
theorem drop_scope {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b B F : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hb : Derives Γ (.mem b w))
    (hB : Derives Γ (successor B b)) (hf : Derives Γ (SyntaxAtomSyntax.zeroScalar w F))
    (hp : Derives Γ (InternalProofConjunction.proved test w z B F)) : Derives Γ (InternalProofConjunction.proved test w z b F) := by
  have he := weaken_falsum hZ w z b B F hw hz hb hB hf
  let E := (Formula.mem (Fin.last m) w.castSucc).conj
    ((InternalMPProof.annotated test w.castSucc z.castSucc B.castSucc F.castSucc (Fin.last m)).conj
      ((empty B.castSucc).imp (ProofTreeEntrySyntax.root test w.castSucc (Fin.last m) F.castSucc)))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hp
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hi : Derives Δ (InternalProofOperations.strengtheningInput test w.castSucc z.castSucc b.castSucc B.castSucc F.castSucc F.castSucc (Fin.last m)) :=
    .conjI (of_eq (successor_rename B b Fin.castSucc) (under hB E))
      (.conjI (of_eq (WeakenFreeProgramSyntax.executed_rename w z b B F F Fin.castSucc) (under he E)) (.conjI (.conjL hE) (.conjL (.conjR hE))))
  have out := from_result test w.castSucc z.castSucc b.castSucc F.castSucc (Fin.last m)
    (InternalProofOperations.strengthening (ZFContext.under hZ E) test w.castSucc z.castSucc b.castSucc B.castSucc F.castSucc F.castSucc (Fin.last m)
      (of_eq (omega_rename w Fin.castSucc) (under hw E)) (of_eq (empty_rename z Fin.castSucc) (under hz E)) hi)
  exact of_eq (InternalProofConjunction.proved_rename test w z b F Fin.castSucc).symm out

/-- The unchanged original closed proof root, with an internal proof code. -/
def closed {m} (test : Formula 1) (w F : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (ProofTreeEntrySyntax.root test w.castSucc (Fin.last m) F.castSucc))
theorem closed_rename {m l} (test : Formula 1) (w F : Fin m) (r : Fin m → Fin l) :
    (closed test w F).rename r = closed test (r w) (r F) := by
  simp only [closed, Formula.rename, ProofTreeEntryFacts.root_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem close_empty {m} {Γ : Context m} (test : Formula 1) (w z b F : Fin m)
    (hb : Derives Γ (empty b)) (hp : Derives Γ (InternalProofConjunction.proved test w z b F)) : Derives Γ (closed test w F) := by
  let E := (Formula.mem (Fin.last m) w.castSucc).conj
    ((InternalMPProof.annotated test w.castSucc z.castSucc b.castSucc F.castSucc (Fin.last m)).conj
      ((empty b.castSucc).imp (ProofTreeEntrySyntax.root test w.castSucc (Fin.last m) F.castSucc)))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hp
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hr := Derives.impE (.conjR (.conjR hE)) (of_eq (empty_rename b Fin.castSucc) (under hb E))
  have out : Derives Δ (closed test w.castSucc F.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, ProofTreeEntryFacts.root_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjL hE) hr)
  exact of_eq (closed_rename test w F Fin.castSucc).symm out

private def property {m} (test : Formula 1) (w z F b : Fin m) : Formula m :=
  (InternalProofConjunction.proved test w z b F).imp (closed test w F)
private theorem property_rename {m l} (test : Formula 1) (w z F b : Fin m) (r : Fin m → Fin l) :
    (property test w z F b).rename r = property test (r w) (r z) (r F) (r b) := by
  simp only [property, Formula.rename, InternalProofConjunction.proved_rename, closed_rename]
private def matrix {m} (test : Formula 1) (w z F : Fin m) : Formula (m+1) :=
  property test w.castSucc z.castSucc F.castSucc (Fin.last m)
private theorem matrix_pred {m l} (test : Formula 1) (w z F : Fin m) (r : Fin m → Fin l) (b : Fin l) :
    MinimalPredicates.pred (matrix test w z F) r b = property test (r w) (r z) (r F) b := by
  simp only [matrix, MinimalPredicates.pred, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem base {m} {Γ : Context m} (test : Formula 1) (w z F : Fin m) :
    Derives Γ (OmegaInductionSyntax.base (matrix test w z F) id) := by
  simp only [OmegaInductionSyntax.base, matrix_pred, paramsUp, id_eq]
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let E := empty (Fin.last m)
  let P := InternalProofConjunction.proved test w.castSucc z.castSucc (Fin.last m) F.castSucc
  let Δ := Context.add P (Context.add E (Context.image Formula.raise Γ))
  exact close_empty test w.castSucc z.castSucc (Fin.last m) F.castSucc
    (.hyp (Or.inr (Or.inl rfl)) : Derives Δ E) (.hyp (Or.inl rfl))

private theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z F : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hf : Derives Γ (SyntaxAtomSyntax.zeroScalar w F)) :
    Derives Γ (OmegaInductionSyntax.step (matrix test w z F) id w) := by
  simp only [OmegaInductionSyntax.step, matrix_pred, paramsUp, id_eq]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m).castSucc w.castSucc.castSucc
  let I := property test w.castSucc.castSucc z.castSucc.castSucc F.castSucc.castSucc (Fin.last m).castSucc
  let S := successor (Fin.last (m+1)) (Fin.last m).castSucc
  let P := InternalProofConjunction.proved test w.castSucc.castSucc z.castSucc.castSucc (Fin.last (m+1)) F.castSucc.castSucc
  let Γ2 := Context.image Formula.raise (Context.image Formula.raise Γ)
  let Δ := Context.add P (Context.add S (Context.add I (Context.add M Γ2)))
  have hZ2 := ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc
  have hZΔ : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add hZ2 M) I) S) P
  have hw2 : Derives Γ2 (omega w.castSucc.castSucc) := of_eq (by simp only [omega_rename]) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw))
  have hz2 : Derives Γ2 (empty z.castSucc.castSucc) := of_eq (by simp only [empty_rename]) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hz))
  have hf2 : Derives Γ2 (SyntaxAtomSyntax.zeroScalar w.castSucc.castSucc F.castSucc.castSucc) := of_eq (by simp only [SyntaxAtomSyntax.zeroScalar_rename]) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hf))
  have hd := drop_scope hZΔ test w.castSucc.castSucc z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) F.castSucc.castSucc
    (add (add (add (add hw2 M) I) S) P) (add (add (add (add hz2 M) I) S) P)
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) : Derives Δ M) (.hyp (Or.inr (Or.inl rfl)))
    (add (add (add (add hf2 M) I) S) P) (.hyp (Or.inl rfl))
  exact Derives.impE (.hyp (Or.inr (Or.inr (Or.inl rfl))) : Derives Δ I) hd

/-- Eliminate ALL internal free scopes by original object omega induction.
The source proof code and number of slots need not be externally standard. -/
theorem close {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b F : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hb : Derives Γ (.mem b w))
    (hf : Derives Γ (SyntaxAtomSyntax.zeroScalar w F)) (hp : Derives Γ (InternalProofConjunction.proved test w z b F)) :
    Derives Γ (closed test w F) := by
  have hall := OmegaInduction.induction_on_omega (matrix test w z F) id w (ZFContext.separation hZ _) hw (base test w z F) (step hZ test w z F hw hz hf)
  have hall' : Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property test w.castSucc z.castSucc F.castSucc (Fin.last m)))) :=
    of_eq (by simp only [OmegaInductionSyntax.holds, matrix_pred, paramsUp, id_eq]) hall
  have hi : Derives Γ ((Formula.mem b w).imp (property test w z F b)) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE b hall')
  exact .impE (.impE hi hb) hp

private theorem contradiction_of_root {m} {Γ : Context m} (target : Bool) (w p F : Fin m)
    (hq : Derives Γ (PureQuotationSyntax.formula (.falsum : PureSyntaxQuotation.Fm [] []) w F))
    (hr : Derives Γ (ProofTreeEntrySyntax.root (OriginalAxiomCodeTest.test target) w p F)) :
    Derives Γ (InternalConsistency.contradiction target w p) := by
  apply Derives.exI F
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, PureQuotationSyntax.formula_rename,
    ProofTreeEntryFacts.root_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hq hr)

private theorem inconsistentAt_rename {m l} (target : Bool) (w : Fin m) (r : Fin m → Fin l) :
    (InternalConsistency.inconsistentAt target w).rename r = InternalConsistency.inconsistentAt target (r w) := by
  simp only [InternalConsistency.inconsistentAt, InternalConsistency.contradiction, Formula.rename,
    PureQuotationSyntax.formula_rename, ProofTreeEntryFacts.root_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

/-- Directly consume the same falsum quotation and closed Root used in the
final Con contract. No alternate contradiction code or proof checker. -/
theorem inconsistent_of_closed {m} {Γ : Context m} (target : Bool) (w F : Fin m)
    (hq : Derives Γ (PureQuotationSyntax.formula (.falsum : PureSyntaxQuotation.Fm [] []) w F))
    (hc : Derives Γ (closed (OriginalAxiomCodeTest.test target) w F)) :
    Derives Γ (InternalConsistency.inconsistentAt target w) := by
  let E := (Formula.mem (Fin.last m) w.castSucc).conj
    (ProofTreeEntrySyntax.root (OriginalAxiomCodeTest.test target) w.castSucc (Fin.last m) F.castSucc)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hc
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hq1 := of_eq (PureQuotationSyntax.formula_rename (.falsum : PureSyntaxQuotation.Fm [] []) w F Fin.castSucc) (under hq E)
  have hcontr := contradiction_of_root target w.castSucc (Fin.last m) F.castSucc hq1 (.conjR hE)
  have out : Derives Δ (InternalConsistency.inconsistentAt target w.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, InternalConsistency.contradiction, Formula.rename,
      PureQuotationSyntax.formula_rename, ProofTreeEntryFacts.root_rename, Formula.liftRen,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjL hE) hcontr)
  exact of_eq (inconsistentAt_rename target w Fin.castSucc).symm out

/-- An actual open falsum proof yields the ORIGINAL internal inconsistency
formula for full ZF or U, uniformly over all internal scope/proof codes. -/
theorem inconsistent {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (target : Bool) (w z b F : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hb : Derives Γ (.mem b w))
    (hq : Derives Γ (PureQuotationSyntax.formula (.falsum : PureSyntaxQuotation.Fm [] []) w F))
    (hp : Derives Γ (InternalProofConjunction.proved (OriginalAxiomCodeTest.test target) w z b F)) :
    Derives Γ (InternalConsistency.inconsistentAt target w) := by
  have hf := OriginalQuotationNodeFields.tree_to_constructor hZ 0 List.nil w F Fin.elim0 hw (.eqRefl w) hq
  exact inconsistent_of_closed target w F hq (close hZ (OriginalAxiomCodeTest.test target) w z b F hw hz hb hf hp)

def input {m} (target : Bool) (w z b F : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((Formula.mem b w).conj
    ((PureQuotationSyntax.formula (.falsum : PureSyntaxQuotation.Fm [] []) w F).conj
      (InternalProofConjunction.proved (OriginalAxiomCodeTest.test target) w z b F))))

def sentence {m} (target : Bool) (w z b F : Fin m) : Source.Sentence :=
  ((input target w z b F).imp (InternalConsistency.inconsistentAt target w)).close

/-- Native ZF certificate; consumes an open proof, does not assert the
outstanding U-to-ZF translation or the final internal Con implication. -/
theorem kernel_certificate {m} (target : Bool) (w z b F : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence target w z b F)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input target w z b F
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact inconsistent (ZFContext.add (ZFContext.source_ZF m) E) target w z b F (.conjL h) (.conjL (.conjR h))
    (.conjL (.conjR (.conjR h))) (.conjL (.conjR (.conjR (.conjR h)))) (.conjR (.conjR (.conjR (.conjR h))))

/-- Complete the contradiction tail from an ACTUAL pointwise output proof.
This consumes the accepted exact falsum-code preservation, then the original
strengthening rule and object omega induction. It does not supply that proof. -/
theorem compiled_inconsistent {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (target : Bool)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b F t Q A B C : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (ht : Derives Γ (.mem t w))
    (hA : Derives Γ (successor A b)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hq : Derives Γ (PureQuotationSyntax.formula (.falsum : PureSyntaxQuotation.Fm [] []) w F))
    (hc : Derives Γ (ForcingPointwiseCode.compiled R H w z f j b F t Q))
    (hp : Derives Γ (InternalProofConjunction.proved (OriginalAxiomCodeTest.test target) w z t Q)) :
    Derives Γ (InternalConsistency.inconsistentAt target w) := by
  have he := ForcingPointwiseCode.falsum hZ R H w z f j b F t Q A B C hw hA hB hC hq hc
  let P := InternalProofConjunction.proved (OriginalAxiomCodeTest.test target) w.castSucc z.castSucc t.castSucc (Fin.last m)
  have hpF : Derives Γ (InternalProofConjunction.proved (OriginalAxiomCodeTest.test target) w z t F) :=
    of_eq (by simp only [P, Formula.instantiate, InternalProofConjunction.proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, InternalProofConjunction.proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hp))
  exact inconsistent hZ target w z t F hw hz ht hq hpF

def compiledInput {k m} (target : Bool) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b F t Q A B C : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((Formula.mem t w).conj ((successor A b).conj
    ((successor B A).conj ((successor C B).conj
      ((PureQuotationSyntax.formula (.falsum : PureSyntaxQuotation.Fm [] []) w F).conj
        ((ForcingPointwiseCode.compiled R H w z f j b F t Q).conj
          (InternalProofConjunction.proved (OriginalAxiomCodeTest.test target) w z t Q))))))))

def compiledSentence {k m} (target : Bool) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b F t Q A B C : Fin m) : Source.Sentence :=
  ((compiledInput target R H w z f j b F t Q A B C).imp (InternalConsistency.inconsistentAt target w)).close

theorem compiled_kernel_certificate {k m} (target : Bool) (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j b F t Q A B C : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (compiledSentence target R H w z f j b F t Q A B C)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := compiledInput target R H w z f j b F t Q A B C
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact compiled_inconsistent (ZFContext.add (ZFContext.source_ZF m) E) target R H w z f j b F t Q A B C
    (.conjL h)
    (.conjL (.conjR h))
    (.conjL (.conjR (.conjR h)))
    (.conjL (.conjR (.conjR (.conjR h))))
    (.conjL (.conjR (.conjR (.conjR (.conjR h)))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR h))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h))))))))
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h))))))))

end PPAC.Migration.InternalFalseRoot
