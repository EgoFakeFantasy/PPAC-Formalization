import PPAC.Migration.ForcingProofContext

/-! Pinned force_mono/ex: consume the SAME generated context and Curry body,
generate its actual first-free-slot abstraction internally, and feed the
existing guarded forall rule. Global weakening/abstraction matching is a
separate actual operation obligation; it is not inferred from the Global label.
No alternative proof kernel, syntax operation, recursor or induction. -/
namespace PPAC.Migration.ForcingProofUniversal
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open SyntaxLogicalSyntax (binaryCode binaryCode_rename)
open InternalProofBackground (implication implication_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
attribute [local irreducible] NaturalRecursionSyntax.matrix

/-- F is the ACTUAL Local -> Tail code from the SAME Curry execution;
J is produced by the EXISTING mode3 abstraction, not supplied as an answer. -/
def bodyData {m} (test : Formula 1) (w z b A B W Local Tail F J : Fin m) : Formula m :=
  (binaryCode 2 w Local Tail F).conj
    ((formulaCode w F z B).conj ((implication test w z B W F).conj
      ((SyntaxTopFormulaSyntax.abstracted w z b A B F J).conj (formulaCode w J A b))))

theorem bodyData_rename {m l} (test : Formula 1) (w z b A B W Local Tail F J : Fin m) (ρ : Fin m → Fin l) :
    (bodyData test w z b A B W Local Tail F J).rename ρ =
      bodyData test (ρ w) (ρ z) (ρ b) (ρ A) (ρ B) (ρ W) (ρ Local) (ρ Tail) (ρ F) (ρ J) := by
  simp only [bodyData, Formula.rename, binaryCode_rename, formulaCode_rename,
    implication_rename, SyntaxTopFormulaSyntax.abstracted_rename]

private def bodyBody {m} (test : Formula 1) (w z b A B W Local Tail : Fin m) : Formula (m+2) :=
  bodyData test (old 2 w) (old 2 z) (old 2 b) (old 2 A) (old 2 B) (old 2 W)
    (old 2 Local) (old 2 Tail) (slot 2 0) (slot 2 1)

def bodyResult {m} (test : Formula 1) (w z b A B W Local Tail : Fin m) : Formula m :=
  existsMany 2 (bodyBody test w z b A B W Local Tail)

theorem bodyResult_rename {m l} (test : Formula 1) (w z b A B W Local Tail : Fin m) (ρ : Fin m → Fin l) :
    (bodyResult test w z b A B W Local Tail).rename ρ =
      bodyResult test (ρ w) (ρ z) (ρ b) (ρ A) (ρ B) (ρ W) (ρ Local) (ρ Tail) := by
  simp only [bodyResult, existsMany_rename, bodyBody, bodyData_rename, lift_old, lift_slot]

private theorem at_body {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B W Local Tail F : Fin m) (hw : Derives Γ (omega w))
    (he : Derives Γ (SyntaxTopEnvironmentSyntax.abstractInput w z b A B))
    (hLocal : Derives Γ (formulaCode w Local z B)) (hTail : Derives Γ (formulaCode w Tail z B))
    (hc : Derives Γ (binaryCode 2 w Local Tail F))
    (hp : Derives Γ (implication test w z B W F)) :
    Derives Γ (bodyResult test w z b A B W Local Tail) := by
  have hF := Derives.impE (.conjR (FormulaCodeKnownLogical.binary2_iff hZ w z B Local Tail F hw hc))
    (.conjI (.conjR (FormulaCodeProperties.guards w Local z B hLocal)) (.conjI hLocal hTail))
  have hj := SyntaxTopFormulaExistence.abstract_exists hZ w z b A B F hw (.conjI he hF)
  let E := SyntaxTopFormulaSyntax.abstracted w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc F.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hj
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hJ := SyntaxTopFormulaTyping.abstract_target_type w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc F.castSucc (Fin.last m) hE
  have hf := of_eq (formulaCode_rename w F z B Fin.castSucc) (under hF E)
  have hctor := of_eq (binaryCode_rename 2 w Local Tail F Fin.castSucc) (under hc E)
  have hproof := of_eq (implication_rename test w z B W F Fin.castSucc) (under hp E)
  have ho : Derives Δ (bodyResult test w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc W.castSucc Local.castSucc Tail.castSucc) := by
    apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two F.castSucc (Fin.last m))
    exact of_eq (by simp only [bodyBody, bodyData_rename, assign_old, assign_slot]; rfl)
      (.conjI hctor (.conjI hf (.conjI hproof (.conjI hE hJ))))
  exact of_eq (bodyResult_rename test w z b A B W Local Tail Fin.castSucc).symm ho

/-- Eliminate the SAME actual Curry witness, generate its typed abstraction,
and retain BOTH formula witnesses in OBJECT EX2. No provided F/J/forall code. -/
theorem at_layout {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B Extra Pre Tail : Fin m) (H v : Fin 6 → Fin m)
    (hw : Derives Γ (omega w))
    (he : Derives Γ (SyntaxTopEnvironmentSyntax.abstractInput w z b A B))
    (hTail : Derives Γ (formulaCode w Tail z B))
    (h : Derives Γ (ForcingProofContext.resultData test w z B Extra Pre Tail H v)) :
    Derives Γ (bodyResult test w z b A B (v 3) (v 4) Tail) := by
  have hl := Derives.conjL h
  have hLocal := Derives.conjR (.conjL (.conjR (.conjR (.conjR (.conjR hl)))))
  have hc := Derives.conjR (.conjR h)
  let E := (binaryCode 2 w.castSucc (v 4).castSucc Tail.castSucc (Fin.last m)).conj
    (implication test w.castSucc z.castSucc B.castSucc (v 3).castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hc
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ho := at_body (ZFContext.under hZ E) test w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc
    (v 3).castSucc (v 4).castSucc Tail.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw E))
    (of_eq (SyntaxTopEnvironmentSyntax.abstractInput_rename w z b A B Fin.castSucc) (under he E))
    (of_eq (formulaCode_rename w (v 4) z B Fin.castSucc) (under hLocal E))
    (of_eq (formulaCode_rename w Tail z B Fin.castSucc) (under hTail E))
    (.conjL hE) (.conjR hE)
  exact of_eq (bodyResult_rename test w z b A B (v 3) (v 4) Tail Fin.castSucc).symm ho

/-- Feed the ACTUAL newly generated body abstraction to the EXISTING full
guarded forall producer. The ONE remaining global abstraction is explicitly
an actual operation premise; this theorem does not establish its freshness. -/
theorem generalize_body {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B G W Local Tail F J : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hG : Derives Γ (formulaCode w G z b))
    (hGlobal : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B W G))
    (h : Derives Γ (bodyData test w z b A B W Local Tail F J)) :
    Derives Γ (InternalProofUniversal.guarded test w z b G J) := by
  have hp := Derives.conjL (.conjR (.conjR h))
  let E := (binaryCode 2 w.castSucc W.castSucc F.castSucc (Fin.last m)).conj
    (InternalProofConjunction.proved test w.castSucc z.castSucc B.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hp
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hAbs := Derives.conjL (.conjR (.conjR (.conjR h)))
  have hi : Derives Δ (InternalProofUniversal.input test w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc
      G.castSucc W.castSucc F.castSucc J.castSucc (Fin.last m)) := .conjI
    (of_eq (omega_rename w Fin.castSucc) (under hw E)) (.conjI
      (of_eq (empty_rename z Fin.castSucc) (under hz E)) (.conjI
        (of_eq (formulaCode_rename w G z b Fin.castSucc) (under hG E)) (.conjI
          (of_eq (SyntaxTopFormulaSyntax.abstracted_rename w z b A B W G Fin.castSucc) (under hGlobal E)) (.conjI
            (of_eq (SyntaxTopFormulaSyntax.abstracted_rename w z b A B F J Fin.castSucc) (under hAbs E)) hE))))
  have ho := InternalProofUniversal.guarded_generalize (ZFContext.under hZ E) test
    w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc G.castSucc W.castSucc F.castSucc J.castSucc (Fin.last m) hi
  exact of_eq (InternalProofUniversal.guarded_rename test w z b G J Fin.castSucc).symm ho

def resultData {m} (test : Formula 1) (w z b A B Extra Pre Tail : Fin m) (H v : Fin 6 → Fin m) : Formula m :=
  (ForcingProofContext.resultData test w z B Extra Pre Tail H v).conj
    (bodyResult test w z b A B (v 3) (v 4) Tail)

theorem resultData_rename {m l} (test : Formula 1) (w z b A B Extra Pre Tail : Fin m)
    (H v : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (resultData test w z b A B Extra Pre Tail H v).rename ρ =
      resultData test (ρ w) (ρ z) (ρ b) (ρ A) (ρ B) (ρ Extra) (ρ Pre) (ρ Tail) (fun i => ρ (H i)) (fun i => ρ (v i)) := by
  simp only [resultData, Formula.rename, ForcingProofContext.resultData_rename, bodyResult_rename]

private def resultBody {m} (test : Formula 1) (w z b A B Extra Pre Tail : Fin m) (H : Fin 6 → Fin m) : Formula (m+6) :=
  resultData test (old 6 w) (old 6 z) (old 6 b) (old 6 A) (old 6 B) (old 6 Extra) (old 6 Pre) (old 6 Tail)
    (fun i => old 6 (H i)) (slot 6)

def result {m} (test : Formula 1) (w z b A B Extra Pre Tail : Fin m) (H : Fin 6 → Fin m) : Formula m :=
  existsMany 6 (resultBody test w z b A B Extra Pre Tail H)

theorem result_rename {m l} (test : Formula 1) (w z b A B Extra Pre Tail : Fin m) (H : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (result test w z b A B Extra Pre Tail H).rename ρ =
      result test (ρ w) (ρ z) (ρ b) (ρ A) (ρ B) (ρ Extra) (ρ Pre) (ρ Tail) (fun i => ρ (H i)) := by
  simp only [result, existsMany_rename, resultBody, resultData_rename, lift_old, lift_slot]

def input {m} (test : Formula 1) (w z b A B C Refl Pre Extra Ctx Tail Y Middle : Fin m)
    (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) : Formula m :=
  (SyntaxTopEnvironmentSyntax.abstractInput w z b A B).conj
    (ForcingProofContext.input test w z B C Refl Pre Extra Ctx Tail Y Middle G H U F P N)

theorem input_rename {m l} (test : Formula 1) (w z b A B C Refl Pre Extra Ctx Tail Y Middle : Fin m)
    (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (ρ : Fin m → Fin l) :
    (input test w z b A B C Refl Pre Extra Ctx Tail Y Middle G H U F P N).rename ρ =
      input test (ρ w) (ρ z) (ρ b) (ρ A) (ρ B) (ρ C) (ρ Refl) (ρ Pre) (ρ Extra) (ρ Ctx) (ρ Tail) (ρ Y) (ρ Middle)
        (fun i => ρ (G i)) (fun i => ρ (H i)) (fun i => ρ (U i)) (fun i => ρ (F i)) (fun i => ρ (P i)) (fun i => ρ (N i)) := by
  simp only [input, Formula.rename, SyntaxTopEnvironmentSyntax.abstractInput_rename, ForcingProofContext.input_rename]

/-- Source old-context result -> generated canonical context -> SAME Curry
body -> ACTUAL mode3 body abstraction. ALL six layout and both body/output
witnesses are generated and object-bound. No background abstraction is asserted. -/
theorem derive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B C Refl Pre Extra Ctx Tail Y Middle : Fin m)
    (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m)
    (hi : Derives Γ (input test w z b A B C Refl Pre Extra Ctx Tail Y Middle G H U F P N)) :
    Derives Γ (result test w z b A B Extra Pre Tail H) := by
  have hs := Derives.conjR hi
  have hc := ForcingProofContext.derive hZ test w z B C Refl Pre Extra Ctx Tail Y Middle G H U F P N hs
  let E := ForcingProofContext.resultData test (old 6 w) (old 6 z) (old 6 B) (old 6 Extra) (old 6 Pre) (old 6 Tail)
    (fun i => old 6 (H i)) (slot 6)
  let Δ := Context.add E (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 E _ hc
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hi6 := of_eq (input_rename test w z b A B C Refl Pre Extra Ctx Tail Y Middle G H U F P N (old 6))
    (HornBinderRules.under_body 6 hi E)
  have hs6 := Derives.conjR hi6
  have hr6 := Derives.conjR (.conjR (.conjR (.conjR (.conjR hs6))))
  have hTail := Derives.conjL (.conjR (.conjR hr6))
  have hp := at_layout (HornBinderRules.zf_body 6 hZ E) test (old 6 w) (old 6 z) (old 6 b) (old 6 A) (old 6 B)
    (old 6 Extra) (old 6 Pre) (old 6 Tail) (fun i => old 6 (H i)) (slot 6)
    (.conjL hs6) (.conjL hi6) hTail hE
  have ho : Derives Δ (result test (old 6 w) (old 6 z) (old 6 b) (old 6 A) (old 6 B) (old 6 Extra) (old 6 Pre) (old 6 Tail)
      (fun i => old 6 (H i))) := by
    apply HornBinderRules.intro_many 6 _ (slot 6)
    exact of_eq (by simp only [resultBody, resultData_rename, assign_old, assign_slot]; rfl) (.conjI hE hp)
  exact of_eq (result_rename test w z b A B Extra Pre Tail H (old 6)).symm ho

def sentence {m} (test : Formula 1) (w z b A B C Refl Pre Extra Ctx Tail Y Middle : Fin m)
    (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) : Source.Sentence :=
  ((input test w z b A B C Refl Pre Extra Ctx Tail Y Middle G H U F P N).imp
    (result test w z b A B Extra Pre Tail H)).close

theorem kernel_certificate {m} (test : Formula 1) (w z b A B C Refl Pre Extra Ctx Tail Y Middle : Fin m)
    (G : Fin 5 → Fin m) (H : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (sentence test w z b A B C Refl Pre Extra Ctx Tail Y Middle G H U F P N)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input test w z b A B C Refl Pre Extra Ctx Tail Y Middle G H U F P N
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have hE : Derives Γ E := .hyp (Or.inl rfl)
  exact derive (ZFContext.add (ZFContext.source_ZF m) E) test w z b A B C Refl Pre Extra Ctx Tail Y Middle G H U F P N hE

/-- Both actual body witnesses plus the EXISTING original guarded forall
output. The sole explicit global operation must still be matched by the source
freshening consumer; no equality/freshness answer is silently inserted. -/
def guarded {m} (test : Formula 1) (w z b A B G W Local Tail : Fin m) : Formula m :=
  existsMany 2 ((bodyData test (old 2 w) (old 2 z) (old 2 b) (old 2 A) (old 2 B) (old 2 W) (old 2 Local) (old 2 Tail) (slot 2 0) (slot 2 1)).conj
    (InternalProofUniversal.guarded test (old 2 w) (old 2 z) (old 2 b) (old 2 G) (slot 2 1)))

theorem guarded_rename {m l} (test : Formula 1) (w z b A B G W Local Tail : Fin m) (ρ : Fin m → Fin l) :
    (guarded test w z b A B G W Local Tail).rename ρ =
      guarded test (ρ w) (ρ z) (ρ b) (ρ A) (ρ B) (ρ G) (ρ W) (ρ Local) (ρ Tail) := by
  simp only [guarded, existsMany_rename, Formula.rename, bodyData_rename, InternalProofUniversal.guarded_rename, lift_old, lift_slot]

theorem generalize_layout {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B G Extra Pre Tail : Fin m) (H v : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hG : Derives Γ (formulaCode w G z b))
    (hGlobal : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B (v 3) G))
    (h : Derives Γ (resultData test w z b A B Extra Pre Tail H v)) :
    Derives Γ (guarded test w z b A B G (v 3) (v 4) Tail) := by
  let E := bodyBody test w z b A B (v 3) (v 4) Tail
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ (.conjR h)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hp := generalize_body (HornBinderRules.zf_body 2 hZ E) test (old 2 w) (old 2 z) (old 2 b)
    (old 2 A) (old 2 B) (old 2 G) (old 2 (v 3)) (old 2 (v 4)) (old 2 Tail) (slot 2 0) (slot 2 1)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E))
    (of_eq (empty_rename z (old 2)) (HornBinderRules.under_body 2 hz E))
    (of_eq (formulaCode_rename w G z b (old 2)) (HornBinderRules.under_body 2 hG E))
    (of_eq (SyntaxTopFormulaSyntax.abstracted_rename w z b A B (v 3) G (old 2)) (HornBinderRules.under_body 2 hGlobal E)) hE
  have ho : Derives Δ (guarded test (old 2 w) (old 2 z) (old 2 b) (old 2 A) (old 2 B) (old 2 G)
      (old 2 (v 3)) (old 2 (v 4)) (old 2 Tail)) := by
    apply HornBinderRules.intro_many 2 _ (slot 2)
    exact of_eq (by simp only [Formula.rename, bodyData_rename, InternalProofUniversal.guarded_rename, assign_old, assign_slot]; rfl) (.conjI hE hp)
  exact of_eq (guarded_rename test w z b A B G (v 3) (v 4) Tail (old 2)).symm ho

def guardedInput {m} (test : Formula 1) (w z b A B G Extra Pre Tail : Fin m) (H v : Fin 6 → Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((formulaCode w G z b).conj
    ((SyntaxTopFormulaSyntax.abstracted w z b A B (v 3) G).conj
      (resultData test w z b A B Extra Pre Tail H v))))

def guardedSentence {m} (test : Formula 1) (w z b A B G Extra Pre Tail : Fin m) (H v : Fin 6 → Fin m) : Source.Sentence :=
  ((guardedInput test w z b A B G Extra Pre Tail H v).imp
    (guarded test w z b A B G (v 3) (v 4) Tail)).close

/-- Actual global-operation conditional certificate, not source freshness.
The generated body and forall/Root witnesses remain internal and are not input. -/
theorem guarded_kernel_certificate {m} (test : Formula 1) (w z b A B G Extra Pre Tail : Fin m) (H v : Fin 6 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (guardedSentence test w z b A B G Extra Pre Tail H v)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := guardedInput test w z b A B G Extra Pre Tail H v
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have hE : Derives Γ E := .hyp (Or.inl rfl)
  exact generalize_layout (ZFContext.add (ZFContext.source_ZF m) E) test w z b A B G Extra Pre Tail H v
    (.conjL hE) (.conjL (.conjR hE)) (.conjL (.conjR (.conjR hE)))
    (.conjL (.conjR (.conjR (.conjR hE)))) (.conjR (.conjR (.conjR (.conjR hE))))

end PPAC.Migration.ForcingProofUniversal
