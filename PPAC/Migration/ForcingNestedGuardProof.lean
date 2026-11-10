import PPAC.Migration.ForcingGlobalWeakening

/-! Restore the literal M -> (O -> Tail) body of pinned force_mono/neg/ex.
The existing context stores Global AND (M AND O). Generate two original
AND codes, reuse existing projections/join/chain and Curry.twice, then use
the unchanged mode3 and guarded-forall producers. No guard truth, desired
body code, abstraction answer or Root proof is supplied. Final matching
against a complete independently queried new parent is still required. -/
namespace PPAC.Migration.ForcingNestedGuardProof
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open SyntaxLogicalSyntax (binaryCode binaryCode_rename)
open InternalProofBackground (implication implication_rename)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

private structure Leaves {m} (Γ : Context m) (test : Formula 1) (w z b G M O L Whole Tail : Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  hw : Derives Γ (omega w)
  hz : Derives Γ (empty z)
  global_type : Derives Γ (formulaCode w G z b)
  member_type : Derives Γ (formulaCode w M z b)
  order_type : Derives Γ (formulaCode w O z b)
  local_type : Derives Γ (formulaCode w L z b)
  whole_type : Derives Γ (formulaCode w Whole z b)
  tail_type : Derives Γ (formulaCode w Tail z b)
  local_ctor : Derives Γ (binaryCode 0 w M O L)
  whole_ctor : Derives Γ (binaryCode 0 w G L Whole)
  tail_proof : Derives Γ (implication test w z b Whole Tail)
private theorem Leaves.in_body {m l} {Γ : Context m} {test : Formula 1} {w z b G M O L Whole Tail : Fin m}
    (h : Leaves Γ test w z b G M O L Whole Tail) (E : Formula (m+l)) :
    Leaves (Context.add E (raisedContext l Γ)) test (old l w) (old l z) (old l b) (old l G)
      (old l M) (old l O) (old l L) (old l Whole) (old l Tail) :=
  ⟨HornBinderRules.zf_body l h.zf E,
    of_eq (omega_rename w (old l)) (HornBinderRules.under_body l h.hw E),
    of_eq (empty_rename z (old l)) (HornBinderRules.under_body l h.hz E),
    of_eq (formulaCode_rename w G z b (old l)) (HornBinderRules.under_body l h.global_type E),
    of_eq (formulaCode_rename w M z b (old l)) (HornBinderRules.under_body l h.member_type E),
    of_eq (formulaCode_rename w O z b (old l)) (HornBinderRules.under_body l h.order_type E),
    of_eq (formulaCode_rename w L z b (old l)) (HornBinderRules.under_body l h.local_type E),
    of_eq (formulaCode_rename w Whole z b (old l)) (HornBinderRules.under_body l h.whole_type E),
    of_eq (formulaCode_rename w Tail z b (old l)) (HornBinderRules.under_body l h.tail_type E),
    of_eq (binaryCode_rename 0 w M O L (old l)) (HornBinderRules.under_body l h.local_ctor E),
    of_eq (binaryCode_rename 0 w G L Whole (old l)) (HornBinderRules.under_body l h.whole_ctor E),
    of_eq (implication_rename test w z b Whole Tail (old l)) (HornBinderRules.under_body l h.tail_proof E)⟩

private theorem at_two_codes {m} {Γ : Context m} {test : Formula 1} {w z b G M O L Whole Tail : Fin m}
    (h : Leaves Γ test w z b G M O L Whole Tail) (C1 C2 : Fin m)
    (h1 : Derives Γ (FormulaCodeConstructSyntax.typedAt 2 5 w (SyntaxAtomSyntax.two G M) C1 z b))
    (h2 : Derives Γ (FormulaCodeConstructSyntax.typedAt 2 5 w (SyntaxAtomSyntax.two C1 O) C2 z b)) :
    Derives Γ (InternalProofCurry.doubleResult test w z b G M O Tail) := by
  have p1 := ForcingRelationGuardProof.project h.zf test false w z b C1 O C2 h.hw h.hz (.conjR h1) h.order_type (.conjR h2) (.conjL h2)
  have po := ForcingRelationGuardProof.project h.zf test true w z b C1 O C2 h.hw h.hz (.conjR h1) h.order_type (.conjR h2) (.conjL h2)
  have pg0 := ForcingRelationGuardProof.project h.zf test false w z b G M C1 h.hw h.hz h.global_type h.member_type (.conjR h1) (.conjL h1)
  have pm0 := ForcingRelationGuardProof.project h.zf test true w z b G M C1 h.hw h.hz h.global_type h.member_type (.conjR h1) (.conjL h1)
  have pg := ForcingRelationGuardProof.chain h.zf test w z b C2 C1 G h.hw h.hz (.conjR h2) (.conjR h1) h.global_type p1 pg0
  have pm := ForcingRelationGuardProof.chain h.zf test w z b C2 C1 M h.hw h.hz (.conjR h2) (.conjR h1) h.member_type p1 pm0
  have pl := ForcingProofContext.join h.zf test w z b C2 M O L h.hw h.hz (.conjR h2) h.member_type h.order_type h.local_ctor pm po
  have pw := ForcingProofContext.join h.zf test w z b C2 G L Whole h.hw h.hz (.conjR h2) h.global_type h.local_type h.whole_ctor pg pl
  have pt := ForcingRelationGuardProof.chain h.zf test w z b C2 Whole Tail h.hw h.hz (.conjR h2) h.whole_type h.tail_type pw h.tail_proof
  exact InternalProofCurry.twice h.zf test w z b G M O C1 C2 Tail
    h.hw h.hz h.global_type h.member_type h.order_type h.tail_type (.conjL h1) (.conjL h2) pt

private theorem after_first {m} {Γ : Context m} {test : Formula 1} {w z b G M O L Whole Tail : Fin m}
    (h : Leaves Γ test w z b G M O L Whole Tail) (C1 : Fin m)
    (h1 : Derives Γ (FormulaCodeConstructSyntax.typedAt 2 5 w (SyntaxAtomSyntax.two G M) C1 z b)) :
    Derives Γ (InternalProofCurry.doubleResult test w z b G M O Tail) := by
  let E := (Formula.mem (Fin.last m) w.castSucc).conj
    (FormulaCodeConstructSyntax.typedAt 2 5 w.castSucc (SyntaxAtomSyntax.two C1.castSucc O.castSucc) (Fin.last m) z.castSucc b.castSucc)
  apply Derives.exE (p := E) (ForcingProofContext.and_exists h.zf w z b C1 O h.hw (.conjR h1) h.order_type)
  have hE : Derives (Context.add E (Context.image Formula.raise Γ)) E := .hyp (Or.inl rfl)
  exact of_eq (InternalProofCurry.doubleResult_rename test w z b G M O Tail Fin.castSucc).symm
    (at_two_codes (h.in_body E) C1.castSucc (Fin.last m)
      (of_eq (by simp only [FormulaCodeConstructSyntax.typedAt_rename, SyntaxAtomSyntax.two_map]) (SourceLogic.under h1 E)) (.conjR hE))

private theorem nested {m} {Γ : Context m} {test : Formula 1} {w z b G M O L Whole Tail : Fin m}
    (h : Leaves Γ test w z b G M O L Whole Tail) :
    Derives Γ (InternalProofCurry.doubleResult test w z b G M O Tail) := by
  let E := (Formula.mem (Fin.last m) w.castSucc).conj
    (FormulaCodeConstructSyntax.typedAt 2 5 w.castSucc (SyntaxAtomSyntax.two G.castSucc M.castSucc) (Fin.last m) z.castSucc b.castSucc)
  apply Derives.exE (p := E) (ForcingProofContext.and_exists h.zf w z b G M h.hw h.global_type h.member_type)
  have hE : Derives (Context.add E (Context.image Formula.raise Γ)) E := .hyp (Or.inl rfl)
  exact of_eq (InternalProofCurry.doubleResult_rename test w z b G M O Tail Fin.castSucc).symm
    (after_first (h.in_body E) (Fin.last m) (.conjR hE))

/-- Actual double Curry witnesses I=(O->Tail), K=(M->I), actual mode3 J,
and the original guarded forall output under the SAME unextended G. -/
def data {m} (test : Formula 1) (w z b A B G W M O Tail I K J : Fin m) : Formula m :=
  (InternalProofCurry.doubleData test w z B W M O Tail I K).conj
    ((formulaCode w K z B).conj ((SyntaxTopFormulaSyntax.abstracted w z b A B K J).conj
      (InternalProofUniversal.guarded test w z b G J)))
theorem data_rename {m l} (test : Formula 1) (w z b A B G W M O Tail I K J : Fin m) (ρ : Fin m → Fin l) :
    (data test w z b A B G W M O Tail I K J).rename ρ =
      data test (ρ w) (ρ z) (ρ b) (ρ A) (ρ B) (ρ G) (ρ W) (ρ M) (ρ O) (ρ Tail) (ρ I) (ρ K) (ρ J) := by
  simp only [data, Formula.rename, InternalProofCurry.doubleData_rename, formulaCode_rename,
    SyntaxTopFormulaSyntax.abstracted_rename, InternalProofUniversal.guarded_rename]
def body {m} (test : Formula 1) (w z b A B G W M O Tail : Fin m) : Formula (m+3) :=
  data test (old 3 w) (old 3 z) (old 3 b) (old 3 A) (old 3 B) (old 3 G) (old 3 W)
    (old 3 M) (old 3 O) (old 3 Tail) (slot 3 0) (slot 3 1) (slot 3 2)
def produced {m} (test : Formula 1) (w z b A B G W M O Tail : Fin m) : Formula m :=
  existsMany 3 (body test w z b A B G W M O Tail)
theorem produced_rename {m l} (test : Formula 1) (w z b A B G W M O Tail : Fin m) (ρ : Fin m → Fin l) :
    (produced test w z b A B G W M O Tail).rename ρ =
      produced test (ρ w) (ρ z) (ρ b) (ρ A) (ρ B) (ρ G) (ρ W) (ρ M) (ρ O) (ρ Tail) := by
  simp only [produced, existsMany_rename, body, data_rename, lift_old, lift_slot]
private theorem intro_produced {m} {Γ : Context m} (test : Formula 1) (w z b A B G W M O Tail I K J : Fin m)
    (hd : Derives Γ (data test w z b A B G W M O Tail I K J)) :
    Derives Γ (produced test w z b A B G W M O Tail) := by
  apply HornBinderRules.intro_many 3 _ (Fin.cases I (SyntaxAtomSyntax.two K J))
  exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]; rfl) hd

private theorem at_curry {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B G W M O Tail I K : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hG : Derives Γ (formulaCode w G z b)) (hM : Derives Γ (formulaCode w M z B))
    (hO : Derives Γ (formulaCode w O z B)) (hTail : Derives Γ (formulaCode w Tail z B))
    (ha : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B W G))
    (hc : Derives Γ (InternalProofCurry.doubleData test w z B W M O Tail I K)) :
    Derives Γ (produced test w z b A B G W M O Tail) := by
  have hI := Derives.impE (.conjR (FormulaCodeKnownLogical.binary2_iff hZ w z B O Tail I hw (.conjL hc)))
    (.conjI (.conjR (FormulaCodeProperties.guards w O z B hO)) (.conjI hO hTail))
  have hK := Derives.impE (.conjR (FormulaCodeKnownLogical.binary2_iff hZ w z B M I K hw (.conjL (.conjR hc))))
    (.conjI (.conjR (FormulaCodeProperties.guards w M z B hM)) (.conjI hM hI))
  have he := SyntaxTopFormulaExistence.abstract_exists hZ w z b A B K hw
    (.conjI (SyntaxTopFormulaTyping.abstract_environment w z b A B W G ha) hK)
  let E := SyntaxTopFormulaSyntax.abstracted w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc K.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hc1 := of_eq (InternalProofCurry.doubleData_rename test w z B W M O Tail I K Fin.castSucc) (SourceLogic.under hc E)
  have hK1 := of_eq (formulaCode_rename w K z B Fin.castSucc) (SourceLogic.under hK E)
  have hJ := SyntaxTopFormulaTyping.abstract_target_type w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc K.castSucc (Fin.last m) hE
  have hb : Derives Δ (ForcingProofUniversal.bodyData test w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc
    W.castSucc M.castSucc I.castSucc K.castSucc (Fin.last m)) :=
    .conjI (.conjL (.conjR hc1)) (.conjI hK1 (.conjI (.conjR (.conjR hc1)) (.conjI hE hJ)))
  have hp := ForcingProofUniversal.generalize_body (ZFContext.under hZ E) test
    w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc G.castSucc W.castSucc M.castSucc I.castSucc K.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (SourceLogic.under hw E))
    (of_eq (empty_rename z Fin.castSucc) (SourceLogic.under hz E))
    (of_eq (formulaCode_rename w G z b Fin.castSucc) (SourceLogic.under hG E))
    (of_eq (SyntaxTopFormulaSyntax.abstracted_rename w z b A B W G Fin.castSucc) (SourceLogic.under ha E)) hb
  exact of_eq (produced_rename test w z b A B G W M O Tail Fin.castSucc).symm
    (intro_produced test w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc G.castSucc W.castSucc
      M.castSucc O.castSucc Tail.castSucc I.castSucc K.castSucc (Fin.last m)
      (.conjI hc1 (.conjI hK1 (.conjI hE hp))))

private theorem from_double {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B G W M O Tail : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hG : Derives Γ (formulaCode w G z b)) (hM : Derives Γ (formulaCode w M z B))
    (hO : Derives Γ (formulaCode w O z B)) (hTail : Derives Γ (formulaCode w Tail z B))
    (ha : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B W G))
    (hd : Derives Γ (InternalProofCurry.doubleResult test w z B W M O Tail)) :
    Derives Γ (produced test w z b A B G W M O Tail) := by
  let E := InternalProofCurry.doubleBody test w z B W M O Tail
  apply HornBinderRules.eliminate_many 2 E _ hd
  have hE : Derives (Context.add E (raisedContext 2 Γ)) E := .hyp (Or.inl rfl)
  exact of_eq (produced_rename test w z b A B G W M O Tail (old 2)).symm
    (at_curry (HornBinderRules.zf_body 2 hZ E) test (old 2 w) (old 2 z) (old 2 b) (old 2 A) (old 2 B)
      (old 2 G) (old 2 W) (old 2 M) (old 2 O) (old 2 Tail) (slot 2 0) (slot 2 1)
      (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E))
      (of_eq (empty_rename z (old 2)) (HornBinderRules.under_body 2 hz E))
      (of_eq (formulaCode_rename w G z b (old 2)) (HornBinderRules.under_body 2 hG E))
      (of_eq (formulaCode_rename w M z B (old 2)) (HornBinderRules.under_body 2 hM E))
      (of_eq (formulaCode_rename w O z B (old 2)) (HornBinderRules.under_body 2 hO E))
      (of_eq (formulaCode_rename w Tail z B (old 2)) (HornBinderRules.under_body 2 hTail E))
      (of_eq (SyntaxTopFormulaSyntax.abstracted_rename w z b A B W G (old 2)) (HornBinderRules.under_body 2 ha E)) hE)

/-- Read the actual canonical context result. Generate both reassociation
ANDs, both original Curry outputs and the literal nested body's abstraction,
then ACTUALLY consume the existing guarded forall. Only original typing
metadata, actual weakening and actual context/Root records are inputs. -/
theorem produce {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B G Extra Pre Tail : Fin m) (H ctx : Fin 6 → Fin m)
    (hf : Derives Γ (ForcingFreshBackground.input w z b A B G (ctx 3)))
    (hG : Derives Γ (formulaCode w G z b)) (hTail : Derives Γ (formulaCode w Tail z B))
    (hd : Derives Γ (ForcingProofContext.resultData test w z B Extra Pre Tail H ctx)) :
    Derives Γ (produced test w z b A B G (ctx 3) (H 0) (H 3) Tail) := by
  have hw := Derives.conjL hf
  have hz := Derives.conjL (Derives.conjR hf)
  have hl := Derives.conjL hd
  have g := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hl)))
  have l := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hl))))
  have whole := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hl))))
  have types := Derives.conjR (Derives.impE (.conjL
    (FormulaCodeKnownLogical.binary0_iff hZ w z B (H 0) (H 3) (ctx 4) hw (.conjL l))) (.conjR l))
  have leaves : Leaves Γ test w z B (ctx 3) (H 0) (H 3) (ctx 4) (ctx 5) Tail :=
    ⟨hZ,hw,hz,.conjR g,.conjL types,.conjR types,.conjR l,.conjR whole,hTail,
      .conjL l,.conjL whole,.conjL (.conjR hd)⟩
  have ha := ForcingFreshBackground.derive hZ w z b A B G (ctx 3) hf
  exact from_double hZ test w z b A B G (ctx 3) (H 0) (H 3) Tail
    hw hz hG (.conjL types) (.conjR types) hTail ha (nested leaves)

/-- SAME actual Global.data supplies the weakening and original runtime
metadata. No separate weak-Global or abstraction answer is requested. -/
theorem from_global {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1) (Reln : Source.Formula (k+2))
    (w z A1 A2 A3 f b B R S K Extra Tail : Fin m) (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m)
    (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) (oldCtx : Fin 6 → Fin m) (y : Fin 7 → Fin m)
    (hg : Derives Γ (ForcingGlobalWeakening.data test Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx y))
    (hTail : Derives Γ (formulaCode w Tail z B))
    (hd : Derives Γ (ForcingProofContext.resultData test w z B (y 0) (Pre 1) Tail
      (ForcingMemberRows.leafFields (fun i => x (i.addNat 24))) (fun i => y i.succ))) :
    Derives Γ (produced test w z b (C 1) B (oldCtx 3) (y 4)
      (ForcingMemberRows.leafFields (fun i => x (i.addNat 24)) 0)
      (ForcingMemberRows.leafFields (fun i => x (i.addNat 24)) 3) Tail) := by
  have source := Derives.conjL hg
  have fresh := Derives.conjL (Derives.conjR source)
  have freshInput := Derives.conjL fresh
  have base := Derives.conjL (Derives.conjR (Derives.conjR freshInput))
  have oldLayout := Derives.conjR (Derives.conjR (Derives.conjR source))
  have oldGlobal := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR oldLayout)))
  have hf : Derives Γ (ForcingFreshBackground.input w z b (C 1) B (oldCtx 3) (y 4)) :=
    .conjI (.conjL (.conjL base)) (.conjI (.conjL freshInput)
      (.conjI (.conjL (.conjR freshInput)) (.conjR (.conjR (.conjR hg)))))
  exact produce hZ test w z b (C 1) B (oldCtx 3) (y 0) (Pre 1) Tail
    (ForcingMemberRows.leafFields (fun i => x (i.addNat 24))) (fun i => y i.succ) hf (.conjR oldGlobal) hTail hd

def sentence {m} (target : Bool) (w z b A B G Extra Pre Tail : Fin m) (H ctx : Fin 6 → Fin m) : Source.Sentence :=
  (((ForcingFreshBackground.input w z b A B G (ctx 3)).conj
    ((formulaCode w G z b).conj ((formulaCode w Tail z B).conj
      (ForcingProofContext.resultData (OriginalAxiomCodeTest.test target) w z B Extra Pre Tail H ctx)))).imp
        (produced (OriginalAxiomCodeTest.test target) w z b A B G (ctx 3) (H 0) (H 3) Tail)).close
theorem kernel_certificate {m} (target : Bool) (w z b A B G Extra Pre Tail : Fin m) (H ctx : Fin 6 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence target w z b A B G Extra Pre Tail H ctx)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact produce (ZFContext.add (ZFContext.source_ZF m) _) (OriginalAxiomCodeTest.test target)
    w z b A B G Extra Pre Tail H ctx (.conjL (.hyp (Or.inl rfl)))
    (.conjL (.conjR (.hyp (Or.inl rfl)))) (.conjL (.conjR (.conjR (.hyp (Or.inl rfl)))))
    (.conjR (.conjR (.conjR (.hyp (Or.inl rfl)))))

def globalSentence {k m} (target : Bool) (Reln : Source.Formula (k+2))
    (w z A1 A2 A3 f b B R S K Extra Tail : Fin m) (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m)
    (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) (oldCtx : Fin 6 → Fin m) (y : Fin 7 → Fin m) : Source.Sentence :=
  (((ForcingGlobalWeakening.data (OriginalAxiomCodeTest.test target) Reln w z A1 A2 A3 f b B R S K Extra raw v C Refl Pre U0 P x oldCtx y).conj
    ((formulaCode w Tail z B).conj
      (ForcingProofContext.resultData (OriginalAxiomCodeTest.test target) w z B (y 0) (Pre 1) Tail
        (ForcingMemberRows.leafFields (fun i => x (i.addNat 24))) (fun i => y i.succ)))).imp
    (produced (OriginalAxiomCodeTest.test target) w z b (C 1) B (oldCtx 3) (y 4)
      (ForcingMemberRows.leafFields (fun i => x (i.addNat 24)) 0)
      (ForcingMemberRows.leafFields (fun i => x (i.addNat 24)) 3) Tail)).close
theorem global_kernel_certificate {k m} (target : Bool) (Reln : Source.Formula (k+2))
    (w z A1 A2 A3 f b B R S K Extra Tail : Fin m) (raw : Fin 16 → Fin m) (v : Fin 10 → Fin m)
    (C Refl Pre U0 : Fin 2 → Fin m) (P : Fin 2 → Fin 3 → Fin m) (x : Fin 48 → Fin m) (oldCtx : Fin 6 → Fin m) (y : Fin 7 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (globalSentence target Reln w z A1 A2 A3 f b B R S K Extra Tail raw v C Refl Pre U0 P x oldCtx y)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact from_global (ZFContext.add (ZFContext.source_ZF m) _) (OriginalAxiomCodeTest.test target)
    Reln w z A1 A2 A3 f b B R S K Extra Tail raw v C Refl Pre U0 P x oldCtx y
    (.conjL (.hyp (Or.inl rfl))) (.conjL (.conjR (.hyp (Or.inl rfl)))) (.conjR (.conjR (.hyp (Or.inl rfl))))

end PPAC.Migration.ForcingNestedGuardProof
