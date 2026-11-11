import PPAC.Migration.ForcingFreshParentOpening
import PPAC.Migration.InternalProofQuantifier

/-! The old compiled parent supplies the actual proof of the fresh
instance. Use the original proof substitution and guarded forall rules. -/
namespace PPAC.Migration.ForcingOldParentInstance
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open InternalProofConjunction (proved proved_rename)
open InternalProofBackground (implication implication_rename)
open SyntaxLogicalSyntax (binaryCode binaryCode_rename singleCode singleCode_rename)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open SyntaxWeakenFreeSyntax (weakened weakened_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 500000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private theorem substitute_proof {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (w z b B L F N : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hx : Derives Γ (FreeSubstProgramSyntax.executed w z b B L F N))
    (hp : Derives Γ (proved test w z b F)) : Derives Γ (proved test w z B N) := by
  let P := (Formula.mem (Fin.last m) w.castSucc).conj
    ((InternalMPProof.annotated test w.castSucc z.castSucc b.castSucc F.castSucc (Fin.last m)).conj
      ((empty b.castSucc).imp (ProofTreeEntrySyntax.root test w.castSucc (Fin.last m) F.castSucc)))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) hp
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz P)
  have hx1 := of_eq (FreeSubstProgramSyntax.executed_rename w z b B L F N Fin.castSucc) (under hx P)
  have out := InternalProofOperations.substitution hZ1 test w.castSucc z.castSucc B.castSucc b.castSucc
    L.castSucc N.castSucc F.castSucc (Fin.last m) hw1 hz1
    (.conjI hx1 (.conjI (.conjL hP) (.conjL (.conjR hP))))
  apply of_eq (proved_rename test w z B N Fin.castSucc).symm
  let args : Fin 5 → Fin (m+1) :=
    Fin.cases B.castSucc (Fin.cases N.castSucc (Fin.cases b.castSucc (SyntaxAtomSyntax.two L.castSucc (Fin.last m))))
  let E := InternalProofOperations.result test 5 (old 2 w) (old 2 z) (Fin.last (m+1))
    (fun i => (args i).castSucc)
  let Ξ := Context.add E (Context.image Formula.raise Δ)
  apply Derives.exE (p := E) out
  have record : Derives Ξ E := .hyp (Or.inl rfl)
  have hOut : Derives Ξ (proved test (old 2 w) (old 2 z) (old 2 B) (old 2 N)) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, InternalMPProof.annotated_rename, empty_rename,
      ProofTreeEntryFacts.root_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]; rfl)
      (.conjI (.conjL record) (.conjR (.conjR record)))
  exact of_eq (by simp only [Formula.raise, proved_rename]; rfl) hOut

/-- Raise the actual proof by the original rule5 using the term-list
realization of the same shift code already used by formula weakening. -/
theorem raise_proof {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (w z b B F N I J : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w z I))
    (hJ : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (hWeak : Derives Γ (weakened w z b B F N))
    (hp : Derives Γ (proved test w z b F)) : Derives Γ (proved test w z B N) := by
  have hRen := Derives.impE (.conjL (SyntaxWeakenFreeUnique.at_codes_iff hZ w z b B F N I J hw hI hJ)) hWeak
  let C := SyntaxFreeSubstSyntax.codeConversion w.castSucc b.castSucc B.castSucc (Fin.last m) J.castSucc
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply Derives.exE (p := C) (SyntaxFreeSubstCode.from_map hZ w b B J hw (SyntaxFreeShiftCode.map_code w b B J hJ))
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ C
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw C)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz C)
  have hI1 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w z I Fin.castSucc) (under hI C)
  have hr1 := of_eq (SyntaxRenameJudgmentSyntax.renamed_rename w I J z b z B F N Fin.castSucc) (under hRen C)
  have hs := SyntaxFormulaFreeSubstSyntax.intro_substituted w.castSucc z.castSucc b.castSucc B.castSucc (Fin.last m)
    F.castSucc N.castSucc I.castSucc J.castSucc hI1 hC hr1
  have hx := Derives.impE (.conjR (FreeSubstProgramCorrectness.executed_iff hZ1 w.castSucc z.castSucc b.castSucc
    B.castSucc (Fin.last m) F.castSucc N.castSucc hw1)) hs
  exact of_eq (proved_rename test w z B N Fin.castSucc).symm
    (substitute_proof hZ1 test w.castSucc z.castSucc b.castSucc B.castSucc (Fin.last m) F.castSucc N.castSucc
      hw1 hz1 hx (of_eq (proved_rename test w z b F Fin.castSucc) (under hp C)))


private theorem exists_imp {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b G N : Fin m) (hw : Derives Γ (omega w))
    (hG : Derives Γ (formulaCode w G z b)) (hN : Derives Γ (formulaCode w N z b)) :
    Derives Γ (.ex ((Formula.mem (Fin.last m) w.castSucc).conj
      (binaryCode 2 w.castSucc G.castSucc N.castSucc (Fin.last m)))) := by
  have hGnat := Derives.conjL (FormulaCodeProperties.guards w G z b hG)
  have hNnat := Derives.conjL (FormulaCodeProperties.guards w N z b hN)
  have hi := SyntaxForestSyntax.intro_inputs 2 w (SyntaxAtomSyntax.two G N)
    (fun i => Fin.cases hGnat (fun j => Fin.cases hNnat (fun e => Fin.elim0 e) j) i)
  exact of_eq (by simp only [SyntaxNodeSyntax.existsConstructor, SyntaxAtomSyntax.two_map]; rfl)
    (SyntaxConstructors.exists_constructor hZ 2 7 w (SyntaxAtomSyntax.two G N) hw hi)

private theorem guarded_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z B A t F U G Y I : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hG : Derives Γ (formulaCode w G z B))
    (hAll : Derives Γ (singleCode 9 w F U))
    (hInst : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z B A t F Y))
    (hI : Derives Γ (binaryCode 2 w G U I))
    (hp : Derives Γ (proved test w z B I)) : Derives Γ (implication test w z B G Y) := by
  have hY := SyntaxTopFormulaTyping.instantiate_target_type w z B A t F Y hInst
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (binaryCode 2 w.castSucc G.castSucc Y.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (exists_imp hZ w z B G Y hw hG hY)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hproof := InternalProofQuantifier.guarded_eliminate (ZFContext.under hZ E) test
    w.castSucc z.castSucc B.castSucc A.castSucc F.castSucc t.castSucc Y.castSucc U.castSucc
    G.castSucc I.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw E))
    (of_eq (empty_rename z Fin.castSucc) (under hz E))
    (of_eq (SyntaxTopFormulaSyntax.instantiated_rename w z B A t F Y Fin.castSucc) (under hInst E))
    (of_eq (singleCode_rename 9 w F U Fin.castSucc) (under hAll E))
    (of_eq (formulaCode_rename w G z B Fin.castSucc) (under hG E))
    (of_eq (binaryCode_rename 2 w G U I Fin.castSucc) (under hI E))
    (.conjR hE) (of_eq (proved_rename test w z B I Fin.castSucc) (under hp E))
  apply of_eq (implication_rename test w z B G Y Fin.castSucc).symm
  apply Derives.exI (Fin.last m)
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename,
    SyntaxAtomSyntax.two_map, proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]; rfl)
    (.conjI (.conjR hE) hproof)

private def frame {m} (w z b B A t F Parent U G W Y I J : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((successor B b).conj
    ((SyntaxIdentityMapSyntax.identityCode w z I).conj ((SyntaxFreeShiftSyntax.shiftCode w b B J).conj
      ((weakened w z b B G W).conj ((weakened w z b B Parent U).conj
        ((singleCode 9 w F U).conj (SyntaxTopFormulaSyntax.instantiated w z B A t F Y))))))))

private theorem frame_rename {m l} (w z b B A t F Parent U G W Y I J : Fin m) (r : Fin m → Fin l) :
    (frame w z b B A t F Parent U G W Y I J).rename r =
      frame (r w) (r z) (r b) (r B) (r A) (r t) (r F) (r Parent) (r U) (r G) (r W) (r Y) (r I) (r J) := by
  simp only [frame, Formula.rename, omega_rename, empty_rename, successor_rename,
    SyntaxIdentityMapSyntax.identityCode_rename, SyntaxFreeShiftSyntax.shiftCode_rename, weakened_rename,
    singleCode_rename, SyntaxTopFormulaSyntax.instantiated_rename]

private theorem with_raised_code {m} {Γ : Context m}
    (hZ : ZFContext.Evidence Γ) (test : Formula 1) (w z b B G N W U I J P : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hB : Derives Γ (successor B b))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w z I))
    (hJ : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (hWG : Derives Γ (weakened w z b B G W)) (hWN : Derives Γ (weakened w z b B N U))
    (hP : Derives Γ (binaryCode 2 w G N P)) (hp : Derives Γ (proved test w z b P)) (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (X : Fin l),
      ZFContext.Evidence Δ → (∀ {F : Formula m}, Derives Γ F → Derives Δ (F.rename r)) →
      Derives Δ (binaryCode 2 (r w) (r W) (r U) X) →
      Derives Δ (proved test (r w) (r z) (r B) X) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  have hW := SyntaxWeakenFreeOutput.target_type w z b B G W hWG
  have hU := SyntaxWeakenFreeOutput.target_type w z b B N U hWN
  refine NativeProofQuotation.eliminate_objects hZ 1 (fun r x =>
    (Formula.mem (x 0) (r w)).conj (binaryCode 2 (r w) (r W) (r U) (x 0)))
    (exists_imp hZ w z B W U hw hW hU) out ?_
  intro l Δ r x hZ1 lift hE
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hz1 := of_eq (empty_rename z r) (lift hz)
  have hB1 := of_eq (successor_rename B b r) (lift hB)
  have hWG1 := of_eq (weakened_rename w z b B G W r) (lift hWG)
  have hWN1 := of_eq (weakened_rename w z b B N U r) (lift hWN)
  have hG1 := SyntaxWeakenFreeOutput.source_type hZ1 (r w) (r z) (r b) (r B) (r G) (r W) hw1 hWG1
  have scopes := Derives.conjR (FormulaCodeProperties.guards (r w) (r G) (r z) (r b) hG1)
  have hP1 := of_eq (binaryCode_rename 2 w G N P r) (lift hP)
  have hWhole := Derives.impE (.conjR (SyntaxWeakenFreeLogicalInternal.binary_iff hZ1 2 (r w) (r z)
    (r b) (r B) (r P) (x 0) (r G) (r N) (r W) (r U)
    hw1 (.conjL scopes) (.conjR scopes) hB1 hP1 (.conjR hE))) (.conjI hWG1 hWN1)
  have hRaised := raise_proof hZ1 test (r w) (r z) (r b) (r B) (r P) (x 0) (r I) (r J)
    hw1 hz1 (of_eq (SyntaxIdentityMapSyntax.identityCode_rename _ _ _ r) (lift hI))
    (of_eq (SyntaxFreeShiftSyntax.shiftCode_rename _ _ _ _ r) (lift hJ)) hWhole
    (of_eq (proved_rename test w z b P r) (lift hp))
  exact use r (x 0) hZ1 lift (.conjR hE) hRaised

/-- Raise the original Root proof of an implication to the common next free
scope, using the actual weakening records of both operands. -/
theorem raise_implication {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b B G N W U I J : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hB : Derives Γ (successor B b))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w z I))
    (hJ : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (hWG : Derives Γ (weakened w z b B G W)) (hWN : Derives Γ (weakened w z b B N U))
    (hp : Derives Γ (implication test w z b G N)) : Derives Γ (implication test w z B W U) := by
  let out := implication test w z B W U
  refine NativeProofQuotation.eliminate_objects hZ 1 (fun r x =>
    (binaryCode 2 (r w) (r G) (r N) (x 0)).conj (proved test (r w) (r z) (r b) (x 0)))
    hp out ?_
  intro l Δ r x hZ1 lift hP
  refine of_eq (implication_rename test _ _ _ _ _ r).symm ?_
  refine with_raised_code hZ1 test (r w) (r z) (r b) (r B) (r G) (r N) (r W) (r U) (r I) (r J)
    (x 0) (of_eq (omega_rename w r) (lift hw)) (of_eq (empty_rename z r) (lift hz))
    (of_eq (successor_rename B b r) (lift hB))
    (of_eq (SyntaxIdentityMapSyntax.identityCode_rename _ _ _ r) (lift hI))
    (of_eq (SyntaxFreeShiftSyntax.shiftCode_rename _ _ _ _ r) (lift hJ))
    (of_eq (weakened_rename _ _ _ _ _ _ r) (lift hWG)) (of_eq (weakened_rename _ _ _ _ _ _ r) (lift hWN))
    (.conjL hP) (.conjR hP) (implication test (r w) (r z) (r B) (r W) (r U)) ?_
  intro l' Ξ s X _ _ hCode hProof
  refine of_eq (implication_rename test _ _ _ _ _ s).symm ?_
  apply Derives.exI X
  exact of_eq (by
    simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename,
      SyntaxAtomSyntax.two_map, proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    rfl) (.conjI hCode hProof)

private theorem from_implication_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b B A t F Parent U G W Y I J P : Fin m)
    (hf : Derives Γ (frame w z b B A t F Parent U G W Y I J))
    (hP : Derives Γ (binaryCode 2 w G Parent P)) (hp : Derives Γ (proved test w z b P)) :
    Derives Γ (implication test w z B W Y) := by
  have hw := Derives.conjL hf
  have hz := Derives.conjL (.conjR hf)
  have next := Derives.conjR (.conjR hf)
  have maps := Derives.conjR next
  have weak := Derives.conjR (.conjR maps)
  have hW := SyntaxWeakenFreeOutput.target_type w z b B G W (.conjL weak)
  refine with_raised_code hZ test w z b B G Parent W U I J P hw hz (.conjL next)
    (.conjL maps) (.conjL (.conjR maps)) (.conjL weak) (.conjL (.conjR weak))
    hP hp (implication test w z B W Y) ?_
  intro l Δ r X hZ1 lift hCode hRaised
  have hFrame := of_eq (frame_rename _ _ _ _ _ _ _ _ _ _ _ _ _ _ r) (lift hf)
  have inst := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hFrame))))))
  exact of_eq (implication_rename test w z B W Y r).symm
    (guarded_at hZ1 test (r w) (r z) (r B) (r A) (r t) (r F) (r U) (r W) (r Y) X
      (of_eq (omega_rename w r) (lift hw)) (of_eq (empty_rename z r) (lift hz))
      (of_eq (formulaCode_rename w W z B r) (lift hW)) (.conjL inst) (.conjR inst) hCode hRaised)

private theorem from_frame {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b B A t F Parent U G W Y I J : Fin m)
    (hf : Derives Γ (frame w z b B A t F Parent U G W Y I J))
    (hp : Derives Γ (implication test w z b G Parent)) :
    Derives Γ (implication test w z B W Y) := by
  let E := (binaryCode 2 w.castSucc G.castSucc Parent.castSucc (Fin.last m)).conj
    (proved test w.castSucc z.castSucc b.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hp
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hf1 := of_eq (frame_rename w z b B A t F Parent U G W Y I J Fin.castSucc) (under hf E)
  exact of_eq (implication_rename test w z B W Y Fin.castSucc).symm
    (from_implication_code (ZFContext.under hZ E) test w.castSucc z.castSucc b.castSucc B.castSucc A.castSucc
      t.castSucc F.castSucc Parent.castSucc U.castSucc G.castSucc W.castSucc Y.castSucc I.castSucc J.castSucc
      (Fin.last m) hf1 (.conjL hE) (.conjR hE))


/-- The old Root proof at its original scope gives a proof of the very same
raw instance retained by the fresh-parent opening, under the weakened
background. The new parent body and its instance are read from that record. -/
theorem from_opened {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z a f alpha b A B t R S n x Parent G W : Fin m) (v : Fin 10 → Fin m) (u : Fin 9 → Fin m)
    (hOpen : Derives Γ (ForcingFreshParentOpening.data w z a f alpha b A B t R S n x Parent v u))
    (hWeakG : Derives Γ (weakened w z b B G W))
    (hOld : Derives Γ (implication test w z b G Parent)) :
    Derives Γ (implication test w z B W (u 8)) := by
  have src := Derives.conjL hOpen
  have hw := Derives.conjL src
  have rest := Derives.conjR hOpen
  have images := Derives.conjL rest
  have maps := Derives.conjL (.conjR images)
  have rest := Derives.conjR (.conjR rest)
  have liftNew := Derives.conjL rest
  have rest := Derives.conjR (.conjR rest)
  have newBody := Derives.conjL rest
  have rest := Derives.conjR rest
  have newParent := Derives.conjL rest
  have inverse := Derives.conjL (.conjR (.conjR (.conjR (.conjR rest))))
  have inst := Derives.conjR (.conjR (.conjR (.conjR (.conjR inverse))))
  have oldFields := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR src))))))
  have typed := SyntaxMixedFormulaJudgmentTyping.input_of_substituted hZ w (v 8) (v 9) a f z B n (u 6) hw newParent
  have hAll := ForcingMixedUnary.quantified_constructor hZ true w (v 8) (v 9) a f z B n x
    (u 6) (u 5) alpha A (u 2) (u 3) hw (.conjI (.conjR typed) (.conjL typed))
    (.conjL oldFields) newParent liftNew newBody
  have hWU := ForcingWeakenedImages.from_queries hZ w a f z b B R S n Parent (u 6) v
    (.conjI images (.conjI (.conjR oldFields) newParent))
  have hf : Derives Γ (frame w z b B A t (u 5) Parent (u 6) G W (u 8) (v 0) (v 1)) := by
    refine .conjI hw (.conjI (.conjL (.conjR src)) ?_)
    refine .conjI (.conjL (.conjR (.conjR (.conjR (.conjR src))))) ?_
    exact .conjI (.conjL maps) (.conjI (.conjL (.conjR maps))
      (.conjI hWeakG (.conjI hWU (.conjI hAll inst))))
  exact from_frame hZ test w z b B A t (u 5) Parent (u 6) G W (u 8) (v 0) (v 1) hf hOld

def sentence {m} (test : Formula 1) (w z a f alpha b A B t R S n x Parent G W : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) : Source.Sentence :=
  (((ForcingFreshParentOpening.data w z a f alpha b A B t R S n x Parent v u).conj
      ((weakened w z b B G W).conj (implication test w z b G Parent))).imp
    (implication test w z B W (u 8))).close

theorem kernel_certificate {m} (test : Formula 1) (w z a f alpha b A B t R S n x Parent G W : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (sentence test w z a f alpha b A B t R S n x Parent G W v u)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact from_opened (ZFContext.add (ZFContext.source_ZF m) _) test w z a f alpha b A B t R S n x Parent G W v u
    (.conjL (.hyp (Or.inl rfl))) (.conjL (.conjR (.hyp (Or.inl rfl)))) (.conjR (.conjR (.hyp (Or.inl rfl))))


/-- Use the existing canonical context and row to discharge both old guards.
The tail is the same operand of the actual opened implication. -/
theorem consume_guards {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z B C Refl Pre Extra Y Middle Tail : Fin m)
    (Gb : Fin 5 → Fin m) (H ctx : Fin 6 → Fin m) (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hExtra : Derives Γ (formulaCode w Extra z B)) (hY : Derives Γ (formulaCode w Y z B))
    (hRow : Derives Γ (ForcingTransitiveGuardProof.row w z B C Refl Pre Gb H U F P N))
    (hl : Derives Γ (ForcingProofContext.layoutData w z B Extra Pre H ctx))
    (hOuter : Derives Γ (binaryCode 2 w (H 0) Middle Y))
    (hInner : Derives Γ (binaryCode 2 w (H 5) Tail Middle))
    (hp : Derives Γ (implication test w z B (ctx 3) Y)) :
    Derives Γ (ForcingProofContext.resultData test w z B Extra Pre Tail H ctx) := by
  have tOuter := Derives.conjR (Derives.impE
    (.conjL (FormulaCodeKnownLogical.binary2_iff hZ w z B (H 0) Middle Y hw hOuter)) hY)
  have tInner := Derives.conjR (Derives.impE
    (.conjL (FormulaCodeKnownLogical.binary2_iff hZ w z B (H 5) Tail Middle hw hInner)) (.conjR tOuter))
  have global := Derives.conjL (.conjR (.conjR (.conjR hl)))
  have localGuard := Derives.conjL (.conjR (.conjR (.conjR (.conjR hl))))
  have context := Derives.conjR (.conjR (.conjR (.conjR (.conjR hl))))
  have tg := Derives.conjR global
  have tl := Derives.conjR localGuard
  have tc := Derives.conjR context
  have c := Derives.conjL context
  have pW := ForcingRelationGuardProof.project hZ test false w z B (ctx 3) (ctx 4) (ctx 5) hw hz tg tl tc c
  have pY := ForcingRelationGuardProof.chain hZ test w z B (ctx 5) (ctx 3) Y hw hz tc tg hY pW hp
  have projection := Derives.conjR
    (ForcingProofContext.canonical_projections hZ test w z B C Refl Pre Extra Gb H U F P N ctx hw hz hExtra hRow hl)
  have guards := ForcingTransitiveGuardProof.at_background hZ test w z B C Refl Pre Gb H U F P N hw hz hRow
  have hGb := Derives.conjL hRow
  have pMember := ForcingRelationGuardProof.chain hZ test w z B (ctx 5) (Gb 0) (H 0)
    hw hz tc hGb (.conjL tOuter) projection (.conjL guards)
  have pOrder := ForcingRelationGuardProof.chain hZ test w z B (ctx 5) (Gb 0) (H 5)
    hw hz tc hGb (.conjL tInner) projection (.conjR guards)
  have pMiddle := ForcingNegMemberProof.discharge hZ test w z B (ctx 5) (H 0) Middle Y
    hw hz tc hY hOuter pMember pY
  have pTail := ForcingNegMemberProof.discharge hZ test w z B (ctx 5) (H 5) Tail Middle
    hw hz tc (.conjR tOuter) hInner pOrder pMiddle
  exact .conjI hl (.conjI pTail (InternalProofCurry.from_implication hZ test w z B
    (ctx 3) (ctx 4) (ctx 5) Tail hw hz tg tl (.conjR tInner) c pTail))

end PPAC.Migration.ForcingOldParentInstance
