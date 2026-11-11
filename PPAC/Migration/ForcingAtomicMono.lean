import PPAC.Migration.NativeProofQuotation
import PPAC.Migration.ForcingNegMemberProof
import PPAC.Migration.ForcingProofContext
import PPAC.Migration.ForcingRawGuardOpening

/-! Consume the actual instantiated atomic monotonicity proof under the
same compiled forcing background as the source induction. -/
namespace PPAC.Migration.ForcingAtomicMono
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
open InternalProofBackground (implication implication_rename)
open InternalProofConjunction (proved proved_rename)
open SyntaxCodedMixedTermSyntax (substituted substituted_rename)

set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

private abbrev test : Formula 1 := OriginalAxiomCodeTest.test false

private theorem lift_proved {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b G F : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hG : Derives Γ (formulaCode w G z b)) (hF : Derives Γ (formulaCode w F z b))
    (hp : Derives Γ (proved test w z b F)) : Derives Γ (implication test w z b G F) := by
  let E := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxLogicalSyntax.binaryCode 2 w.castSucc G.castSucc F.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (SyntaxConstructors.exists_constructor hZ 2 7 w (SyntaxAtomSyntax.two G F) hw
    (.conjI (.conjL (FormulaCodeProperties.guards w G z b hG))
      (.conjI (.conjL (FormulaCodeProperties.guards w F z b hF)) (.eqRefl w))))
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h := InternalProofImplication.weaken_proof (ZFContext.under hZ E) test w.castSucc z.castSucc b.castSucc
    G.castSucc F.castSucc (Fin.last m) (of_eq (omega_rename w Fin.castSucc) (under hw E))
    (of_eq (empty_rename z Fin.castSucc) (under hz E))
    (of_eq (formulaCode_rename w G z b Fin.castSucc) (under hG E))
    (of_eq (formulaCode_rename w F z b Fin.castSucc) (under hF E)) (.conjR hE)
    (of_eq (proved_rename test w z b F Fin.castSucc) (under hp E))
  apply of_eq (implication_rename test w z b G F Fin.castSucc).symm
  apply Derives.exI (Fin.last m)
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename,
    SyntaxAtomSyntax.two_map, proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]; rfl)
    (.conjI (.conjR hE) h)

private theorem discharge_chain {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b G : Fin m) (heads : Fin 4 → Fin m) (tails : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hG : Derives Γ (formulaCode w G z b)) (ht : Derives Γ (formulaCode w (tails 0) z b))
    (hCtor : ∀ i : Fin 4, Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w (heads i) (tails i.succ) (tails i.castSucc)))
    (hGuards : ∀ i : Fin 4, Derives Γ (implication test w z b G (heads i)))
    (hp : Derives Γ (proved test w z b (tails 0))) :
    Derives Γ (implication test w z b G (tails 4)) := by
  have step (i : Fin 4) (hT : Derives Γ (formulaCode w (tails i.castSucc) z b))
      (hP : Derives Γ (implication test w z b G (tails i.castSucc))) :
      Derives Γ (formulaCode w (tails i.succ) z b) ∧ Derives Γ (implication test w z b G (tails i.succ)) :=
    ⟨.conjR (.conjR (.impE (.conjL (FormulaCodeKnownLogical.binary2_iff hZ w z b
      (heads i) (tails i.succ) (tails i.castSucc) hw (hCtor i))) hT)),
      ForcingNegMemberProof.discharge hZ test w z b G (heads i) (tails i.succ) (tails i.castSucc)
        hw hz hG hT (hCtor i) (hGuards i) hP⟩
  have h0 := lift_proved hZ w z b G (tails 0) hw hz hG ht hp
  have h1 := step 0 ht h0
  have h2 := step 1 h1.1 h1.2
  have h3 := step 2 h2.1 h2.2
  exact (step 3 h3.1 h3.2).2

def heads {m} (Pre Fp : Fin m) (H : Fin 6 → Fin m) : Fin 4 → Fin m :=
  Fin.cases Pre (Fin.cases (H 1) (Fin.cases (H 4) (fun _ => Fp)))

/-- Use the existing canonical context to eliminate the actual preorder,
q-membership and q≤p guards of the instantiated source proof. The two atomic
conclusions must be the actual fields of its four implications. -/
theorem at_instance {m} {Γ : Context m} {free : PureSyntaxQuotation.Ctx} {φ : PureSyntaxQuotation.Fm [] free}
    (hZ : ZFContext.Evidence Γ) (hProof : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] φ)
    (w z a b B L N Extra Pre Fp : Fin m) (H layout : Fin 6 → Fin m) (tails : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral free.length a))
    (hN : Derives Γ (PureQuotationSyntax.formula φ w N))
    (hF : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w B L z a z b N (tails 0)))
    (hCtor : ∀ i : Fin 4, Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w (heads Pre Fp H i) (tails i.succ) (tails i.castSucc)))
    (hExtra : Derives Γ (formulaCode w Extra z b))
    (hLayout : Derives Γ (ForcingProofContext.layoutData w z b Extra Pre H layout))
    (hp : Derives Γ (implication (OriginalAxiomCodeTest.test false) w z b (layout 3) Fp)) :
    Derives Γ (implication (OriginalAxiomCodeTest.test false) w z b (layout 3) (tails 4)) := by
  have typed := SyntaxMixedFormulaJudgment.target_type w B L z a z b N (tails 0) hF
  have split (i : Fin 4) (h : Derives Γ (formulaCode w (tails i.castSucc) z b)) :
      Derives Γ ((formulaCode w (heads Pre Fp H i) z b).conj (formulaCode w (tails i.succ) z b)) :=
    .conjR (.impE (.conjL (FormulaCodeKnownLogical.binary2_iff hZ w z b
      (heads Pre Fp H i) (tails i.succ) (tails i.castSucc) hw (hCtor i))) h)
  have types0 := split 0 typed
  have types1 := split 1 (.conjR types0)
  have types2 := split 2 (.conjR types1)
  have hPre := Derives.conjL types0
  have hH1 := Derives.conjL types1
  have hH4 := Derives.conjL types2
  have l0 := Derives.conjL hLayout
  have l1 := Derives.conjL (.conjR hLayout)
  have l2 := Derives.conjL (.conjR (.conjR hLayout))
  have l3 := Derives.conjL (.conjR (.conjR (.conjR hLayout)))
  have t0 := Derives.conjR l0
  have t1 := Derives.conjR l1
  have t2 := Derives.conjR l2
  have t3 := Derives.conjR l3
  have tH2 := Derives.conjL (.conjR (.impE
    (.conjL (FormulaCodeKnownLogical.binary0_iff hZ w z b (H 2) (H 4) (layout 0) hw (.conjL l0))) t0))
  have to2 := ForcingRelationGuardProof.project hZ test true w z b Extra (layout 2) (layout 3) hw hz hExtra t2 t3 (.conjL l3)
  have toPre := ForcingRelationGuardProof.project hZ test false w z b Pre (layout 1) (layout 2) hw hz hPre t1 t2 (.conjL l2)
  have to1 := ForcingRelationGuardProof.project hZ test true w z b Pre (layout 1) (layout 2) hw hz hPre t1 t2 (.conjL l2)
  have from1 := ForcingRelationGuardProof.chain hZ test w z b (layout 3) (layout 2) (layout 1) hw hz t3 t2 t1 to2 to1
  have toMem := ForcingRelationGuardProof.project hZ test false w z b (H 1) (layout 0) (layout 1) hw hz hH1 t0 t1 (.conjL l1)
  have to0 := ForcingRelationGuardProof.project hZ test true w z b (H 1) (layout 0) (layout 1) hw hz hH1 t0 t1 (.conjL l1)
  have from0 := ForcingRelationGuardProof.chain hZ test w z b (layout 3) (layout 1) (layout 0) hw hz t3 t1 t0 from1 to0
  have toOrder := ForcingRelationGuardProof.project hZ test true w z b (H 2) (H 4) (layout 0) hw hz tH2 hH4 t0 (.conjL l0)
  have pPre := ForcingRelationGuardProof.chain hZ test w z b (layout 3) (layout 2) Pre hw hz t3 t2 hPre to2 toPre
  have pMem := ForcingRelationGuardProof.chain hZ test w z b (layout 3) (layout 1) (H 1) hw hz t3 t1 hH1 from1 toMem
  have pOrder := ForcingRelationGuardProof.chain hZ test w z b (layout 3) (layout 0) (H 4) hw hz t3 t0 hH4 from0 toOrder
  have proven := NativeProofQuotation.instantiate_derives hZ hProof w z a b B L N (tails 0) hw hz ha hN hF
  exact discharge_chain hZ w z b (layout 3) (heads Pre Fp H) tails hw hz t3 typed hCtor
    (fun i => Fin.cases pPre (Fin.cases pMem (Fin.cases pOrder (fun _ => hp))) i) proven

private structure PairImages {m} (Γ : Context m) (w t a f z b B I D S V : Fin m)
    (xs ys : Fin 2 → Fin m) : Prop where
  omega : Derives Γ (omega w)
  width : Derives Γ (SyntaxNumeralSyntax.numeral 2 t)
  input : Derives Γ (SyntaxForestSyntax.forest 2 w xs B)
  identity : Derives Γ (ForcingAtomicCode.identityImages w a f I)
  output : Derives Γ (SyntaxForestSyntax.forest 2 w ys V)
  runs : ∀ j, Derives Γ (substituted w D S a f z b (xs j) (ys j))

private theorem PairImages.map {m l} {Γ : Context m} {Δ : Context l} {w t a f z b B I D S V : Fin m}
    {xs ys : Fin 2 → Fin m} (h : PairImages Γ w t a f z b B I D S V xs ys)
    (r : Fin m → Fin l) (carry : ∀ {p : Formula m}, Derives Γ p → Derives Δ (p.rename r)) :
    PairImages Δ (r w) (r t) (r a) (r f) (r z) (r b) (r B) (r I) (r D) (r S) (r V)
      (fun j => r (xs j)) (fun j => r (ys j)) :=
  ⟨of_eq (omega_rename w r) (carry h.omega),
    of_eq (SyntaxNumeralSyntax.numeral_rename 2 t r) (carry h.width),
    of_eq (SyntaxForestSyntax.forest_rename 2 w xs B r) (carry h.input),
    of_eq (ForcingAtomicCode.identityImages_rename w a f I r) (carry h.identity),
    of_eq (SyntaxForestSyntax.forest_rename 2 w ys V r) (carry h.output),
    fun j => of_eq (substituted_rename w D S a f z b (xs j) (ys j) r) (carry (h.runs j))⟩

private theorem pair_at_variable {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    {w t a f z b B I D S V x u y o : Fin m} {xs ys : Fin 2 → Fin m}
    (h : PairImages Γ w t a f z b B I D S V xs ys)
    (bound : Bool) (i : Fin m) (hi : Derives Γ (.mem i (SyntaxTermSyntax.limit bound t f)))
    (hx : Derives Γ (SyntaxVariableSyntax.code bound w i x))
    (hp : Derives Γ (ForcingRawGuardOpening.path w t a f z b B I D S V x u y o)) :
    Derives Γ (.equal y o) := by
  have h0 := Derives.conjL hp
  have h1 := Derives.conjL (.conjR hp)
  have h2 := Derives.conjR (.conjR hp)
  have e0 := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w B I t f a f x u h0)
  have e1 := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w D S a f z b u y h1)
  have e2 := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w V S t f z b x o h2)
  cases bound with
  | false =>
    have f0 := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ false w B I t f a f x u i h.omega e0 hx)) h0
    have hu := ForcingMemberGuard.identity_field hZ w a f I i u h.identity (.conjL f0) (.conjR f0)
    have f1 := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ false w D S a f z b u y i h.omega e1 hu)) h1
    have f2 := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ false w V S t f z b x o i h.omega e2 hx)) h2
    exact StructuralListFieldValues.unique hZ w S i y o h.omega
      (SyntaxVariableDecode.index_natural false w i x hx) (.conjR f1) (.conjR f2)
  | true =>
    have f0 := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ true w B I t f a f x u i h.omega e0 hx)) h0
    have f2 := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ true w V S t f z b x o i h.omega e2 hx)) h2
    apply Derives.impE (SyntaxPositionSyntax.below_imp 2 i (.equal y o) ?_)
      (.impE (.conjL (SyntaxNumeralMembers.member_iff hZ 2 t i h.width)) hi)
    intro j
    apply Derives.impI
    let E := SyntaxNumeralSyntax.numeral j.val i
    let Δ := Context.add E Γ
    have hj : Derives Δ E := .hyp (Or.inl rfl)
    have hw := SourceLogic.add h.omega E
    have hZ1 := ZFContext.add hZ E
    have hu := Derives.impE (.conjL (SyntaxForestFieldValues.field_at hZ1 2 w xs B j i u hw
      (SourceLogic.add h.input E) hj)) (SourceLogic.add (.conjR f0) E)
    have ho := Derives.impE (.conjL (SyntaxForestFieldValues.field_at hZ1 2 w ys V j i o hw
      (SourceLogic.add h.output E) hj)) (SourceLogic.add (.conjR f2) E)
    have hRun := SyntaxMixedFormulaAtomicSubst.term_source w D S a f z b u y (xs j) hu (SourceLogic.add h1 E)
    have hy := SyntaxCodedMixedTermUnique.unique hZ1 w D S a f z b (xs j) y (ys j) hw hRun (SourceLogic.add (h.runs j) E)
    exact eq_trans hy (eq_symm ho)

private theorem paired_terms {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    {w t a f z b B I D S V x u y o : Fin m} {xs ys : Fin 2 → Fin m}
    (h : PairImages Γ w t a f z b B I D S V xs ys)
    (hp : Derives Γ (ForcingRawGuardOpening.path w t a f z b B I D S V x u y o)) :
    Derives Γ (.equal y o) := by
  apply OriginalTermScopeElimination.eliminate w t f x (.equal y o)
    (SyntaxCodedMixedTermTyping.source_type w B I t f a f x u (.conjL hp))
  intro bound
  let E := SyntaxTermSyntax.branchWitness bound w (SyntaxTermSyntax.limit bound t f) x
  have hE : Derives (Context.add E (Context.image Formula.raise Γ)) E := .hyp (Or.inl rfl)
  have path := of_eq (ForcingRawGuardOpening.path_rename w t a f z b B I D S V x u y o Fin.castSucc)
    (SourceLogic.under hp E)
  have h1 := h.map Fin.castSucc (fun p => SourceLogic.under p E)
  cases bound
  · exact pair_at_variable (ZFContext.under hZ E) h1 false (Fin.last m) (.conjL hE) (.conjR hE) path
  · exact pair_at_variable (ZFContext.under hZ E) h1 true (Fin.last m) (.conjL hE) (.conjR hE) path

private def four {α : Type} (a b c d : α) : Fin 4 → α :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

private theorem term_diagram {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    {w t a f z b B I D S V : Fin m} {xs ys : Fin 2 → Fin m}
    (h : PairImages Γ w t a f z b B I D S V xs ys) (It If R0 S0 : Fin m)
    (ht : Derives Γ (SyntaxIdentityMapSyntax.identityCode w t It))
    (hf : Derives Γ (SyntaxIdentityMapSyntax.identityCode w f If))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w It If R0 S0 t f t f)) :
    Derives Γ (ForcingTermDiagram.diagram w (four t t a z) (four f f f b) (four R0 B D V) (four S0 I S S)) := by
  apply OriginalUniversalBlock.intro_many 5
  apply Derives.impI
  let r := old 5 (m := m)
  let bounds := four (r t) (r t) (r a) (r z)
  let frees := four (r f) (r f) (r f) (r b)
  let R := four (r R0) (r B) (r D) (r V)
  let S' := four (r S0) (r I) (r S) (r S)
  let x := slot 5 (m := m)
  let E := (ForcingTermDiagram.step (r w) bounds frees R S' 0 (x 0) (x 1)).conj
    ((ForcingTermDiagram.step (r w) bounds frees R S' 1 (x 1) (x 2)).conj
      ((ForcingTermDiagram.step (r w) bounds frees R S' 2 (x 2) (x 3)).conj
        (ForcingTermDiagram.step (r w) bounds frees R S' 3 (x 0) (x 4))))
  let Δ := Context.add E (raisedContext 5 Γ)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ5 := HornBinderRules.zf_body 5 hZ E
  have h5 := h.map r (fun p => HornBinderRules.under_body 5 p E)
  have same := ForcingBinderFormula.identity_term_output hZ5 (r w) (r t) (r f) (r It) (r If) (r R0) (r S0)
    (x 0) (x 1) h5.omega
    (of_eq (SyntaxIdentityMapSyntax.identityCode_rename w t It r) (HornBinderRules.under_body 5 ht E))
    (of_eq (SyntaxIdentityMapSyntax.identityCode_rename w f If r) (HornBinderRules.under_body 5 hf E))
    (of_eq (IndexTermImageCodeSyntax.environment_rename w It If R0 S0 t f t f r)
      (HornBinderRules.under_body 5 he E)) (.conjL hE)
  have first := SyntaxMixedFormulaAtomicSubst.term_source (r w) (r B) (r I) (r t) (r f) (r a) (r f)
    (x 1) (x 2) (x 0) (eq_symm same) (.conjL (.conjR hE))
  exact paired_terms hZ5 h5 (.conjI first (.conjI (.conjL (.conjR (.conjR hE))) (.conjR (.conjR (.conjR hE)))))

private theorem pair_formula_at_identity {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    {w t a f z b B I D S V : Fin m} {xs ys : Fin 2 → Fin m}
    (h : PairImages Γ w t a f z b B I D S V xs ys) (It If R0 S0 n c Y O : Fin m)
    (ht : Derives Γ (SyntaxIdentityMapSyntax.identityCode w t It))
    (hf : Derives Γ (SyntaxIdentityMapSyntax.identityCode w f If))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w It If R0 S0 t f t f))
    (hp : Derives Γ (ForcingRawGuardOpening.formulaPath w t a f z b B I D S V n c Y O)) :
    Derives Γ (.equal Y O) := by
  have h0 := Derives.conjL hp
  have type := SyntaxMixedFormulaJudgmentTyping.source_type hZ w B I t f a f n c h.omega h0
  have id := SyntaxIdentityInduction.reflexive hZ w It If t f n h.omega ht hf type
  have mixed := Derives.impE (.conjL (IndexFormulaRenameBridge.rename_iff hZ w It If R0 S0 t f t f n n h.omega he)) id
  exact ForcingFormulaInduction.cancel hZ w (four t t a z) (four f f f b) (four R0 B D V) (four S0 I S S)
    n n c Y O h.omega (term_diagram hZ h It If R0 S0 ht hf he) mixed h0 (.conjL (.conjR hp)) (.conjR (.conjR hp))

theorem with_identity_images {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w t f : Fin m) (hw : Derives Γ (omega w)) (htn : Derives Γ (.mem t w))
    (hfn : Derives Γ (.mem f w)) (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (It If R S : Fin l), ZFContext.Evidence Δ →
      (∀ {p : Formula m}, Derives Γ p → Derives Δ (p.rename r)) →
      Derives Δ (SyntaxIdentityMapSyntax.identityCode (r w) (r t) It) →
      Derives Δ (SyntaxIdentityMapSyntax.identityCode (r w) (r f) If) →
      Derives Δ (IndexTermImageCodeSyntax.environment (r w) It If R S (r t) (r f) (r t) (r f)) →
      Derives Δ (out.rename r)) : Derives Γ out := by
  let E := SyntaxIdentityMapSyntax.identityCode w.castSucc t.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (SyntaxIdentityCode.exists_code hZ w t hw htn)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hZ1 := ZFContext.under hZ E
  let F := SyntaxIdentityMapSyntax.identityCode w.castSucc.castSucc f.castSucc.castSucc (Fin.last (m+1))
  let Ξ := Context.add F (Context.image Formula.raise Δ)
  apply Derives.exE (p := F) (SyntaxIdentityCode.exists_code hZ1 w.castSucc f.castSucc hw1 (under hfn E))
  have hF : Derives Ξ F := .hyp (Or.inl rfl)
  have lift2 {p : Formula m} (proof : Derives Γ p) : Derives Ξ (p.rename (old 2)) :=
    of_eq (rename_comp p Fin.castSucc Fin.castSucc) (under (under proof E) F)
  have hw2 := of_eq (omega_rename w (old 2)) (lift2 hw)
  have hZ2 := ZFContext.under hZ1 F
  let It := (slot 2 0 : Fin (m+2))
  let If := (slot 2 1 : Fin (m+2))
  have ht : Derives Ξ (SyntaxIdentityMapSyntax.identityCode (old 2 w) (old 2 t) It) :=
    of_eq (SyntaxIdentityMapSyntax.identityCode_rename w.castSucc t.castSucc (Fin.last m) Fin.castSucc) (under hE F)
  have hf : Derives Ξ (SyntaxIdentityMapSyntax.identityCode (old 2 w) (old 2 f) If) := hF
  let Q := IndexTermImageCodeSyntax.environment (old 2 (old 2 w)) (old 2 It) (old 2 If) (slot 2 0) (slot 2 1)
    (old 2 (old 2 t)) (old 2 (old 2 f)) (old 2 (old 2 t)) (old 2 (old 2 f))
  let Ω := Context.add Q (raisedContext 2 Ξ)
  apply HornBinderRules.eliminate_many 2 Q _
    (IndexTermImageEnvironment.exists_environment hZ2 (old 2 w) It If (old 2 t) (old 2 f) (old 2 t) (old 2 f)
      hw2 (SyntaxIdentityCode.map_code _ _ _ ht) (SyntaxIdentityCode.map_code _ _ _ hf))
  let r := fun i : Fin m => old 2 (old 2 i)
  have lift4 {p : Formula m} (proof : Derives Γ p) : Derives Ω (p.rename r) :=
    of_eq (rename_comp p (old 2) (old 2)) (HornBinderRules.under_body 2 (lift2 proof) Q)
  have hResult := use r (old 2 It) (old 2 If) (slot 2 0) (slot 2 1) (HornBinderRules.zf_body 2 hZ2 Q) lift4
    (of_eq (SyntaxIdentityMapSyntax.identityCode_rename (old 2 w) (old 2 t) It (old 2))
      (HornBinderRules.under_body 2 ht Q))
    (of_eq (SyntaxIdentityMapSyntax.identityCode_rename (old 2 w) (old 2 f) If (old 2))
      (HornBinderRules.under_body 2 hf Q)) (.hyp (Or.inl rfl))
  exact of_eq (by simp only [Formula.raise, rename_comp, r]; rfl) hResult

private theorem paired_formula {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    {w t a f z b B I D S V : Fin m} {xs ys : Fin 2 → Fin m}
    (h : PairImages Γ w t a f z b B I D S V xs ys) (n c Y O : Fin m)
    (hp : Derives Γ (ForcingRawGuardOpening.formulaPath w t a f z b B I D S V n c Y O)) :
    Derives Γ (.equal Y O) := by
  have hn := SyntaxMixedFormulaJudgmentTyping.source_type hZ w B I t f a f n c h.omega (.conjL hp)
  have hfn := Derives.conjR (.conjR (FormulaCodeProperties.guards w n t f hn))
  apply with_identity_images hZ w t f h.omega (SyntaxNumerals.range hZ 2 w t h.omega h.width) hfn (.equal Y O)
  intro l Δ r It If R0 S0 hZ1 lift hIt hIf he
  exact pair_formula_at_identity hZ1 (h.map r lift) It If R0 S0 (r n) (r c) (r Y) (r O) hIt hIf he
    (of_eq (ForcingRawGuardOpening.formulaPath_rename w t a f z b B I D S V n c Y O r) (lift hp))

/-- Compare the ACTUAL original atomic compiler followed by a mixed query
with the direct query using the very same two transformed argument codes.
The original free term list is read on both paths. -/
theorem compare_compiled {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (Reln : Formula (k+2)) (w t a f z b D S V x y X Y C N F O : Fin m)
    (hw : Derives Γ (omega w))
    (ht : Derives Γ (SyntaxNumeralSyntax.numeral 2 t))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hc : Derives Γ (ForcingAtomicCode.compiled equality Reln w a x y C))
    (hn : Derives Γ (PureQuotationSyntax.formula (ForcingAtomicCode.template equality Reln) w N))
    (hV : Derives Γ (SyntaxForestSyntax.forest 2 w (SetLanguage.args2 Y X) V))
    (hx : Derives Γ (substituted w D S a f z b x X))
    (hy : Derives Γ (substituted w D S a f z b y Y))
    (hF : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w D S a f z b C F))
    (hO : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w V S t f z b N O)) :
    Derives Γ (.equal F O) := by
  apply ForcingAtomicCode.eliminate_compiled hZ equality Reln w a x y C hc (.equal F O)
  intro l Δ r v hZ1 lift h2 hK hQ hB hI hRun
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have ht1 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 t r) (lift ht)
  have hf1 := of_eq (SyntaxNumeralSyntax.numeral_rename (k+2) f r) (lift hf)
  have hn1 := of_eq (PureQuotationSyntax.formula_rename (ForcingAtomicCode.template equality Reln) w N r) (lift hn)
  have e0 := SyntaxNumerals.unique hZ1 2 (v 0) (r t) h2 ht1
  have e1 := SyntaxNumerals.unique hZ1 (k+2) (v 1) (r f) hK hf1
  have e2 := OriginalTreeQuotationUnique.tree_unique hZ1
    (PureSyntaxQuotation.formulaTree (ForcingAtomicCode.template equality Reln)) (r w) (v 2) (r N)
    hw1 (.conjL hQ) hn1
  let A : Formula (l+1) :=
    (ForcingAtomicCode.identityImages (r w).castSucc (r a).castSucc (Fin.last l) (v 4).castSucc).conj
      (SyntaxMixedFormulaJudgmentSyntax.substituted (r w).castSucc (v 3).castSucc (v 4).castSucc
        (v 0).castSucc (Fin.last l) (r a).castSucc (Fin.last l) (v 2).castSucc (r C).castSucc)
  have transferred : Derives Δ ((ForcingAtomicCode.identityImages (r w) (r a) (r f) (v 4)).conj
      (SyntaxMixedFormulaJudgmentSyntax.substituted (r w) (v 3) (v 4) (v 0) (r f) (r a) (r f) (v 2) (r C))) :=
    of_eq (by simp only [A, Formula.instantiate, Formula.rename, ForcingAtomicCode.identityImages_rename,
      SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.eqSubst A e1 (of_eq (by simp only [A, Formula.instantiate, Formula.rename,
        ForcingAtomicCode.identityImages_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename,
        Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hI hRun)))
  have first := SyntaxMixedFormulaJudgmentSubst.subst_n (r w) (v 3) (v 4) (r t) (r f) (r a) (r f) (v 2) (r C)
    (r N) e2 (SyntaxMixedFormulaJudgmentSubst.subst_a (r w) (v 3) (v 4) (v 0) (r f) (r a) (r f)
      (v 2) (r C) (r t) e0 (.conjR transferred))
  have hv : Derives Δ (SyntaxForestSyntax.forest 2 (r w) (SetLanguage.args2 (r Y) (r X)) (r V)) :=
    of_eq (by rw [SyntaxForestSyntax.forest_rename, ProofTreeEntryFacts.args2_map]) (lift hV)
  have pair : PairImages Δ (r w) (r t) (r a) (r f) (r z) (r b) (v 3) (v 4) (r D) (r S) (r V)
      (SetLanguage.args2 (r y) (r x)) (SetLanguage.args2 (r Y) (r X)) :=
    ⟨hw1, ht1, hB, .conjL transferred, hv,
      Fin.cases (of_eq (substituted_rename w D S a f z b y Y r) (lift hy))
        (Fin.cases (of_eq (substituted_rename w D S a f z b x X r) (lift hx)) (fun j => Fin.elim0 j))⟩
  exact paired_formula hZ1 pair (r N) (r C) (r F) (r O)
    (.conjI first (.conjI (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w D S a f z b C F r) (lift hF))
      (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w V S t f z b N O r) (lift hO))))

/-- Produce the direct mixed execution for the SAME compiler output. The
independent direct candidate is generated by the original total compiler and
identified with the actual output by the two-argument comparison. -/
theorem direct_at_pair {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (Reln : Formula (k+2)) (w t a f z b D S V x y X Y C N F : Fin m)
    (hw : Derives Γ (omega w))
    (ht : Derives Γ (SyntaxNumeralSyntax.numeral 2 t))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hc : Derives Γ (ForcingAtomicCode.compiled equality Reln w a x y C))
    (hn : Derives Γ (PureQuotationSyntax.formula (ForcingAtomicCode.template equality Reln) w N))
    (hV : Derives Γ (SyntaxForestSyntax.forest 2 w (SetLanguage.args2 Y X) V))
    (hx : Derives Γ (substituted w D S a f z b x X))
    (hy : Derives Γ (substituted w D S a f z b y Y))
    (hF : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w D S a f z b C F)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w V S t f z b N F) := by
  let φ := ForcingAtomicCode.template equality Reln
  have htN := PureQuotationFormulaTyping.formula_type hZ φ w t f N hw
    (by
      change Derives Γ (SyntaxNumeralSyntax.numeral (List.replicate 2 YesMetaZFC.SetTheory.SetSort.set).length t)
      simpa only [List.length_replicate] using ht)
    (by
      change Derives Γ (SyntaxNumeralSyntax.numeral (List.replicate (k+2) YesMetaZFC.SetTheory.SetSort.set).length f)
      simpa only [List.length_replicate] using hf) hn
  have htX := SyntaxCodedMixedTermTyping.target_type w D S a f z b x X hx
  have htY := SyntaxCodedMixedTermTyping.target_type w D S a f z b y Y hy
  have hS := Derives.conjR (.conjL (SyntaxMixedFormulaJudgment.legal w D S a f z b C F hF))
  have hTyped := ForcingAtomicCode.bound_forest_typed hZ w t z b V (SetLanguage.args2 Y X) hw ht
    (.conjL htX) (Fin.cases htY (Fin.cases htX (fun j => Fin.elim0 j))) hV
  have he := SyntaxMixedFormulaOutputInduction.actual_exists hZ w V S t f z b N hw (.conjI htN (.conjI hTyped hS))
  apply NativeProofQuotation.eliminate_objects hZ 1 (fun r xs =>
    SyntaxMixedFormulaJudgmentSyntax.substituted (r w) (r V) (r S) (r t) (r f) (r z) (r b) (r N) (xs 0)) he
    (SyntaxMixedFormulaJudgmentSyntax.substituted w V S t f z b N F)
  intro l Δ r xs hZ1 lift hO
  have hEq := compare_compiled hZ1 equality Reln (r w) (r t) (r a) (r f) (r z) (r b) (r D) (r S)
    (r V) (r x) (r y) (r X) (r Y) (r C) (r N) (r F) (xs 0)
    (of_eq (omega_rename w r) (lift hw))
    (of_eq (SyntaxNumeralSyntax.numeral_rename 2 t r) (lift ht))
    (of_eq (SyntaxNumeralSyntax.numeral_rename (k+2) f r) (lift hf))
    (of_eq (ForcingAtomicCode.compiled_rename equality Reln w a x y C r) (lift hc))
    (of_eq (PureQuotationSyntax.formula_rename φ w N r) (lift hn))
    (of_eq (by rw [SyntaxForestSyntax.forest_rename, ProofTreeEntryFacts.args2_map]) (lift hV))
    (of_eq (substituted_rename w D S a f z b x X r) (lift hx))
    (of_eq (substituted_rename w D S a f z b y Y r) (lift hy))
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w D S a f z b C F r) (lift hF)) hO
  exact of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w V S t f z b N F r).symm
    (SyntaxMixedFormulaJudgmentSubst.subst_q (r w) (r V) (r S) (r t) (r f) (r z) (r b) (r N)
      (xs 0) (r F) (eq_symm hEq) hO)

def directData {k m} (equality : Bool) (Reln : Formula (k+2)) (w a f z b D S x y F : Fin m)
    (v : Fin 5 → Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral 2 (v 0)).conj
    ((PureQuotationSyntax.formula (ForcingAtomicCode.template equality Reln) w (v 1)).conj
      ((substituted w D S a f z b x (v 2)).conj
        ((substituted w D S a f z b y (v 3)).conj
          ((SyntaxForestSyntax.forest 2 w (SetLanguage.args2 (v 3) (v 2)) (v 4)).conj
            (SyntaxMixedFormulaJudgmentSyntax.substituted w (v 4) S (v 0) f z b (v 1) F)))))

theorem directData_rename {k m l} (equality : Bool) (Reln : Formula (k+2)) (w a f z b D S x y F : Fin m)
    (v : Fin 5 → Fin m) (r : Fin m → Fin l) :
    (directData equality Reln w a f z b D S x y F v).rename r =
      directData equality Reln (r w) (r a) (r f) (r z) (r b) (r D) (r S) (r x) (r y) (r F) (fun i => r (v i)) := by
  simp only [directData, Formula.rename, SyntaxNumeralSyntax.numeral_rename, PureQuotationSyntax.formula_rename,
    substituted_rename, SyntaxForestSyntax.forest_rename, ProofTreeEntryFacts.args2_map,
    SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

def direct {k m} (equality : Bool) (Reln : Formula (k+2)) (w a f z b D S x y F : Fin m) : Formula m :=
  existsMany 5 (directData equality Reln (old 5 w) (old 5 a) (old 5 f) (old 5 z) (old 5 b)
    (old 5 D) (old 5 S) (old 5 x) (old 5 y) (old 5 F) (slot 5))

theorem direct_rename {k m l} (equality : Bool) (Reln : Formula (k+2))
    (w a f z b D S x y F : Fin m) (r : Fin m → Fin l) :
    (direct equality Reln w a f z b D S x y F).rename r =
      direct equality Reln (r w) (r a) (r f) (r z) (r b) (r D) (r S) (r x) (r y) (r F) := by
  simp only [direct, existsMany_rename, directData_rename, lift_old, lift_slot]

private theorem with_pair_outputs {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (Reln : Formula (k+2)) (w t a f z b D S x y X Y C N F : Fin m)
    (hw : Derives Γ (omega w))
    (ht : Derives Γ (SyntaxNumeralSyntax.numeral 2 t))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hc : Derives Γ (ForcingAtomicCode.compiled equality Reln w a x y C))
    (hn : Derives Γ (PureQuotationSyntax.formula (ForcingAtomicCode.template equality Reln) w N))
    (hx : Derives Γ (substituted w D S a f z b x X)) (hy : Derives Γ (substituted w D S a f z b y Y))
    (hF : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w D S a f z b C F)) :
    Derives Γ (direct equality Reln w a f z b D S x y F) := by
  have nx := SyntaxCodedMixedTermTyping.output_natural w D S a f z b x X hx
  have ny := SyntaxCodedMixedTermTyping.output_natural w D S a f z b y Y hy
  have he := SyntaxForests.exists_forest hZ 2 w (SetLanguage.args2 Y X) hw (.conjI ny (.conjI nx (.eqRefl w)))
  apply NativeProofQuotation.eliminate_objects hZ 1 (fun r xs => (Formula.mem (xs 0) (r w)).conj
    (SyntaxForestSyntax.forest 2 (r w) (SetLanguage.args2 (r Y) (r X)) (xs 0))) he
    (direct equality Reln w a f z b D S x y F)
  intro l Δ r xs hZ1 lift h
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have ht1 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 t r) (lift ht)
  have hn1 := of_eq (PureQuotationSyntax.formula_rename (ForcingAtomicCode.template equality Reln) w N r) (lift hn)
  have hx1 := of_eq (substituted_rename w D S a f z b x X r) (lift hx)
  have hy1 := of_eq (substituted_rename w D S a f z b y Y r) (lift hy)
  have hDirect := direct_at_pair hZ1 equality Reln (r w) (r t) (r a) (r f) (r z) (r b) (r D) (r S) (xs 0)
    (r x) (r y) (r X) (r Y) (r C) (r N) (r F) hw1 ht1
    (of_eq (SyntaxNumeralSyntax.numeral_rename (k+2) f r) (lift hf))
    (of_eq (ForcingAtomicCode.compiled_rename equality Reln w a x y C r) (lift hc)) hn1 (.conjR h) hx1 hy1
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w D S a f z b C F r) (lift hF))
  let v := fun i : Fin 5 => [r t, r N, r X, r Y, xs 0][i]
  have data : Derives Δ (directData equality Reln (r w) (r a) (r f) (r z) (r b) (r D) (r S) (r x) (r y) (r F) v) :=
    .conjI ht1 (.conjI hn1 (.conjI hx1 (.conjI hy1 (.conjI (.conjR h) hDirect))))
  apply of_eq (direct_rename equality Reln w a f z b D S x y F r).symm
  unfold direct
  apply HornBinderRules.intro_many 5 _ v
  exact of_eq (by simp only [directData_rename, assign_old, assign_slot]) data

private theorem with_source_quote {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (Reln : Formula (k+2)) (w t a f z b D S x y C N F : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ht : Derives Γ (SyntaxNumeralSyntax.numeral 2 t))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hc : Derives Γ (ForcingAtomicCode.compiled equality Reln w a x y C))
    (hn : Derives Γ (PureQuotationSyntax.formula (ForcingAtomicCode.template equality Reln) w N))
    (hx : Derives Γ (SyntaxTermSyntax.term w a z x)) (hy : Derives Γ (SyntaxTermSyntax.term w a z y))
    (hF : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w D S a f z b C F)) :
    Derives Γ (direct equality Reln w a f z b D S x y F) := by
  have lists := Derives.conjL (SyntaxMixedFormulaJudgment.legal w D S a f z b C F hF)
  have type := SyntaxMixedFormulaJudgmentTyping.source_type hZ w D S a f z b C F hw hF
  have contexts := Derives.conjR (FormulaCodeProperties.guards w C a f type)
  have hxt := ForcingAtomicCode.closed_term_target w a z f x hz contexts hx
  have hyt := ForcingAtomicCode.closed_term_target w a z f y hz contexts hy
  have ex := SyntaxCodedMixedTermExistence.exists_output hZ w D S a f z b x hw (.conjI lists hxt)
  have ey := SyntaxCodedMixedTermExistence.exists_output hZ w D S a f z b y hw (.conjI lists hyt)
  apply NativeProofQuotation.eliminate_objects hZ 1 (fun r xs =>
    substituted (r w) (r D) (r S) (r a) (r f) (r z) (r b) (r x) (xs 0)) ex
    (direct equality Reln w a f z b D S x y F)
  intro l Δ r xs hZ1 lift hX
  apply of_eq (direct_rename equality Reln w a f z b D S x y F r).symm
  apply NativeProofQuotation.eliminate_objects hZ1 1 (fun s ys =>
    substituted (s (r w)) (s (r D)) (s (r S)) (s (r a)) (s (r f)) (s (r z)) (s (r b)) (s (r y)) (ys 0))
    (of_eq (SyntaxCodedMixedTermSyntax.existsOutput_rename w D S a f z b y r) (lift ey))
    (direct equality Reln (r w) (r a) (r f) (r z) (r b) (r D) (r S) (r x) (r y) (r F))
  intro l' Δ' s ys hZ2 move hY
  let ρ := fun i => s (r i)
  have carry {p : Formula m} (proof : Derives Γ p) : Derives Δ' (p.rename ρ) :=
    of_eq (rename_comp p r s) (move (lift proof))
  exact of_eq (direct_rename equality Reln (r w) (r a) (r f) (r z) (r b) (r D) (r S) (r x) (r y) (r F) s).symm
    (with_pair_outputs hZ2 equality Reln (ρ w) (ρ t) (ρ a) (ρ f) (ρ z) (ρ b) (ρ D) (ρ S)
      (ρ x) (ρ y) (s (xs 0)) (ys 0) (ρ C) (ρ N) (ρ F)
      (of_eq (omega_rename w ρ) (carry hw))
      (of_eq (SyntaxNumeralSyntax.numeral_rename 2 t ρ) (carry ht))
      (of_eq (SyntaxNumeralSyntax.numeral_rename (k+2) f ρ) (carry hf))
      (of_eq (ForcingAtomicCode.compiled_rename equality Reln w a x y C ρ) (carry hc))
      (of_eq (PureQuotationSyntax.formula_rename (ForcingAtomicCode.template equality Reln) w N ρ) (carry hn))
      (of_eq (substituted_rename (r w) (r D) (r S) (r a) (r f) (r z) (r b) (r x) (xs 0) s) (move hX)) hY
      (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w D S a f z b C F ρ) (carry hF)))

/-- Read the original atomic compiler and produce the two target term images,
their original forest, and the direct execution to the actual query output. -/
theorem direct_from_compiled {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (Reln : Formula (k+2)) (w a f z b D S x y C F : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hc : Derives Γ (ForcingAtomicCode.compiled equality Reln w a x y C))
    (hx : Derives Γ (SyntaxTermSyntax.term w a z x)) (hy : Derives Γ (SyntaxTermSyntax.term w a z y))
    (hF : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w D S a f z b C F)) :
    Derives Γ (direct equality Reln w a f z b D S x y F) := by
  apply ForcingAtomicCode.eliminate_compiled hZ equality Reln w a x y C hc (direct equality Reln w a f z b D S x y F)
  intro l Δ r v hZ1 lift ht _ hn _ _ _
  exact of_eq (direct_rename equality Reln w a f z b D S x y F r).symm
    (with_source_quote hZ1 equality Reln (r w) (v 0) (r a) (r f) (r z) (r b) (r D) (r S)
      (r x) (r y) (r C) (v 2) (r F) (of_eq (omega_rename w r) (lift hw)) (of_eq (empty_rename z r) (lift hz)) ht
      (of_eq (SyntaxNumeralSyntax.numeral_rename (k+2) f r) (lift hf))
      (of_eq (ForcingAtomicCode.compiled_rename equality Reln w a x y C r) (lift hc)) (.conjL hn)
      (of_eq (SyntaxTermSyntax.term_rename w a z x r) (lift hx))
      (of_eq (SyntaxTermSyntax.term_rename w a z y r) (lift hy))
      (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w D S a f z b C F r) (lift hF)))

/-- A source atom term has empty free scope. The two actual condition
overwrites therefore read the same bound-table field for that term. -/
theorem closed_image_agreement {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a f z b D S T x X Y : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hx : Derives Γ (SyntaxTermSyntax.term w a z x))
    (hX : Derives Γ (substituted w D S a f z b x X))
    (hY : Derives Γ (substituted w D T a f z b x Y)) : Derives Γ (.equal X Y) := by
  apply OriginalTermScopeElimination.eliminate w a z x (.equal X Y) hx
  intro bound
  cases bound with
  | false =>
    let E := SyntaxTermSyntax.branchWitness false w z x
    have hE : Derives (Context.add E (Context.image Formula.raise Γ)) E := .hyp (Or.inl rfl)
    have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz E)
    exact .botE (.impE (empty_at z.castSucc (Fin.last m) hz1) (.conjL hE))
  | true =>
    let E := SyntaxTermSyntax.branchWitness true w a x
    let Δ := Context.add E (Context.image Formula.raise Γ)
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
    have left := of_eq (substituted_rename w D S a f z b x X Fin.castSucc) (under hX E)
    have right := of_eq (substituted_rename w D T a f z b x Y Fin.castSucc) (under hY E)
    have hZ1 := ZFContext.under hZ E
    have read (L U : Fin (m+1))
        (h : Derives Δ (substituted w.castSucc D.castSucc L a.castSucc f.castSucc z.castSucc b.castSucc x.castSucc U)) :
        Derives Δ (StructuralListFieldSyntax.field w.castSucc D.castSucc (Fin.last m) U) :=
      .conjR (.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ1 true w.castSucc D.castSucc L
        a.castSucc f.castSucc z.castSucc b.castSucc x.castSucc U (Fin.last m) hw1
        (.conjL (SyntaxCodedMixedTermTyping.input_of_substituted _ _ _ _ _ _ _ _ _ h)) (.conjR hE))) h)
    exact StructuralListFieldValues.unique hZ1 w.castSucc D.castSucc (Fin.last m) X.castSucc Y.castSucc hw1
      (SyntaxVariableDecode.index_natural true w.castSucc (Fin.last m) x.castSucc (.conjR hE))
      (read S.castSucc X.castSucc left) (read T.castSucc Y.castSucc right)

end PPAC.Migration.ForcingAtomicMono
