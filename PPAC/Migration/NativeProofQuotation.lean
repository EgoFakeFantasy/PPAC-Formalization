import PPAC.Migration.InternalProofTemplates
import PPAC.Migration.InternalProofUniversal
import PPAC.Migration.Internal.NativeIndexFormulaQuotation
import PPAC.Migration.InternalFalseRoot
import PPAC.Migration.ForcingAtomicBasic

/-! Replay fixed pure nativeZF Hilbert derivations as actual original proof
trees. Each quotation candidate and each witness remains an object value. -/
namespace PPAC.Migration.NativeProofQuotation
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open InternalProofConjunction (proved proved_rename)
open YesMetaZFC.Logic.FirstOrder (HilbertDerivation VariableRenaming VariableSubstitution)
open YesMetaZFC.SetTheory (SetSort)
attribute [local implicit_reducible] YesMetaZFC.SetTheory.signature
attribute [local irreducible] NaturalRecursionSyntax.matrix
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

private theorem eliminate_objects {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (k : Nat) (body : ∀ {l}, (Fin m → Fin l) → (Fin k → Fin l) → Formula l)
    (hex : Derives Γ (existsMany k (body (old k) (slot k)))) (out : Formula m)
    (use : ∀ {l} {Δ : Context l} (r : Fin m → Fin l) (xs : Fin k → Fin l),
      ZFContext.Evidence Δ → (∀ {p : Formula m}, Derives Γ p → Derives Δ (p.rename r)) →
      Derives Δ (body r xs) → Derives Δ (out.rename r)) : Derives Γ out := by
  let B := body (old k) (slot k)
  apply HornBinderRules.eliminate_many k B out hex
  exact use (old k) (slot k) (HornBinderRules.zf_body k hZ B)
    (fun hp => HornBinderRules.under_body k hp B) (.hyp (Or.inl rfl))

private abbrev test : Formula 1 := OriginalAxiomCodeTest.test false

private theorem from_result {m} {Γ : Context m} (kind : Fin 6) (w z : Fin m)
    (env : Fin ((ProofTreeBranchConstruction.shape kind).extra+2) → Fin m)
    (hr : Derives Γ (InternalProofOperations.existsResult test kind w z env)) :
    Derives Γ (proved test w z (env 0) (env 1)) := by
  let E := InternalProofOperations.result test kind w.castSucc z.castSucc (Fin.last m) (fun i => (env i).castSucc)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hr
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have out : Derives Δ (proved test w.castSucc z.castSucc (env 0).castSucc (env 1).castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, InternalMPProof.annotated_rename,
      empty_rename, ProofTreeEntryFacts.root_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.conjI (.conjL hE) (.conjR (.conjR hE)))
  exact of_eq (proved_rename test w z (env 0) (env 1) Fin.castSucc).symm out

private theorem substitute_at_list {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a b L N F : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (he : Derives Γ (FreeSubstProgramSyntax.executed w z a b L N F))
    (hp : Derives Γ (proved test w z a N)) : Derives Γ (proved test w z b F) := by
  apply eliminate_objects hZ 1 (fun r xs =>
    (Formula.mem (xs 0) (r w)).conj ((InternalMPProof.annotated test (r w) (r z) (r a) (r N) (xs 0)).conj
      ((empty (r a)).imp (ProofTreeEntrySyntax.root test (r w) (xs 0) (r N))))) hp
    (proved test w z b F)
  intro l Δ r xs hZ1 lift h
  have hi : Derives Δ (InternalProofOperations.substitutionInput test
      (r w) (r z) (r b) (r a) (r L) (r F) (r N) (xs 0)) :=
    .conjI (of_eq (FreeSubstProgramSyntax.executed_rename w z a b L N F r) (lift he))
      (.conjI (.conjL h) (.conjL (.conjR h)))
  have result := InternalProofOperations.substitution hZ1 test (r w) (r z) (r b) (r a) (r L) (r F) (r N) (xs 0)
    (of_eq (omega_rename w r) (lift hw)) (of_eq (empty_rename z r) (lift hz)) hi
  exact of_eq (proved_rename test w z b F r).symm (from_result 5 _ _ _ result)

private theorem strengthen_at_execution {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b B F N : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hB : Derives Γ (successor B b)) (he : Derives Γ (WeakenFreeProgramSyntax.executed w z b B F N))
    (hp : Derives Γ (proved test w z B N)) : Derives Γ (proved test w z b F) := by
  apply eliminate_objects hZ 1 (fun r xs =>
    (Formula.mem (xs 0) (r w)).conj ((InternalMPProof.annotated test (r w) (r z) (r B) (r N) (xs 0)).conj
      ((empty (r B)).imp (ProofTreeEntrySyntax.root test (r w) (xs 0) (r N))))) hp
    (proved test w z b F)
  intro l Δ r xs hZ1 lift h
  have hi : Derives Δ (InternalProofOperations.strengtheningInput test
      (r w) (r z) (r b) (r B) (r F) (r N) (xs 0)) :=
    .conjI (of_eq (successor_rename B b r) (lift hB))
      (.conjI (of_eq (WeakenFreeProgramSyntax.executed_rename w z b B F N r) (lift he))
        (.conjI (.conjL h) (.conjL (.conjR h))))
  have result := InternalProofOperations.strengthening hZ1 test (r w) (r z) (r b) (r B) (r F) (r N) (xs 0)
    (of_eq (omega_rename w r) (lift hw)) (of_eq (empty_rename z r) (lift hz)) hi
  exact of_eq (proved_rename test w z b F r).symm (from_result 4 _ _ _ result)

private theorem original_free_list {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a b L : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ht : Derives Γ (SyntaxMixedImageCodeSyntax.termList w a z b L)) :
    Derives Γ (SyntaxFreeSubstSyntax.termList w a b L) := by
  apply eliminate_objects hZ 1 (fun r xs => SyntaxMixedImageCodeSyntax.encoded
    (r w) (xs 0) (r a) (r z) (r b) (r L))
    (SyntaxMixedImageCodeExistence.exists_graph hZ w a z b L hw ht) (SyntaxFreeSubstSyntax.termList w a b L)
  intro l Δ r xs hZ1 lift h
  let g := xs 0
  have hMap : Derives Δ (SyntaxTermImageSyntax.imageMap (r w) g (r a) (r z) (r b)) := .conjL h
  have hValue : Derives Δ (SyntaxFreeSubstSyntax.values (r w) g (r b)) := by
    apply Derives.allI
    apply Derives.allI
    apply Derives.impI
    let E := GraphSyntax.edge g.castSucc.castSucc (Fin.last l).castSucc (Fin.last (l+1))
    let Ξ := Context.add E (raisedContext 2 Δ)
    have hM := of_eq (SyntaxTermImageSyntax.imageMap_rename (r w) g (r a) (r z) (r b) (old 2))
      (HornBinderRules.under_body 2 hMap E)
    have hTerm := SyntaxTermImageSyntax.image_type (old 2 (r w)) (old 2 g) (old 2 (r a)) (old 2 (r z))
      (old 2 (r b)) (Fin.last l).castSucc (Fin.last (l+1)) hM (Derives.hyp (Γ := Ξ) (Or.inl rfl))
    have hZero := of_eq (empty_rename (r z) (old 2)) (HornBinderRules.under_body 2
      (of_eq (empty_rename z r) (lift hz)) E)
    exact SyntaxOpenTerm.free_branch _ _ _ _ hZero hTerm
  have context : Derives Δ (SyntaxTermSyntax.contexts (r w) (r a) (r b)) :=
    .conjI (.conjL hMap) (.conjR (.conjL (.conjR hMap)))
  exact of_eq (SyntaxFreeSubstSyntax.termList_rename w a b L r).symm
    (SyntaxFreeSubstSyntax.intro_list (r w) (r a) (r b) (r L) g (.conjR h)
      (.conjI context (.conjI (SyntaxTermImageSyntax.image_sequence _ _ _ _ _ hMap) hValue)))

private def substitutionExecuted {m} (w z a b N F : Fin m) : Formula m := .ex
  (FreeSubstProgramSyntax.executed w.castSucc z.castSucc a.castSucc b.castSucc (Fin.last m) N.castSucc F.castSucc)

private theorem substitutionExecuted_rename {m l} (w z a b N F : Fin m) (r : Fin m → Fin l) :
    (substitutionExecuted w z a b N F).rename r = substitutionExecuted (r w) (r z) (r a) (r b) (r N) (r F) := by
  simp only [substitutionExecuted, Formula.rename, FreeSubstProgramSyntax.executed_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem execution_from_mixed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a b R L N F : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (h : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R L z a z b N F)) :
    Derives Γ (FreeSubstProgramSyntax.executed w z a b L N F) := by
  have legal := SyntaxMixedFormulaJudgment.legal w R L z a z b N F h
  have hBound : Derives Γ (SyntaxMixedImageCodeSyntax.termList w z z b R) := .conjL (.conjL legal)
  have hFree : Derives Γ (SyntaxMixedImageCodeSyntax.termList w a z b L) := .conjR (.conjL legal)
  have hb : Derives Γ (.mem b w) := .conjR (.conjL (.conjR hFree))
  have hNil := StructuralListLengthConstruct.nil_of_empty_length hZ w R z
    (.conjR (.conjL (.conjR (.conjR hBound)))) hz
  have hList := original_free_list hZ w z a b L hw hz hFree
  apply eliminate_objects hZ 1 (fun r xs => SyntaxIdentityMapSyntax.identityCode (r w) (r z) (xs 0))
    (SyntaxIdentityCode.exists_code hZ w z hw (SyntaxNumerals.range hZ 0 w z hw hz))
    (FreeSubstProgramSyntax.executed w z a b L N F)
  intro l Δ r xs hZ1 lift hI
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hb1 : Derives Δ (.mem (r b) (r w)) := lift hb
  apply of_eq (FreeSubstProgramSyntax.executed_rename w z a b L N F r).symm
  apply eliminate_objects hZ1 1 (fun s ys => IndexTermImageCodeSyntax.converted true
    (s (r w)) (s (xs 0)) (ys 0) (s (r z)) (s (r z)) (s (r b)))
    (FreeSubstImageCode.identity_image_exists hZ1 (r w) (r z) (r b) (xs 0) hw1 hb1 hI)
    (FreeSubstProgramSyntax.executed (r w) (r z) (r a) (r b) (r L) (r N) (r F))
  intro l' Δ' s ys hZ2 move hR
  let ρ := fun i => s (r i)
  have carry {p : Formula m} (hp : Derives Γ p) : Derives Δ' (p.rename ρ) :=
    of_eq (rename_comp p r s) (move (lift hp))
  have hw2 := of_eq (omega_rename w ρ) (carry hw)
  have hz2 := of_eq (empty_rename z ρ) (carry hz)
  have hTyped := IndexTermImageCodeTyping.term_list true (ρ w) (s (xs 0)) (ys 0) (ρ z) (ρ z) (ρ b) hR
  have he := StructuralNil.unique hZ2 (ρ w) (ρ R) (ys 0) hw2
    (of_eq (StructuralListSyntax.nilCode_rename w R ρ) (carry hNil))
    (StructuralListLengthConstruct.nil_of_empty_length hZ2 (ρ w) (ys 0) (ρ z)
      (.conjR (.conjL (.conjR (.conjR hTyped)))) hz2)
  have hMixed := SyntaxMixedFormulaAdvancedOutput.subst_bound_code (ρ w) (ρ N) (ρ R) (ρ L)
    (ρ z) (ρ a) (ρ z) (ρ b) (ρ F) (ys 0) he
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w R L z a z b N F ρ) (carry h))
  have hRun := Derives.impE (.conjR (FormulaTransformRecursionCorrectness.execution_iff hZ2
    (ρ w) (ys 0) (ρ L) (ρ z) (ρ a) (ρ z) (ρ b) (ρ N) (ρ F) hw2)) hMixed
  exact of_eq (FreeSubstProgramSyntax.executed_rename (r w) (r z) (r a) (r b) (r L) (r N) (r F) s).symm
    (FreeSubstProgramSyntax.intro_executed (ρ w) (ρ z) (ρ a) (ρ b) (ρ L) (ρ N) (ρ F) (s (xs 0)) (ys 0)
      (of_eq (SyntaxFreeSubstSyntax.termList_rename w a b L ρ) (carry hList))
      (of_eq (SyntaxIdentityMapSyntax.identityCode_rename (r w) (r z) (xs 0) s) (move hI)) hR hRun)

private theorem substitute_from_quotations {m} {Γ : Context m} {free target : PureSyntaxQuotation.Ctx}
    (hZ : ZFContext.Evidence Γ) (φ : PureSyntaxQuotation.Fm [] free)
    (τ : NativeSubstitutionSyntax.Mapping free [] target)
    (w z a b N F : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral free.length a))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral target.length b))
    (hN : Derives Γ (PureQuotationSyntax.formula φ w N))
    (hF : Derives Γ (PureQuotationSyntax.formula (φ.substituteFree τ) w F)) :
    Derives Γ (substitutionExecuted w z a b N F) := by
  let σ : NativeSubstitutionSyntax.Mapping [] [] target := VariableSubstitution.boundId
  apply eliminate_objects hZ 2 (fun r xs => NativeSubstitutionSyntax.environment σ τ
    (r w) (r z) (r a) (r z) (r b) (xs 0) (xs 1))
    (NativeSubstitutionEnvironment.exists_environment hZ σ τ w z a z b hw hz ha hz hb)
    (substitutionExecuted w z a b N F)
  intro l Δ r xs hZ1 lift hEnv
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hz1 := of_eq (empty_rename z r) (lift hz)
  have ha1 := of_eq (SyntaxNumeralSyntax.numeral_rename free.length a r) (lift ha)
  have hb1 := of_eq (SyntaxNumeralSyntax.numeral_rename target.length b r) (lift hb)
  have hn1 := of_eq (PureQuotationSyntax.formula_rename φ w N r) (lift hN)
  have hq1 := of_eq (PureQuotationSyntax.formula_rename (φ.substituteFree τ) w F r) (lift hF)
  have hValue := NativeFormulaQuotationValue.at_candidate hZ1 φ σ τ (r w) (xs 0) (xs 1)
    (r z) (r a) (r z) (r b) (r N) (r F) hw1 hz1 ha1 hz1 hb1 hEnv hn1 hq1
  have he := execution_from_mixed hZ1 (r w) (r z) (r a) (r b) (xs 0) (xs 1) (r N) (r F) hw1 hz1 (.conjL hValue)
  apply of_eq (substitutionExecuted_rename w z a b N F r).symm
  apply Derives.exI (xs 1)
  exact of_eq (by simp only [Formula.instantiate, FreeSubstProgramSyntax.executed_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) he

private def Replay {free : PureSyntaxQuotation.Ctx} (φ : PureSyntaxQuotation.Fm [] free) : Prop :=
  ∀ {m} {Γ : Context m}, ZFContext.Evidence Γ → ∀ w z b F,
    Derives Γ (omega w) → Derives Γ (empty z) →
    Derives Γ (SyntaxNumeralSyntax.numeral free.length b) →
    Derives Γ (PureQuotationSyntax.formula φ w F) → Derives Γ (proved test w z b F)

private theorem replay_mp {free : PureSyntaxQuotation.Ctx} (left right : PureSyntaxQuotation.Fm [] free)
    (hl : Replay left) (hi : Replay (.imp left right)) : Replay right := by
  intro m Γ hZ w z b F hw hz hb hF
  let trees := fun i : Fin 2 => [PureSyntaxQuotation.formulaTree left,
    PureSyntaxQuotation.formulaTree (.imp left right)][i]
  apply ProjectCompilerQuotation.eliminate_quotations hZ 2 trees w hw (proved test w z b F)
  intro l Δ r xs hZ1 lift hqs
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hz1 := of_eq (empty_rename z r) (lift hz)
  have hb1 := of_eq (SyntaxNumeralSyntax.numeral_rename free.length b r) (lift hb)
  have hF1 := of_eq (PureQuotationSyntax.formula_rename right w F r) (lift hF)
  have hc : Derives Δ (SyntaxNodeSyntax.constructor 2 7 (r w) (SyntaxAtomSyntax.two (xs 0) (r F)) (xs 1)) :=
    OriginalQuotationNodeFields.tree_to_constructor hZ1 7
      [PureSyntaxQuotation.formulaTree left, PureSyntaxQuotation.formulaTree right] (r w) (xs 1)
      (SyntaxAtomSyntax.two (xs 0) (r F)) hw1
      (.conjI (hqs 0) (.conjI hF1 (.eqRefl (r w)))) (hqs 1)
  exact of_eq (proved_rename test w z b F r).symm
    (InternalProofConjunction.modus_ponens hZ1 test (r w) (r z) (r b) (xs 0) (r F) (xs 1) hw1 hz1
      (PureQuotationFormulaTyping.formula_type hZ1 left (r w) (r z) (r b) (xs 0) hw1 hz1 hb1 (hqs 0))
      (PureQuotationFormulaTyping.formula_type hZ1 right (r w) (r z) (r b) (r F) hw1 hz1 hb1 hF1)
      hc (hl hZ1 (r w) (r z) (r b) (xs 0) hw1 hz1 hb1 (hqs 0))
      (hi hZ1 (r w) (r z) (r b) (xs 1) hw1 hz1 hb1 (hqs 1)))

private theorem replay_substituted {m} {Γ : Context m} {free target : PureSyntaxQuotation.Ctx}
    (hZ : ZFContext.Evidence Γ) (φ : PureSyntaxQuotation.Fm [] free)
    (τ : NativeSubstitutionSyntax.Mapping free [] target)
    (w z a b N F : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral free.length a))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral target.length b))
    (hN : Derives Γ (PureQuotationSyntax.formula φ w N))
    (hF : Derives Γ (PureQuotationSyntax.formula (φ.substituteFree τ) w F))
    (hp : Derives Γ (proved test w z a N)) : Derives Γ (proved test w z b F) := by
  apply eliminate_objects hZ 1 (fun r xs =>
    FreeSubstProgramSyntax.executed (r w) (r z) (r a) (r b) (xs 0) (r N) (r F))
    (substitute_from_quotations hZ φ τ w z a b N F hw hz ha hb hN hF) (proved test w z b F)
  intro l Δ r xs hZ1 lift he
  exact of_eq (proved_rename test w z b F r).symm
    (substitute_at_list hZ1 (r w) (r z) (r a) (r b) (xs 0) (r N) (r F)
      (of_eq (omega_rename w r) (lift hw)) (of_eq (empty_rename z r) (lift hz)) he
      (of_eq (proved_rename test w z a N r) (lift hp)))

private theorem replay_substitution {free target : PureSyntaxQuotation.Ctx} (φ : PureSyntaxQuotation.Fm [] free)
    (τ : NativeSubstitutionSyntax.Mapping free [] target) (hφ : Replay φ) :
    Replay (φ.substituteFree τ) := by
  intro m Γ hZ w z b F hw hz hb hF
  apply eliminate_objects hZ 1 (fun r xs =>
    (Formula.mem (xs 0) (r w)).conj (SyntaxNumeralSyntax.numeral free.length (xs 0)))
    (SyntaxNumerals.exists_numeral hZ free.length w hw) (proved test w z b F)
  intro l Δ r xs hZ1 lift ha
  have hw1 := of_eq (omega_rename w r) (lift hw)
  apply of_eq (proved_rename test w z b F r).symm
  apply ProjectCompilerQuotation.eliminate_quotations hZ1 1 (fun _ => PureSyntaxQuotation.formulaTree φ)
    (r w) hw1 (proved test (r w) (r z) (r b) (r F))
  intro l' Δ' s code hZ2 move hqs
  let ρ := fun i => s (r i)
  have carry {p : Formula m} (hp : Derives Γ p) : Derives Δ' (p.rename ρ) :=
    of_eq (rename_comp p r s) (move (lift hp))
  have hw2 := of_eq (omega_rename w ρ) (carry hw)
  have hz2 := of_eq (empty_rename z ρ) (carry hz)
  have ha2 := of_eq (SyntaxNumeralSyntax.numeral_rename free.length (xs 0) s) (move (.conjR ha))
  have hb2 := of_eq (SyntaxNumeralSyntax.numeral_rename target.length b ρ) (carry hb)
  have hF2 := of_eq (PureQuotationSyntax.formula_rename (φ.substituteFree τ) w F ρ) (carry hF)
  exact of_eq (proved_rename test (r w) (r z) (r b) (r F) s).symm
    (replay_substituted hZ2 φ τ (ρ w) (ρ z) (s (xs 0)) (ρ b) (code 0) (ρ F)
      hw2 hz2 ha2 hb2 (hqs 0) hF2 (hφ hZ2 (ρ w) (ρ z) (s (xs 0)) (code 0) hw2 hz2 ha2 (hqs 0)))

private theorem proved_at_equal {m} {Γ : Context m} (w z b F G : Fin m)
    (he : Derives Γ (.equal F G)) (hp : Derives Γ (proved test w z b F)) :
    Derives Γ (proved test w z b G) := by
  let P := proved test w.castSucc z.castSucc b.castSucc (Fin.last m)
  exact of_eq (by simp only [P, Formula.instantiate, proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, proved_rename, Fin.lastCases_last,
      Fin.lastCases_castSucc, id_eq]) hp))

private theorem replay_forall {free : PureSyntaxQuotation.Ctx} (φ : PureSyntaxQuotation.Fm [] (.set :: free))
    (hφ : Replay φ) : Replay (φ.forallFreeTop .set) := by
  intro m Γ hZ w z b F hw hz hb hF
  apply InternalProofTemplates.eliminate_binder_scopes hZ w z b hw
    (SyntaxNumerals.range hZ 0 w z hw hz) (SyntaxNumerals.range hZ free.length w b hw hb) (proved test w z b F)
  intro l Δ r A B hZ1 lift hA hB
  have hw1 := of_eq (omega_rename w r) (lift hw)
  apply of_eq (proved_rename test w z b F r).symm
  let trees := fun i : Fin 2 => [PureSyntaxQuotation.formulaTree φ,
    PureSyntaxQuotation.formulaTree φ.abstractFreeTop][i]
  apply ProjectCompilerQuotation.eliminate_quotations hZ1 2 trees (r w) hw1 (proved test (r w) (r z) (r b) (r F))
  intro l' Δ' s xs hZ2 move hqs
  let ρ := fun i => s (r i)
  have carry {p : Formula m} (hp : Derives Γ p) : Derives Δ' (p.rename ρ) :=
    of_eq (rename_comp p r s) (move (lift hp))
  have hw2 := of_eq (omega_rename w ρ) (carry hw)
  have hz2 := of_eq (empty_rename z ρ) (carry hz)
  have hb2 := of_eq (SyntaxNumeralSyntax.numeral_rename free.length b ρ) (carry hb)
  have hA2 := of_eq (successor_rename A (r z) s) (move hA)
  have hB2 := of_eq (successor_rename B (r b) s) (move hB)
  have hBn := SyntaxNumeralSyntax.intro_succ free.length (s B) (ρ b) hb2 hB2
  have ha := Derives.conjL (NativeTopQuotationValue.abstract_at_candidate hZ2 φ (ρ w) (ρ z) (ρ b)
    (s A) (s B) (xs 0) (xs 1) hw2 hz2 hb2 (hqs 0) hA2 hB2 (hqs 1))
  have hp := hφ hZ2 (ρ w) (ρ z) (s B) (xs 0) hw2 hz2 hBn (hqs 0)
  have hAll := InternalProofUniversal.generalize hZ2 test (ρ w) (ρ z) (ρ b)
    (s A) (s B) (xs 0) (xs 1) hw2 hz2 ha hp
  have hF2 := of_eq (PureQuotationSyntax.formula_rename (φ.forallFreeTop .set) w F ρ) (carry hF)
  have hc : Derives Δ' (SyntaxLogicalSyntax.singleCode 9 (ρ w) (xs 1) (ρ F)) :=
    OriginalQuotationNodeFields.tree_to_constructor hZ2 9 [PureSyntaxQuotation.formulaTree φ.abstractFreeTop]
      (ρ w) (ρ F) (fun _ => xs 1) hw2 (.conjI (hqs 1) (.eqRefl (ρ w))) hF2
  apply of_eq (proved_rename test (r w) (r z) (r b) (r F) s).symm
  apply eliminate_objects hZ2 1 (fun t ys =>
    (SyntaxLogicalSyntax.singleCode 9 (t (ρ w)) (t (xs 1)) (ys 0)).conj
      (proved test (t (ρ w)) (t (ρ z)) (t (ρ b)) (ys 0))) hAll (proved test (ρ w) (ρ z) (ρ b) (ρ F))
  intro l'' Ξ t ys hZ3 up h
  have he := SyntaxLogicalFields.single_unique hZ3 9 (t (ρ w)) (t (xs 1)) (ys 0) (t (ρ F))
    (of_eq (omega_rename (ρ w) t) (up hw2)) (.conjL h)
    (of_eq (SyntaxLogicalSyntax.singleCode_rename 9 (ρ w) (xs 1) (ρ F) t) (up hc))
  exact of_eq (proved_rename test (ρ w) (ρ z) (ρ b) (ρ F) t).symm
    (proved_at_equal (t (ρ w)) (t (ρ z)) (t (ρ b)) (ys 0) (t (ρ F)) he (.conjR h))

private theorem weaken_at_codes {m} {Γ : Context m} {free : PureSyntaxQuotation.Ctx}
    (hZ : ZFContext.Evidence Γ) (φ : PureSyntaxQuotation.Fm [] free)
    (w z b B F N I J : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (hB : Derives Γ (successor B b))
    (hF : Derives Γ (PureQuotationSyntax.formula φ w F))
    (hN : Derives Γ (PureQuotationSyntax.formula (φ.weakenFree SetSort.set) w N))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w z I))
    (hJ : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J)) :
    Derives Γ (WeakenFreeProgramSyntax.executed w z b B F N) := by
  apply eliminate_objects hZ 1 (fun r xs =>
    (SyntaxMapCodeSyntax.encoded (r w) (xs 0) (r z) (r z) (r I)).conj
      (SyntaxRenameTermIdentity.diagonal (xs 0))) hI (WeakenFreeProgramSyntax.executed w z b B F N)
  intro l Δ r gs hZ1 lift hg
  have hJ1 := of_eq (SyntaxFreeShiftSyntax.shiftCode_rename w b B J r) (lift hJ)
  apply of_eq (WeakenFreeProgramSyntax.executed_rename w z b B F N r).symm
  apply eliminate_objects hZ1 1 (fun s xs =>
    (SyntaxMapCodeSyntax.encoded (s (r w)) (xs 0) (s (r b)) (s (r B)) (s (r J))).conj
      (SyntaxFreeShiftSyntax.shiftMap (s (r w)) (s (r b)) (s (r B)) (xs 0))) hJ1
    (WeakenFreeProgramSyntax.executed (r w) (r z) (r b) (r B) (r F) (r N))
  intro l' Δ' s hs hZ2 move h
  let ρ := fun i => s (r i)
  have carry {p : Formula m} (hp : Derives Γ p) : Derives Δ' (p.rename ρ) :=
    of_eq (rename_comp p r s) (move (lift hp))
  have hw2 := of_eq (omega_rename w ρ) (carry hw)
  have hz2 := of_eq (empty_rename z ρ) (carry hz)
  have hb2 := of_eq (SyntaxNumeralSyntax.numeral_rename free.length b ρ) (carry hb)
  have hB2 := of_eq (successor_rename B b ρ) (carry hB)
  have hBn := SyntaxNumeralSyntax.intro_succ free.length (ρ B) (ρ b) hb2 hB2
  have hF2 := of_eq (PureQuotationSyntax.formula_rename φ w F ρ) (carry hF)
  have hN2 := of_eq (PureQuotationSyntax.formula_rename (φ.weakenFree SetSort.set) w N ρ) (carry hN)
  have hI2 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w z I ρ) (carry hI)
  have hJ2 := of_eq (SyntaxFreeShiftSyntax.shiftCode_rename w b B J ρ) (carry hJ)
  have hG := of_eq (SyntaxMapCodeSyntax.encoded_rename (r w) (gs 0) (r z) (r z) (r I) s)
    (move (.conjL hg))
  let shift : VariableRenaming free (.set :: free) := VariableRenaming.weaken SetSort.set
  have values (j : Fin free.length) : Derives Δ'
      (SchemaIndexQuotation.value j.val (shift (NativeTopQuotationIndices.entryAt free j)).index (hs 0)) := by
    simpa only [shift, VariableRenaming.weaken, YesMetaZFC.Logic.FirstOrder.Variable.index,
      NativeTopQuotationIndices.index_entryAt, Nat.succ_eq_add_one] using
      SchemaIndexQuotation.shift_value hZ2 (ρ w) (ρ b) (ρ B) (hs 0) hb2 (.conjR h) j
  have iff := NativeIndexFormulaQuotation.formula_iff hZ2 φ (fun i => i) shift (ρ w) (ρ I) (ρ J)
    (ρ z) (ρ b) (ρ z) (ρ B) (ρ F) (ρ N) (s (gs 0)) (hs 0)
    hw2 hz2 hb2 hz2 hBn hG (.conjL h) (fun j => Fin.elim0 j) values hF2
  have rename := Derives.impE (.conjR iff) (by
    rw [← YesMetaZFC.Logic.FirstOrder.Formula.renameMapped_eq_substituteMapped]
    exact hN2)
  exact of_eq (WeakenFreeProgramSyntax.executed_rename (r w) (r z) (r b) (r B) (r F) (r N) s).symm
    (WeakenFreeProgramCorrectness.forward hZ2 (ρ w) (ρ z) (ρ b) (ρ B) (ρ F) (ρ N) hw2
      (SyntaxWeakenFreeSyntax.intro_weakened (ρ w) (ρ z) (ρ b) (ρ B) (ρ F) (ρ N) (ρ I) (ρ J) hI2 hJ2 rename))

private theorem weaken_from_quotations {m} {Γ : Context m} {free : PureSyntaxQuotation.Ctx}
    (hZ : ZFContext.Evidence Γ) (φ : PureSyntaxQuotation.Fm [] free)
    (w z b B F N : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (hB : Derives Γ (successor B b))
    (hF : Derives Γ (PureQuotationSyntax.formula φ w F))
    (hN : Derives Γ (PureQuotationSyntax.formula (φ.weakenFree SetSort.set) w N)) :
    Derives Γ (WeakenFreeProgramSyntax.executed w z b B F N) := by
  apply eliminate_objects hZ 1 (fun r xs => SyntaxIdentityMapSyntax.identityCode (r w) (r z) (xs 0))
    (SyntaxIdentityCode.exists_code hZ w z hw (SyntaxNumerals.range hZ 0 w z hw hz))
    (WeakenFreeProgramSyntax.executed w z b B F N)
  intro l Δ r xs hZ1 lift hI
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hb1 := of_eq (SyntaxNumeralSyntax.numeral_rename free.length b r) (lift hb)
  have hB1 := of_eq (successor_rename B b r) (lift hB)
  apply of_eq (WeakenFreeProgramSyntax.executed_rename w z b B F N r).symm
  apply eliminate_objects hZ1 1 (fun s ys => SyntaxFreeShiftSyntax.shiftCode (s (r w)) (s (r b)) (s (r B)) (ys 0))
    (SyntaxFreeShiftCode.exists_code hZ1 (r w) (r b) (r B) hw1 (SyntaxNumerals.range hZ1 free.length (r w) (r b) hw1 hb1) hB1)
    (WeakenFreeProgramSyntax.executed (r w) (r z) (r b) (r B) (r F) (r N))
  intro l' Δ' s ys hZ2 move hJ
  let ρ := fun i => s (r i)
  have carry {p : Formula m} (hp : Derives Γ p) : Derives Δ' (p.rename ρ) :=
    of_eq (rename_comp p r s) (move (lift hp))
  exact of_eq (WeakenFreeProgramSyntax.executed_rename (r w) (r z) (r b) (r B) (r F) (r N) s).symm
    (weaken_at_codes hZ2 φ (ρ w) (ρ z) (ρ b) (ρ B) (ρ F) (ρ N) (s (xs 0)) (ys 0)
      (of_eq (omega_rename w ρ) (carry hw)) (of_eq (empty_rename z ρ) (carry hz))
      (of_eq (SyntaxNumeralSyntax.numeral_rename free.length b ρ) (carry hb))
      (of_eq (successor_rename B b ρ) (carry hB))
      (of_eq (PureQuotationSyntax.formula_rename φ w F ρ) (carry hF))
      (of_eq (PureQuotationSyntax.formula_rename (φ.weakenFree SetSort.set) w N ρ) (carry hN))
      (of_eq (SyntaxIdentityMapSyntax.identityCode_rename (r w) (r z) (xs 0) s) (move hI)) hJ)

private theorem replay_strengthening {free : PureSyntaxQuotation.Ctx} (φ : PureSyntaxQuotation.Fm [] free)
    (hφ : Replay (φ.weakenFree SetSort.set)) : Replay φ := by
  intro m Γ hZ w z b F hw hz hb hF
  apply InternalProofTemplates.eliminate_successor hZ w b hw (SyntaxNumerals.range hZ free.length w b hw hb)
    (proved test w z b F)
  intro l Δ r B hZ1 lift hB
  have hw1 := of_eq (omega_rename w r) (lift hw)
  apply of_eq (proved_rename test w z b F r).symm
  apply ProjectCompilerQuotation.eliminate_quotations hZ1 1
    (fun _ => PureSyntaxQuotation.formulaTree (φ.weakenFree SetSort.set)) (r w) hw1 (proved test (r w) (r z) (r b) (r F))
  intro l' Δ' s xs hZ2 move hqs
  let ρ := fun i => s (r i)
  have carry {p : Formula m} (hp : Derives Γ p) : Derives Δ' (p.rename ρ) :=
    of_eq (rename_comp p r s) (move (lift hp))
  have hw2 := of_eq (omega_rename w ρ) (carry hw)
  have hz2 := of_eq (empty_rename z ρ) (carry hz)
  have hb2 := of_eq (SyntaxNumeralSyntax.numeral_rename free.length b ρ) (carry hb)
  have hB2 := of_eq (successor_rename B (r b) s) (move hB)
  have hBn := SyntaxNumeralSyntax.intro_succ free.length (s B) (ρ b) hb2 hB2
  have hF2 := of_eq (PureQuotationSyntax.formula_rename φ w F ρ) (carry hF)
  exact of_eq (proved_rename test (r w) (r z) (r b) (r F) s).symm
    (strengthen_at_execution hZ2 (ρ w) (ρ z) (ρ b) (s B) (ρ F) (xs 0) hw2 hz2 hB2
      (weaken_from_quotations hZ2 φ (ρ w) (ρ z) (ρ b) (s B) (ρ F) (xs 0) hw2 hz2 hb2 hB2 hF2 (hqs 0))
      (hφ hZ2 (ρ w) (ρ z) (s B) (xs 0) hw2 hz2 hBn (hqs 0)))

private theorem annotate_root {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z p F : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hr : Derives Γ (ProofTreeEntrySyntax.root test w p F)) :
    Derives Γ (InternalMPProof.annotated test w z z F p) := by
  have normalized := ProofTreeRootForward.root_forward test hZ w p F hw hr
  let out := InternalMPProof.annotated test w z z F p
  apply ProofTreeRootSyntax.disjoin_elim
    (ProofTreeRootSyntax.kinds.map (fun kind => ProofTreeRootSyntax.branch kind w p F)) out (.conjR normalized)
  intro branch hbranch
  obtain ⟨kind, _, rfl⟩ := List.mem_map.mp hbranch
  apply Derives.impI
  let Q := ProofTreeRootSyntax.branch kind w p F
  let k := (ProofTreeBranchConstruction.shape kind).extra + 2
  apply eliminate_objects (ZFContext.add hZ Q) k
    (fun r xs => ProofTreeRootSyntax.matrix kind (r w) (r p) (r F) xs)
    (Derives.hyp (Or.inl rfl)) out
  intro l Δ r xs hZ1 lift h
  have hw1 := of_eq (omega_rename w r) (lift (SourceLogic.add hw Q))
  have hz1 := of_eq (empty_rename z r) (lift (SourceLogic.add hz Q))
  have hn := of_eq (ProofTreeEntryFacts.node_rename test w p r) (lift (SourceLogic.add (.conjL normalized) Q))
  have he := OmegaUniversal.empty_unique (r z) (xs 0) (ZFContext.arithmetic hZ1).base.extensionality
    hz1 (.conjL (.conjR (.conjR h)))
  let tag := (ProofTreeBranchConstruction.shape kind).tag
  have hCtor : Derives Δ (SyntaxNodeSyntax.constructor k tag (r w) xs (r p)) := .conjL (.conjR h)
  have h0 := Derives.impE (.conjR (RawCodeFieldAtConstructor.constructor_at hZ1 k tag (r w) xs (r p)
    0 (r z) (r z) hw1 hCtor hz1)) he
  have sameF := Derives.conjR (.conjR (.conjR h))
  apply of_eq (InternalMPProof.annotated_rename test w z z F p r).symm
  apply eliminate_objects hZ1 1 (fun s ns =>
    (Formula.mem (ns 0) (s (r w))).conj (SyntaxNumeralSyntax.numeral 1 (ns 0)))
    (SyntaxNumerals.exists_numeral hZ1 1 (r w) hw1) (InternalMPProof.annotated test (r w) (r z) (r z) (r F) (r p))
  intro l' Δ' s ns hZ2 move hOne
  have hw2 := of_eq (omega_rename (r w) s) (move hw1)
  have hCtor2 := of_eq (SyntaxNodeSyntax.constructor_rename k tag (r w) xs (r p) s) (move hCtor)
  have h1 := Derives.impE (.conjR (RawCodeFieldAtConstructor.constructor_at hZ2 k tag (s (r w))
    (fun i => s (xs i)) (s (r p)) 1 (ns 0) (s (r F)) hw2 hCtor2 (.conjR hOne)))
    (eq_symm (move sameF))
  exact of_eq (InternalMPProof.annotated_rename test (r w) (r z) (r z) (r F) (r p) s).symm
    (.conjI (of_eq (ProofTreeEntryFacts.node_rename test (r w) (r p) s) (move hn))
      (.conjI (of_eq (RawCodeFieldSyntax.field_rename (r w) (r p) (r z) (r z) s) (move h0))
        (ProofSubstitutionProjectionSyntax.intro_atOne (s (r w)) (s (r p)) (s (r F)) (ns 0) (.conjR hOne) h1)))

private theorem proved_of_root {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z F : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hp : Derives Γ (InternalAxiomProof.provable false w F)) : Derives Γ (proved test w z z F) := by
  apply eliminate_objects hZ 1 (fun r xs =>
    (Formula.mem (xs 0) (r w)).conj (ProofTreeEntrySyntax.root test (r w) (xs 0) (r F))) hp
    (proved test w z z F)
  intro l Δ r xs hZ1 lift h
  have hn := annotate_root hZ1 (r w) (r z) (xs 0) (r F)
    (of_eq (omega_rename w r) (lift hw)) (of_eq (empty_rename z r) (lift hz)) (.conjR h)
  have hr : Derives Δ ((empty (r z)).imp (ProofTreeEntrySyntax.root test (r w) (xs 0) (r F))) :=
    .impI (SourceLogic.add (.conjR h) (empty (r z)))
  apply of_eq (proved_rename test w z z F r).symm
  apply Derives.exI (xs 0)
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, InternalMPProof.annotated_rename,
    empty_rename, ProofTreeEntryFacts.root_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.conjI (.conjL h) (.conjI hn hr))

private theorem replay_theory {free : PureSyntaxQuotation.Ctx} (φ : PureSyntaxQuotation.Fm [] [])
    (hφ : nativeZF φ) : Replay (φ.fromSentence : PureSyntaxQuotation.Fm [] free) := by
  intro m Γ hZ w z b F hw hz hb hF
  cases free with
  | nil =>
    have hp := proved_of_root hZ w z F hw hz (InternalAxiomProof.from_native_quotation hZ φ hφ w F hw hF)
    have he := OmegaUniversal.empty_unique z b (ZFContext.arithmetic hZ).base.extensionality hz hb
    let P := proved test w.castSucc z.castSucc (Fin.last m) F.castSucc
    exact of_eq (by simp only [P, Formula.instantiate, proved_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, proved_rename, Fin.lastCases_last,
        Fin.lastCases_castSucc, id_eq]) hp))
  | cons sort tail =>
    let τ : NativeSubstitutionSyntax.Mapping [] [] (sort :: tail) := fun v => .fvar (VariableRenaming.empty v)
    have hs : φ.substituteFree τ = (φ.fromSentence : PureSyntaxQuotation.Fm [] (sort :: tail)) :=
      (YesMetaZFC.Logic.FirstOrder.Formula.renameMapped_eq_substituteMapped
        (fun v => v) VariableRenaming.empty φ).symm
    have ht : PureSyntaxQuotation.formulaTree (φ.fromSentence : PureSyntaxQuotation.Fm [] (sort :: tail)) =
        PureSyntaxQuotation.formulaTree φ :=
      InternalProofTemplates.quotation_rename_indices (fun v => v)
        (VariableRenaming.empty (Γ := sort :: tail)) (fun _ => rfl) (fun v => nomatch v) φ
    have hN : Derives Γ (PureQuotationSyntax.formula φ w F) := of_eq (congrArg
      (fun t => OriginalTreeQuotationSyntax.tree t w F) ht) hF
    exact replay_substituted hZ φ τ w z z b F F hw hz hz hb hN (of_eq (by rw [hs]) hF)
      (proved_of_root hZ w z F hw hz (InternalAxiomProof.from_native_quotation hZ φ hφ w F hw hN))

private theorem from_hilbert {free : PureSyntaxQuotation.Ctx} {φ : PureSyntaxQuotation.Fm [] free}
    (h : HilbertDerivation nativeZF free φ) : Replay φ := by
  induction h with
  | logical_axiom cert =>
    intro m Γ hZ w z b F hw hz hb hF
    exact InternalProofTemplates.from_logical_quotation hZ test cert w z b F hw hz hb hF
  | theory_axiom hφ => exact replay_theory _ hφ
  | modus_ponens _ _ hl hi => exact replay_mp _ _ hl hi
  | @forall_generalization free sort φ _ hφ =>
    cases sort
    exact replay_forall φ hφ
  | @free_strengthening free sort φ _ hφ =>
    cases sort
    exact replay_strengthening φ hφ
  | free_substitution τ _ hφ => exact replay_substitution _ τ hφ

/-- A fixed pure nativeZF proof yields an actual original closed proof at any
object value quoting the exact conclusion. All six rule nodes are checked. -/
theorem from_derives {m} {Γ : Context m} {φ : PureSyntaxQuotation.Fm [] []}
    (hZ : ZFContext.Evidence Γ) (hφ : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] φ)
    (w z F : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hF : Derives Γ (PureQuotationSyntax.formula φ w F)) :
    Derives Γ (InternalAxiomProof.provable false w F) := by
  obtain ⟨proof⟩ := hφ
  exact InternalFalseRoot.close_empty test w z z F hz (from_hilbert proof hZ w z z F hw hz hz hF)

/-- Original Root production for the fixed member/equality monotonicity proof
from the pinned atomic forcing argument. The quote is an object value. -/
theorem atomic_monotone {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Formula (n+2)) (P x y p q : Fin n)
    (w z F : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hF : Derives Γ (PureQuotationSyntax.formula
      (Translation.sentence (ForcingAtomicBasic.monotoneSentence equality R P x y p q)) w F)) :
    Derives Γ (InternalAxiomProof.provable false w F) :=
  from_derives hZ (ForcingAtomicBasic.monotone_kernel_certificate equality R P x y p q) w z F hw hz hF

private def atomicMonoMatrix {n} (equality : Bool) (R : Formula (n+2)) (P x y p q : Fin n) : Formula n :=
  (ForcingAtomicBasic.preorder R id P).imp ((Formula.mem q P).imp ((ReplacementPredicates.rel R id q p).imp
    ((ForcingAtomicRelations.forces equality R id P x y p).imp (ForcingAtomicRelations.forces equality R id P x y q))))

/-- The literal body of the pinned atomic monotonicity sentence, with its
parameters exposed as free variables in the original pure signature. -/
def atomicMonoTemplate {n} (equality : Bool) (R : Formula (n+2)) (P x y p q : Fin n) :
    PureSyntaxQuotation.Fm [] (List.replicate n SetSort.set) :=
  Syntax.formula Syntax.variables (atomicMonoMatrix equality R P x y p q)

private theorem atomic_open_derives {n} (equality : Bool) (R : Formula (n+2)) (P x y p q : Fin n) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (atomicMonoTemplate equality R P x y p q) := by
  let M := atomicMonoMatrix equality R P x y p q
  have h := ReverseZFReplay.source_sentence (ForcingAtomicBasic.monotone_kernel_certificate equality R P x y p q)
  have hd : Derives (SetLanguage.ZF.at n) (M.close.rename Fin.elim0) := by
    apply Derives.weaken _ (of_eq (closed_rename M.close (fun _ : Fin 1 => P)) (Derives.rename (fun _ => P) h))
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, (closed_rename s (fun _ : Fin 1 => P)).symm⟩
  have ho := specialize_close M id hd
  rw [Reverse.source_rename_id] at ho
  exact ZFReplay.source_derives_at ho Syntax.variables

/-- Consume a real mixed substitution into the fixed atomic proof. The output,
term list, and ambient free scope are arbitrary internal codes. The unchanged
mode-3 proof rule consumes the same list and produces the same output formula. -/
theorem atomic_monotone_instance {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (equality : Bool) (R : Formula (n+2)) (P x y p q : Fin n)
    (w z a b B L N F : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral n a))
    (hN : Derives Γ (PureQuotationSyntax.formula (atomicMonoTemplate equality R P x y p q) w N))
    (hF : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w B L z a z b N F)) :
    Derives Γ (proved (OriginalAxiomCodeTest.test false) w z b F) := by
  obtain ⟨proof⟩ := atomic_open_derives equality R P x y p q
  exact substitute_at_list hZ w z a b L N F hw hz (execution_from_mixed hZ w z a b B L N F hw hz hF)
    (from_hilbert proof hZ w z a N hw hz (of_eq (by rw [List.length_replicate]) ha) hN)

/-- Closure in the original nativeZF kernel quantifies the actual substituted
formula, image lists and ambient scope as object variables. -/
theorem atomic_monotone_kernel_certificate {n m}
    (equality : Bool) (R : Formula (n+2)) (P x y p q : Fin n) (w z a b B L N F : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence
      (((omega w).conj ((empty z).conj ((SyntaxNumeralSyntax.numeral n a).conj
        ((PureQuotationSyntax.formula (atomicMonoTemplate equality R P x y p q) w N).conj
          (SyntaxMixedFormulaJudgmentSyntax.substituted w B L z a z b N F))))).imp
        (proved (OriginalAxiomCodeTest.test false) w z b F)).close) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let H := (omega w).conj ((empty z).conj ((SyntaxNumeralSyntax.numeral n a).conj
    ((PureQuotationSyntax.formula (atomicMonoTemplate equality R P x y p q) w N).conj
      (SyntaxMixedFormulaJudgmentSyntax.substituted w B L z a z b N F))))
  have h : Derives (Context.add H (SetLanguage.ZF.at m)) H := .hyp (Or.inl rfl)
  exact atomic_monotone_instance (ZFContext.add (ZFContext.source_ZF m) _) equality R P x y p q
    w z a b B L N F (.conjL h) (.conjL (.conjR h)) (.conjL (.conjR (.conjR h)))
    (.conjL (.conjR (.conjR (.conjR h)))) (.conjR (.conjR (.conjR (.conjR h))))

end PPAC.Migration.NativeProofQuotation
