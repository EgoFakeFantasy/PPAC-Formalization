/- Pinned CodeLinks.ordinalRank:95 / ordinalType:101.
Construct every auxiliary action witness over the SAME group/filter and apply
actual Selected covariance to the existing Cohen rank/type producers. -/
import PPAC.Migration.ForcingCodeSelection

namespace PPAC.Migration.ForcingCodeRanks
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingMapConditions (MapRel)
open ForcingProductSymmetry (orderFormula)
open ForcingCodeSelection (IsSelected relation mapRel_relation)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private theorem atomic_congr {k n : Nat} {R : Formula (k+2)} {S : Formula (n+2)}
    {env : Fin k → M.Carrier .set} {other : Fin n → M.Carrier .set}
    (hR : ∀ x y, MapRel R env x y ↔ MapRel S other x y)
    (eq : Bool) (P x y p : M.Carrier .set) :
    ForcingAtomicRelations.Forces eq R env P x y p ↔ ForcingAtomicRelations.Forces eq S other P x y p := by
  simp only [ForcingAtomicRelations.Forces,ForcingAtomicGraphs.Good,ForcingAtomicStep.Equation,
    ForcingAtomicStep.MemBody,ForcingAtomicStep.EqBody,ForcingAtomicStep.EqHalf,hR]

private theorem basic_congr {k n m : Nat} {R : Formula (k+2)} {S : Formula (n+2)}
    {H : Formula (k+1)} {J : Formula (n+1)}
    {env : Fin k → M.Carrier .set} {other : Fin n → M.Carrier .set}
    (hR : ∀ x y, MapRel R env x y ↔ MapRel S other x y)
    (hH : ∀ x, ForcingClassEvaluation.Predicate H env x ↔ ForcingClassEvaluation.Predicate J other x)
    (v : Fin m → M.Carrier .set) (P p : M.Carrier .set) (phi : ForcingFormula.Basic m) :
    ForcingFormula.BasicForce R H env v P p phi ↔ ForcingFormula.BasicForce S J other v P p phi := by
  induction phi generalizing p with
  | bot => rfl
  | mem x y | equal x y => exact atomic_congr hR _ _ _ _ _
  | conj a b ia ib => exact and_congr (ia v p) (ib v p)
  | neg a ia => simp only [ForcingFormula.BasicForce,hR,ia]
  | ex a ia => simp only [ForcingFormula.BasicForce,hR,hH,ia]

/-- Adding temporary action-witness slots does not change the actual predicate. -/
theorem selected_reindex {k n : Nat} (env : Fin k → M.Carrier .set)
    (other : Fin n → M.Carrier .set) (base : Fin k → Fin n) (he : ∀ i, other (base i) = env i)
    (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order : Fin k)
    (a d : M.Carrier .set) :
    IsSelected other (fun j => base (rho j)) (base I) (base G) (base F) (base mul) (base q)
      (base bound) (base labels) (base E) (base root) (base w) (base chain) (base codes) (base order) a d ↔
    IsSelected env rho I G F mul q bound labels E root w chain codes order a d := by
  have hR (x y : M.Carrier .set) : MapRel (orderFormula (base (rho 0)) (base mul)) other x y ↔
      MapRel (orderFormula (rho 0) mul) env x y := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,he]
  have hH (x : M.Carrier .set) : ForcingClassEvaluation.Predicate
      (ForcingPairUnion.domain (fun j => base (rho j)) (base G) (base F)) other x ↔
      ForcingClassEvaluation.Predicate (ForcingPairUnion.domain rho G F) env x := by
    simp only [ForcingPairUnion.domain_semantics,he]
  have hForce {m : Nat} (v : Fin m → M.Carrier .set) (P p : M.Carrier .set) (phi : Formula m) :
      ForcingFormula.Force (orderFormula (base (rho 0)) (base mul))
        (ForcingPairUnion.domain (fun j => base (rho j)) (base G) (base F)) other v P p phi ↔
      ForcingFormula.Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env v P p phi :=
    basic_congr hR hH v P p (ForcingFormula.toBasic phi)
  simp only [IsSelected,ForcingPersistentSelection.Selected,ForcingPersistentWorks.Works,
    ForcingPersistentWorks.Represented,ForcingPersistentWorks.Bundle,ForcingTailCodes.Represents,
    ForcingTailCodes.At,ForcingEligibleFamily.Family,ForcingEligibleFamily.Row,
    ForcingEligibleMapFamily.Family,ForcingEligibleMapFamily.MapRow,ForcingEligibleFamily.Data,
    ForcingLocalQuotient.Classes,ForcingLocalQuotient.Projection,ForcingLocalQuotient.Class,
    ForcingEligibleObjects.Carrier,ForcingEligibility.Eligible,ForcingEligibility.EligibleName,
    ForcingLocalAtomic.EqG,ForcingPersistentCodes.Same,ForcingPrincipalFilter.EqF,
    hForce,atomic_congr hR,he]

theorem covariant (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order : Fin k) (group : M.Carrier .set)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmallD : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hSmall : ForcingSupportSize.Small (env w) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hBound : ForcingSupportedNames.Supported (fun j => env (rho j)) (env G) (env bound))
    (hq : ForcingSupportSize.Injection (env (rho 0)) (env I) (env q))
    (hA : ForcingSupportedNames.Range (env (rho 0)) (env q) (env A))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env A) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hGroup : ForcingTailGroup.TailGroup (env w) (env (rho 0)) (env G) (env chain) group) :
    ForcingCohenSelection.Covariant (relation rho I G F mul q bound labels E root w chain codes order)
      env (env (rho 2)) (env w) group (env codes) := by
  intro pi a d e hpi ha hd he hMoved hSelected
  have hPi := (hG pi).mp ((hGroup pi).mp hpi).1
  obtain ⟨inv,hInv,hInverse⟩ := ForcingConditionGraphs.exists_inverse hM hPi
  obtain ⟨c,hcPerm,hConj⟩ := ForcingConjugationGraph.exists_graph hM hG hPi hInv hInverse
  obtain ⟨act,hAct⟩ := ForcingProductFamily.exists_action hM hp hPi
  obtain ⟨ai,hAI⟩ := ForcingProductFamily.exists_action hM hp hInv
  have hData : ForcingProductCovariance.SystemData (fun j => env (rho j))
      (env I) (env K) (env B) (env w) (env G) (env F) (env mu) pi inv c act ai :=
    ⟨hp,hG,hPi,hInv,hInverse,hcPerm,hConj,hAct,hAI,hF⟩
  obtain ⟨ac,hc⟩ := ForcingLocalTransport.part_of_action hAct
  have hac := ForcingLocalTransport.part_permutation hc
  obtain ⟨e',hde',_⟩ := hac.1.1.2 d ((hp.2.2.1 d).mpr hd)
  have he' := (hp.2.2.1 e').mp (hac.1.2 d e' hde')
  have hcCopy := hc
  obtain ⟨f,t,_,hf,_,ht,_,hGraph⟩ := hcCopy
  have hMoved' := ConstructionCohenCompatibility.moved_of_image hM hp.1 hp.2.1 hf ht hd
    ((hGraph d e').mp hde').2.2
  have heq : e' = e := ConstructionCohenCompatibility.entries_ext hM hp.1 hp.2.1 he' he
    (fun i j b => (hMoved' i j b).trans (hMoved i j b).symm)
  subst e'
  let other : Fin (k+6) → M.Carrier .set :=
    Fin.cases pi (Fin.cases inv (Fin.cases c (Fin.cases act (Fin.cases ai (Fin.cases group env)))))
  let up : Fin k → Fin (k+6) := fun j => j.succ.succ.succ.succ.succ.succ
  have henv (j : Fin k) : other (up j) = env j := by
    simp only [other,up,Fin.cases_succ]
  have hStep := ForcingCodeSelection.isSelected_covariance hM hChoice other (fun j => up (rho j))
    (up I) (up K) (up B) (up w) (up G) (up F) (up mul) (up one) (up mu) (up history) (up kappa) (up mark) (up H) (up C) (up incoming) (up base) (up q) (up A) (up Hq) (up labelMap) (up top) (up bit) (up labels) (up E) (up bound) 0 1 2 3 4
    (up zero) (up root) (up vertices) (up chain) (up names) (up codes) (up order) 5 a
    hm hJ hData hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound
    hq hA hHq hE hChain hCarrier ha hGroup hpi hc hde'
  have hs := (mapRel_relation hM env rho I G F mul q bound labels E root w chain codes order a d).mp hSelected
  have hs' := (selected_reindex env other up henv rho I G F mul q bound labels E root w chain codes order a d).mpr hs
  exact (mapRel_relation hM env rho I G F mul q bound labels E root w chain codes order a e).mpr
    ((selected_reindex env other up henv rho I G F mul q bound labels E root w chain codes order a e).mp (hStep.mpr hs'))

theorem construct (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order r index U : Fin k)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmallD : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hSmall : ForcingSupportSize.Small (env w) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hBound : ForcingSupportedNames.Supported (fun j => env (rho j)) (env G) (env bound))
    (hq : ForcingSupportSize.Injection (env (rho 0)) (env I) (env q))
    (hA : ForcingSupportedNames.Range (env (rho 0)) (env q) (env A))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env A) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hRootCode : ConstructionComponentCarrier.Code (env root) (env r) (env index) (env U))
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder
      (KuratowskiZF.interpretation hM) (env order) (env codes)) :
    ∃ group support fixing ranks selection,
      ForcingTailGroup.TailGroup (env w) (env (rho 0)) (env G) (env chain) group ∧
      ForcingSupportedNames.Range (env (rho 0)) (env r) support ∧
      ForcingLabelPermutations.Fixing (env G) support fixing ∧
      (Project.FirstOrderSemantics.reduct M).MemberSubset fixing group ∧
      ForcingConjugationGraph.Subgroup (env I) (env G) group ∧
      (Project.FirstOrderSemantics.reduct M).mem group (env F) ∧
      ForcingCohenSelection.Covariant (relation rho I G F mul q bound labels E root w chain codes order) env (env (rho 2)) (env w) group (env codes) ∧
      ForcingCohenRankConsumers.Monotone (relation rho I G F mul q bound labels E root w chain codes order) env (env (rho 2)) (env w) (env codes) ∧
      ForcingOrdinalRanks.Ranks (ForcingCohenSelection.liftRelation (relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w) env (env codes) (env order) (env (rho 6)) ranks ∧
      ForcingCollectedName.Collected (ForcingCohenSelection.liftRelation (relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w) env (env codes) ranks (env (rho 6)) selection ∧
      ForcingOrdinalFixed.FixedFamily (fun j => env (rho j)) (env G) (env F) group (env codes) ranks ∧
      ForcingOrdinalFixed.Fixed (fun j => env (rho j)) (env G) (env F) group selection := by
  obtain ⟨group,support,fixing,hGroup,hRange,hFixing,hInclude,hSub,hMember,_⟩ :=
    ForcingTailGroup.tailGroup_supported hM hw hMu.1.1 hSmallD hm hJ hq hChain hRootCode hG hF
  have hCov := covariant hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base
    q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group
    hm hJ hp hG hF hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound
    hq hA hHq hE hChain hCarrier hGroup
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  obtain ⟨ranks,selection,hRanks,hType,hFamily,hFixed⟩ :=
    ForcingCohenSelection.exists_fixed_ranks hM (relation rho I G F mul q bound labels E root w chain codes order) id env rho I w
      hp hG hNormal hSub hMember hCov hOrder
  exact ⟨group,support,fixing,ranks,selection,hGroup,hRange,hFixing,hInclude,hSub,hMember,hCov,
    ForcingCodeSelection.monotone hM env rho I G F mul q bound labels E root w chain codes order,
    hRanks,hType,hFamily,hFixed⟩

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order r index U : Fin k) : Project.Sentence where
  formula :=
    let R := relation rho I G F mul q bound labels E root w chain codes order
    let L := ForcingCohenSelection.liftRelation R id (rho 0) I (rho 2) w
    let up : Fin k → Fin (k+5) := fun j => j.succ.succ.succ.succ.succ
    Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small w mu))
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul one mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn labelMap K))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K labelMap top bit labels))
    (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K labelMap top bit bound))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho G bound))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q A))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A Hq))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq E))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
    (.imp (ConstructionComponentCarrier.code root r index U)
    (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound codes))
    (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ForcingTailGroup.tailGroup (up w) (up (rho 0)) (up G) (up chain) 4)
      (.conj (ProjectSyntax.encode id (ForcingSupportedNames.range (up (rho 0)) (up r) 3))
      (.conj (ProjectSyntax.encode id (ForcingLabelPermutations.fixing (up G) 3 2))
      (.conj (ProjectSyntax.encode id (Source.SetLanguage.subset 2 4))
      (.conj (ProjectSyntax.encode id (ForcingConjugationGraph.subgroup (up I) (up G) 4))
      (.conj (.mem (.bound 4) (.bound (up F)))
      (.conj (ForcingCohenSelection.covariant R up (up (rho 2)) (up w) 4 (up codes))
      (.conj (ProjectSyntax.encode id (ForcingCohenRankConsumers.monotone R up (up (rho 2)) (up w) (up codes)))
      (.conj (ProjectSyntax.encode id (ForcingOrdinalRanks.ranks L up (up codes) (up order) (up (rho 6)) 1))
      (.conj (ProjectSyntax.encode id (ForcingCollectedName.collected L up (up codes) 1 (up (rho 6)) 0))
      (.conj (ProjectSyntax.encode id (ForcingOrdinalFixed.fixedFamily (fun j => up (rho j)) (up G) (up F) 4 (up codes) 1))
      (ProjectSyntax.encode id (ForcingOrdinalFixed.fixed (fun j => up (rho j)) (up G) (up F) 4 0)))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ForcingTailCodes.carrier_freeClosed,ConstructionComponentCarrier.code_freeClosed,
      ForcingTailGroup.tailGroup_freeClosed,ForcingCohenSelection.covariant_freeClosed,
      Project.Formula.isSetCodedWellOrder_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order r index U : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order r index U)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ConstructionSaturationIndex.hartogs_semantics hM,
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),ConstructionComponentCofinal.chain_semantics hM,
    ForcingTailCodes.carrier_semantics hM,ConstructionComponentCarrier.code_semantics hM,
    ForcingTailGroup.tailGroup_semantics hM,ForcingLabelPermutations.subset_semantics (M := M),
    ForcingConjugationGraph.subgroup_semantics (M := M),ForcingCohenSelection.covariant_semantics hM,
    ForcingCohenRankConsumers.monotone_semantics (M := M),ForcingOrdinalRanks.ranks_semantics (M := M),
    ForcingCollectedName.collected_semantics (M := M),ForcingOrdinalFixed.fixedFamily_semantics (M := M),
    ForcingOrdinalFixed.fixed_semantics (M := M)]
  exact construct hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order r index U

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order r index U : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order r index U))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let witness := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => witness }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (constructionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order r index U)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order r index U)).mp
      (construction_models rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order r index U hL hChoice)

end PPAC.Migration.ForcingCodeRanks
