/- Pinned GermSelectors.preliminary_total/preliminary_onto, consuming the
actual ConcreteQuotients count and constructing one internal rank/table. -/
import PPAC.Migration.ForcingIdealProbeCount
import PPAC.Migration.ForcingCodeRanks

namespace PPAC.Migration.ForcingConcreteGermDensity
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingProductSymmetry (orderFormula)
open ForcingSupportSize (MapsTo Injection)
open ForcingPrincipalFilter (EqF)
open ConstructionComponentCofinal (Chain EncodedCommon)
open ConstructionComponentCarrier (Code)
open ForcingGermPreliminary (PreliminaryAt)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Dense (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order ranks selection top labelSet r : Fin k)
    (rankBound tab delta : M.Carrier .set) : Prop :=
  (∀ d vertex label, ForcingCohenConditions.Condition (env (rho 2)) (env w) d →
    ForcingPowerName.Subset delta d → EncodedCommon (env (rho 0)) (env I) (env mul) (env q) (env root) vertex →
    (Project.FirstOrderSemantics.reduct M).mem label (env labelSet) →
    ∃ e tau, ForcingCohenConditions.Condition (env (rho 2)) (env w) e ∧
      ForcingPowerName.Subset d e ∧ ForcingTailCodes.Entry (fun j => env (rho j)) (env G) (env F) (env bound) vertex tau ∧
      PreliminaryAt hM env rho I G F mul q bound labels E root w chain codes order ranks selection top labelSet r rankBound tab e vertex label tau) ∧
  (∀ d vertex code tau, ForcingCohenConditions.Condition (env (rho 2)) (env w) d →
    ForcingPowerName.Subset delta d → (Project.FirstOrderSemantics.reduct M).mem code (env codes) →
    ForcingClassEvaluation.Predicate (ForcingPairUnion.domain rho G F) env tau →
    ForcingPersistentWorks.Works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
      (env I) (env G) (env F) (env mul) (env q) (env bound) (env labels) (env E) (env root) (env w) (env chain) d code →
    ForcingCodeLinks.Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) d vertex tau code →
    ∃ e label, ForcingCohenConditions.Condition (env (rho 2)) (env w) e ∧ ForcingPowerName.Subset d e ∧
      PreliminaryAt hM env rho I G F mul q bound labels E root w chain codes order ranks selection top labelSet r rankBound tab e vertex label tau)

def dense {k n : Nat} (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order ranks selection top labelSet r : Fin k) (base : Fin k → Fin n) (rankBound tab delta : Fin n) : Project.Formula 1 n :=
  let up3 : Fin n → Fin (n+3) := fun j => j.succ.succ.succ
  let up4 : Fin n → Fin (n+4) := fun j => j.succ.succ.succ.succ
  let up5 : Fin n → Fin (n+5) := fun j => j.succ.succ.succ.succ.succ
  let up6 : Fin n → Fin (n+6) := fun j => j.succ.succ.succ.succ.succ.succ
  (.conj (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (up3 (base (rho 2))) (up3 (base w)) 2))
      (.imp (Project.Formula.subset (.bound (up3 delta)) (.bound 2))
      (.imp (ConstructionComponentCofinal.encodedCommon (up3 (base (rho 0))) (up3 (base I)) (up3 (base mul)) (up3 (base q)) (up3 (base root)) 1)
      (.imp (.mem (.bound 0) (.bound (up3 (base labelSet))))
      (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition (up5 (base (rho 2))) (up5 (base w)) 1))
      (.conj (Project.Formula.subset (.bound 4) (.bound 1))
      (.conj (ForcingTailCodes.entry (fun j => up5 (base (rho j))) (up5 (base G)) (up5 (base F)) (up5 (base bound)) 3 0)
      (ForcingGermPreliminary.preliminaryAt rho I G F mul q bound labels E root w chain codes order ranks selection top labelSet r (fun j => up5 (base j)) (up5 rankBound) (up5 tab) 1 3 2 0)))))))))))))
      (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (up4 (base (rho 2))) (up4 (base w)) 3))
      (.imp (Project.Formula.subset (.bound (up4 delta)) (.bound 3))
      (.imp (.mem (.bound 1) (.bound (up4 (base codes))))
      (.imp (ProjectSyntax.encode id (MinimalPredicates.pred (ForcingPairUnion.domain rho G F) (fun j => up4 (base j)) 0))
      (.imp (ForcingPersistentWorks.works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) (fun j => up4 (base j)) (fun j => up4 (base (rho j))) (up4 (base I)) (up4 (base G)) (up4 (base F)) (up4 (base mul)) (up4 (base q)) (up4 (base bound)) (up4 (base labels)) (up4 (base E)) (up4 (base root)) (up4 (base w)) (up4 (base chain)) 3 1)
      (.imp (ForcingCodeLinks.links (orderFormula (rho 0) mul) (fun j => up4 (base j)) (up4 (base (rho 6))) (up4 (base w)) (up4 (base (rho 0))) (up4 (base I)) (up4 (base mul)) (up4 (base q)) (up4 (base chain)) 3 2 0 1)
      (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition (up6 (base (rho 2))) (up6 (base w)) 1))
      (.conj (Project.Formula.subset (.bound 5) (.bound 1))
      (ForcingGermPreliminary.preliminaryAt rho I G F mul q bound labels E root w chain codes order ranks selection top labelSet r (fun j => up6 (base j)) (up6 rankBound) (up6 tab) 1 4 0 2))))))))))))))))

theorem dense_freeClosed {k n : Nat} (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order ranks selection top labelSet r : Fin k) (base : Fin k → Fin n) (rankBound tab delta : Fin n) :
    (dense rho I G F mul q bound labels E root w chain codes order ranks selection top labelSet r base rankBound tab delta).FreeClosed := by
  simp -implicitDefEqProofs [dense,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionComponentCofinal.encodedCommon_freeClosed,ForcingTailCodes.entry_freeClosed,
    ForcingPersistentWorks.works_freeClosed,ForcingCodeLinks.links_freeClosed,ForcingGermPreliminary.preliminaryAt_freeClosed]

theorem dense_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order ranks selection top labelSet r : Fin k) (base : Fin k → Fin n) (rankBound tab delta : Fin n) :
    Project.Formula.satisfies env (dense rho I G F mul q bound labels E root w chain codes order ranks selection top labelSet r base rankBound tab delta) ↔
      Dense hM (fun j => env.bound (base j)) rho I G F mul q bound labels E root w chain codes order ranks selection top labelSet r (env.bound rankBound) (env.bound tab) (env.bound delta) := by
  simp only [dense,Dense,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingCohenConditions.condition_semantics (M := M),
    ConstructionComponentCofinal.encodedCommon_semantics hM,ForcingTailCodes.entry_semantics hM,
    ForcingClassEvaluation.predicate_semantics (M := M),ForcingPersistentWorks.works_semantics hM,
    ForcingCodeLinks.links_semantics hM,ForcingGermPreliminary.preliminaryAt_semantics hM]
  rfl

theorem source_construct (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {k : Nat}
    (env : Fin k → M.Carrier .set)
    (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p b t Ap Hp XP ordinal enum list delta zero root vertices chain names Ar Hr codes order ranks selection group P Power continuum coordS localS labelSet s j sigma d z : Fin k)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hq : Injection (env (rho 0)) (env I) (env q))
    (hAq : ForcingSupportedNames.Range (env (rho 0)) (env q) (env Aq))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env Aq) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hrI : Injection (env (rho 0)) (env I) (env r))
    (hpI : Injection (env (rho 0)) (env I) (env p))
    (hAp : ForcingSupportedNames.Range (env (rho 0)) (env p) (env Ap))
    (hHp : ForcingLabelPermutations.Fixing (env G) (env Ap) (env Hp))
    (hXP : ForcingLocalNames.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env Hp) (env XP))
    (ha : (Project.FirstOrderSemantics.reduct M).mem (env a) (env (rho 0)))
    (hb : (Project.FirstOrderSemantics.reduct M).mem (env b) (env (rho 0)))
    (hae : ForcingDiagramOrder.Product (env mul) (env a) (env mark) (env t))
    (hSuba : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env a) (env q))
    (hSubp : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env t) (env p))
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) (env enum) (env ordinal) (env XP))
    (hList : ForcingCollectedName.Collected ForcingPowerName.trueTest Fin.elim0 (env ordinal) (env enum) (env (rho 6)) (env list))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hzero : ForcingWithTopCarrier.Empty (env zero))
    (hNames : ForcingPowerName.Candidates (fun j => env (rho j)) (env G) (env F) (env bound) (env names))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hRoot : Code (env root) (env r) (env a) (env U))
    (hAr : ForcingSupportedNames.Range (env (rho 0)) (env r) (env Ar))
    (hHr : ForcingLabelPermutations.Fixing (env G) (env Ar) (env Hr))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) (env order) (env codes))
    (hRanks : ForcingOrdinalRanks.Ranks
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env order) (env (rho 6)) (env ranks))
    (hSelection : ForcingCollectedName.Collected
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env ranks) (env (rho 6)) (env selection))
    (hTwo : ∃ o, (Project.FirstOrderSemantics.reduct M).IsOrdinalOne o ∧ (Project.FirstOrderSemantics.reduct M).SuccessorOf (env B) o)
    (hP : ForcingCohenCoordinates.Cartesian (env mu) (env mu) (env P))
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hCard : ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env mul) (env mark) (env mu))
    (hmark : (Project.FirstOrderSemantics.reduct M).mem (env mark) (env (rho 0)))
    (hEHS : ForcingHS.HS ForcingProductFamily.actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
    (hCoord : ForcingCohenCoordinates.Cartesian (env (rho 0)) (env K) (env coordS))
    (hLocal : ForcingCohenCoordinates.Cartesian (env coordS) (env B) (env localS))
    (hK : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) (env K) (env mu))
    (hParameters : ConstructionConcreteCardinals.Parameters hM (env w) (env Power) (env continuum) (env mu))
    (hLabelCard : (Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) (env labelSet) (env mu))
    (hAllIdeals : ConstructionIdealProbes.AllIdeals (env mu) (env history) (env kappa))
    (hbNe : env b ≠ env one)
    (hEf : ForcingSupportedNames.Supported (fun i => env (rho i)) (env Hp) (env E))
    (hs : Injection (env (rho 0)) (env I) (env s))
    (hSub : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env s) (env b) (env p))
    (hd : ForcingCohenConditions.Condition (env (rho 2)) (env w) (env d))
    (hSupp : ForcingLocalRecordPullback.Supported (env (rho 0)) (env s) (env d))
    (hRestr : ConstructionCohenCompatibility.Restricted (env Ap) (env d) (env delta))
    (hz : ForcingSupportingRoot.Code (env z) (env d) (env s))
    (hj : ConstructionPlacementTriple.ImageAt (env s) (env (rho 0)) (env j))
    (hSigma : ForcingRelationClassMove.Value (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun i => env (rho i))
      (env G) (env F) (env I) (env K) (env labelMap) (env top) (env bit) (env labels) (env E) (env j) (env sigma))
    (hOut : ForcingOutsideLocal.Outside (orderFormula (rho 0) mul) env (env (rho 6)) (env z) (env sigma) (env list))
    (hBound : ForcingSupportedNames.Supported (fun j => env (rho j)) (env G) (env bound))
    (hTail : ForcingTailGroup.TailGroup (env w) (env (rho 0)) (env G) (env chain) (env group)) :
    ∃ rankBound tab, ForcingRawRank.Rank (env selection) rankBound ∧
      ForcingOrdinalTable.Table hM (env labelSet) rankBound tab ∧
      ForcingOrdinalFixed.Fixed (fun j => env (rho j)) (env G) (env F) (env group) (env selection) ∧
      Dense hM env rho I G F mul q bound labels E root w chain codes order ranks selection top labelSet r rankBound tab (env delta) := by
  have hSmallW := (ForcingSupportSize.native_small hM _ _).mpr hMu.2
  have hIncl := ForcingTailGroup.root_le_tailGroup hChain hRoot hAr hHr hTail
  have hSubgroup := ForcingTailGroup.subgroup hM hw hChain hRoot hAr hG hTail
  obtain ⟨Ar',hAr',hArI,hArSmall⟩ := ConstructionDescentPlacement.diagram_range hM hMu.1.1 hrI hSmall
  have hArEq := ForcingCohenOrderAction.image_unique hM hAr hAr'
  subst Ar'
  have hMember := (hF (env group)).mpr ⟨hSubgroup,env Ar,env Hr,hArI,hArSmall,hHr,hIncl⟩
  let R := ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order
  let L := ForcingCohenSelection.liftRelation R id (rho 0) I (rho 2) w
  have hCov := ForcingCodeRanks.covariant hM hChoice env rho
    I K B w G F mul one mu history kappa mark H C incoming base q Aq Hq labelMap top bit labels E bound zero root vertices chain names codes order (env group)
    hm hJ hp hG hF hw hMu hI hSmall hSmallW hMergers hRow hLabelMap hTop hLabels hLabelBound hBound hq hAq hHq hE hChain hCarrier hTail
  have hInvariant := ForcingCohenSelection.lift_invariant hM R id env rho I w hp hCov
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hFamily := ForcingOrdinalFixed.ranks_fixed hM L env (fun j => env (rho j)) hp hG hNormal hSubgroup hMember hInvariant hOrder hRanks
  have hType := ForcingOrdinalFixed.collected_fixed hM L env (fun j => env (rho j)) hp hG hNormal hSubgroup hMember hFamily hInvariant hSelection
  have hCount := ForcingIdealProbeCount.source_construct hM hChoice env rho
    w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p b t Ap Hp XP ordinal enum list delta zero root vertices chain names Ar Hr codes order ranks selection group P Power continuum coordS localS labelSet s j sigma d z
    hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hrI hpI hAp hHp hXP ha hb hae hSuba hSubp hEnum hList hJ hzero hNames hChain hRoot hAr hHr hCarrier hOrder hRanks hSelection hFamily hIncl hTwo hP hVertices hCard hmark hEHS hCoord hLocal hK hParameters hLabelCard hAllIdeals hbNe hEf hs hSub hd hSupp hRestr hz hj hSigma hOut
  obtain ⟨rankBound,hRank⟩ := ForcingRawRank.exists_rank hM (env selection)
  obtain ⟨tab,hTable⟩ := ForcingOrdinalTable.chooseTable hM hChoice (env labelSet) rankBound
    (ForcingGermDensity.ordinal_native (ForcingRawRank.rank_spec.mp hRank).1.1)
  refine ⟨rankBound,tab,hRank,hTable,hType,?_,?_⟩
  · intro f vertex label hf hdf hCommon hLabel
    exact ForcingGermDensity.total_at hM hChoice env rho
      w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names codes order ranks selection group r a U Ar Hr labelSet
      rankBound tab vertex label f
      hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hVertices hChain hCarrier hRoot hAr hHr hIncl hOrder hRanks hSelection hFamily hType hRank hTable hf hCommon hLabel
      (fun g hg hfg => hCount g hg (fun x hx => hfg x (hdf x hx)))
  · intro f vertex code tau hf hdf hCode hHS hWorks hLinks
    exact ForcingGermDensity.onto_at hM hChoice env rho
      w mu history kappa one mark H C incoming base I K B G F mul top labels bound E q zero root vertices chain names codes order ranks selection group r a U Ar Hr labelSet
      rankBound tab vertex f code tau
      hw hMu hI hSmall hMergers hRow hm hp hG hF hTop hChain hCarrier hRoot hAr hHr hIncl hOrder hRanks hSelection hFamily hType hRank hTable hf hCode hHS hWorks hLinks
      (fun g hg hfg => hCount g hg (fun x hx => hfg x (hdf x hx)))

def sourceSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p b t Ap Hp XP ordinal enum list delta zero root vertices chain names Ar Hr codes order ranks selection group P Power continuum coordS localS labelSet s j sigma d z : Fin k) : Project.Sentence where
  formula :=
    let R := ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order
    let L := ForcingCohenSelection.liftRelation R id (rho 0) I (rho 2) w
    Project.Formula.forallClosure k
    (.imp (Project.Formula.isOmega (.bound w))
      (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
      (.imp (ConstructionSaturationIndex.hartogs mu I)
      (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
      (.imp (ConstructionSaturationMergers.allMergers w history kappa)
      (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul one mark H C incoming base kappa)
      (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
      (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
      (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
      (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn labelMap K))
      (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
      (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K labelMap top bit labels))
      (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K labelMap top bit bound))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
      (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q Aq))
      (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Aq Hq))
      (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq E))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection r (rho 0) I))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection p (rho 0) I))
      (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) p Ap))
      (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Ap Hp))
      (.imp (ProjectSyntax.encode id (ForcingLocalNames.carrier rho G F bound Hp XP))
      (.imp (.mem (.bound a) (.bound (rho 0)))
      (.imp (.mem (.bound b) (.bound (rho 0)))
      (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product mul a mark t))
      (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul r a q))
      (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul r t p))
      (.imp (Project.Formula.isBijectionFromTo PureKuratowskiProject.convention (.bound enum) (.bound ordinal) (.bound XP))
      (.imp (ProjectSyntax.encode id (ForcingCollectedName.collected ForcingPowerName.trueTest Fin.elim0 ordinal enum (rho 6) list))
      (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
      (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty zero))
      (.imp (ForcingTailCodes.candidates rho G F bound names)
      (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
      (.imp (ConstructionComponentCarrier.code root r a U)
      (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) r Ar))
      (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Ar Hr))
      (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
      (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound codes))
      (.imp (ProjectSyntax.encode id (ForcingOrdinalRanks.ranks L id codes order (rho 6) ranks))
      (.imp (ProjectSyntax.encode id (ForcingCollectedName.collected L id codes ranks (rho 6) selection))
      (.imp (ForcingProductParameters.two B)
      (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian mu mu P))
      (.imp (ConstructionComponentCarrier.carrier (rho 0) I mul q vertices)
      (.imp (ConstructionSaturationCardinals.cardinalsF (rho 0) mul mark mu)
      (.imp (.mem (.bound mark) (.bound (rho 0)))
      (.imp (ProjectSyntax.encode id (ForcingHS.hs ForcingProductFamily.actionFormula rho G (rho 6) F E))
      (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (rho 0) K coordS))
      (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian coordS B localS))
      (.imp (Project.Formula.cardinalLessOrEqual PureKuratowskiProject.convention (.bound K) (.bound mu))
      (.imp (ConstructionConcreteCardinals.parameters w Power continuum mu)
      (.imp (Project.Formula.equinumerous PureKuratowskiProject.convention (.bound labelSet) (.bound mu))
      (.imp (ConstructionIdealProbes.allIdeals mu history kappa)
      (.imp (.neg (Project.Formula.extensionalEq (.bound b) (.bound one)))
      (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hp E))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection s (rho 0) I))
      (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul s b p))
      (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d))
      (.imp (ForcingLocalRecordPullback.supported (rho 0) s d)
      (.imp (ConstructionCohenCompatibility.restricted Ap d delta)
      (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z d s))
      (.imp (ConstructionPlacementTriple.imageAt s (rho 0) j)
      (.imp (ProjectSyntax.encode id (ForcingRelationClassMove.value (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F I K labelMap top bit labels E j sigma))
      (.imp (ProjectSyntax.encode id (ForcingOutsideLocal.outside (orderFormula (rho 0) mul) id (rho 6) z sigma list))
      (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho G bound))
      (.imp (ForcingTailGroup.tailGroup w (rho 0) G chain group)
      (.existsE (.existsE (.conj (ProjectSyntax.encode id (LayerRankSyntax.rank selection.succ.succ 1))
      (.conj (ForcingOrdinalTable.table labelSet.succ.succ 1 0)
      (.conj (ProjectSyntax.encode id (ForcingOrdinalFixed.fixed (fun j => (rho j).succ.succ) G.succ.succ F.succ.succ group.succ.succ selection.succ.succ))
      (dense rho I G F mul q bound labels E root w chain codes order ranks selection top labelSet r (fun j => j.succ.succ) 1 0 delta.succ.succ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ForcingTailCodes.candidates_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,
      ForcingTailCodes.carrier_freeClosed,Project.Formula.isSetCodedWellOrder_freeClosed,
      
      ForcingProductParameters.two_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,ConstructionSaturationCardinals.cardinalsF_freeClosed,
      ConstructionConcreteCardinals.parameters_freeClosed,ConstructionIdealProbes.allIdeals_freeClosed,
      Project.Formula.extensionalEq,ForcingLocalRecordPullback.supported_freeClosed,
      ConstructionCohenCompatibility.restricted_freeClosed,ConstructionPlacementTriple.imageAt_freeClosed,ForcingTailGroup.tailGroup_freeClosed,
      ForcingOrdinalTable.table_freeClosed,dense_freeClosed]

theorem source_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p b t Ap Hp XP ordinal enum list delta zero root vertices chain names Ar Hr codes order ranks selection group P Power continuum coordS localS labelSet s j sigma d z : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p b t Ap Hp XP ordinal enum list delta zero root vertices chain names Ar Hr codes order ranks selection group P Power continuum coordS localS labelSet s j sigma d z)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,ForcingSupportSize.small_semantics (M := M),
    ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ForcingTailCodes.candidates_semantics hM,
    ConstructionComponentCofinal.chain_semantics hM,ConstructionComponentCarrier.code_semantics hM,
    ForcingLocalNames.carrier_semantics (M := M),
    ForcingDiagramOrder.product_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    Project.Formula.satisfies_isBijectionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ForcingCollectedName.collected_semantics (M := M),
    ForcingTailCodes.carrier_semantics hM,Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),
    ForcingOrdinalRanks.ranks_semantics (M := M),
    
    ForcingCohenCoordinates.cartesian_semantics (M := M),
    ForcingProductParameters.two_semantics (M := M),
    ConstructionComponentCarrier.carrier_semantics hM,ConstructionSaturationCardinals.cardinalsF_semantics hM,
    ForcingHS.hs_semantics (M := M),ConstructionConcreteCardinals.parameters_semantics hM,
    Project.Formula.satisfies_cardinalLessOrEqual_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_equinumerous_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    
    ConstructionIdealProbes.allIdeals_semantics hM,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    ForcingCohenConditions.condition_semantics (M := M),ForcingLocalRecordPullback.supported_semantics hM,
    ConstructionCohenCompatibility.restricted_semantics hM,ForcingSupportingRoot.code_semantics (M := M),
    ConstructionPlacementTriple.imageAt_semantics hM,ForcingRelationClassMove.value_semantics (M := M),
    ForcingOutsideLocal.outside_semantics (M := M),ForcingTailGroup.tailGroup_semantics hM,
    ForcingRawRank.rank_semantics (M := M),ForcingOrdinalTable.table_semantics hM,
    ForcingOrdinalFixed.fixed_semantics (M := M),dense_semantics hM]
  exact source_construct hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p b t Ap Hp XP ordinal enum list delta zero root vertices chain names Ar Hr codes order ranks selection group P Power continuum coordS localS labelSet s j sigma d z

theorem source_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p b t Ap Hp XP ordinal enum list delta zero root vertices chain names Ar Hr codes order ranks selection group P Power continuum coordS localS labelSet s j sigma d z : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p b t Ap Hp XP ordinal enum list delta zero root vertices chain names Ar Hr codes order ranks selection group P Power continuum coordS localS labelSet s j sigma d z))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let witness := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    {bound := Fin.elim0,free := fun _ => witness}
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p b t Ap Hp XP ordinal enum list delta zero root vertices chain names Ar Hr codes order ranks selection group P Power continuum coordS localS labelSet s j sigma d z)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p b t Ap Hp XP ordinal enum list delta zero root vertices chain names Ar Hr codes order ranks selection group P Power continuum coordS localS labelSet s j sigma d z)).mp
      (source_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p b t Ap Hp XP ordinal enum list delta zero root vertices chain names Ar Hr codes order ranks selection group P Power continuum coordS localS labelSet s j sigma d z hL hChoice)

end PPAC.Migration.ForcingConcreteGermDensity
