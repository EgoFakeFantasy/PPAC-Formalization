/- Pinned GermSelectors.OrdinalCount:161 and preliminary_total:167–179.
The same actual Selected relation, rank history/type and fixed ordinal table
are consumed. The exact count premise remains conditional until CodeCardinals.
No external standardness bound is imposed on ordinals or Cohen conditions. -/
import PPAC.Migration.ForcingGermPreliminary

namespace PPAC.Migration.ForcingGermDensity
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingProductSymmetry (orderFormula)
open ForcingPrincipalFilter (EqF)
open ForcingGermPreliminary (Preliminary)
open ForcingCheckName (Checked)
open ForcingSupportSize (Injection)
open ConstructionComponentCofinal (Chain EncodedCommon)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def OrdinalCount (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (mul w top selection r labelSet : Fin k) (d : M.Carrier .set) : Prop :=
  ∀ e, ForcingCohenConditions.Condition (env (rho 2)) (env w) e →
    ForcingPowerName.Subset d e → ∀ theta ntheta,
      ForcingRawRank.Ordinal theta → Checked (env top) theta ntheta →
      EqF (orderFormula (rho 0) mul) env (env (rho 6)) e (env r) (env selection) ntheta →
      (Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) (env labelSet) theta

def ordinalCount {k m : Nat} (rho : Fin 7 → Fin k)
    (mul w top selection r labelSet : Fin k) (base : Fin k → Fin m) (d : Fin m) : Project.Formula 1 m :=
  let up : Fin m → Fin (m+3) := fun i => i.succ.succ.succ
  .forallE (.forallE (.forallE
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (up (base (rho 2))) (up (base w)) 2))
    (.imp (Project.Formula.subset (.bound (up d)) (.bound 2))
    (.imp (ProjectSyntax.encode id (OrdinalSyntax.ordinal 1))
    (.imp (ProjectSyntax.encode id (ForcingCheckName.checkName (up (base top)) 1 0))
    (.imp (ForcingPrincipalFilter.eqF (orderFormula (rho 0) mul) (fun i => up (base i)) (up (base (rho 6))) 2 (up (base r)) (up (base selection)) 0)
      (Project.Formula.equinumerous PureKuratowskiProject.convention (.bound (up (base labelSet))) (.bound 1)))))))))

theorem ordinalCount_freeClosed {k m : Nat} (rho : Fin 7 → Fin k)
    (mul w top selection r labelSet : Fin k) (base : Fin k → Fin m) (d : Fin m) :
    (ordinalCount rho mul w top selection r labelSet base d).FreeClosed := by
  simp -implicitDefEqProofs [ordinalCount,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ForcingPrincipalFilter.eqF_freeClosed]

theorem ordinalCount_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (rho : Fin 7 → Fin k)
    (mul w top selection r labelSet : Fin k) (base : Fin k → Fin m) (d : Fin m) :
    Project.Formula.satisfies env (ordinalCount rho mul w top selection r labelSet base d) ↔
      OrdinalCount hM (fun i => env.bound (base i)) rho mul w top selection r labelSet (env.bound d) := by
  simp only [ordinalCount,OrdinalCount,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_subset_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenConditions.condition_semantics (M := M),ForcingRawRank.ordinal_semantics (M := M),
    ForcingCheckName.checkName_semantics (M := M),ForcingPrincipalFilter.eqF_semantics hM,
    Project.Formula.satisfies_equinumerous_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  constructor
  · intro h e he hde theta ntheta ht hn hf
    exact h e theta ntheta he hde ht hn hf
  · intro h e theta ntheta he hde ht hn hf
    exact h e he hde theta ntheta ht hn hf

private theorem ordinal_native {theta : M.Carrier .set} (h : ForcingRawRank.Ordinal theta) :
    (Project.FirstOrderSemantics.reduct M).IsOrdinal theta := by
  simp only [ForcingRawRank.Ordinal,OrdinalSyntax.ordinal,OrdinalSyntax.transitiveSet,
    OrdinalSyntax.linear,OrdinalSyntax.irreflexive,OrdinalSyntax.membershipTransitive,
    OrdinalSyntax.comparable,OrdinalSyntax.wellFounded,OrdinalSyntax.minimalExists,
    OrdinalSyntax.setMinimal,RestrictionSyntax.subset,MinimalPredicates.inhabited,
    Source.Formula.Realize,Source.Formula.neg,Fin.lastCases_last,Fin.lastCases_castSucc] at h
  obtain ⟨ht,⟨hi,htr,hcmp⟩,hleast⟩ := h
  refine ⟨(fun x hx y hy => ht x y hx hy),⟨⟨hi,fun x hx y hy z hz hxy hyz => htr x y z hx hy hz ⟨hxy,hyz⟩,?_⟩,?_⟩⟩
  · intro x hx y hy
    rcases hcmp x y hx hy with he | hxy | hyx
    · exact Or.inl (he ▸ fun _ => Iff.rfl)
    · exact Or.inr (Or.inl hxy)
    · exact Or.inr (Or.inr hyx)
  · intro b hb hne
    obtain ⟨x,hx,hmin⟩ := hleast b ⟨hb,hne⟩
    refine ⟨x,hx,?_⟩
    intro y hy
    rcases hcmp x y (hb x hx) (hb y hy) with he | hxy | hyx
    · exact Or.inl (he ▸ fun _ => Iff.rfl)
    · exact Or.inr hxy
    · exact False.elim (hmin y hy hyx)

theorem preliminary_total (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d : Fin k)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G)) (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hq : Injection (env (rho 0)) (env I) (env q))
    (hAq : ForcingSupportedNames.Range (env (rho 0)) (env q) (env Aq))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env Aq) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hRoot : ConstructionComponentCarrier.Code (env root) (env r) (env rootIndex) (env rootU))
    (hRootA : ForcingStabilizerTransport.Image (env r) (env (rho 0)) (env rootA))
    (hRootH : ForcingLabelPermutations.Fixing (env G) (env rootA) (env rootH))
    (hIncl : (Project.FirstOrderSemantics.reduct M).MemberSubset (env rootH) (env group))
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) (env order) (env codes))
    (hRanks : ForcingOrdinalRanks.Ranks
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env order) (env (rho 6)) (env ranks))
    (hSelection : ForcingCollectedName.Collected
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env ranks) (env (rho 6)) (env selection))
    (hFamily : ForcingOrdinalFixed.FixedFamily (fun j => env (rho j)) (env G) (env F) (env group) (env codes) (env ranks))
    (hType : ForcingOrdinalFixed.Fixed (fun j => env (rho j)) (env G) (env F) (env group) (env selection))
    (hRank : ForcingRawRank.Rank (env selection) (env rankBound))
    (hTable : ForcingOrdinalTable.Table hM (env labelSet) (env rankBound) (env tab))
    (hd : ForcingCohenConditions.Condition (env (rho 2)) (env w) (env d))
    (hCommon : EncodedCommon (env (rho 0)) (env I) (env mul) (env q) (env root) (env vertex))
    (hj : (Project.FirstOrderSemantics.reduct M).mem (env label) (env labelSet))
    (hCount : OrdinalCount hM env rho mul w top selection r labelSet (env d)) :
    ∃ e tau, ForcingCohenConditions.Condition (env (rho 2)) (env w) e ∧
      ForcingPowerName.Subset (env d) e ∧
      ForcingTailCodes.Entry (fun j => env (rho j)) (env G) (env F) (env bound) (env vertex) tau ∧
      Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r e (env vertex) (env label) tau := by
  let R := ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order
  have hr := (ForcingTailGroup.root_vertex hChain hRoot).1
  obtain ⟨z,hz⟩ := ForcingSupportingRoot.exists_code hM (env d) (env r)
  obtain ⟨rank,hrank,e,ze,theta,ntheta,he,hde,hze,htheta,hbound,hntheta,hForce⟩ :=
    ForcingCohenRankConsumers.orderType_decide hM hChoice env rho G F mul I w R id
      hw hMu hI hSmall hMergers hRow hm hp hG hF hr hRootA hRootH hTop hOrder hRanks hSelection hType hIncl hd hz
  have heq := ForcingRawRank.unique_rank hM hrank hRank
  have hbound' : theta = env rankBound ∨ (Project.FirstOrderSemantics.reduct M).mem theta (env rankBound) := heq ▸ hbound
  have hEq : EqF (orderFormula (rho 0) mul) env (env (rho 6)) e (env r) (env selection) ntheta := ⟨ze,hze,hForce⟩
  have hElig : ForcingOrdinalTable.Eligible hM (env labelSet) (env rankBound) theta :=
    ⟨ordinal_native htheta,hbound',hCount e he hde theta ntheta htheta hntheta hEq⟩
  obtain ⟨f,hBij,hIndices⟩ := ForcingOrdinalTable.indices_bijection hM hTable hElig
  obtain ⟨beta,hbeta,hjbeta⟩ := hBij.1.1.2.2 (env label) hj
  obtain ⟨nbeta,hnbeta⟩ := ForcingCheckName.exists_checked hM (env top) beta
  obtain ⟨g,zg,a,na,hg,heg,hzg,ha,han,hRa,hRankEq⟩ :=
    ForcingCohenRankConsumers.member_rank hM hChoice env rho G F mul I w R id
      hw hMu hI hSmall hMergers hRow hm hp hG hF hr hRootA hRootH hTop hSelection hFamily hIncl
      (ForcingCodeSelection.monotone hM env rho I G F mul q bound labels E root w chain codes order) he hze hntheta hnbeta hbeta hForce
  have hSel := (ForcingCodeSelection.mapRel_relation hM env rho I G F mul q bound labels E root w chain codes order a g).mp hRa
  have hgP := (hp.2.2.1 g).mpr hg
  obtain ⟨tau,hEntry,hLinks⟩ := ForcingCodeLinkClosure.working_linked_over hM hChoice env rho
    w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex g a
    hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hVertices hChain
    hgP ((hCarrier a).mp ha) hSel.1 hCommon
  have hHS : ForcingClassEvaluation.Predicate (ForcingPairUnion.domain rho G F) env tau := by
    obtain ⟨_,_,_,_,_,_,_,_,hLocal⟩ := hEntry
    exact (ForcingPairUnion.domain_semantics env rho G F tau).mpr hLocal.1.1
  exact ⟨g,tau,hg,(fun x hx => heg x (hde x hx)),hEntry,
    hj,hHS,theta,a,na,ntheta,beta,nbeta,hElig,ha,han,(hIndices (env label) beta).mpr hjbeta,hntheta,hnbeta,hSel,
    ForcingPrincipalFilter.eqF_mono hM env rho mul hm hp hgP hr heg hEq,⟨zg,hzg,hRankEq⟩,hLinks⟩

def totalSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d : Fin k) : Project.Sentence where
  formula :=
    let R := ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order
    let L := ForcingCohenSelection.liftRelation R id (rho 0) I (rho 2) w
    Project.Formula.forallClosure k (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul one mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
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
    (.imp (ConstructionComponentCarrier.carrier (rho 0) I mul q vertices)
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
    (.imp (ConstructionComponentCarrier.code root r rootIndex rootU)
    (.imp (ProjectSyntax.encode id (ForcingStabilizerTransport.image r (rho 0) rootA))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G rootA rootH))
    (.imp (Project.Formula.subset (.bound rootH) (.bound group))
    (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound codes))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalRanks.ranks L id codes order (rho 6) ranks))
    (.imp (ProjectSyntax.encode id (ForcingCollectedName.collected L id codes ranks (rho 6) selection))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixedFamily rho G F group codes ranks))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixed rho G F group selection))
    (.imp (ProjectSyntax.encode id (LayerRankSyntax.rank selection rankBound))
    (.imp (ForcingOrdinalTable.table labelSet rankBound tab)
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d))
    (.imp (ConstructionComponentCofinal.encodedCommon (rho 0) I mul q root vertex)
    (.imp (.mem (.bound label) (.bound labelSet))
    (.imp (ordinalCount rho mul w top selection r labelSet id d)
    (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2).succ.succ w.succ.succ 1))
      (.conj (Project.Formula.subset (.bound d.succ.succ) (.bound 1))
      (.conj (ForcingTailCodes.entry (fun j => (rho j).succ.succ) G.succ.succ F.succ.succ bound.succ.succ vertex.succ.succ 0)
      (ForcingGermPreliminary.preliminary rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r (fun j => j.succ.succ) 1 vertex.succ.succ label.succ.succ 0)))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ConstructionComponentCofinal.encodedCommon_freeClosed,ConstructionComponentCarrier.code_freeClosed,
      ForcingTailCodes.carrier_freeClosed,ForcingTailCodes.entry_freeClosed,
      ForcingOrdinalTable.table_freeClosed,ForcingGermPreliminary.preliminary_freeClosed,
      ordinalCount_freeClosed,Project.Formula.isSetCodedWellOrder_freeClosed]

theorem total_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (totalSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,
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
    ForcingSupportedNames.supported_semantics (M := M),ConstructionComponentCarrier.carrier_semantics hM,
    ConstructionComponentCofinal.chain_semantics hM,ConstructionComponentCofinal.encodedCommon_semantics hM,
    ForcingTailCodes.entry_semantics hM,
    ForcingTailCodes.carrier_semantics hM,ConstructionComponentCarrier.code_semantics hM,
    ForcingStabilizerTransport.image_semantics (M := M),Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),
    ForcingOrdinalRanks.ranks_semantics (M := M),ForcingCollectedName.collected_semantics (M := M),
    ForcingOrdinalFixed.fixedFamily_semantics (M := M),ForcingOrdinalFixed.fixed_semantics (M := M),
    ForcingRawRank.rank_semantics (M := M),ForcingOrdinalTable.table_semantics hM,
    ForcingCohenConditions.condition_semantics (M := M),ordinalCount_semantics hM,
    ForcingGermPreliminary.preliminary_semantics hM]
  exact preliminary_total hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d

theorem total_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (totalSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d))) := by
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
  apply ConstructibleGround.relative_models hM (totalSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (totalSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d)).mp
      (total_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d hL hChoice)


theorem existing_dense_selected (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w one G F mul q bound labels E root zero vertices chain names codes order : Fin k) (d a : M.Carrier .set)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) (env order) (env codes))
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3)))
    (ha : (Project.FirstOrderSemantics.reduct M).mem a (env codes))
    (hWorks : ForcingPersistentWorks.Works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env I) (env G) (env F) (env mul) (env q) (env bound) (env labels) (env E) (env root) (env w) (env chain) d a) :
    ∃ e, (Project.FirstOrderSemantics.reduct M).mem e (env (rho 3)) ∧ ForcingPowerName.Subset d e ∧
      ∃ b, (Project.FirstOrderSemantics.reduct M).mem b (env codes) ∧
        ForcingCodeSelection.IsSelected env rho I G F mul q bound labels E root w chain codes order b e ∧
        ForcingPersistentCodes.Same (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env chain) e a b := by
  have hAll := ForcingPersistentWorks.selection_models rho I K B w one G F mul q bound labels E root zero vertices chain names codes order hM
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff] at hAll
  have h := (Project.Formula.satisfies_forallClosure_iff (ℳ := Project.FirstOrderSemantics.reduct M) (fun _ => d) _).mp (hAll (fun _ => d)) env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ConstructionComponentCofinal.chain_semantics hM,ForcingTailCodes.carrier_semantics hM] at h
  have supplied := h hm hp hw hChain hCarrier hOrder
  simp only [ForcingPersistentSelection.conclusion,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ForcingPersistentSelection.rel2_semantics,ForcingPersistentSelection.rel3_semantics,
    ForcingPersistentSelection.selected_semantics hM] at supplied
  have dense := supplied.2.2 d a hd ha
  simp only [ForcingPersistentSelection.Selected,ForcingPersistentWorks.lower_semantics,
    ForcingPersistentWorks.working_semantics hM,ForcingPersistentWorks.equalAt_semantics hM] at dense
  exact dense hWorks

theorem preliminary_onto (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul top labels bound E q zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab d a tau : Fin k)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G)) (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hRoot : ConstructionComponentCarrier.Code (env root) (env r) (env rootIndex) (env rootU))
    (hRootA : ForcingStabilizerTransport.Image (env r) (env (rho 0)) (env rootA))
    (hRootH : ForcingLabelPermutations.Fixing (env G) (env rootA) (env rootH))
    (hIncl : (Project.FirstOrderSemantics.reduct M).MemberSubset (env rootH) (env group))
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) (env order) (env codes))
    (hRanks : ForcingOrdinalRanks.Ranks
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env order) (env (rho 6)) (env ranks))
    (hSelection : ForcingCollectedName.Collected
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env ranks) (env (rho 6)) (env selection))
    (hFamily : ForcingOrdinalFixed.FixedFamily (fun j => env (rho j)) (env G) (env F) (env group) (env codes) (env ranks))
    (hType : ForcingOrdinalFixed.Fixed (fun j => env (rho j)) (env G) (env F) (env group) (env selection))
    (hRank : ForcingRawRank.Rank (env selection) (env rankBound))
    (hTable : ForcingOrdinalTable.Table hM (env labelSet) (env rankBound) (env tab))
    (hd : ForcingCohenConditions.Condition (env (rho 2)) (env w) (env d))
    (ha : (Project.FirstOrderSemantics.reduct M).mem (env a) (env codes))
    (hHS : ForcingClassEvaluation.Predicate (ForcingPairUnion.domain rho G F) env (env tau))
    (hWorks : ForcingPersistentWorks.Works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env I) (env G) (env F) (env mul) (env q) (env bound) (env labels) (env E) (env root) (env w) (env chain) (env d) (env a))
    (hLinks : ForcingCodeLinks.Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) (env d) (env vertex) (env tau) (env a))
    (hCount : OrdinalCount hM env rho mul w top selection r labelSet (env d)) :
    ∃ e label, ForcingCohenConditions.Condition (env (rho 2)) (env w) e ∧
      ForcingPowerName.Subset (env d) e ∧
      Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r e (env vertex) label (env tau) := by
  let R := ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order
  have hr := (ForcingTailGroup.root_vertex hChain hRoot).1
  have hdP := (hp.2.2.1 (env d)).mpr hd
  obtain ⟨e,heP,hde,b,hb,hSel,hSame⟩ := existing_dense_selected hM env rho
    I K B w one G F mul q bound labels E root zero vertices chain names codes order (env d) (env a) hm hp hw hChain hCarrier hOrder hdP ha hWorks
  have he := (hp.2.2.1 e).mp heP
  have hLinksE := ForcingCodeLinks.links_same hM env rho mul hm hp hw hChain heP ((hCarrier (env a)).mp ha).1
    (ForcingCodeLinks.links_mono hM env rho mul hm hp heP hde hLinks) hSame
  obtain ⟨z,hz⟩ := ForcingSupportingRoot.exists_code hM e (env r)
  obtain ⟨rank,hrank,f,zf,theta,ntheta,hf,hef,hzf,htheta,hbound,hntheta,hForce⟩ :=
    ForcingCohenRankConsumers.orderType_decide hM hChoice env rho G F mul I w R id
      hw hMu hI hSmall hMergers hRow hm hp hG hF hr hRootA hRootH hTop hOrder hRanks hSelection hType hIncl he hz
  have heq := ForcingRawRank.unique_rank hM hrank hRank
  have hbound' : theta = env rankBound ∨ (Project.FirstOrderSemantics.reduct M).mem theta (env rankBound) := heq ▸ hbound
  have hEq : EqF (orderFormula (rho 0) mul) env (env (rho 6)) f (env r) (env selection) ntheta := ⟨zf,hzf,hForce⟩
  have hElig : ForcingOrdinalTable.Eligible hM (env labelSet) (env rankBound) theta :=
    ⟨ordinal_native htheta,hbound',hCount f hf (fun x hx => hef x (hde x hx)) theta ntheta htheta hntheta hEq⟩
  have hSelF := ForcingCodeSelection.isSelected_mono hef hSel
  obtain ⟨nb,hnb,_⟩ := hRanks.1.2 b hb
  have hRb := (ForcingCodeSelection.mapRel_relation hM env rho I G F mul q bound labels E root w chain codes order b f).mpr hSelF
  obtain ⟨g,zg,beta,nbeta,hg,hfg,hzg,_,hbeta,hnbeta,hRankEq⟩ :=
    ForcingCohenRankConsumers.rank_decide hM hChoice env rho G F mul I w R id
      hw hMu hI hSmall hMergers hRow hm hp hG hF hr hRootA hRootH hTop hOrder hRanks hSelection hFamily hIncl
      hf hzf hb hnb hRb hntheta hForce
  obtain ⟨table,hBij,hIndices⟩ := ForcingOrdinalTable.indices_bijection hM hTable hElig
  obtain ⟨label,hlabel,hIndex⟩ := hBij.2 beta hbeta
  have hgP := (hp.2.2.1 g).mpr hg
  exact ⟨g,label,hg,(fun x hx => hfg x (hef x (hde x hx))),
    hlabel,hHS,theta,b,nb,ntheta,beta,nbeta,hElig,hb,hnb,(hIndices label beta).mpr hIndex,hntheta,hnbeta,
    ForcingCodeSelection.isSelected_mono hfg hSelF,
    ForcingPrincipalFilter.eqF_mono hM env rho mul hm hp hgP hr hfg hEq,⟨zg,hzg,hRankEq⟩,
    ForcingCodeLinks.links_mono hM env rho mul hm hp hgP (fun x hx => hfg x (hef x hx)) hLinksE⟩

def ontoSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul top labels bound E q zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab d a tau : Fin k) : Project.Sentence where
  formula :=
    let R := ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order
    let L := ForcingCohenSelection.liftRelation R id (rho 0) I (rho 2) w
    Project.Formula.forallClosure k (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul one mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
    (.imp (ConstructionComponentCarrier.code root r rootIndex rootU)
    (.imp (ProjectSyntax.encode id (ForcingStabilizerTransport.image r (rho 0) rootA))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G rootA rootH))
    (.imp (Project.Formula.subset (.bound rootH) (.bound group))
    (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound codes))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalRanks.ranks L id codes order (rho 6) ranks))
    (.imp (ProjectSyntax.encode id (ForcingCollectedName.collected L id codes ranks (rho 6) selection))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixedFamily rho G F group codes ranks))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixed rho G F group selection))
    (.imp (ProjectSyntax.encode id (LayerRankSyntax.rank selection rankBound))
    (.imp (ForcingOrdinalTable.table labelSet rankBound tab)
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d))
    (.imp (.mem (.bound a) (.bound codes))
    (.imp (ProjectSyntax.encode id (MinimalPredicates.pred (ForcingPairUnion.domain rho G F) id tau))
    (.imp (ForcingPersistentWorks.works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho I G F mul q bound labels E root w chain d a)
    (.imp (ForcingCodeLinks.links (orderFormula (rho 0) mul) id (rho 6) w (rho 0) I mul q chain d vertex tau a)
    (.imp (ordinalCount rho mul w top selection r labelSet id d)
    (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2).succ.succ w.succ.succ 1))
      (.conj (Project.Formula.subset (.bound d.succ.succ) (.bound 1))
      (ForcingGermPreliminary.preliminary rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r (fun j => j.succ.succ) 1 vertex.succ.succ 0 tau.succ.succ)))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,ForcingTailCodes.carrier_freeClosed,
      ForcingPersistentWorks.works_freeClosed,ForcingCodeLinks.links_freeClosed,
      ForcingOrdinalTable.table_freeClosed,ForcingGermPreliminary.preliminary_freeClosed,
      ordinalCount_freeClosed,Project.Formula.isSetCodedWellOrder_freeClosed]

theorem onto_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul top labels bound E q zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab d a tau : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (ontoSentence rho w mu history kappa one mark H C incoming base I K B G F mul top labels bound E q zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab d a tau)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,ForcingSupportSize.small_semantics (M := M),
    ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),

    ForcingLabelPermutations.fixing_semantics (M := M),

    ConstructionComponentCofinal.chain_semantics hM,

    ForcingTailCodes.carrier_semantics hM,ConstructionComponentCarrier.code_semantics hM,
    ForcingStabilizerTransport.image_semantics (M := M),Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),
    ForcingOrdinalRanks.ranks_semantics (M := M),ForcingCollectedName.collected_semantics (M := M),
    ForcingOrdinalFixed.fixedFamily_semantics (M := M),ForcingOrdinalFixed.fixed_semantics (M := M),
    ForcingRawRank.rank_semantics (M := M),ForcingOrdinalTable.table_semantics hM,
    ForcingCohenConditions.condition_semantics (M := M),ordinalCount_semantics hM,
    ForcingGermPreliminary.preliminary_semantics hM,
    ForcingClassEvaluation.predicate_semantics (M := M),ForcingPersistentWorks.works_semantics hM,
    ForcingCodeLinks.links_semantics hM]
  exact preliminary_onto hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul top labels bound E q zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab d a tau

theorem onto_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul top labels bound E q zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab d a tau : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (ontoSentence rho w mu history kappa one mark H C incoming base I K B G F mul top labels bound E q zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab d a tau))) := by
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
  apply ConstructibleGround.relative_models hM (ontoSentence rho w mu history kappa one mark H C incoming base I K B G F mul top labels bound E q zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab d a tau)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (ontoSentence rho w mu history kappa one mark H C incoming base I K B G F mul top labels bound E q zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab d a tau)).mp
      (onto_models rho w mu history kappa one mark H C incoming base I K B G F mul top labels bound E q zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab d a tau hL hChoice)



end PPAC.Migration.ForcingGermDensity
