/- Pinned CodeLinks.links_descend:405 and working_linked:421.
Reuse root reflection and exact glued representatives; keep literal names/codes. -/
import PPAC.Migration.ForcingLinkedWorking

namespace PPAC.Migration.ForcingCodeLinkClosure
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingProductSymmetry (orderFormula)
open ForcingSupportSize (MapsTo Injection)
open ConstructionComponentCarrier (Code)
open ConstructionComponentCofinal (Chain EncodedArrow EncodedCommon)
open ForcingTailCodes (ChainCode At Entry Represents)
open ForcingPrincipalFilter (EqF)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem links_descend (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau a : Fin k)
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
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hd : (Project.FirstOrderSemantics.reduct M).mem (env d) (env (rho 3)))
    (ha : ChainCode (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env a))
    (hEntry : Entry (fun j => env (rho j)) (env G) (env F) (env bound) (env target) (env tau))
    (hArrow : EncodedArrow (env (rho 0)) (env I) (env mul) (env q) (env source) (env target) (env n))
    (hLinks : ForcingCodeLinks.Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) (env d) (env source) (env tau) (env a)) :
    ForcingCodeLinks.Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) (env d) (env target) (env tau) (env a) := by
  have hCommonSource := ForcingCodeLinks.links_common hM env rho mul hw hChain hLinks
  have hCommonTarget := ForcingComponentGluing.common_between hM hm hJ (ForcingComponentRebase.common_symm hCommonSource)
    (ForcingComponentMatches.arrow_common hArrow (ForcingComponentMatches.arrow_id hm (ForcingComponentMatches.arrow_target hArrow)))
  have hArrowCopy := hArrow
  obtain ⟨s,idxS,US,r,idxR,UR,hcs,hct,hvs,hvt,harr⟩ := hArrowCopy
  obtain ⟨L,vL,m,hL,hvL,hFromTarget⟩ := hChain.2.2.2.2 (env target) ((hVertices (env target)).mpr ⟨r,idxR,UR,hct,hvt⟩) hCommonTarget
  obtain ⟨s',idxS',US',hcs',N,hN,hTail⟩ := hLinks
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hcs hcs'
  have hJoin : ∃ J, (Project.FirstOrderSemantics.reduct M).mem J (env w) ∧ ConstructionFractionOrder.NatLe N J ∧ ConstructionFractionOrder.NatLe L J := by
    rcases ConstructionFractionOrder.nat_compare hM hw hN hL with he | hnl | hln
    · exact ⟨L,hL,Or.inl he,Or.inl rfl⟩
    · exact ⟨L,hL,Or.inr hnl,Or.inl rfl⟩
    · exact ⟨N,hN,Or.inl rfl,Or.inr hln⟩
  obtain ⟨J,hJw,hNJ,hLJ⟩ := hJoin
  refine ⟨r,idxR,UR,hct,J,hJw,?_⟩
  intro i hi hJi
  have ord := hw.members_areOrdinals (ModelTransfer.project_models_iff.mp hM) i hi
  obtain ⟨vi,sigma,_,hvi,hsi,_,heq⟩ := hTail i hi (ZF.eqOrMem_trans ord hNJ hJi)
  obtain ⟨l,hIncreasing⟩ := hChain.2.2.1 L i vL vi (ZF.eqOrMem_trans ord hLJ hJi) hvL hvi
  obtain ⟨nm,hComposite⟩ := ForcingComponentMatches.arrow_comp hm hFromTarget hIncreasing
  obtain ⟨vi',hvi',hSigma⟩ := ha.2 i sigma hsi
  have hViEq := ForcingConditionGraphs.function_unique hChain.1.1 hvi hvi'
  subst vi'
  obtain ⟨t,idxT,UT,AT,HT,hci,hAT,hHT,hSigma⟩ := hSigma
  have hCompositeCopy := hComposite
  obtain ⟨r',idxR',UR',t',idxT',UT',hct',hci',_,_,hcmp⟩ := hCompositeCopy
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hct hct'
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hci hci'
  have hEntryCopy := hEntry
  obtain ⟨r',idxR',UR',AR,HR,hct',hAR,hHR,hTau⟩ := hEntryCopy
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hct hct'
  have hRange : ForcingPowerName.Subset AT AR := fun x hx => (hAR x).mpr
    (ConstructionDescentPlacement.range_antitone ⟨nm,hvt.2.2.1 nm hcmp.1,hcmp.2.1⟩ ((hAT x).mp hx))
  have hSigmaFixed := ForcingSupportedNames.supported_mono hHT hHR hRange hSigma.2
  obtain ⟨z,hz,hForce⟩ := heq
  obtain ⟨zr,hzr⟩ := ForcingSupportingRoot.exists_code hM (env d) r
  exact ⟨vi,sigma,nm,hvi,hsi,hComposite,zr,hzr,
    ForcingOrdinalRoot.eq_at_root hM hChoice env rho G F mul hw hMu hI hSmall hMergers hRow hm hp hG hF
      hvt.1 hAR hHR hvs.1 ⟨env n,hvs.2.2.1 (env n) harr.1,harr.2.1⟩ ((hp.2.2.1 (env d)).mp hd) hz hzr hSigmaFixed hTau.2 hForce⟩

theorem working_linked (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d a : Fin k)
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
    (hd : (Project.FirstOrderSemantics.reduct M).mem (env d) (env (rho 3)))
    (_ha : ChainCode (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env a))
    (hWorks : ForcingPersistentWorks.Works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env I) (env G) (env F) (env mul) (env q) (env bound) (env labels) (env E) (env root) (env w) (env chain) (env d) (env a))
    (hCommon : EncodedCommon (env (rho 0)) (env I) (env mul) (env q) (env root) (env vertex)) :
    ∃ tau, Entry (fun j => env (rho j)) (env G) (env F) (env bound) (env vertex) tau ∧
      ForcingCodeLinks.Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) (env d) (env vertex) tau (env a) := by
  obtain ⟨g,oi,objects,S,mi,maps,P,Q,gluePr,b,hg,hBundle,hb,hRep⟩ := hWorks (env d) hd (fun _ h => h)
  obtain ⟨hObjMap,hObj,hS,hMap,hMaps,hP,hGlue,hQ,hProjection⟩ := hBundle
  have hgf := ForcingPrincipalFilter.principal_filter hd hg
  have hSys := ForcingEligibleSystem.system_of_families hM hChoice env rho G F mul
    hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hLabelBound hgf hq hAq hHq hE hObj hS hMaps
  have hCoh := ForcingComponentFibers.coherent_of_system hM hm hJ hp.2.2.2.1 hObjMap hS hMap hSys (q := env q)
  obtain ⟨hAll,hComm⟩ := ForcingComponentGluing.gluing_laws hM hm hJ hp.2.2.2.1 hObjMap hS hMap hSys hP hGlue hQ hProjection
  obtain ⟨tau,hAt⟩ := ForcingTailCodes.at_total hM hp.2.2.2.1 hObjMap hObj hAll hCommon hb
  exact ⟨tau,ForcingTailCodes.at_entry hAt,
    ForcingCodeLinkRepresentation.links_of_represents_at hM (ForcingPairUnion.domain rho G F) env rho mul hm hp
      hp.2.2.2.1 hObjMap hObj hMaps hCoh hAll hComm hw hChain hd hg hVertices hRep hAt⟩

def descentSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau a : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (Project.Formula.isOmega (.bound w))
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
    (.imp (ConstructionComponentCarrier.carrier (rho 0) I mul q vertices)
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (.mem (.bound d) (.bound (rho 3)))
    (.imp (ForcingTailCodes.chainCode rho G F bound w names chain a)
    (.imp (ForcingTailCodes.entry rho G F bound target tau)
    (.imp (ConstructionComponentCofinal.encodedArrow (rho 0) I mul q source target n)
    (.imp (ForcingCodeLinks.links (orderFormula (rho 0) mul) id (rho 6) w (rho 0) I mul q chain d source tau a)
    (ForcingCodeLinks.links (orderFormula (rho 0) mul) id (rho 6) w (rho 0) I mul q chain d target tau a)))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ConstructionComponentCofinal.encodedArrow_freeClosed,
      ForcingTailCodes.chainCode_freeClosed,ForcingTailCodes.entry_freeClosed,
      ForcingCodeLinks.links_freeClosed]

theorem descent_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau a : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (descentSentence rho w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau a)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,ForcingSupportSize.small_semantics (M := M),
    ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),
    
    
    
    ConstructionComponentCarrier.carrier_semantics hM,
    ConstructionComponentCofinal.chain_semantics hM,
    ConstructionComponentCofinal.encodedArrow_semantics hM,ForcingTailCodes.chainCode_semantics hM,
    ForcingTailCodes.entry_semantics hM,ForcingCodeLinks.links_semantics hM]
  exact links_descend hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau a

theorem descent_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau a : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (descentSentence rho w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau a))) := by
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
  apply ConstructibleGround.relative_models hM (descentSentence rho w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau a)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (descentSentence rho w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau a)).mp
      (descent_models rho w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau a hL hChoice)

def workingSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d a : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (Project.Formula.isOmega (.bound w))
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
    (.imp (.mem (.bound d) (.bound (rho 3)))
    (.imp (ForcingTailCodes.chainCode rho G F bound w names chain a)
    (.imp (ForcingPersistentWorks.works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho I G F mul q bound labels E root w chain d a)
    (.imp (ConstructionComponentCofinal.encodedCommon (rho 0) I mul q root vertex)
    (.existsE (.conj (ForcingTailCodes.entry (fun j => (rho j).succ) G.succ F.succ bound.succ vertex.succ 0) (ForcingCodeLinks.links (orderFormula (rho 0) mul) Fin.succ (rho 6).succ w.succ (rho 0).succ I.succ mul.succ q.succ chain.succ d.succ vertex.succ 0 a.succ))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ConstructionComponentCofinal.encodedCommon_freeClosed,
      ForcingTailCodes.chainCode_freeClosed,ForcingTailCodes.entry_freeClosed,
      ForcingCodeLinks.links_freeClosed,ForcingPersistentWorks.works_freeClosed]

theorem working_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d a : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (workingSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d a)).TrueIn M := by
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
    ForcingTailCodes.chainCode_semantics hM,
    ForcingTailCodes.entry_semantics hM,ForcingCodeLinks.links_semantics hM,ForcingPersistentWorks.works_semantics hM]
  exact working_linked hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d a

theorem working_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d a : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (workingSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d a))) := by
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
  apply ConstructibleGround.relative_models hM (workingSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d a)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (workingSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d a)).mp
      (working_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d a hL hChoice)

end PPAC.Migration.ForcingCodeLinkClosure
