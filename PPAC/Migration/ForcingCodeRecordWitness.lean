/- Pinned CodeCardinals.ordinalType_cardinal_le.total:64-77.
Compose the existing working representative, eligibility/stability, full label
representation density and literal condition pullback. The record is the source
pair (root index, (label index, pulled-back condition)), entirely internal. -/
import PPAC.Migration.ForcingCodeLinkClosure
import PPAC.Migration.ForcingLinkedStability
import PPAC.Migration.ForcingClassRepresentation
import PPAC.Migration.ForcingLocalRecordPullback
import PPAC.Migration.ForcingCodeSelection

namespace PPAC.Migration.ForcingCodeRecordWitness
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingProductSymmetry (orderFormula)
open ForcingSupportSize (Injection)
open ConstructionComponentCarrier (Code)
open ConstructionComponentCofinal (Chain EncodedCommon)
open ForcingTailCodes (ChainCode Entry)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem selected_record (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r index U coordS localS codes order : Fin k) (d a : M.Carrier .set)
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
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3)))
    (_ha : ChainCode (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) a)
    (hSelected : ForcingCodeSelection.IsSelected env rho I G F mul q bound labels E root w chain codes order a d)
    (hRoot : Code (env root) (env r) (env index) (env U))
    (hCard : ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env mul) (env mark) (env mu))
    (hmark : (Project.FirstOrderSemantics.reduct M).mem (env mark) (env (rho 0)))
    (hEHS : ForcingHS.HS ForcingProductFamily.actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
    (hCoord : ForcingCohenCoordinates.Cartesian (env (rho 0)) (env K) (env coordS))
    (hLocal : ForcingCohenCoordinates.Cartesian (env coordS) (env B) (env localS)) :
    ∃ f tau s m x j label name z pb inner rec,
      ForcingCohenConditions.Condition (env (rho 2)) (env w) f ∧ ForcingPowerName.Subset d f ∧
      ForcingCodeSelection.IsSelected env rho I G F mul q bound labels E root w chain codes order a f ∧
      Entry (fun j => env (rho j)) (env G) (env F) (env bound) (env root) tau ∧
      ForcingCodeLinks.Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) f (env root) tau a ∧
      Injection (env (rho 0)) (env I) s ∧
      (Project.FirstOrderSemantics.reduct M).mem m (env (rho 0)) ∧ ForcingDiagramOrder.Sub (env (rho 0)) (env mul) s m (env r) ∧
      (Project.FirstOrderSemantics.reduct M).mem x (env (rho 0)) ∧ PureKuratowski.PairMember M x j s ∧
      (Project.FirstOrderSemantics.reduct M).mem j (env I) ∧
      ForcingLabelNames.Label (env (rho 6)) (env K) (env labelMap) (env top) j (env bit) label ∧
      ForcingHS.HS ForcingProductFamily.actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧
      ForcingRelationClass.Class (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (env (rho 6)) (env labels) (env E) label name ∧
      ForcingSupportingRoot.Code z f s ∧ ForcingAtomicRelations.Forces true (orderFormula (rho 0) mul) env (env (rho 6)) tau name z ∧
      ForcingLocalRecordPullback.Supported (env (rho 0)) s f ∧
      ForcingCohenConditions.Condition (env localS) (env w) pb ∧ ForcingLocalRecordPullback.Pullback (env (rho 0)) s f pb ∧
      PureKuratowski.Code M inner x pb ∧ PureKuratowski.Code M rec m inner := by
  have hWorks := hSelected.1
  have hCommon := hChain.2.2.2.1 (env zero) (env root) hChain.2.1
  obtain ⟨tau,hEntry,hLinks⟩ := ForcingCodeLinkClosure.working_linked_over hM hChoice env rho
    w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq
    zero root vertices chain names root d a hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound
    hq hAq hHq hE hVertices hChain hd _ha hWorks hCommon
  obtain ⟨z0,hz0⟩ := ForcingSupportingRoot.exists_code hM d (env r)
  have hForce := (ForcingLinkedStability.links_stable_at hM hChoice env rho
    w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq
    zero root vertices chain names root r index U d tau z0 a
    hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound
    hq hAq hHq hE hChain hRoot hd hz0 _ha hEntry hWorks hLinks).1
  have hLocalName := hEntry
  obtain ⟨r',index',U',A,Hfix,hRoot',hRange,hFix,hTau⟩ := hLocalName
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hRoot hRoot'
  have hVertex := hCommon
  obtain ⟨r',index',U',s',i',V',hc,_,hv,_,_⟩ := hVertex
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hRoot hc
  have hLarge : ¬ ForcingSupportSize.Small (env I) (env mu) := fun hi =>
    hI.not_cardinalLessOrEqual (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM))
      ((ForcingSupportSize.native_small hM (env I) (env mu)).mp hi)
  have hdC := (hp.2.2.1 d).mp hd
  obtain ⟨f,s,Hs,j,label,name,z,hf,hdf,hs,hsr,hSupport,hCover,hj,hImage,hLabel,hName,hClass,hz,heq⟩ :=
    ForcingClassRepresentation.denseBelow hM hChoice env rho G F mul
      hw hMu hLarge hCard hmark hp hm hv.1 hG hF hLabelMap hTop hLabels hEHS hTau.1.1 hdC hz0 hForce d hdC (fun _ h => h)
  obtain ⟨m,hmD,hSub⟩ := hsr
  obtain ⟨x,hx,hxj⟩ := hImage
  obtain ⟨pb,hpb,hPullback⟩ := ForcingLocalRecordPullback.exists_pullback hM hCoord hLocal hp.1 hp.2.1 hs hf
  obtain ⟨inner,hInner⟩ := KuratowskiZF.exists_code hM x pb
  obtain ⟨rec,hRec⟩ := KuratowskiZF.exists_code hM m inner
  exact ⟨f,tau,s,m,x,j,label,name,z,pb,inner,rec,hf,hdf,ForcingCodeSelection.isSelected_mono hdf hSelected,
    hEntry,ForcingCodeLinks.links_mono hM env rho mul hm hp ((hp.2.2.1 f).mpr hf) hdf hLinks,
    hs,hmD,hSub,hx,hxj,hj,hLabel,hName,hClass,hz,heq,
    (ForcingLocalRecordPullback.supported_iff hSupport).mpr hCover,hpb,hPullback,hInner,hRec⟩

theorem member_record (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r index U coordS localS codes order Ar Hr support ranks selection d z0 theta ntheta beta nb : Fin k)
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
    (hd : ForcingCohenConditions.Condition (env (rho 2)) (env w) (env d))
    (hRoot : Code (env root) (env r) (env index) (env U))
    (hCard : ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env mul) (env mark) (env mu))
    (hmark : (Project.FirstOrderSemantics.reduct M).mem (env mark) (env (rho 0)))
    (hEHS : ForcingHS.HS ForcingProductFamily.actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
    (hCoord : ForcingCohenCoordinates.Cartesian (env (rho 0)) (env K) (env coordS))
    (hLocal : ForcingCohenCoordinates.Cartesian (env coordS) (env B) (env localS)) 
    (hCodes : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hRange : ForcingStabilizerTransport.Image (env r) (env (rho 0)) (env Ar))
    (hFix : ForcingLabelPermutations.Fixing (env G) (env Ar) (env Hr))
    (hIncl : (Project.FirstOrderSemantics.reduct M).MemberSubset (env Hr) (env support))
    (hFamily : ForcingOrdinalFixed.FixedFamily (fun j => env (rho j)) (env G) (env F) (env support) (env codes) (env ranks))
    (hSelection : ForcingCollectedName.Collected (ForcingCohenSelection.liftRelation
      (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env ranks) (env (rho 6)) (env selection))
    (hz0 : ForcingSupportingRoot.Code (env z0) (env d) (env r))
    (hTheta : ForcingCheckName.Checked (env top) (env theta) (env ntheta))
    (hBeta : ForcingCheckName.Checked (env top) (env beta) (env nb))
    (hbt : (Project.FirstOrderSemantics.reduct M).mem (env beta) (env theta))
    (hEq : ForcingAtomicRelations.Forces true (orderFormula (rho 0) mul) env (env (rho 6)) (env selection) (env ntheta) (env z0)) :
    ∃ a rankName zr f tau s m x j label name z pb inner rec,
      (Project.FirstOrderSemantics.reduct M).mem a (env codes) ∧
      PureKuratowski.PairMember M a rankName (env ranks) ∧
      ForcingSupportingRoot.Code zr f (env r) ∧
      ForcingAtomicRelations.Forces true (orderFormula (rho 0) mul) env (env (rho 6)) rankName (env nb) zr ∧
      ForcingCohenConditions.Condition (env (rho 2)) (env w) f ∧ ForcingPowerName.Subset (env d) f ∧
      ForcingCodeSelection.IsSelected env rho I G F mul q bound labels E root w chain codes order a f ∧
      Entry (fun j => env (rho j)) (env G) (env F) (env bound) (env root) tau ∧
      ForcingCodeLinks.Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) f (env root) tau a ∧
      Injection (env (rho 0)) (env I) s ∧
      (Project.FirstOrderSemantics.reduct M).mem m (env (rho 0)) ∧ ForcingDiagramOrder.Sub (env (rho 0)) (env mul) s m (env r) ∧
      (Project.FirstOrderSemantics.reduct M).mem x (env (rho 0)) ∧ PureKuratowski.PairMember M x j s ∧
      (Project.FirstOrderSemantics.reduct M).mem j (env I) ∧
      ForcingLabelNames.Label (env (rho 6)) (env K) (env labelMap) (env top) j (env bit) label ∧
      ForcingHS.HS ForcingProductFamily.actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧
      ForcingRelationClass.Class (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (env (rho 6)) (env labels) (env E) label name ∧
      ForcingSupportingRoot.Code z f s ∧ ForcingAtomicRelations.Forces true (orderFormula (rho 0) mul) env (env (rho 6)) tau name z ∧
      ForcingLocalRecordPullback.Supported (env (rho 0)) s f ∧
      ForcingCohenConditions.Condition (env localS) (env w) pb ∧ ForcingLocalRecordPullback.Pullback (env (rho 0)) s f pb ∧
      PureKuratowski.Code M inner x pb ∧ PureKuratowski.Code M rec m inner := by
  have hCommon := hChain.2.2.2.1 (env zero) (env root) hChain.2.1
  obtain ⟨r',i',U',s',j',V',hc,_,hv,_,_⟩ := hCommon
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hRoot hc
  obtain ⟨e,ze,a,rankName,he,hde,hze,ha,han,hSelected,hRank⟩ :=
    ForcingCohenRankConsumers.member_rank hM hChoice env rho G F mul I w
      (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id
      hw hMu hI hSmall hMergers hRow hm hp hG hF hv.1 hRange hFix hTop hSelection hFamily hIncl
      (ForcingCodeSelection.monotone hM env rho I G F mul q bound labels E root w chain codes order)
      hd hz0 hTheta hBeta hbt hEq
  have hSelected' := (ForcingCodeSelection.mapRel_relation hM env rho I G F mul q bound labels E root w chain codes order a e).mp hSelected
  obtain ⟨f,tau,s,m,x,j,label,name,z,pb,inner,rec,hf,hef,hSel,hEntry,hLinks,hs,hmD,hSub,hx,hxj,hj,hLabel,hName,hClass,hz,hForce,hSupport,hpb,hPullback,hInner,hRec⟩ :=
    selected_record hM hChoice env rho
      w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq
      zero root vertices chain names r index U coordS localS codes order e a
      hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE
      hVertices hChain ((hp.2.2.1 e).mpr he) ((hCodes a).mp ha) hSelected' hRoot hCard hmark hEHS hCoord hLocal
  obtain ⟨zr,hzr,hRank'⟩ := ForcingPrincipalFilter.eqF_mono hM env rho mul hm hp ((hp.2.2.1 f).mpr hf) hv.1 hef ⟨ze,hze,hRank⟩
  exact ⟨a,rankName,zr,f,tau,s,m,x,j,label,name,z,pb,inner,rec,ha,han,hzr,hRank',hf,
    (fun t ht => hef t (hde t ht)),hSel,hEntry,hLinks,hs,hmD,hSub,hx,hxj,hj,hLabel,hName,hClass,hz,hForce,hSupport,hpb,hPullback,hInner,hRec⟩


def memberResult {k : Nat} (rho : Fin 7 → Fin k)
    (w I K G F mul labelMap top bit labels bound E q root chain r localS codes order ranks d nb : Fin k) : Project.Formula 1 k :=
  let L := orderFormula (rho 0) mul
  let up : Fin k → Fin (k+15) := fun j => j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  let body : Project.Formula 1 (k+15) :=
    (.conj (.mem (.bound 14) (.bound (up codes)))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (up ranks) 14 13))
    (.conj (ProjectSyntax.encode id (ForcingSupportingRoot.code 12 11 (up r)))
    (.conj (ProjectSyntax.encode id (ForcingAtomicRelations.forces true L up (up (rho 6)) 13 (up nb) 12))
    (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition (up (rho 2)) (up w) 11))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.subset (up d) 11))
    (.conj (ForcingCodeSelection.selected rho I G F mul q bound labels E root w chain codes order up 14 11)
    (.conj (ForcingTailCodes.entry (fun j => up (rho j)) (up G) (up F) (up bound) (up root) 10)
    (.conj (ForcingCodeLinks.links L up (up (rho 6)) (up w) (up (rho 0)) (up I) (up mul) (up q) (up chain) 11 (up root) 10 14)
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection 9 (up (rho 0)) (up I)))
    (.conj (.mem (.bound 8) (.bound (up (rho 0))))
    (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.sub (up (rho 0)) (up mul) 9 8 (up r)))
    (.conj (.mem (.bound 7) (.bound (up (rho 0))))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 9 7 6))
    (.conj (.mem (.bound 6) (.bound (up I)))
    (.conj (ProjectSyntax.encode id (ForcingLabelNames.label (up (rho 6)) (up K) (up labelMap) (up top) 6 (up bit) 5))
    (.conj (ProjectSyntax.encode id (ForcingHS.hs ForcingProductFamily.actionFormula (fun j => up (rho j)) (up G) (up (rho 6)) (up F) 4))
    (.conj (ProjectSyntax.encode id (ForcingRelationClass.relationClass L (ForcingPairUnion.domain rho G F) up (up (rho 6)) (up labels) (up E) 5 4))
    (.conj (ProjectSyntax.encode id (ForcingSupportingRoot.code 3 11 9))
    (.conj (ProjectSyntax.encode id (ForcingAtomicRelations.forces true L up (up (rho 6)) 10 4 3))
    (.conj (ForcingLocalRecordPullback.supported (up (rho 0)) 9 11)
    (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition (up localS) (up w) 2))
    (.conj (ForcingLocalRecordPullback.pullback (up (rho 0)) 9 11 2)
    (.conj (ProjectSyntax.encode id (PairSyntax.ordered 1 7 2))
    (ProjectSyntax.encode id (PairSyntax.ordered 0 8 1))))))))))))))))))))))))))
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (body)))))))))))))))

theorem memberResult_freeClosed {k : Nat} (rho : Fin 7 → Fin k)
    (w I K G F mul labelMap top bit labels bound E q root chain r localS codes order ranks d nb : Fin k) : (memberResult rho w I K G F mul labelMap top bit labels bound E q root chain r localS codes order ranks d nb).FreeClosed := by
  simp -implicitDefEqProofs [memberResult,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ForcingCodeSelection.selected_freeClosed,ForcingTailCodes.entry_freeClosed,ForcingCodeLinks.links_freeClosed,
    ForcingLocalRecordPullback.supported_freeClosed,ForcingLocalRecordPullback.pullback_freeClosed]


def memberSentence {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r index U coordS localS codes order Ar Hr support ranks selection d z0 theta ntheta beta nb : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (Project.Formula.isOmega (.bound w))
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
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d))
    (.imp (ConstructionComponentCarrier.code root r index U)
    (.imp (ConstructionSaturationCardinals.cardinalsF (rho 0) mul mark mu)
    (.imp (.mem (.bound mark) (.bound (rho 0)))
    (.imp (ProjectSyntax.encode id (ForcingHS.hs ForcingProductFamily.actionFormula rho G (rho 6) F E))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (rho 0) K coordS))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian coordS B localS))
    (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
    (.imp (ProjectSyntax.encode id (ForcingStabilizerTransport.image r (rho 0) Ar))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Ar Hr))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.subset Hr support))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixedFamily rho G F support codes ranks))
    (.imp (ProjectSyntax.encode id (ForcingCollectedName.collected (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w) id codes ranks (rho 6) selection))
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z0 d r))
    (.imp (ProjectSyntax.encode id (ForcingCheckName.checkName top theta ntheta))
    (.imp (ProjectSyntax.encode id (ForcingCheckName.checkName top beta nb))
    (.imp (.mem (.bound beta) (.bound theta))
    (.imp (ProjectSyntax.encode id (ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) id (rho 6) selection ntheta z0))
    (memberResult rho w I K G F mul labelMap top bit labels bound E q root chain r localS codes order ranks d nb))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,ConstructionSaturationCardinals.cardinalsF_freeClosed,
      ForcingTailCodes.carrier_freeClosed,memberResult_freeClosed]

theorem member_models {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r index U coordS localS codes order Ar Hr support ranks selection d z0 theta ntheta beta nb : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (memberSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r index U coordS localS codes order Ar Hr support ranks selection d z0 theta ntheta beta nb)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isOmega_iff,
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
    ConstructionComponentCofinal.chain_semantics hM,ForcingCohenConditions.condition_semantics (M := M),
    ConstructionComponentCarrier.code_semantics hM,ConstructionSaturationCardinals.cardinalsF_semantics hM,
    ForcingHS.hs_semantics (M := M),ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingTailCodes.carrier_semantics hM,
    ForcingStabilizerTransport.image_semantics (M := M),ForcingLabelPermutations.subset_semantics (M := M),
    ForcingOrdinalFixed.fixedFamily_semantics (M := M),ForcingCollectedName.collected_semantics (M := M),
    ForcingSupportingRoot.code_semantics (M := M),ForcingCheckName.checkName_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M)]
  intros
  simp only [memberResult,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,ForcingSupportingRoot.code_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    ForcingCohenConditions.condition_semantics (M := M),ForcingLabelPermutations.subset_semantics (M := M),
    ForcingCodeSelection.selected_semantics hM,ForcingTailCodes.entry_semantics hM,ForcingCodeLinks.links_semantics hM,
    ForcingSupportSize.injection_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),ForcingLabelNames.label_semantics (M := M),
    ForcingHS.hs_semantics (M := M),ForcingRelationClass.relationClass_semantics (M := M),
    ForcingLocalRecordPullback.supported_semantics hM,ForcingLocalRecordPullback.pullback_semantics hM,KuratowskiZF.source_code]
  exact member_record hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r index U coordS localS codes order Ar Hr support ranks selection d z0 theta ntheta beta nb ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›

theorem member_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r index U coordS localS codes order Ar Hr support ranks selection d z0 theta ntheta beta nb : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative
      (memberSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r index U coordS localS codes order Ar Hr support ranks selection d z0 theta ntheta beta nb))) := by
  apply ModelTransfer.derives
  intro N hN
  have hL := ConstructibleSource.model_zf hN
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hN)
  let inhabitant := Classical.choice ((ConstructibleSource.model hN).nonempty .set)
  let env : Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hN)) 0 := ⟨Fin.elim0,fun _ => inhabitant⟩
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hN
  exact (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hL) _).mp
    (member_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r index U coordS localS codes order Ar Hr support ranks selection d z0 theta ntheta beta nb hL hChoice)


end PPAC.Migration.ForcingCodeRecordWitness
