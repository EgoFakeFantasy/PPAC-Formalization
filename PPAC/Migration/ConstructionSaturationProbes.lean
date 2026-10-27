/- Pinned SaturatedMonoids.probes:72 and inclusion_afterRound.
Consume the actual reflected proper-stage request, the SAME selected complete
round, and its actual global final leg. All final divisor profiles and exact
pairwise intersections are transported by existing full conservative maps. -/
import PPAC.Migration.ConstructionSaturationProbeStage

namespace PPAC.Migration.ConstructionSaturationProbes
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row)
open ConstructionTowerValidity (Valid row_field)
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (function_input function_unique)
open ForcingDiagramOrder (Product)
open ConstructionProbeMappedPath (NodeMap)
open ConstructionProbePath (Path)
open ConstructionPersistentProfiles (ProbeProfile)
open ConstructionProbeCones (JoinProperty)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Probes (w K N mul mark a b node : M.Carrier .set) : Prop :=
  ∃ Family, Injection K N Family ∧
    (∀ k p, PureKuratowski.PairMember M k p Family → ProbeProfile w N mul a b mark p node) ∧
    (∀ k l p q, PureKuratowski.PairMember M k p Family → PureKuratowski.PairMember M l q Family →
      k ≠ l → ∃ exit, Product mul a mark exit ∧ JoinProperty N mul p q exit)

theorem probes (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C B history F P zero one K mu kappa
      N mulN eN markN HN CN incoming base a b node : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hB : (Project.FirstOrderSemantics.reduct M).IsOrdinal B)
    (hV : Valid hM w Q R top D mul e mark H C B history)
    (hCover : ConstructionSaturationCover.Covered w history F kappa)
    (hF : ConstructionTowerTransitions.Matrix B history zero P F)
    (hk : (Project.FirstOrderSemantics.reduct M).mem kappa B)
    (hSelected : ∀ i j, (Project.FirstOrderSemantics.reduct M).mem i B →
      (Project.FirstOrderSemantics.reduct M).mem j B →
      (Project.FirstOrderSemantics.reduct M).SuccessorOf j i →
      ∃ raw, ConstructionSaturationIterationValidity.SelectedAt hM w Q R top zero one K mu history F i j raw)
    (hRow : Row history kappa N mulN eN markN HN CN incoming base kappa)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b N) (hne : b ≠ eN)
    (hPath : Path w N mulN eN zero a node) : Probes w K N mulN markN a b node := by
  obtain ⟨j,D0,mul0,e0,mark0,H0,C0,in0,base0,stageLeg,a0,b0,node0,
    hj,hRow0,hStageLeg,haStage,hbStage,hNodeStage,hPath0,hb0,hb0ne⟩ :=
      ConstructionSaturationProbeStage.probe_stage hM hw hB hV hCover hF hk hRow hb hne hPath
  have hjB := hB.transitive kappa hk j hj
  obtain ⟨s,hsB,hSucc,hBefore⟩ := ConstructionCompleteRound.successor_before_last hM hB hk hj
  obtain ⟨raw,Requests,Ds,ms,vs,as_,Ws,Vs,Is,bs,W,G,unitW,markW,HW,CW,NewOut,baseW,O,
    hSourceRow,hSuccessorRow,hPicked,hCandidate,hSavedPack,hOGlobal,hBaseComp⟩ :=
      hSelected j s hjB hsB hSucc
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,_⟩ :=
    ConstructionTowerHistory.row_unique hV.1.1 hRow0 hSourceRow
  obtain ⟨Requests',W',G',unitW',markW',HW',CW',O',hPack,hRequests,hObjW,hOMap,hOProfiles,
    hSmall,hProbes,hMergers,hBuilt⟩ := hCandidate
  obtain ⟨eqW,eqG,eqUnit,eqMark,eqH,eqC,eqO,eqRequests,_⟩ :=
    ConstructionRoundSelection.pack_injective hPack hSavedPack
  subst W' G' unitW' markW' HW' CW' O' Requests'
  obtain ⟨pairBN,hPairBN⟩ := KuratowskiZF.exists_code hM b0 node0
  obtain ⟨pairA,hPairA⟩ := KuratowskiZF.exists_code hM a0 pairBN
  obtain ⟨request,hCodeReq⟩ := KuratowskiZF.exists_code hM zero pairA
  have hCode : ConstructionRequestSchedule.ProbeCode zero a0 b0 node0 request :=
    ⟨pairA,pairBN,hCodeReq,hPairA,hPairBN⟩
  have hRequest := (hRequests request).mpr (Or.inl ⟨a0,b0,node0,hCode,hb0,hb0ne,hPath0⟩)
  obtain ⟨Family,hIndependent,hWitness⟩ := hProbes request a0 b0 node0 hRequest hCode
  obtain ⟨after,hAfterLeg⟩ := ConstructionTowerTransitions.leg_total (zero := zero) (i := s) hV.1
    (ConstructionTowerValidity.incoming_rows hM hV) hk
  have hAfterGlobal : Product F s kappa after := (hF.2.2 s kappa after).mpr ⟨hsB,hk,hAfterLeg⟩
  have hAfterIn := (ConstructionTowerTransitions.matrix_at hV.1 hF hsB hk hBefore
    (row_field 6 hRow)).mp hAfterGlobal
  have hAfterData := hV.2.2.1 s kappa W G unitW markW HW CW NewOut baseW N mulN eN markN HN CN incoming base after
    hsB hk hBefore hSuccessorRow hRow hAfterIn
  have hAfterMap := hAfterData.1
  have hAfterProfiles := hAfterData.2
  have hOIn := (ConstructionTowerTransitions.matrix_at hV.1 hF hjB hsB
    (Or.inl hSucc.predecessor_mem) (row_field 6 hSuccessorRow)).mp hOGlobal
  have hStageIn := (ConstructionTowerTransitions.matrix_at hV.1 hF hjB hk (Or.inl hj)
    (row_field 6 hRow)).mp hStageLeg
  have hComposition := hV.2.2.2.1 j s kappa NewOut incoming O after stageLeg
    hjB hsB hk (Or.inl hSucc.predecessor_mem) hBefore (row_field 6 hSuccessorRow)
    (row_field 6 hRow) hOIn hAfterIn hStageIn
  have hStageMap := (hV.2.2.1 j kappa D0 mul0 e0 mark0 H0 C0 in0 base0 N mulN eN markN HN CN incoming base stageLeg
    hjB hk (Or.inl hj) hRow0 hRow hStageIn).1.1.1.1
  have image_a {aW aN} (haW : PureKuratowski.PairMember M a0 aW O)
      (haN : PureKuratowski.PairMember M aW aN after) : aN = a :=
    function_unique hStageMap.1 ((hComposition a0 aN).mpr ⟨aW,haW,haN⟩) haStage
  have image_b {bW bN} (hbW : PureKuratowski.PairMember M b0 bW O)
      (hbN : PureKuratowski.PairMember M bW bN after) : bN = b :=
    function_unique hStageMap.1 ((hComposition b0 bN).mpr ⟨bW,hbW,hbN⟩) hbStage
  obtain ⟨finalFamily,hFinalMap,hFamilyComp⟩ := ConstructionProbeMappedPath.exists_node_map hM
    hIndependent.1.1 hAfterMap.1.1.1
  have hFinalInjection : Injection K N finalFamily := by
    refine ⟨hFinalMap,?_⟩
    intro k l p hkp hlp
    obtain ⟨x,hkx,hxp⟩ := (hFamilyComp k p).mp hkp
    obtain ⟨y,hly,hyp⟩ := (hFamilyComp l p).mp hlp
    have he := hAfterMap.1.1.2 x y p hxp hyp
    exact hIndependent.1.2 k l x hkx (he.symm ▸ hly)
  refine ⟨finalFamily,hFinalInjection,?_,?_⟩
  · intro k p hkp
    obtain ⟨pW,hkpW,hpWp⟩ := (hFamilyComp k p).mp hkp
    obtain ⟨aW,bW,mappedW,haW,hbW,hMapW,hProfileW⟩ := hWitness k pW hkpW
    obtain ⟨mappedN,aN,bN,dN,pN,hMapN,haN,hbN,hdN,hpN,hProfileN⟩ :=
      hAfterProfiles aW bW markW pW mappedW hProfileW
    have ea := image_a haW haN
    have eb := image_b hbW hbN
    have ed := function_unique hAfterMap.1.1.1.1 hdN hAfterMap.2.2.2.1
    have ep := function_unique hAfterMap.1.1.1.1 hpN hpWp
    subst aN; subst bN; subst dN; subst pN
    have hSameNode := ConstructionRequestMaps.node_map_unique hM hProfileN.2.2.2.2.1 hPath.1
      (ConstructionRoundFields.node_comp hComposition hMapW hMapN) hNodeStage
    exact hSameNode ▸ hProfileN
  · intro k l p q hkp hlq hkl
    obtain ⟨pW,hkpW,hpWp⟩ := (hFamilyComp k p).mp hkp
    obtain ⟨qW,hlqW,hqWq⟩ := (hFamilyComp l q).mp hlq
    obtain ⟨aW,exitW,haW,hExitProduct,hJoinW⟩ := hIndependent.2 k l pW qW hkpW hlqW hkl
    have haWmem := hOMap.1.1.1.2 a0 aW haW
    have hMarkWmem := hObjW.2.2.2.1
    obtain ⟨exit',hExit',hProduct'⟩ := (hObjW.1.2.1 aW haWmem).1 markW hMarkWmem
    have he := (hObjW.1.2.1 aW haWmem).2.1 markW exit' exitW hMarkWmem hProduct' hExitProduct
    have hExitW := he ▸ hExit'
    obtain ⟨aN,haN,_⟩ := hAfterMap.1.1.1.1.2 aW haWmem
    obtain ⟨exitN,hExitN,_⟩ := hAfterMap.1.1.1.1.2 exitW hExitW
    have ea := image_a haW haN
    have hProduct := hAfterMap.2.1 aW markW exitW aN markN exitN hExitProduct haN hAfterMap.2.2.2.1 hExitN
    have hJoin := hAfterMap.1.2.2.1 pW qW exitW p q exitN hpWp hqWq hExitN hJoinW
    exact ⟨exitN,ea ▸ hProduct,hJoin⟩

def AllProbes (w K zero history kappa : M.Carrier .set) : Prop :=
  ∀ N mul e mark H C incoming base a b node,
    Row history kappa N mul e mark H C incoming base kappa →
    (Project.FirstOrderSemantics.reduct M).mem b N → b ≠ e →
    Path w N mul e zero a node → Probes w K N mul mark a b node

def AllHistoriesProbes (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one K mu kappa B : M.Carrier .set) : Prop :=
  ∀ history P F,
    ConstructionSaturationIteration.Recursive hM w Q R top D mul e mark H C zero one K mu B B history →
    ConstructionTowerTransitions.Matrix B history zero P F → AllProbes w K zero history kappa

def ProbeTower (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one u K mu kappa B : M.Carrier .set) : Prop :=
  ConstructionSaturationCover.CoveredTower hM w Q R top D mul e mark H C zero one u K mu kappa B ∧
    AllHistoriesProbes hM w Q R top D mul e mark H C zero one K mu kappa B

theorem tower_probes (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top D mul e mark H C zero one u K mu kappa B : M.Carrier .set}
    (hTower : ConstructionSaturationCover.CoveredTower hM w Q R top D mul e mark H C zero one u K mu kappa B) :
    ProbeTower hM w Q R top D mul e mark H C zero one u K mu kappa B := by
  refine ⟨hTower,?_⟩
  intro history P F hRec hF N m v a W V incoming base a' b node hRow hb hne hPath
  have hCtx := hTower.1.2.1
  have hV := (ConstructionSaturationIterationValidity.recursive_valid_small hM hOrder hChoice
    hCtx hRec (fun _ h => h)).1
  exact probes hM hCtx.1 hTower.1.1.2.2.2.2.1 hV (hTower.2 history P F hRec hF) hF
    hTower.1.1.2.2.2.1.predecessor_mem
    (fun i j hi hj hs => ConstructionSaturationIterationValidity.map_succ_selected hM hOrder hChoice
      hCtx hRec hF hi hj hs) hRow hb hne hPath

theorem exists_probe_tower (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top D mul e mark H C zero one u K mu : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : ConstructionRealCuts.CutCarrier hM w Q R)
    (hCoordinates : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hTop : ConstructionRealCuts.Principal hM w Q u top)
    (hObj : ConstructionRoundFields.ObjectFields hM w Q R top D mul e mark H C)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hK : ∃ k, (Project.FirstOrderSemantics.reduct M).mem k K)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hpow : (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation (KuratowskiZF.interpretation hM) mu mu w)
    (hD : ForcingSupportSize.Small D mu) (hKSmall : ForcingSupportSize.Small K mu) (hOmegaOne : ConstructionSaturationIndex.OmegaOneLe hM w mu) :
    ∃ kappa B, ProbeTower hM w Q R top D mul e mark H C zero one u K mu kappa B := by
  obtain ⟨kappa,B,hTower⟩ := ConstructionSaturationCover.exists_covered_tower hM hOrder hChoice
    hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall hOmegaOne
  exact ⟨kappa,B,tower_probes hM hOrder hChoice hTower⟩



def probesF {m : Nat} (w K N mul mark a b node : Fin m) : Project.Formula 1 m :=
  (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection (0 : Fin (m+1)) K.succ N.succ))
  (.conj (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin
  (m+1)).succ.succ (1 : Fin (m+3)) (0 : Fin (m+3)))) (ConstructionPersistentProfiles.probeProfile
  w.succ.succ.succ N.succ.succ.succ mul.succ.succ.succ a.succ.succ.succ b.succ.succ.succ mark.succ.succ.succ
  (0 : Fin (m+3)) node.succ.succ.succ)))) (.forallE (.forallE (.forallE (.forallE (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin (m+1)).succ.succ.succ.succ (3 : Fin (m+5)) (1 :
  Fin (m+5)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin (m+1)).succ.succ.succ.succ
  (2 : Fin (m+5)) (0 : Fin (m+5)))) (.imp (.neg (Project.Formula.extensionalEq (.bound (3 : Fin (m+5)))
  (.bound (2 : Fin (m+5))))) (.existsE (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product
  mul.succ.succ.succ.succ.succ.succ a.succ.succ.succ.succ.succ.succ mark.succ.succ.succ.succ.succ.succ (0 :
  Fin (m+6)))) (ConstructionProbeCones.joinProperty N.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ (1 : Fin (m+5)).succ (0 : Fin (m+5)).succ (0 : Fin (m+6)))))))))))))))

theorem probesF_freeClosed {m : Nat} (w K N mul mark a b node : Fin m) :
    (probesF w K N mul mark a b node).FreeClosed := by
  simp -implicitDefEqProofs [probesF,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionPersistentProfiles.probeProfile_freeClosed,Project.Formula.extensionalEq,ConstructionProbeCones.joinProperty_freeClosed]

theorem probesF_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w K N mul mark a b node : Fin m) :
    Project.Formula.satisfies env (probesF w K N mul mark a b node) ↔ Probes (env.bound w) (env.bound K) (env.bound N) (env.bound mul) (env.bound mark) (env.bound a) (env.bound b) (env.bound node) := by
  simp only [probesF,Probes,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingSupportSize.injection_semantics (M := M),ConstructionPersistentProfiles.probeProfile_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ForcingDiagramOrder.product_semantics (M := M),ConstructionProbeCones.joinProperty_semantics hM]
  rfl


def allProbes {m : Nat} (w K zero history kappa : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE
  (.forallE (.imp (ConstructionTowerHistory.row
  history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (10 : Fin (m+11)) (9 : Fin (m+11)) (8 : Fin
  (m+11)) (7 : Fin (m+11)) (6 : Fin (m+11)) (5 : Fin (m+11)) (4 : Fin (m+11)) (3 : Fin (m+11))
  kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.imp (.mem (.bound (1 : Fin (m+11)))
  (.bound (10 : Fin (m+11)))) (.imp (.neg (Project.Formula.extensionalEq (.bound (1 : Fin (m+11))) (.bound
  (8 : Fin (m+11))))) (.imp (ConstructionProbePath.path
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (10 : Fin (m+11)) (9 : Fin (m+11)) (8 : Fin
  (m+11)) zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin (m+11)) (0 : Fin (m+11)))
  (probesF w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (10 : Fin (m+11)) (9 : Fin (m+11)) (7 : Fin
  (m+11)) (2 : Fin (m+11)) (1 : Fin (m+11)) (0 : Fin (m+11))))))))))))))))))

theorem allProbes_freeClosed {m : Nat} (w K zero history kappa : Fin m) :
    (allProbes w K zero history kappa).FreeClosed := by
  simp -implicitDefEqProofs [allProbes,Definitional.Formula.FreeClosed,ConstructionTowerHistory.row_freeClosed,Project.Formula.extensionalEq,ConstructionProbePath.path_freeClosed,probesF_freeClosed]

theorem allProbes_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w K zero history kappa : Fin m) :
    Project.Formula.satisfies env (allProbes w K zero history kappa) ↔ AllProbes (env.bound w) (env.bound K) (env.bound zero) (env.bound history) (env.bound kappa) := by
  simp only [allProbes,AllProbes,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionTowerHistory.row_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ConstructionProbePath.path_semantics hM,probesF_semantics hM]
  rfl


def allHistoriesProbes {m : Nat} (w Q R top D mul e mark H C zero one K mu kappa B : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.imp (ConstructionSaturationIteration.recursive w.succ.succ.succ
  Q.succ.succ.succ R.succ.succ.succ top.succ.succ.succ D.succ.succ.succ mul.succ.succ.succ e.succ.succ.succ
  mark.succ.succ.succ H.succ.succ.succ C.succ.succ.succ zero.succ.succ.succ one.succ.succ.succ
  K.succ.succ.succ mu.succ.succ.succ B.succ.succ.succ B.succ.succ.succ (2 : Fin (m+3))) (.imp
  (ConstructionTowerTransitions.matrix B.succ.succ.succ (2 : Fin (m+3)) zero.succ.succ.succ (1 : Fin (m+3))
  (0 : Fin (m+3))) (allProbes w.succ.succ.succ K.succ.succ.succ zero.succ.succ.succ (2 : Fin (m+3))
  kappa.succ.succ.succ))))))

theorem allHistoriesProbes_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one K mu kappa B : Fin m) :
    (allHistoriesProbes w Q R top D mul e mark H C zero one K mu kappa B).FreeClosed := by
  simp -implicitDefEqProofs [allHistoriesProbes,Definitional.Formula.FreeClosed,ConstructionSaturationIteration.recursive_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,allProbes_freeClosed]

theorem allHistoriesProbes_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one K mu kappa B : Fin m) :
    Project.Formula.satisfies env (allHistoriesProbes w Q R top D mul e mark H C zero one K mu kappa B) ↔ AllHistoriesProbes hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound K) (env.bound mu) (env.bound kappa) (env.bound B) := by
  simp only [allHistoriesProbes,AllHistoriesProbes,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    
    ConstructionSaturationIteration.recursive_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,allProbes_semantics hM]
  rfl


def probeTower {m : Nat} (w Q R top D mul e mark H C zero one u K mu kappa B : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionSaturationCover.coveredTower w Q R top D mul e mark H C zero one u K mu kappa B)
  (allHistoriesProbes w Q R top D mul e mark H C zero one K mu kappa B))

theorem probeTower_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one u K mu kappa B : Fin m) :
    (probeTower w Q R top D mul e mark H C zero one u K mu kappa B).FreeClosed := by
  simp -implicitDefEqProofs [probeTower,Definitional.Formula.FreeClosed,ConstructionSaturationCover.coveredTower_freeClosed,allHistoriesProbes_freeClosed]

theorem probeTower_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one u K mu kappa B : Fin m) :
    Project.Formula.satisfies env (probeTower w Q R top D mul e mark H C zero one u K mu kappa B) ↔ ProbeTower hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound u) (env.bound K) (env.bound mu) (env.bound kappa) (env.bound B) := by
  simp only [probeTower,ProbeTower,
    Project.Formula.satisfies_conj_iff,
    
    ConstructionSaturationCover.coveredTower_semantics hM,allHistoriesProbes_semantics hM]


def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 15 (.imp (Project.Formula.isOmega (.bound (0 : Fin 15))) (.imp
    (ConstructionFractionOrder.carrier (0 : Fin 15) (1 : Fin 15)) (.imp (ConstructionRealCuts.cutCarrier (0
    : Fin 15) (1 : Fin 15) (2 : Fin 15)) (.imp (ConstructionFractionOrder.coordinates (0 : Fin 15) (12 : Fin
    15) (11 : Fin 15) (11 : Fin 15)) (.imp (Project.Formula.isOrdinalOne (.bound (11 : Fin 15))) (.imp
    (ConstructionRealCuts.principal (0 : Fin 15) (1 : Fin 15) (12 : Fin 15) (3 : Fin 15)) (.imp
    (ConstructionRoundStepSyntax.objectFields (0 : Fin 15) (1 : Fin 15) (2 : Fin 15) (3 : Fin 15) (4 : Fin
    15) (5 : Fin 15) (6 : Fin 15) (7 : Fin 15) (8 : Fin 15) (9 : Fin 15)) (.imp (Project.Formula.isEmpty
    (.bound (10 : Fin 15))) (.imp (.mem (.bound (10 : Fin 15)) (.bound (0 : Fin 15))) (.imp (.existsE (.mem
    (.bound (0 : Fin 16)) (.bound (13 : Fin 15).succ))) (.imp (Project.Formula.isInfiniteCardinal
    PureKuratowskiProject.convention (.bound (0 : Fin 15)) (.bound (14 : Fin 15))) (.imp
    (Project.Formula.isCardinalExponentiation PureKuratowskiProject.convention (.bound (14 : Fin 15))
    (.bound (14 : Fin 15)) (.bound (0 : Fin 15))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small
    (4 : Fin 15) (14 : Fin 15))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (13 : Fin 15) (14
    : Fin 15))) (.imp (ConstructionSaturationIndex.omegaOneLe (0 : Fin 15) (14 : Fin 15)) (.existsE (.existsE (probeTower (0 : Fin
    15).succ.succ (1 : Fin 15).succ.succ (2 : Fin 15).succ.succ (3 : Fin 15).succ.succ (4 : Fin
    15).succ.succ (5 : Fin 15).succ.succ (6 : Fin 15).succ.succ (7 : Fin 15).succ.succ (8 : Fin
    15).succ.succ (9 : Fin 15).succ.succ (10 : Fin 15).succ.succ (11 : Fin 15).succ.succ (12 : Fin
    15).succ.succ (13 : Fin 15).succ.succ (14 : Fin 15).succ.succ (1 : Fin 17) (0 : Fin
    17))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,ConstructionFractionOrder.carrier_freeClosed,
      ConstructionRealCuts.cutCarrier_freeClosed,ConstructionFractionOrder.coordinates_freeClosed,
      Project.Formula.isOrdinalOne,ConstructionRealCuts.principal_freeClosed,
      ConstructionRoundStepSyntax.objectFields_freeClosed,Project.Formula.isEmpty,
      Project.Formula.isInfiniteCardinal,Project.Formula.isCardinalExponentiation,Project.Formula.isFunctionSpace,
      ConstructionSaturationIndex.omegaOneLe_freeClosed,probeTower_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isOrdinalOne_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isCardinalExponentiation_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    ConstructionFractionOrder.coordinates_semantics hM,ConstructionRealCuts.principal_semantics hM,
    ConstructionRoundStepSyntax.objectFields_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationIndex.omegaOneLe_semantics hM,probeTower_semantics hM]
  exact fun hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall hOmegaOne =>
    exists_probe_tower hM hOrder hChoice hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall hOmegaOne

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative constructionSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let z := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => z }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM constructionSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) constructionSentence).mp
    (construction_models hL (ConstructionRoundSelection.l_order hM) hChoice)




end PPAC.Migration.ConstructionSaturationProbes
