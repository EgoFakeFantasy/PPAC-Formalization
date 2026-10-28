/- Pinned SaturatedMonoids.realizes_prescription:121 / finiteMergers:146.
Consume arbitrary internal finite optional start data at its actual proper
stage, reflect Valid with the existing conservative map, execute the SAME
selected complete round and reuse existing exact RootSystem transport.
The internal empty-index case is constructed explicitly. -/
import PPAC.Migration.ConstructionSaturationPrescriptionStage

namespace PPAC.Migration.ConstructionSaturationMergers
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row)
open ConstructionTowerValidity (Valid row_field)
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (IdentityGraph)
open ConstructionMergerRelations (Prescription)
open ConstructionRequestCarrier (WellFormed)
open ConstructionMergerRootSystem (RootSystem)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Realizes (n prescription N mul : M.Carrier .set) : Prop :=
  ∃ identity roots, MapsTo N N identity ∧ IdentityGraph N identity ∧ MapsTo n N roots ∧
    RootSystem n prescription N mul identity roots

theorem identity_rebase {n prescription S N mul oldIdentity identity roots : M.Carrier .set}
    (hP : Prescription n N prescription) (hOld : IdentityGraph S oldIdentity)
    (hId : IdentityGraph N identity) (hRoots : RootSystem n prescription N mul oldIdentity roots) :
    RootSystem n prescription N mul identity roots := by
  intro i j ri rj hi hj hij hri hrj
  have hR := hRoots i j ri rj hi hj hij hri hrj
  refine ⟨hR.1,?_⟩
  intro a b hStart
  obtain ⟨oa,ob,q,ha,hb,hProdI,hProdJ,hJoin⟩ := hR.2 a b hStart
  have hBounds := hP.1 i j a b hStart
  exact ⟨oa,ob,q,(hId a oa).mpr ⟨hBounds.2.2.1,((hOld a oa).mp ha).2⟩,
    (hId b ob).mpr ⟨hBounds.2.2.2,((hOld b ob).mp hb).2⟩,hProdI,hProdJ,hJoin⟩

theorem realizes_prescription (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C B history F Pairs zero one K mu kappa
      N mulN eN markN HN CN incoming base n prescription : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hB : (Project.FirstOrderSemantics.reduct M).IsOrdinal B)
    (hV : Valid hM w Q R top D mul e mark H C B history)
    (hCover : ConstructionSaturationCover.Covered w history F kappa)
    (hF : ConstructionTowerTransitions.Matrix B history zero Pairs F)
    (hk : (Project.FirstOrderSemantics.reduct M).mem kappa B)
    (hSelected : ∀ i j, (Project.FirstOrderSemantics.reduct M).mem i B →
      (Project.FirstOrderSemantics.reduct M).mem j B →
      (Project.FirstOrderSemantics.reduct M).SuccessorOf j i →
      ∃ raw, ConstructionSaturationIterationValidity.SelectedAt hM w Q R top zero one K mu history F i j raw)
    (hRow : Row history kappa N mulN eN markN HN CN incoming base kappa)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hWell : WellFormed n N prescription) (hP : Prescription n N prescription)
    (hValid : ConstructionMergerRelations.Valid n N mulN prescription) :
    Realizes n prescription N mulN := by
  classical
  have hObjN := (hV.2.1 kappa hk N mulN eN markN HN CN incoming base hRow).1
  obtain ⟨identity,hPerm,hIdentity⟩ := ForcingConditionGraphs.exists_identity hM N
  by_cases hnPositive : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i n
  · obtain ⟨j,D0,mul0,e0,mark0,H0,C0,in0,base0,stageLeg,P0,S,lift,identityS,
      hj,hRow0,hStageLeg,hWell0,hP0,hBack,hPS,hLift,hIdentityS,hLiftComposition,hForward⟩ :=
        ConstructionSaturationPrescriptionStage.prescription_stage hM hw hCover hRow hn hWell hP
    have hjB := hB.transitive kappa hk j hj
    have hStageIn := (ConstructionTowerTransitions.matrix_at hV.1 hF hjB hk (Or.inl hj)
      (row_field 6 hRow)).mp hStageLeg
    have hStageMap := (hV.2.2.1 j kappa D0 mul0 e0 mark0 H0 C0 in0 base0
      N mulN eN markN HN CN incoming base stageLeg hjB hk (Or.inl hj) hRow0 hRow hStageIn).1
    have hObj0 := (hV.2.1 j hjB D0 mul0 e0 mark0 H0 C0 in0 base0 hRow0).1
    have hValid0 := ConstructionMergerPrescriptionMap.valid_of_map hObj0.1 hObjN.1 hP0 hStageMap.1
      hStageMap.2.1 (ConstructionMergerPrescriptionMap.mapped hM hBack) hValid
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
    obtain ⟨pairNP,hPairNP⟩ := KuratowskiZF.exists_code hM n P0
    obtain ⟨request,hCodeReq⟩ := KuratowskiZF.exists_code hM one pairNP
    have hCode : ConstructionRequestSchedule.MergerCode one n P0 request := ⟨pairNP,hCodeReq,hPairNP⟩
    have hRequest := (hRequests request).mpr
      (Or.inr ⟨n,P0,hCode,hn,hnPositive,hWell0,hP0,hValid0⟩)
    obtain ⟨rootsW,hRootsW,hRootSystemW⟩ := hMergers request n P0 hRequest hCode
    obtain ⟨after,hAfterLeg⟩ := ConstructionTowerTransitions.leg_total (zero := zero) (i := s) hV.1
      (ConstructionTowerValidity.incoming_rows hM hV) hk
    have hAfterGlobal : ForcingDiagramOrder.Product F s kappa after :=
      (hF.2.2 s kappa after).mpr ⟨hsB,hk,hAfterLeg⟩
    have hAfterIn := (ConstructionTowerTransitions.matrix_at hV.1 hF hsB hk hBefore
      (row_field 6 hRow)).mp hAfterGlobal
    have hAfterMap := (hV.2.2.1 s kappa W G unitW markW HW CW NewOut baseW
      N mulN eN markN HN CN incoming base after hsB hk hBefore hSuccessorRow hRow hAfterIn).1
    have hOIn := (ConstructionTowerTransitions.matrix_at hV.1 hF hjB hsB
      (Or.inl hSucc.predecessor_mem) (row_field 6 hSuccessorRow)).mp hOGlobal
    have hComposition := hV.2.2.2.1 j s kappa NewOut incoming O after stageLeg
      hjB hsB hk (Or.inl hSucc.predecessor_mem) hBefore (row_field 6 hSuccessorRow)
      (row_field 6 hRow) hOIn hAfterIn hStageIn
    obtain ⟨ON,rootsN,hON,hRootsN,hOC,hRC,hRootN⟩ := ConstructionConeTransport.exists_merger_map hM
      hObjW.1 hOMap.1.1.1 hRootsW hAfterMap.1 hAfterMap.2.1 hRootSystemW
    have eqON := ConstructionRequestMaps.node_map_unique hM hON hStageMap.1.1.1 hOC hComposition
    subst ON
    have hRootP := ConstructionConeTransport.merger_pullback hM hPS hLift hForward hLiftComposition hRootN
    exact ⟨identity,rootsN,hPerm.1,hIdentity,hRootsN,identity_rebase hP hIdentityS hIdentity hRootP⟩
  · obtain ⟨roots,hRoots,_⟩ := ZF.exists_constantFunction (ModelTransfer.project_models_iff.mp hM)
      (KuratowskiZF.interpretation hM) (source := n) hObjN.1.1.1
    refine ⟨identity,roots,hPerm.1,hIdentity,(ForcingSupportSize.native_mapsTo hM n N roots).mpr hRoots,?_⟩
    intro i j ri rj hi
    exact False.elim (hnPositive ⟨i,hi⟩)

/-- Exact source RootSystem.realization: equality of the actual products
is equivalent to the GIVEN CopyRel, without adding a transitive closure. -/
def Realization (n N mul prescription roots : M.Carrier .set) : Prop :=
  ∀ i j x y ri rj u v,
    (Project.FirstOrderSemantics.reduct M).mem i n →
    (Project.FirstOrderSemantics.reduct M).mem j n →
    (Project.FirstOrderSemantics.reduct M).mem x N →
    (Project.FirstOrderSemantics.reduct M).mem y N →
    PureKuratowski.PairMember M i ri roots → PureKuratowski.PairMember M j rj roots →
    ForcingDiagramOrder.Product mul ri x u → ForcingDiagramOrder.Product mul rj y v →
      (u = v ↔ ConstructionMergerRelations.CopyRel n N mul prescription i x j y)

theorem root_realization {n N mul e prescription identity roots : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid N mul e)
    (hP : Prescription n N prescription) (hId : IdentityGraph N identity)
    (hMap : MapsTo n N roots) (hRoots : RootSystem n prescription N mul identity roots) :
    Realization n N mul prescription roots := by
  classical
  intro i j x y ri rj u v hi hj hx hy hri hrj hu hv
  have hriN := hMap.2 i ri hri
  have hrjN := hMap.2 j rj hrj
  by_cases hij : i = j
  · subst j
    have er := ForcingConditionGraphs.function_unique hMap.1 hrj hri
    subst rj
    apply Iff.trans ?_ (ConstructionMergerRelations.rel_same_copy hi hx hy).symm
    constructor
    · intro he
      exact (hm.2.1 ri hriN).2.2 x y u hx hy hu (he.symm ▸ hv)
    · intro he
      subst y
      exact (hm.2.1 ri hriN).2.1 x u v hx hu hv
  · have hR := hRoots i j ri rj hi hj hij hri hrj
    constructor
    · intro he
      have huN := ConstructionMergerRelations.product_range hm hriN hx hu
      have hBoth : ConstructionBaseMonoid.Divides N mul ri u ∧ ConstructionBaseMonoid.Divides N mul rj u :=
        ⟨⟨x,hx,hu⟩,⟨y,hy,he.symm ▸ hv⟩⟩
      by_cases hSome : ∃ a b, ConstructionMergerRelations.Start prescription i j a b
      · obtain ⟨a,b,hStart⟩ := hSome
        obtain ⟨oa,ob,q,hia,hjb,hI,hJ,hJoin⟩ := hR.2 a b hStart
        have ea := ((hId a oa).mp hia).2
        have eb := ((hId b ob).mp hjb).2
        subst oa ob
        obtain ⟨t,ht,hqt⟩ := (hJoin u huN).mp hBoth
        have hBounds := hP.1 i j a b hStart
        have ha := hBounds.2.2.1
        have hb := hBounds.2.2.2
        obtain ⟨aTimesT,hatN,hat⟩ := (hm.2.1 a ha).1 t ht
        obtain ⟨bt,hbtN,hbt⟩ := (hm.2.1 b hb).1 t ht
        have hIat := (hm.2.2 ri a t q aTimesT u hriN ha ht hI hat).mp hqt
        have hJbt := (hm.2.2 rj b t q bt u hrjN hb ht hJ hbt).mp hqt
        have ex := (hm.2.1 ri hriN).2.2 x aTimesT u hx hatN hu hIat
        have ey := (hm.2.1 rj hrjN).2.2 y bt u hy hbtN (he.symm ▸ hv) hJbt
        exact ⟨hi,hx,hj,hy,Or.inr ⟨hij,a,b,t,hStart,ht,ex.symm ▸ hat,ey.symm ▸ hbt⟩⟩
      · exact False.elim (hR.1 hSome u huN hBoth)
    · intro hRel
      rcases hRel.2.2.2.2 with ⟨he,_⟩ | ⟨_,a,b,t,hStart,ht,hat,hbt⟩
      · exact False.elim (hij he)
      · obtain ⟨oa,ob,q,hia,hjb,hI,hJ,hJoin⟩ := hR.2 a b hStart
        have ea := ((hId a oa).mp hia).2
        have eb := ((hId b ob).mp hjb).2
        subst oa ob
        have hBounds := hP.1 i j a b hStart
        have ha := hBounds.2.2.1
        have hb := hBounds.2.2.2
        have hqN := ConstructionMergerRelations.product_range hm hriN ha hI
        obtain ⟨z,hz,hqz⟩ := (hm.2.1 q hqN).1 t ht
        have hIxz := (hm.2.2 ri a t q x z hriN ha ht hI hat).mp hqz
        have hJyz := (hm.2.2 rj b t q y z hrjN hb ht hJ hbt).mp hqz
        exact ((hm.2.1 ri hriN).2.1 x u z hx hu hIxz).trans
          ((hm.2.1 rj hrjN).2.1 y v z hy hv hJyz).symm

/-- Retain the SAME root graph, both full cone laws and the actual source
HasFiniteMergers equality iff CopyRel conclusion. -/
def Complete (n prescription N mul : M.Carrier .set) : Prop :=
  ∃ identity roots, MapsTo N N identity ∧ IdentityGraph N identity ∧ MapsTo n N roots ∧
    RootSystem n prescription N mul identity roots ∧ Realization n N mul prescription roots

theorem complete_realization {n prescription N mul e : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid N mul e) (hP : Prescription n N prescription)
    (hReal : Realizes n prescription N mul) : Complete n prescription N mul := by
  obtain ⟨identity,roots,hIdMap,hId,hMap,hRoots⟩ := hReal
  exact ⟨identity,roots,hIdMap,hId,hMap,hRoots,root_realization hm hP hId hMap hRoots⟩


def AllMergers (w history kappa : M.Carrier .set) : Prop :=
  ∀ N mul e mark H C incoming base n prescription,
    Row history kappa N mul e mark H C incoming base kappa →
    (Project.FirstOrderSemantics.reduct M).mem n w →
    WellFormed n N prescription → Prescription n N prescription →
    ConstructionMergerRelations.Valid n N mul prescription → Complete n prescription N mul

def AllHistoriesMergers (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one K mu kappa B : M.Carrier .set) : Prop :=
  ∀ history P F,
    ConstructionSaturationIteration.Recursive hM w Q R top D mul e mark H C zero one K mu B B history →
    ConstructionTowerTransitions.Matrix B history zero P F → AllMergers w history kappa

def MergerTower (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one u K mu kappa B : M.Carrier .set) : Prop :=
  ConstructionSaturationProbes.ProbeTower hM w Q R top D mul e mark H C zero one u K mu kappa B ∧
    AllHistoriesMergers hM w Q R top D mul e mark H C zero one K mu kappa B

theorem tower_mergers (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top D mul e mark H C zero one u K mu kappa B : M.Carrier .set}
    (hTower : ConstructionSaturationProbes.ProbeTower hM w Q R top D mul e mark H C zero one u K mu kappa B) :
    MergerTower hM w Q R top D mul e mark H C zero one u K mu kappa B := by
  refine ⟨hTower,?_⟩
  intro history Pairs F hRec hF N m v a W V incoming base n prescription hRow hn hWell hP hValid
  have hCtx := hTower.1.1.2.1
  have hData := hTower.1.1.1
  have hV := (ConstructionSaturationIterationValidity.recursive_valid_small hM hOrder hChoice
    hCtx hRec (fun _ h => h)).1
  have hReal := realizes_prescription hM hCtx.1 hData.2.2.2.2.1 hV
    (hTower.1.2 history Pairs F hRec hF) hF hData.2.2.2.1.predecessor_mem
    (fun i j hi hj hs => ConstructionSaturationIterationValidity.map_succ_selected hM hOrder hChoice
      hCtx hRec hF hi hj hs) hRow hn hWell hP hValid
  exact complete_realization (hV.2.1 kappa hData.2.2.2.1.predecessor_mem
    N m v a W V incoming base hRow).1.1 hP hReal

theorem exists_merger_tower (hM : FirstOrder.Theory.Models M nativeZF)
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
    ∃ kappa B, MergerTower hM w Q R top D mul e mark H C zero one u K mu kappa B := by
  obtain ⟨kappa,B,hTower⟩ := ConstructionSaturationProbes.exists_probe_tower hM hOrder hChoice
    hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall hOmegaOne
  exact ⟨kappa,B,tower_mergers hM hOrder hChoice hTower⟩


def realization {m : Nat} (n N mul prescription roots : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (7 : Fin
  (m+8))) (.bound n.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound (6 : Fin (m+8))) (.bound
  n.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound (5 : Fin (m+8))) (.bound
  N.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound (4 : Fin (m+8))) (.bound
  N.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  roots.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8)) (3 : Fin (m+8)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge roots.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin
  (m+8)) (2 : Fin (m+8)))) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product
  mul.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin (m+8)) (5 : Fin (m+8)) (1 : Fin (m+8)))) (.imp
  (ProjectSyntax.encode id (ForcingDiagramOrder.product mul.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin
  (m+8)) (4 : Fin (m+8)) (0 : Fin (m+8)))) (.iff (Project.Formula.extensionalEq (.bound (1 : Fin (m+8)))
  (.bound (0 : Fin (m+8)))) (ConstructionMergerRelations.rel n.succ.succ.succ.succ.succ.succ.succ.succ
  N.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ
  prescription.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8)) (5 : Fin (m+8)) (6 : Fin (m+8)) (4 :
  Fin (m+8))))))))))))))))))))

theorem realization_freeClosed {m : Nat} (n N mul prescription roots : Fin m) :
    (realization n N mul prescription roots).FreeClosed := by
  simp -implicitDefEqProofs [realization,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq,ConstructionMergerRelations.rel_freeClosed]

theorem realization_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n N mul prescription roots : Fin m) :
    Project.Formula.satisfies env (realization n N mul prescription roots) ↔ Realization (env.bound n) (env.bound N) (env.bound mul) (env.bound prescription) (env.bound roots) := by
  simp only [realization,Realization,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingDiagramOrder.product_semantics (M := M),Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ConstructionMergerRelations.rel_semantics hM]
  rfl


def complete {m : Nat} (n prescription N mul : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (1 : Fin (m+2)) N.succ.succ
  N.succ.succ)) (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph N.succ.succ (1 : Fin
  (m+2)))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin (m+2)) n.succ.succ
  N.succ.succ)) (.conj (ConstructionMergerRootSystem.rootSystem n.succ.succ prescription.succ.succ
  N.succ.succ mul.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2))) (realization n.succ.succ N.succ.succ
  mul.succ.succ prescription.succ.succ (0 : Fin (m+2)))))))))

theorem complete_freeClosed {m : Nat} (n prescription N mul : Fin m) :
    (complete n prescription N mul).FreeClosed := by
  simp -implicitDefEqProofs [complete,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionMergerRootSystem.rootSystem_freeClosed,realization_freeClosed]

theorem complete_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n prescription N mul : Fin m) :
    Project.Formula.satisfies env (complete n prescription N mul) ↔ Complete (env.bound n) (env.bound prescription) (env.bound N) (env.bound mul) := by
  simp only [complete,Complete,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),ForcingConditionGraphs.identityGraph_semantics (M := M),ConstructionMergerRootSystem.rootSystem_semantics hM,realization_semantics hM]
  rfl


def allMergers {m : Nat} (w history kappa : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp
  (ConstructionTowerHistory.row history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin (m+10)) (8 : Fin (m+10)) (7 : Fin (m+10))
  (6 : Fin (m+10)) (5 : Fin (m+10)) (4 : Fin (m+10)) (3 : Fin (m+10)) (2 : Fin (m+10))
  kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.imp (.mem (.bound (1 : Fin (m+10))) (.bound
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp (ConstructionRequestCarrier.wellFormed (1 :
  Fin (m+10)) (9 : Fin (m+10)) (0 : Fin (m+10))) (.imp (ConstructionMergerRelations.prescription (1 : Fin
  (m+10)) (9 : Fin (m+10)) (0 : Fin (m+10))) (.imp (ConstructionMergerRelations.valid (1 : Fin (m+10)) (9 :
  Fin (m+10)) (8 : Fin (m+10)) (0 : Fin (m+10))) (complete (1 : Fin (m+10)) (0 : Fin (m+10)) (9 : Fin
  (m+10)) (8 : Fin (m+10))))))))))))))))))

theorem allMergers_freeClosed {m : Nat} (w history kappa : Fin m) :
    (allMergers w history kappa).FreeClosed := by
  simp -implicitDefEqProofs [allMergers,Definitional.Formula.FreeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionRequestCarrier.wellFormed_freeClosed,ConstructionMergerRelations.prescription_freeClosed,ConstructionMergerRelations.valid_freeClosed,complete_freeClosed]

theorem allMergers_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w history kappa : Fin m) :
    Project.Formula.satisfies env (allMergers w history kappa) ↔ AllMergers (env.bound w) (env.bound history) (env.bound kappa) := by
  simp only [allMergers,AllMergers,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionTowerHistory.row_semantics hM,ConstructionRequestCarrier.wellFormed_semantics hM,ConstructionMergerRelations.prescription_semantics hM,ConstructionMergerRelations.valid_semantics hM,complete_semantics hM]
  rfl


def allHistoriesMergers {m : Nat} (w Q R top D mul e mark H C zero one K mu kappa B : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.imp (ConstructionSaturationIteration.recursive w.succ.succ.succ
  Q.succ.succ.succ R.succ.succ.succ top.succ.succ.succ D.succ.succ.succ mul.succ.succ.succ e.succ.succ.succ
  mark.succ.succ.succ H.succ.succ.succ C.succ.succ.succ zero.succ.succ.succ one.succ.succ.succ
  K.succ.succ.succ mu.succ.succ.succ B.succ.succ.succ B.succ.succ.succ (2 : Fin (m+3))) (.imp
  (ConstructionTowerTransitions.matrix B.succ.succ.succ (2 : Fin (m+3)) zero.succ.succ.succ (1 : Fin (m+3))
  (0 : Fin (m+3))) (allMergers w.succ.succ.succ (2 : Fin (m+3)) kappa.succ.succ.succ))))))

theorem allHistoriesMergers_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one K mu kappa B : Fin m) :
    (allHistoriesMergers w Q R top D mul e mark H C zero one K mu kappa B).FreeClosed := by
  simp -implicitDefEqProofs [allHistoriesMergers,Definitional.Formula.FreeClosed,ConstructionSaturationIteration.recursive_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,allMergers_freeClosed]

theorem allHistoriesMergers_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one K mu kappa B : Fin m) :
    Project.Formula.satisfies env (allHistoriesMergers w Q R top D mul e mark H C zero one K mu kappa B) ↔ AllHistoriesMergers hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound K) (env.bound mu) (env.bound kappa) (env.bound B) := by
  simp only [allHistoriesMergers,AllHistoriesMergers,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    
    ConstructionSaturationIteration.recursive_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,allMergers_semantics hM]
  rfl


def mergerTower {m : Nat} (w Q R top D mul e mark H C zero one u K mu kappa B : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionSaturationProbes.probeTower w Q R top D mul e mark H C zero one u K mu kappa B)
  (allHistoriesMergers w Q R top D mul e mark H C zero one K mu kappa B))

theorem mergerTower_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one u K mu kappa B : Fin m) :
    (mergerTower w Q R top D mul e mark H C zero one u K mu kappa B).FreeClosed := by
  simp -implicitDefEqProofs [mergerTower,Definitional.Formula.FreeClosed,ConstructionSaturationProbes.probeTower_freeClosed,allHistoriesMergers_freeClosed]

theorem mergerTower_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one u K mu kappa B : Fin m) :
    Project.Formula.satisfies env (mergerTower w Q R top D mul e mark H C zero one u K mu kappa B) ↔ MergerTower hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound u) (env.bound K) (env.bound mu) (env.bound kappa) (env.bound B) := by
  simp only [mergerTower,MergerTower,
    Project.Formula.satisfies_conj_iff,
    
    ConstructionSaturationProbes.probeTower_semantics hM,allHistoriesMergers_semantics hM]


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
    : Fin 15))) (.imp (ConstructionSaturationIndex.omegaOneLe (0 : Fin 15) (14 : Fin 15)) (.existsE (.existsE (mergerTower (0 : Fin
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
      ConstructionSaturationIndex.omegaOneLe_freeClosed,mergerTower_freeClosed]

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
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationIndex.omegaOneLe_semantics hM,mergerTower_semantics hM]
  exact fun hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall hOmegaOne =>
    exists_merger_tower hM hOrder hChoice hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall hOmegaOne

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




end PPAC.Migration.ConstructionSaturationMergers
