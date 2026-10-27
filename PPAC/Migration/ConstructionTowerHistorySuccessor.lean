/- Pinned Round.step/fromBase/map_succ on the SAME actual record history.
Read its last internal stage, derive all old-leg parents from full validity,
and consume the accepted complete selected successor in the SAME internal L.
No given old-leg family, its Hom/profile/naturality laws, or new object. -/
import PPAC.Migration.ConstructionTowerHistoryInitial

namespace PPAC.Migration.ConstructionTowerHistorySuccessor
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row Charts)
open ConstructionTowerValidity (Valid row_field)
open ConstructionTowerTransitions (Before Order Matrix)
open ConstructionRoundFields (ObjectFields MapFields Profiles)
open ConstructionDirectedWeightData (WeightFamily Stable)
open ConstructionTowerSuccessor (FullLegs ProfileLegs BaseNatural)
open ForcingConditionGraphs (FunctionOn function_unique)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}
variable {w Q R top D mul e mark H C zero one request prev J S E Domains F Muls Units
  Marks Heights Costs Incoming Origins Times P N mulN eN markN HN CN K f : M.Carrier .set}

theorem parents (hM : FirstOrder.Theory.Models M nativeZF)
    (hV : Valid hM w Q R top D mul e mark H C J S)
    (hSucc : (Project.FirstOrderSemantics.reduct M).SuccessorOf J prev)
    (hCharts : Charts J S Domains Muls Units Marks Heights Costs Incoming Origins Times)
    (hE : Order J E) (hF : Matrix J S zero P F)
    (hRow : Row S prev N mulN eN markN HN CN K f prev) :
    ObjectFields hM w Q R top N mulN eN markN HN CN ∧
    MapFields hM w Q D N mul mulN e eN mark markN H C HN CN f ∧
    Profiles w D N mul mulN f ∧ WeightFamily J Domains N K ∧ Stable J E Domains F K ∧
    FullLegs hM w Q J Domains Muls Units Marks Heights Costs K N mulN eN markN HN CN ∧
    ProfileLegs w J Domains Muls K N mulN ∧ BaseNatural J Origins K f ∧
    ∃ identity, PureKuratowski.PairMember M prev identity K ∧ ForcingConditionGraphs.IdentityGraph N identity := by
  have hp := hSucc.predecessor_mem
  obtain ⟨hObj,hBase,hBaseProfiles,next,identity,hNext,hKF,hId,hIdentity⟩ :=
    hV.2.1 prev hp N mulN eN markN HN CN K f hRow
  have heq := (ModelTransfer.extensionality hM).eq_of_same_members next J
    (fun x => (hNext x).trans (hSucc x).symm)
  subst next
  obtain ⟨cD,cm,ce,ca,cH,cC,cK,cB,cT⟩ := hCharts
  have charts : Charts J S Domains Muls Units Marks Heights Costs Incoming Origins Times :=
    ⟨cD,cm,ce,ca,cH,cC,cK,cB,cT⟩
  have before (i) (hi : (Project.FirstOrderSemantics.reduct M).mem i J) : Before i prev := by
    rcases (hSucc i).mp hi with hi | he
    · exact Or.inl hi
    · exact Or.inr ((ModelTransfer.extensionality hM).eq_of_same_members i prev he)
  have get (i : M.Carrier .set) (hi : (Project.FirstOrderSemantics.reduct M).mem i J) :=
    ConstructionTowerValidity.stage_at hM hV charts hi
  have hFull : FullLegs hM w Q J Domains Muls Units Marks Heights Costs K N mulN eN markN HN CN := by
    refine ⟨cD.1,cm.1,ce.1,ca.1,cH.1,cC.1,?_⟩
    intro i A m u a W V ki hi hA hm hu ha hW hV0 hki
    obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
    have eqDi := function_unique cD.1 d_i hA
    subst Di
    have eqmi := function_unique cm.1 m_i hm
    subst mi
    have eqei := function_unique ce.1 u_i hu
    subst ei
    have eqai := function_unique ca.1 a_i ha
    subst ai
    have eqHi := function_unique cH.1 h_i hW
    subst Hi
    have eqCi := function_unique cC.1 c_i hV0
    subst Ci
    exact (hV.2.2.1 i prev A m u a W V Ki fi N mulN eN markN HN CN K f ki
      hi hp (before i hi) r_i hRow hki).1
  have hWeight : WeightFamily J Domains N K := by
    refine ⟨hKF,?_⟩
    intro i A ki hi hA hki
    obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
    have eqDi := function_unique cD.1 d_i hA
    subst Di
    exact (hFull.2.2.2.2.2.2 i A mi ei ai Hi Ci ki hi hA m_i u_i a_i h_i c_i hki).1.1.1
  have hProfile : ProfileLegs w J Domains Muls K N mulN := by
    intro i A m ki hi hA hm hki
    obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
    have eqDi := function_unique cD.1 d_i hA
    subst Di
    have eqmi := function_unique cm.1 m_i hm
    subst mi
    exact (hV.2.2.1 i prev A m ei ai Hi Ci Ki fi N mulN eN markN HN CN K f ki
      hi hp (before i hi) r_i hRow hki).2
  have hStable : Stable J E Domains F K := by
    intro i j x y r ki kj hij hxy hki hkj hxr
    have hi := hxy.1.1
    have hj := hxy.2.1.1
    have bij := ((hE.2 i j).mp hij).2.2
    obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,ri⟩ := hV.1.2 i hi
    obtain ⟨Dj,mj,ej,aj,Hj,Cj,Kj,fj,rj⟩ := hV.1.2 j hj
    obtain ⟨t,ht,htxy⟩ := hxy.2.2
    have hKj := row_field 6 rj
    have hK := row_field 6 hRow
    have ht' := (ConstructionTowerTransitions.matrix_at hV.1 hF hi hj bij hKj).mp ht
    have hc := hV.2.2.2.1 i j prev Kj K t kj ki hi hj hp bij (before j hj)
      hKj hK ht' hkj hki
    obtain ⟨z,htxz,hkzr⟩ := (hc x r).mp hxr
    have hm := (hV.2.2.1 i j Di mi ei ai Hi Ci Ki fi Dj mj ej aj Hj Cj Kj fj t
      hi hj bij ri rj ht').1
    have hMaps : MapsTo Di Dj t := hm.1.1.1
    exact (function_unique hMaps.1 htxz htxy) ▸ hkzr
  have hNatural : BaseNatural J Origins K f := by
    intro i fi ki hi hfi hki
    exact hV.2.2.2.2 i prev fi f K ki hi hp (before i hi)
      ((cB.2 i fi).mp hfi).2 (row_field 7 hRow) (row_field 6 hRow) hki
  exact ⟨hObj,hBase,hBaseProfiles,hWeight,hStable,hFull,hProfile,hNatural,identity,hId,hIdentity⟩

def Value (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one request prev J S output : M.Carrier .set) : Prop :=
  ∃ Domains Muls Units Marks Heights Costs Incoming Origins Times E P F
      N mulN eN markN HN CN K f next,
    Charts J S Domains Muls Units Marks Heights Costs Incoming Origins Times ∧ Order J E ∧
    Matrix J S zero P F ∧ Row S prev N mulN eN markN HN CN K f prev ∧
    (Project.FirstOrderSemantics.reduct M).SuccessorOf next J ∧
    ConstructionTowerCanonicalSuccessor.Value hM w Q R top zero one D mul e mark H C
      N mulN eN markN HN CN f request J E Domains F Muls Units Marks Heights Costs K Origins next output

theorem exists_value (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hV : Valid hM w Q R top D mul e mark H C J S)
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hSucc : (Project.FirstOrderSemantics.reduct M).SuccessorOf J prev)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : ConstructionRealCuts.CutCarrier hM w Q R)
    {u : M.Carrier .set} (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (htop : ConstructionRealCuts.Principal hM w Q u top)
    (hObjD : ObjectFields hM w Q R top D mul e mark H C)
    (hq : ConstructionRequestSchedule.Request w D mul e zero one request) :
    ∃ output, Value hM w Q R top D mul e mark H C zero one request prev J S output := by
  obtain ⟨Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,hCharts,_,hE,hF,_⟩ :=
    ConstructionTowerTransitions.exists_tables hM zero hV.1 (ConstructionTowerValidity.incoming_rows hM hV)
  obtain ⟨N,mulN,eN,markN,HN,CN,K,f,hRow⟩ := hV.1.2 prev hSucc.predecessor_mem
  obtain ⟨hObjN,hBase,_,hWeight,hStable,hFull,hProfiles,hNatural,_⟩ :=
    parents hM hV hSucc hCharts hE hF hRow
  have hKP := ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)
  obtain ⟨next,hNext⟩ := KP.exists_successor hKP J
  have hNextOrd := KP.successor_isOrdinal hKP hJ hNext
  obtain ⟨output,hValue,_⟩ := ConstructionTowerCanonicalSuccessor.exists_value hM hOrder
    hw hz hzw hQ hR hu hone htop hObjD hObjN hBase hq hWeight hStable hFull hProfiles hNatural hJ hNextOrd hNext
  exact ⟨output,Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,
    N,mulN,eN,markN,HN,CN,K,f,next,hCharts,hE,hF,hRow,hNext,hValue⟩

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hV : Valid hM w Q R top D mul e mark H C J S)
    {x y : M.Carrier .set}
    (hx : Value hM w Q R top D mul e mark H C zero one request prev J S x)
    (hy : Value hM w Q R top D mul e mark H C zero one request prev J S y) : x = y := by
  obtain ⟨Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,
    N,mulN,eN,markN,HN,CN,K,f,next,hCharts,hE,hF,hRow,hNext,hx⟩ := hx
  obtain ⟨Domains',Muls',Units',Marks',Heights',Costs',Incoming',Origins',Times',E',P',F',
    N',mulN',eN',markN',HN',CN',K',f',next',hCharts',hE',hF',hRow',hNext',hy⟩ := hy
  obtain ⟨cD,cm,ce,ca,cH,cC,cI,cO,cT⟩ := hCharts
  obtain ⟨cD',cm',ce',ca',cH',cC',cI',cO',cT'⟩ := hCharts'
  have eqDomains := ConstructionTowerHistory.chart_unique hM 0 cD' cD
  subst Domains'
  have eqMuls := ConstructionTowerHistory.chart_unique hM 1 cm' cm
  subst Muls'
  have eqUnits := ConstructionTowerHistory.chart_unique hM 2 ce' ce
  subst Units'
  have eqMarks := ConstructionTowerHistory.chart_unique hM 3 ca' ca
  subst Marks'
  have eqHeights := ConstructionTowerHistory.chart_unique hM 4 cH' cH
  subst Heights'
  have eqCosts := ConstructionTowerHistory.chart_unique hM 5 cC' cC
  subst Costs'
  have eqIncoming := ConstructionTowerHistory.chart_unique hM 6 cI' cI
  subst Incoming'
  have eqOrigins := ConstructionTowerHistory.chart_unique hM 7 cO' cO
  subst Origins'
  have eqTimes := ConstructionTowerHistory.chart_unique hM 8 cT' cT
  subst Times'
  have eqE := ConstructionTowerTransitions.order_unique hM hE' hE
  subst E'
  obtain ⟨eqP,eqF⟩ := ConstructionTowerTransitions.matrix_unique hM hF' hF
  subst P'; subst F'
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,_⟩ := ConstructionTowerHistory.row_unique hV.1.1 hRow hRow'
  have eqNext := (ModelTransfer.extensionality hM).eq_of_same_members next' next
    (fun x => (hNext' x).trans (hNext x).symm)
  subst next'
  exact ConstructionTowerCanonicalSuccessor.value_unique hM hOrder hx hy


def value {m : Nat} (w Q R top D mul e mark H C zero one request prev J S output : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.conj (ConstructionTowerHistory.charts
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  S.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (20 : Fin (m+21)) (19 : Fin (m+21)) (18 : Fin (m+21)) (17 : Fin (m+21)) (16 : Fin (m+21)) (15 : Fin
  (m+21)) (14 : Fin (m+21)) (13 : Fin (m+21)) (12 : Fin (m+21))) (.conj (ConstructionTowerTransitions.order
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (11 : Fin (m+21))) (.conj (ConstructionTowerTransitions.matrix
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  S.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (10 : Fin (m+21)) (9 : Fin (m+21))) (.conj (ConstructionTowerHistory.row
  S.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  prev.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (8 : Fin (m+21)) (7 : Fin (m+21)) (6 : Fin (m+21)) (5 : Fin (m+21)) (4 : Fin (m+21)) (3 : Fin (m+21)) (2 :
  Fin (m+21)) (1 : Fin (m+21))
  prev.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
  (.conj (Project.Formula.isSuccessor (.bound (0 : Fin (m+21))) (.bound
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
  (ConstructionTowerCanonicalSuccessor.value
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (8 : Fin (m+21)) (7 : Fin (m+21)) (6 : Fin (m+21)) (5 : Fin (m+21)) (4 : Fin (m+21)) (3 : Fin (m+21)) (1 :
  Fin (m+21))
  request.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (11 : Fin (m+21)) (20 : Fin (m+21)) (9 : Fin (m+21)) (19 : Fin (m+21)) (18 : Fin (m+21)) (17 : Fin (m+21))
  (16 : Fin (m+21)) (15 : Fin (m+21)) (2 : Fin (m+21)) (13 : Fin (m+21)) (0 : Fin (m+21))
  output.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)))))))))))))
  ))))))))))))))

theorem value_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one request prev J S output : Fin m) :
    (value w Q R top D mul e mark H C zero one request prev J S output).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,ConstructionTowerHistory.charts_freeClosed,ConstructionTowerTransitions.order_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerHistory.row_freeClosed,Project.Formula.isSuccessor,ConstructionTowerCanonicalSuccessor.value_freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one request prev J S output : Fin m) :
    Project.Formula.satisfies env (value w Q R top D mul e mark H C zero one request prev J S output) ↔ Value hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound request) (env.bound prev) (env.bound J) (env.bound S) (env.bound output) := by
  simp only [value,Value,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Term.eval_bound,
    ConstructionTowerHistory.charts_semantics hM,ConstructionTowerTransitions.order_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerHistory.row_semantics hM,Project.Formula.satisfies_isSuccessor_iff,ConstructionTowerCanonicalSuccessor.value_semantics hM]
  rfl

def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 17 (.imp (ConstructionTowerValidity.valid (0 : Fin 17) (1 : Fin 17) (2 : Fin
    17) (3 : Fin 17) (4 : Fin 17) (5 : Fin 17) (6 : Fin 17) (7 : Fin 17) (8 : Fin 17) (9 : Fin 17) (14 : Fin
    17) (15 : Fin 17)) (.imp (Project.Formula.isOrdinal (.bound (14 : Fin 17))) (.imp
    (Project.Formula.isSuccessor (.bound (14 : Fin 17)) (.bound (13 : Fin 17))) (.imp
    (Project.Formula.isOmega (.bound (0 : Fin 17))) (.imp (Project.Formula.isEmpty (.bound (10 : Fin 17)))
    (.imp (.mem (.bound (10 : Fin 17)) (.bound (0 : Fin 17))) (.imp (ConstructionFractionOrder.carrier (0 :
    Fin 17) (1 : Fin 17)) (.imp (ConstructionRealCuts.cutCarrier (0 : Fin 17) (1 : Fin 17) (2 : Fin 17))
    (.imp (ConstructionFractionOrder.coordinates (0 : Fin 17) (16 : Fin 17) (11 : Fin 17) (11 : Fin 17))
    (.imp (Project.Formula.isOrdinalOne (.bound (11 : Fin 17))) (.imp (ConstructionRealCuts.principal (0 :
    Fin 17) (1 : Fin 17) (16 : Fin 17) (3 : Fin 17)) (.imp (ConstructionRoundStepSyntax.objectFields (0 :
    Fin 17) (1 : Fin 17) (2 : Fin 17) (3 : Fin 17) (4 : Fin 17) (5 : Fin 17) (6 : Fin 17) (7 : Fin 17) (8 :
    Fin 17) (9 : Fin 17)) (.imp (ConstructionRequestSchedule.request (0 : Fin 17) (4 : Fin 17) (5 : Fin 17)
    (6 : Fin 17) (10 : Fin 17) (11 : Fin 17) (12 : Fin 17)) (.existsE (.conj (value (0 : Fin 17).succ (1 :
    Fin 17).succ (2 : Fin 17).succ (3 : Fin 17).succ (4 : Fin 17).succ (5 : Fin 17).succ (6 : Fin 17).succ
    (7 : Fin 17).succ (8 : Fin 17).succ (9 : Fin 17).succ (10 : Fin 17).succ (11 : Fin 17).succ (12 : Fin
    17).succ (13 : Fin 17).succ (14 : Fin 17).succ (15 : Fin 17).succ (0 : Fin 18)) (.forallE (.imp (value
    (0 : Fin 17).succ.succ (1 : Fin 17).succ.succ (2 : Fin 17).succ.succ (3 : Fin 17).succ.succ (4 : Fin
    17).succ.succ (5 : Fin 17).succ.succ (6 : Fin 17).succ.succ (7 : Fin 17).succ.succ (8 : Fin
    17).succ.succ (9 : Fin 17).succ.succ (10 : Fin 17).succ.succ (11 : Fin 17).succ.succ (12 : Fin
    17).succ.succ (13 : Fin 17).succ.succ (14 : Fin 17).succ.succ (15 : Fin 17).succ.succ (0 : Fin 19))
    (Project.Formula.extensionalEq (.bound (0 : Fin 19)) (.bound (1 : Fin 19)))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ConstructionTowerValidity.valid_freeClosed,Project.Formula.isOrdinal,Project.Formula.isSuccessor,
      Project.Formula.isOmega,Project.Formula.isEmpty,Project.Formula.isOrdinalOne,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionFractionOrder.coordinates_freeClosed,
      ConstructionRealCuts.cutCarrier_freeClosed,ConstructionRealCuts.principal_freeClosed,
      ConstructionRoundStepSyntax.objectFields_freeClosed,ConstructionRequestSchedule.request_freeClosed,
      value_freeClosed,Project.Formula.extensionalEq]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M))) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_isOrdinal_iff,Project.Formula.satisfies_isSuccessor_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_isOrdinalOne_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    ConstructionTowerValidity.valid_semantics hM,ConstructionFractionOrder.carrier_semantics hM,
    ConstructionRealCuts.cutCarrier_semantics hM,ConstructionFractionOrder.coordinates_semantics hM,
    ConstructionRealCuts.principal_semantics hM,ConstructionRoundStepSyntax.objectFields_semantics hM,
    ConstructionRequestSchedule.request_semantics hM,value_semantics hM]
  intro hV hJ hSucc hw hz hzw hQ hR hu hone htop hObjD hq
  obtain ⟨output,hout⟩ := exists_value hM hOrder hV hJ hSucc hw hz hzw hQ hR hu hone htop hObjD hq
  exact ⟨output,hout,fun other hOther => value_unique hM hOrder hV hOther hout⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative constructionSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  apply ConstructibleGround.relative_models hM constructionSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality (ConstructibleSource.model_zf hM)) constructionSentence).mp
    (construction_models (ConstructibleSource.model_zf hM) (ConstructionRoundSelection.l_order hM))

end PPAC.Migration.ConstructionTowerHistorySuccessor
