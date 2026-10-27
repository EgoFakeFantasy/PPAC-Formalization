/- Pinned Round.underFunctor / DirectedColimit parents: derive ALL original
weighted diagram and Under-base input laws from pointwise record validity.
Actual tables are constructed by the accepted native graph producers.
No colimit/ordinal recursion/choice backend is duplicated. -/
import PPAC.Migration.ConstructionTowerValidity

namespace PPAC.Migration.ConstructionTowerDiagram
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row Charts)
open ConstructionTowerValidity (Valid row_field)
open ConstructionTowerTransitions (Before Order Matrix)
open ConstructionRoundFields (ObjectFields MapFields Profiles)
open ConstructionDirectedSystem
open ConstructionDirectedMonoidData (Family HomLaws ConicalFamily)
open ConstructionDirectedConservativeData (ConservativeTransitions JoinsFamily)
open ConstructionDirectedWeightData (WeightFamily Stable HeightBounds CostBounds UniformFamily SupremumLaws)
open ConstructionTowerLimit (ProfileTransitions OriginLegs OriginNatural OriginProfiles)
open ForcingConditionGraphs (FunctionOn function_unique)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}
variable {w Q R top D mul e mark H C J S E Domains F Muls Units Marks Heights Costs Incoming Origins Times P zero : M.Carrier .set}

def Data (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C J E Domains F Muls Units Marks Heights Costs Origins : M.Carrier .set) : Prop :=
  IndexLaws J E ∧ TransitionLaws J E Domains F ∧ Family J Domains Muls Units ∧
  HomLaws J E Domains F Muls Units ∧ ConservativeTransitions J E Domains F Muls ∧
  WeightFamily J Domains R Heights ∧ WeightFamily J Domains R Costs ∧
  Stable J E Domains F Heights ∧ Stable J E Domains F Costs ∧
  HeightBounds J Heights top ∧ CostBounds J Costs top ∧
  UniformFamily hM w Q J Domains Muls Heights Costs ∧ SupremumLaws J E Domains F Muls Costs ∧
  ConicalFamily J Domains Muls Units ∧ JoinsFamily J Domains Muls Units ∧
  ConstructionDirectedMarks.MarkFamily J Domains Units Marks ∧
  ConstructionDirectedMarks.Stable J E Domains F Marks ∧ ProfileTransitions w J E Domains F Muls ∧
  OriginLegs hM w Q J Domains Muls Units Marks Heights Costs Origins D mul e mark H C ∧
  OriginNatural J E F Origins ∧ OriginProfiles w J Domains Muls Origins D mul

theorem data_of_valid (hM : FirstOrder.Theory.Models M nativeZF)
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hV : Valid hM w Q R top D mul e mark H C J S)
    (hCharts : Charts J S Domains Muls Units Marks Heights Costs Incoming Origins Times)
    (hE : Order J E) (hF : Matrix J S zero P F) :
    Data hM w Q R top D mul e mark H C J E Domains F Muls Units Marks Heights Costs Origins := by
  have hRows := ConstructionTowerValidity.incoming_rows hM hV
  have hIndex := ConstructionTowerTransitions.order_index_laws hM hJ hE
  obtain ⟨cD,cm,ce,ca,cH,cC,cK,cB,cTime⟩ := hCharts
  have charts : Charts J S Domains Muls Units Marks Heights Costs Incoming Origins Times :=
    ⟨cD,cm,ce,ca,cH,cC,cK,cB,cTime⟩
  have get (i : M.Carrier .set) (hi : (Project.FirstOrderSemantics.reduct M).mem i J) :=
    ConstructionTowerValidity.stage_at hM hV charts hi
  have maps {i j Di mi ei ai Hi Ci Ki fi Dj mj ej aj Hj Cj Kj fj t : M.Carrier .set}
      (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
      (hj : (Project.FirstOrderSemantics.reduct M).mem j J)
      (hij : PureKuratowski.PairMember M i j E)
      (ri : Row S i Di mi ei ai Hi Ci Ki fi i) (rj : Row S j Dj mj ej aj Hj Cj Kj fj j)
      (ht : Product F i j t) : MapFields hM w Q Di Dj mi mj ei ej ai aj Hi Ci Hj Cj t ∧
        Profiles w Di Dj mi mj t := by
    have before := ((hE.2 i j).mp hij).2.2
    exact hV.2.2.1 i j Di mi ei ai Hi Ci Ki fi Dj mj ej aj Hj Cj Kj fj t hi hj before ri rj
      ((ConstructionTowerTransitions.matrix_at hV.1 hF hi hj before (row_field 6 rj)).mp ht)
  have same {i j K f g : M.Carrier .set}
      (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
      (hj : (Project.FirstOrderSemantics.reduct M).mem j J)
      (hij : Before i j) (hK : ConstructionTowerHistory.Field 6 S j K)
      (hf : Product F i j f) (hg : Product F i j g) : f = g := by
    obtain ⟨next,_,hFn⟩ := hRows j K hj hK
    exact function_unique hFn
      ((ConstructionTowerTransitions.matrix_at hV.1 hF hi hj hij hK).mp hf)
      ((ConstructionTowerTransitions.matrix_at hV.1 hF hi hj hij hK).mp hg)
  have edge {i j K f x y : M.Carrier .set}
      (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
      (hj : (Project.FirstOrderSemantics.reduct M).mem j J)
      (hij : Before i j) (hK : ConstructionTowerHistory.Field 6 S j K)
      (hf : Product F i j f) (hxy : Transition J Domains F i j x y) :
      PureKuratowski.PairMember M x y f := by
    obtain ⟨g,hg,hxy⟩ := hxy.2.2
    exact (same hi hj hij hK hg hf) ▸ hxy
  have exists_map (i j : M.Carrier .set)
      (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
      (hj : (Project.FirstOrderSemantics.reduct M).mem j J) :
      ∃ f, Product F i j f := by
    obtain ⟨f,hf⟩ := ConstructionTowerTransitions.leg_total (zero := zero) (i := i) hV.1 hRows hj
    exact ⟨f,(hF.2.2 i j f).mpr ⟨hi,hj,hf⟩⟩
  have hFamily : Family J Domains Muls Units := by
    refine ⟨cD.1,cm.1,ce.1,?_⟩
    intro i N m u hN hm hu
    have hi := ForcingConditionGraphs.function_input cD.1 hN
    obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
    have eqDi := function_unique cD.1 d_i hN
    subst Di
    have eqmi := function_unique cm.1 m_i hm
    subst mi
    have eqei := function_unique ce.1 u_i hu
    subst ei
    exact o_i.1
  have hCons : ConservativeTransitions J E Domains F Muls := by
    intro i j N L m n t hi hj hij hN hL hm hn ht
    obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
    obtain ⟨Dj,mj,ej,aj,Hj,Cj,Kj,fj,r_j,d_j,m_j,u_j,a_j,h_j,c_j,k_j,f_j,o_j,b_j,p_j,self_j⟩ := get j hj
    have eqDi := function_unique cD.1 d_i hN
    subst Di
    have eqmi := function_unique cm.1 m_i hm
    subst mi
    have eqDj := function_unique cD.1 d_j hL
    subst Dj
    have eqmj := function_unique cm.1 m_j hn
    subst mj
    exact (maps hi hj hij r_i r_j ht).1.1
  have hTransitions : TransitionLaws J E Domains F := by
    refine ⟨?_,?_,?_,?_⟩
    · intro i j x hx hj hij
      have hi := hx.1
      obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
      obtain ⟨Dj,mj,ej,aj,Hj,Cj,Kj,fj,r_j,d_j,m_j,u_j,a_j,h_j,c_j,k_j,f_j,o_j,b_j,p_j,self_j⟩ := get j hj
      obtain ⟨f,hf⟩ := exists_map i j hi hj
      have hm := (maps hi hj hij r_i r_j hf).1
      have hMaps : MapsTo Di Dj f := hm.1.1.1
      have hxd := ConstructionDirectedMonoidData.domain_mem hFamily d_i hx
      obtain ⟨y,hxy,_⟩ := hMaps.1.2 x hxd
      exact ⟨y,hx,⟨hj,Dj,d_j,hMaps.2 x y hxy⟩,f,hf,hxy⟩
    · intro i j x y z hij hxy hxz
      have hi := hxy.1.1
      have hj := hxy.2.1.1
      obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
      obtain ⟨Dj,mj,ej,aj,Hj,Cj,Kj,fj,r_j,d_j,m_j,u_j,a_j,h_j,c_j,k_j,f_j,o_j,b_j,p_j,self_j⟩ := get j hj
      obtain ⟨f,hf,hfx⟩ := hxy.2.2
      have hm := (maps hi hj hij r_i r_j hf).1
      have hMaps : MapsTo Di Dj f := hm.1.1.1
      have hBefore := ((hE.2 i j).mp hij).2.2
      exact function_unique hMaps.1 hfx (edge hi hj hBefore (row_field 6 r_j) hf hxz)
    · intro i x hx
      have hi := hx.1
      obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
      obtain ⟨next,identity,_,_,hId,hIdentity⟩ := self_i
      have hProd := (ConstructionTowerTransitions.matrix_at hV.1 hF hi hi
        (Or.inr rfl) (row_field 6 r_i)).mpr hId
      exact ⟨hx,hx,identity,hProd,(hIdentity x x).mpr
        ⟨ConstructionDirectedMonoidData.domain_mem hFamily d_i hx,rfl⟩⟩
    · intro i j k x y z hij hjk hxy hyz
      have hi := hxy.1.1
      have hj := hxy.2.1.1
      have hk := hyz.2.1.1
      have hik := hIndex.2.1 i j k hi hj hk hij hjk
      have bij := ((hE.2 i j).mp hij).2.2
      have bjk := ((hE.2 j k).mp hjk).2.2
      have bik := ((hE.2 i k).mp hik).2.2
      obtain ⟨L,hL⟩ := ConstructionTowerHistory.field_total 6 hV.1 hj
      obtain ⟨K,hK⟩ := ConstructionTowerHistory.field_total 6 hV.1 hk
      obtain ⟨f,hf,hfx⟩ := hxy.2.2
      obtain ⟨g,hg,hgy⟩ := hyz.2.2
      obtain ⟨h,hh⟩ := exists_map i k hi hk
      have hf' := (ConstructionTowerTransitions.matrix_at hV.1 hF hi hj bij hL).mp hf
      have hg' := (ConstructionTowerTransitions.matrix_at hV.1 hF hj hk bjk hK).mp hg
      have hh' := (ConstructionTowerTransitions.matrix_at hV.1 hF hi hk bik hK).mp hh
      have hc := hV.2.2.2.1 i j k L K f g h hi hj hk bij bjk hL hK hf' hg' hh'
      exact ⟨hxy.1,hyz.2.1,h,hh,(hc x z).mpr ⟨y,hfx,hgy⟩⟩
  have hHom : HomLaws J E Domains F Muls Units := by
    constructor
    · intro i j x y z xx yy zz hij hp hxx hyy hzz
      have hi := hp.1.1
      have hj := hxx.2.1.1
      obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
      obtain ⟨Dj,mj,ej,aj,Hj,Cj,Kj,fj,r_j,d_j,m_j,u_j,a_j,h_j,c_j,k_j,f_j,o_j,b_j,p_j,self_j⟩ := get j hj
      obtain ⟨f,hf,hfx⟩ := hxx.2.2
      have hm := (maps hi hj hij r_i r_j hf).1
      have bij := ((hE.2 i j).mp hij).2.2
      have hfy := edge hi hj bij (row_field 6 r_j) hf hyy
      have hfz := edge hi hj bij (row_field 6 r_j) hf hzz
      have hprod := (ConstructionDirectedMonoidData.product_data hFamily d_i m_i hp).2.2.2
      exact ConstructionDirectedMonoidData.product_mk hj d_j m_j
        (ConstructionDirectedMonoidData.domain_mem hFamily d_j hxx.2.1)
        (ConstructionDirectedMonoidData.domain_mem hFamily d_j hyy.2.1)
        (ConstructionDirectedMonoidData.domain_mem hFamily d_j hzz.2.1)
        (hm.2.1 x y z xx yy zz hprod hfx hfy hfz)
    · intro i j u uu hij hu hxu
      have hi := hu.1.1
      have hj := hxu.2.1.1
      obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
      obtain ⟨Dj,mj,ej,aj,Hj,Cj,Kj,fj,r_j,d_j,m_j,u_j,a_j,h_j,c_j,k_j,f_j,o_j,b_j,p_j,self_j⟩ := get j hj
      have heu := function_unique ce.1 hu.2 u_i
      subst u
      obtain ⟨f,hf,hfu⟩ := hxu.2.2
      have hm := (maps hi hj hij r_i r_j hf).1
      have hMaps : MapsTo Di Dj f := hm.1.1.1
      have he := function_unique hMaps.1 hfu hm.2.2.1
      exact ⟨hxu.2.1,he.symm ▸ u_j⟩
  have hWH : WeightFamily J Domains R Heights := by
    refine ⟨cH.1,?_⟩
    intro i N W hi hN hW
    obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
    have eqDi := function_unique cD.1 d_i hN
    subst Di
    have eqHi := function_unique cH.1 h_i hW
    subst Hi
    exact o_i.2.2.2.2.2.1
  have hWC : WeightFamily J Domains R Costs := by
    refine ⟨cC.1,?_⟩
    intro i N W hi hN hV0
    obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
    have eqDi := function_unique cD.1 d_i hN
    subst Di
    have eqCi := function_unique cC.1 c_i hV0
    subst Ci
    exact o_i.2.2.2.2.2.2.2.1
  have hStableH : Stable J E Domains F Heights := by
    intro i j x y r Wi Wj hij hxy hWi hWj hxr
    have hi := hxy.1.1
    have hj := hxy.2.1.1
    obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
    obtain ⟨Dj,mj,ej,aj,Hj,Cj,Kj,fj,r_j,d_j,m_j,u_j,a_j,h_j,c_j,k_j,f_j,o_j,b_j,p_j,self_j⟩ := get j hj
    have eqHi := function_unique cH.1 h_i hWi
    subst Hi
    have eqHj := function_unique cH.1 h_j hWj
    subst Hj
    obtain ⟨f,hf,hfx⟩ := hxy.2.2
    have hm := (maps hi hj hij r_i r_j hf).1
    exact (hm.2.2.2.2.1 x y r hfx).mpr hxr
  have hStableC : Stable J E Domains F Costs := by
    intro i j x y r Wi Wj hij hxy hWi hWj hxr
    have hi := hxy.1.1
    have hj := hxy.2.1.1
    obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
    obtain ⟨Dj,mj,ej,aj,Hj,Cj,Kj,fj,r_j,d_j,m_j,u_j,a_j,h_j,c_j,k_j,f_j,o_j,b_j,p_j,self_j⟩ := get j hj
    have eqCi := function_unique cC.1 c_i hWi
    subst Ci
    have eqCj := function_unique cC.1 c_j hWj
    subst Cj
    obtain ⟨f,hf,hfx⟩ := hxy.2.2
    have hm := (maps hi hj hij r_i r_j hf).1
    exact (hm.2.2.2.2.2.1 x y r hfx).mpr hxr
  have hHB : HeightBounds J Heights top := by
    intro i W hi hW
    obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
    have eqHi := function_unique cH.1 h_i hW
    subst Hi
    exact o_i.2.2.2.2.2.2.1
  have hCB : CostBounds J Costs top := by
    intro i W hi hW
    obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
    have eqCi := function_unique cC.1 c_i hW
    subst Ci
    exact o_i.2.2.2.2.2.2.2.2.1
  have hUniform : UniformFamily hM w Q J Domains Muls Heights Costs := by
    intro i N m W V hi hN hm hW hV0
    obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
    have eqDi := function_unique cD.1 d_i hN
    subst Di
    have eqmi := function_unique cm.1 m_i hm
    subst mi
    have eqHi := function_unique cH.1 h_i hW
    subst Hi
    have eqCi := function_unique cC.1 c_i hV0
    subst Ci
    exact o_i.2.2.2.2.2.2.2.2.2.1
  have hSup : SupremumLaws J E Domains F Muls Costs := by
    intro i j N L m n V W t hi hj hij hN hL hm hn hV0 hW ht x y fx fy cap hfx hfy hCap
    obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
    obtain ⟨Dj,mj,ej,aj,Hj,Cj,Kj,fj,r_j,d_j,m_j,u_j,a_j,h_j,c_j,k_j,f_j,o_j,b_j,p_j,self_j⟩ := get j hj
    have eqDi := function_unique cD.1 d_i hN
    subst Di
    have eqmi := function_unique cm.1 m_i hm
    subst mi
    have eqCi := function_unique cC.1 c_i hV0
    subst Ci
    have eqDj := function_unique cD.1 d_j hL
    subst Dj
    have eqmj := function_unique cm.1 m_j hn
    subst mj
    have eqCj := function_unique cC.1 c_j hW
    subst Cj
    have hMap := (maps hi hj hij r_i r_j ht).1
    obtain ⟨_,_,cap0,_,_,_,hOld,hNew,_⟩ := hMap.2.2.2.2.2.2 x y fx fy hfx hfy
    exact (ConstructionProbeCostSupremum.cap_unique hM hOld hCap) ▸ hNew
  have hCon : ConicalFamily J Domains Muls Units := by
    intro i N m u hi hN hm hu
    obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
    have eqDi := function_unique cD.1 d_i hN
    subst Di
    have eqmi := function_unique cm.1 m_i hm
    subst mi
    have eqei := function_unique ce.1 u_i hu
    subst ei
    exact o_i.2.1
  have hJoins : JoinsFamily J Domains Muls Units := by
    intro i N m u hi hN hm hu
    obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
    have eqDi := function_unique cD.1 d_i hN
    subst Di
    have eqmi := function_unique cm.1 m_i hm
    subst mi
    have eqei := function_unique ce.1 u_i hu
    subst ei
    exact o_i.2.2.1
  have hMarks : ConstructionDirectedMarks.MarkFamily J Domains Units Marks := by
    refine ⟨ca.1,?_⟩
    intro i N u a hi hN hu ha
    obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
    have eqDi := function_unique cD.1 d_i hN
    subst Di
    have eqei := function_unique ce.1 u_i hu
    subst ei
    have eqai := function_unique ca.1 a_i ha
    subst ai
    exact ⟨o_i.2.2.2.1,o_i.2.2.2.2.1⟩
  have hMarkStable : ConstructionDirectedMarks.Stable J E Domains F Marks := by
    intro i j a b hij ha hab
    have hi := hab.1.1
    have hj := hab.2.1.1
    obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
    obtain ⟨Dj,mj,ej,aj,Hj,Cj,Kj,fj,r_j,d_j,m_j,u_j,a_j,h_j,c_j,k_j,f_j,o_j,b_j,p_j,self_j⟩ := get j hj
    have eqai := function_unique ca.1 a_i ha
    subst ai
    obtain ⟨f,hf,hfab⟩ := hab.2.2
    have hm := (maps hi hj hij r_i r_j hf).1
    have hMaps : MapsTo Di Dj f := hm.1.1.1
    have he := function_unique hMaps.1 hfab hm.2.2.2.1
    exact he.symm ▸ a_j
  have hProfiles : ProfileTransitions w J E Domains F Muls := by
    intro i j N L m n t hi hj hij hN hL hm hn ht
    obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
    obtain ⟨Dj,mj,ej,aj,Hj,Cj,Kj,fj,r_j,d_j,m_j,u_j,a_j,h_j,c_j,k_j,f_j,o_j,b_j,p_j,self_j⟩ := get j hj
    have eqDi := function_unique cD.1 d_i hN
    subst Di
    have eqmi := function_unique cm.1 m_i hm
    subst mi
    have eqDj := function_unique cD.1 d_j hL
    subst Dj
    have eqmj := function_unique cm.1 m_j hn
    subst mj
    exact (maps hi hj hij r_i r_j ht).2
  have hOrigins : OriginLegs hM w Q J Domains Muls Units Marks Heights Costs Origins D mul e mark H C := by
    refine ⟨cB.1,?_⟩
    intro i N m u a W V f hi hN hm hu ha hW hV0 hf
    obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
    have eqDi := function_unique cD.1 d_i hN
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
    have eqfi := function_unique cB.1 f_i hf
    subst fi
    exact b_i
  have hNat : OriginNatural J E F Origins := by
    intro i j f g t hi hj hij hf hg ht
    obtain ⟨K,hK⟩ := ConstructionTowerHistory.field_total 6 hV.1 hj
    have bij := ((hE.2 i j).mp hij).2.2
    exact hV.2.2.2.2 i j f g K t hi hj bij
      ((cB.2 i f).mp hf).2 ((cB.2 j g).mp hg).2 hK
      ((ConstructionTowerTransitions.matrix_at hV.1 hF hi hj bij hK).mp ht)
  have hOP : OriginProfiles w J Domains Muls Origins D mul := by
    intro i N m f hi hN hm hf
    obtain ⟨Di,mi,ei,ai,Hi,Ci,Ki,fi,r_i,d_i,m_i,u_i,a_i,h_i,c_i,k_i,f_i,o_i,b_i,p_i,self_i⟩ := get i hi
    have eqDi := function_unique cD.1 d_i hN
    subst Di
    have eqmi := function_unique cm.1 m_i hm
    subst mi
    have eqfi := function_unique cB.1 f_i hf
    subst fi
    exact p_i
  exact ⟨hIndex,hTransitions,hFamily,hHom,hCons,hWH,hWC,hStableH,hStableC,hHB,hCB,
    hUniform,hSup,hCon,hJoins,hMarks,hMarkStable,hProfiles,hOrigins,hNat,hOP⟩


def data {m : Nat} (w Q R top D mul e mark H C J E Domains F Muls Units Marks Heights Costs Origins : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionDirectedSystem.indexLaws J E) (.conj (ConstructionDirectedSystem.transitionLaws J E
  Domains F) (.conj (ConstructionDirectedMonoidData.family J Domains Muls Units) (.conj
  (ConstructionDirectedMonoidData.homLaws J E Domains F Muls Units) (.conj
  (ConstructionDirectedConservativeData.conservativeTransitions J E Domains F Muls) (.conj
  (ConstructionDirectedWeightData.weightFamily J Domains R Heights) (.conj
  (ConstructionDirectedWeightData.weightFamily J Domains R Costs) (.conj
  (ConstructionDirectedWeightData.stable J E Domains F Heights) (.conj
  (ConstructionDirectedWeightData.stable J E Domains F Costs) (.conj
  (ConstructionDirectedWeightData.heightBounds J Heights top) (.conj
  (ConstructionDirectedWeightData.costBounds J Costs top) (.conj
  (ConstructionDirectedWeightData.uniformFamily w Q J Domains Muls Heights Costs) (.conj
  (ConstructionDirectedWeightData.supremumLaws J E Domains F Muls Costs) (.conj
  (ConstructionDirectedMonoidData.conicalFamily J Domains Muls Units) (.conj
  (ConstructionDirectedConservativeData.joinsFamily J Domains Muls Units) (.conj
  (ConstructionDirectedMarks.markFamily J Domains Units Marks) (.conj (ConstructionDirectedMarks.stable J E
  Domains F Marks) (.conj (ConstructionTowerLimit.profileTransitions w J E Domains F Muls) (.conj
  (ConstructionTowerLimit.originLegs w Q J Domains Muls Units Marks Heights Costs Origins D mul e mark H C)
  (.conj (ConstructionTowerLimit.originNatural J E F Origins) (ConstructionTowerLimit.originProfiles w J
  Domains Muls Origins D mul)))))))))))))))))))))

theorem data_freeClosed {m : Nat} (w Q R top D mul e mark H C J E Domains F Muls Units Marks Heights Costs Origins : Fin m) :
    (data w Q R top D mul e mark H C J E Domains F Muls Units Marks Heights Costs Origins).FreeClosed := by
  simp -implicitDefEqProofs [data,Definitional.Formula.FreeClosed,ConstructionDirectedSystem.indexLaws_freeClosed,ConstructionDirectedSystem.transitionLaws_freeClosed,ConstructionDirectedMonoidData.family_freeClosed,ConstructionDirectedMonoidData.homLaws_freeClosed,ConstructionDirectedConservativeData.conservativeTransitions_freeClosed,ConstructionDirectedWeightData.weightFamily_freeClosed,ConstructionDirectedWeightData.stable_freeClosed,ConstructionDirectedWeightData.heightBounds_freeClosed,ConstructionDirectedWeightData.costBounds_freeClosed,ConstructionDirectedWeightData.uniformFamily_freeClosed,ConstructionDirectedWeightData.supremumLaws_freeClosed,ConstructionDirectedMonoidData.conicalFamily_freeClosed,ConstructionDirectedConservativeData.joinsFamily_freeClosed,ConstructionDirectedMarks.markFamily_freeClosed,ConstructionDirectedMarks.stable_freeClosed,ConstructionTowerLimit.profileTransitions_freeClosed,ConstructionTowerLimit.originLegs_freeClosed,ConstructionTowerLimit.originNatural_freeClosed,ConstructionTowerLimit.originProfiles_freeClosed]

theorem data_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C J E Domains F Muls Units Marks Heights Costs Origins : Fin m) :
    Project.Formula.satisfies env (data w Q R top D mul e mark H C J E Domains F Muls Units Marks Heights Costs Origins) ↔ Data hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) (env.bound Muls) (env.bound Units) (env.bound Marks) (env.bound Heights) (env.bound Costs) (env.bound Origins) := by
  simp only [data,Data,
    Project.Formula.satisfies_conj_iff,
    
    ConstructionDirectedSystem.indexLaws_semantics hM,ConstructionDirectedSystem.transitionLaws_semantics hM,ConstructionDirectedMonoidData.family_semantics hM,ConstructionDirectedMonoidData.homLaws_semantics hM,ConstructionDirectedConservativeData.conservativeTransitions_semantics hM,ConstructionDirectedWeightData.weightFamily_semantics hM,ConstructionDirectedWeightData.stable_semantics hM,ConstructionDirectedWeightData.heightBounds_semantics hM,ConstructionDirectedWeightData.costBounds_semantics hM,ConstructionDirectedWeightData.uniformFamily_semantics hM,ConstructionDirectedWeightData.supremumLaws_semantics hM,ConstructionDirectedMonoidData.conicalFamily_semantics hM,ConstructionDirectedConservativeData.joinsFamily_semantics hM,ConstructionDirectedMarks.markFamily_semantics hM,ConstructionDirectedMarks.stable_semantics hM,ConstructionTowerLimit.profileTransitions_semantics hM,ConstructionTowerLimit.originLegs_semantics hM,ConstructionTowerLimit.originNatural_semantics hM,ConstructionTowerLimit.originProfiles_semantics hM]


theorem exists_data (hM : FirstOrder.Theory.Models M nativeZF)
    (zero : M.Carrier .set)
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hV : Valid hM w Q R top D mul e mark H C J S) :
    ∃ Domains Muls Units Marks Heights Costs Incoming Origins Times E P F,
      Charts J S Domains Muls Units Marks Heights Costs Incoming Origins Times ∧
      Order J E ∧ Matrix J S zero P F ∧
      Data hM w Q R top D mul e mark H C J E Domains F Muls Units Marks Heights Costs Origins := by
  obtain ⟨Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,hCharts,_,hE,hF,_⟩ :=
    ConstructionTowerTransitions.exists_tables hM zero hV.1 (ConstructionTowerValidity.incoming_rows hM hV)
  exact ⟨Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,
    hCharts,hE,hF,data_of_valid hM hJ hV hCharts hE hF⟩

def extractionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 13 (.imp (Project.Formula.isOrdinal (.bound (10 : Fin 13))) (.imp
    (ConstructionTowerValidity.valid (0 : Fin 13) (1 : Fin 13) (2 : Fin 13) (3 : Fin 13) (4 : Fin 13) (5 :
    Fin 13) (6 : Fin 13) (7 : Fin 13) (8 : Fin 13) (9 : Fin 13) (10 : Fin 13) (11 : Fin 13)) (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.conj (ConstructionTowerHistory.charts (10 : Fin
    13).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (11 : Fin
    13).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (11 : Fin 25) (10 : Fin 25) (9 : Fin 25)
    (8 : Fin 25) (7 : Fin 25) (6 : Fin 25) (5 : Fin 25) (4 : Fin 25) (3 : Fin 25)) (.conj
    (ConstructionTowerTransitions.order (10 : Fin
    13).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin 25)) (.conj
    (ConstructionTowerTransitions.matrix (10 : Fin
    13).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (11 : Fin
    13).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin
    13).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin 25) (0 : Fin 25)) (data (0 :
    Fin 13).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
    13).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin
    13).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
    13).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin
    13).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin
    13).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin
    13).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin
    13).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin
    13).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin
    13).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (10 : Fin
    13).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin 25) (11 : Fin 25) (0 : Fin 25)
    (10 : Fin 25) (9 : Fin 25) (8 : Fin 25) (7 : Fin 25) (6 : Fin 25) (4 : Fin 25))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOrdinal,
      ConstructionTowerValidity.valid_freeClosed,ConstructionTowerHistory.charts_freeClosed,
      ConstructionTowerTransitions.order_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,data_freeClosed]

theorem extraction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence extractionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) extractionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_isOrdinal_iff,Project.Term.eval_bound,
    ConstructionTowerValidity.valid_semantics hM,ConstructionTowerHistory.charts_semantics hM,
    ConstructionTowerTransitions.order_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,data_semantics hM]
  exact fun hJ hV => exists_data hM (bound 12) hJ hV

theorem extraction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence extractionSentence) := ModelTransfer.derives (fun _ hM => extraction_models hM)

end PPAC.Migration.ConstructionTowerDiagram
