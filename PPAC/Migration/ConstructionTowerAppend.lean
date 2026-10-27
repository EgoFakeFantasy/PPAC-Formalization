/- Pinned ConstructionIteration / Round.underFunctor: append one ACTUAL
normalized stage to a full valid internal history. Reuse native sequence
append and the existing full weighted fan/self-extension contracts. -/
import PPAC.Migration.ConstructionTowerHistorySuccessor

namespace PPAC.Migration.ConstructionTowerAppend
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row Records Field Charts)
open ConstructionTowerValidity (Valid row_field)
open ConstructionTowerTransitions (Before Order Matrix)
open ConstructionRoundFields (ObjectFields MapFields Profiles)
open ConstructionDirectedWeightData (WeightFamily Stable)
open ConstructionTowerSuccessor (FullLegs ProfileLegs BaseNatural SelfExtension)
open ConstructionProbeMappedPath (NodeMap)
open ForcingConditionGraphs (FunctionOn function_unique)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}
variable {w Q R top D mul e mark H C J S next S' output E Domains F Muls Units Marks
  Heights Costs Incoming Origins Times P zero W G unitW markW HL LC Out base
  identity NewDomains NewOut : M.Carrier .set}

def Append (J S output next S' : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).SuccessorOf next J ∧ FunctionOn next S' ∧
  ∀ i code, PureKuratowski.PairMember M i code S' ↔
    PureKuratowski.PairMember M i code S ∨ (i = J ∧ code = output)

theorem exists_append (hM : FirstOrder.Theory.Models M nativeZF)
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hS : FunctionOn J S) (output : M.Carrier .set) :
    ∃ next S', Append J S output next S' := by
  let rawM := Project.FirstOrderSemantics.reduct M
  let I := KuratowskiZF.interpretation hM
  have hKP := ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)
  have hSeq : rawM.IsSequenceOfLength I S J := by
    refine ⟨hJ,⟨?_,?_⟩,?_⟩
    · intro p hp
      obtain ⟨x,y,_,hc⟩ := hS.1 p hp
      exact ⟨x,y,hc⟩
    · intro x y z hy hz
      exact function_unique hS hy hz
    · intro x
      exact ⟨fun hx => by obtain ⟨y,hy,_⟩ := hS.2 x hx; exact ⟨y,hy⟩,
        fun ⟨y,hy⟩ => ForcingConditionGraphs.function_input hS hy⟩
  obtain ⟨next,hSucc⟩ := KP.exists_successor hKP J
  have hNext := KP.successor_isOrdinal hKP hJ hSucc
  obtain ⟨S',hSeq',hGraph⟩ := Structure.IsSequenceOfLength.exists_append hKP I
    (value := output) hSeq hNext hSucc
  have hFn : FunctionOn next S' := by
    constructor
    · intro p hp
      obtain ⟨x,y,hc⟩ := hSeq'.2.1.1 p hp
      exact ⟨x,y,(hSeq'.2.2 x).mpr ⟨y,p,hc,hp⟩,hc⟩
    · intro x hx
      obtain ⟨y,hy⟩ := (hSeq'.2.2 x).mp hx
      exact ⟨y,hy,fun z hz => hSeq'.2.1.2 x z y hz hy⟩
  exact ⟨next,S',hSucc,hFn,hGraph⟩

theorem preserves (hM : FirstOrder.Theory.Models M nativeZF)
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hV : Valid hM w Q R top D mul e mark H C J S)
    (hR : ConstructionRealCuts.CutCarrier hM w Q R) (hTop : ConstructionRealCuts.Cut hM w Q top)
    (hCharts : Charts J S Domains Muls Units Marks Heights Costs Incoming Origins Times)
    (hE : Order J E) (hF : Matrix J S zero P F)
    (hObj : ObjectFields hM w Q R top W G unitW markW HL LC)
    (hBase : MapFields hM w Q D W mul G e unitW mark markW H C HL LC base)
    (hBaseProfiles : Profiles w D W mul G base)
    (hOut : WeightFamily J Domains W Out)
    (hStable : Stable J E Domains F Out)
    (hFull : FullLegs hM w Q J Domains Muls Units Marks Heights Costs Out W G unitW markW HL LC)
    (hProfiles : ProfileLegs w J Domains Muls Out W G)
    (hNatural : BaseNatural J Origins Out base)
    (hSelf : SelfExtension J next Domains Out W identity NewDomains NewOut)
    (hPack : ConstructionRoundSelection.Pack W G unitW markW HL LC NewOut base J output)
    (hAppend : Append J S output next S') :
    Valid hM w Q R top D mul e mark H C next S' := by
  obtain ⟨hSucc,hFn,hEdges⟩ := hAppend
  obtain ⟨_,hNewFn,hIdMap,hId,hDG,hKG,_⟩ := hSelf
  have old_not_self : ¬ (Project.FirstOrderSemantics.reduct M).mem J J := by
    intro h
    exact hJ.wellOrder.linear.irrefl J h h
  have split {i} (hi : (Project.FirstOrderSemantics.reduct M).mem i next) :
      (Project.FirstOrderSemantics.reduct M).mem i J ∨ i = J := by
    rcases (hSucc i).mp hi with hi | he
    · exact Or.inl hi
    · exact Or.inr ((ModelTransfer.extensionality hM).eq_of_same_members i J he)
  have no_before {j} (hj : (Project.FirstOrderSemantics.reduct M).mem j J) : ¬ Before J j := by
    rintro (h | h)
    · exact old_not_self (hJ.transitive j hj J h)
    · exact old_not_self (h ▸ hj)
  have old_of_before {i j}
      (hi : (Project.FirstOrderSemantics.reduct M).mem i next)
      (hj : (Project.FirstOrderSemantics.reduct M).mem j J) (hij : Before i j) :
      (Project.FirstOrderSemantics.reduct M).mem i J := by
    rcases split hi with hi | hi
    · exact hi
    · subst i
      exact False.elim (no_before hj hij)
  have old_row {i A m u a U V K f time}
      (hi : (Project.FirstOrderSemantics.reduct M).mem i J) :
      Row S' i A m u a U V K f time ↔ Row S i A m u a U V K f time := by
    constructor
    · rintro ⟨code,hc,hp⟩
      rcases (hEdges i code).mp hc with hc | ⟨he,_⟩
      · exact ⟨code,hc,hp⟩
      · subst i
        exact False.elim (old_not_self hi)
    · rintro ⟨code,hc,hp⟩
      exact ⟨code,(hEdges i code).mpr (Or.inl hc),hp⟩
  have new_row : Row S' J W G unitW markW HL LC NewOut base J :=
    ⟨output,(hEdges J output).mpr (Or.inr ⟨rfl,rfl⟩),hPack⟩
  have records : Records next S' := by
    refine ⟨hFn,fun i hi => ?_⟩
    rcases split hi with hi | hi
    · obtain ⟨A,m,u,a,U,V,K,f,hr⟩ := hV.1.2 i hi
      exact ⟨A,m,u,a,U,V,K,f,(old_row hi).mpr hr⟩
    · subst i
      exact ⟨W,G,unitW,markW,HL,LC,NewOut,base,new_row⟩
  have old_field (k : Fin 9) {i value}
      (hi : (Project.FirstOrderSemantics.reduct M).mem i J) :
      Field k S' i value ↔ Field k S i value := by
    constructor
    · rintro ⟨A,m,u,a,U,V,K,f,time,hr,hv⟩
      exact ⟨A,m,u,a,U,V,K,f,time,(old_row hi).mp hr,hv⟩
    · rintro ⟨A,m,u,a,U,V,K,f,time,hr,hv⟩
      exact ⟨A,m,u,a,U,V,K,f,time,(old_row hi).mpr hr,hv⟩
  have new_field (k : Fin 9) {value} (hv : Field k S' J value) :
      value = (match k.val with
        | 0 => W | 1 => G | 2 => unitW | 3 => markW | 4 => HL
        | 5 => LC | 6 => NewOut | 7 => base | _ => J) :=
    ConstructionTowerHistory.field_unique k hFn hv (row_field k new_row)
  have old_leg {i ki} (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
      (hki : PureKuratowski.PairMember M i ki NewOut) : PureKuratowski.PairMember M i ki Out := by
    rcases (hKG i ki).mp hki with h | ⟨he,_⟩
    · exact h
    · subst i
      exact False.elim (old_not_self hi)
  have self_leg {ki} (hki : PureKuratowski.PairMember M J ki NewOut) : ki = identity := by
    rcases (hKG J ki).mp hki with h | ⟨_,he⟩
    · exact False.elim (old_not_self (ForcingConditionGraphs.function_input hOut.1 h))
    · exact he
  have hSelfEdge : PureKuratowski.PairMember M J identity NewOut :=
    (hKG J identity).mpr (Or.inr ⟨rfl,rfl⟩)
  have idFields := ConstructionTowerInitial.identity_fields hM hR hTop hObj hIdMap hId
  have idProfiles : Profiles w W W G G identity := ConstructionTowerInitial.identity_profiles hId
  have right_id {A g} (hg : MapsTo A W g) : NodeMap g identity g := by
    intro x y
    constructor
    · intro hxy
      exact ⟨y,hxy,(hId y y).mpr ⟨hg.2 x y hxy,rfl⟩⟩
    · rintro ⟨z,hxz,hzy⟩
      exact ((hId z y).mp hzy).2 ▸ hxz
  have full_at {i A m u a U V K f ki}
      (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
      (ri : Row S i A m u a U V K f i)
      (hki : PureKuratowski.PairMember M i ki NewOut) :
      MapFields hM w Q A W m G u unitW a markW U V HL LC ki ∧
      Profiles w A W m G ki ∧ NodeMap f ki base := by
    obtain ⟨hA,hm,hu,ha,hU,hV0,_,hf,_⟩ := ConstructionTowerHistory.charts_row hCharts hi ri
    have hk := old_leg hi hki
    exact ⟨hFull.2.2.2.2.2.2 i A m u a U V ki hi hA hm hu ha hU hV0 hk,
      hProfiles i A m ki hi hA hm hk,hNatural i f ki hi hf hk⟩
  have new_maps {i ki} (hi : (Project.FirstOrderSemantics.reduct M).mem i next)
      (hki : PureKuratowski.PairMember M i ki NewOut) : ∃ A, MapsTo A W ki := by
    rcases split hi with hi | hi
    · obtain ⟨A,m,u,a,U,V,K,f,ri⟩ := hV.1.2 i hi
      exact ⟨A,(full_at hi ri hki).1.1.1.1⟩
    · subst i
      have he := self_leg hki
      subst ki
      exact ⟨W,hIdMap⟩
  have old_comp {i j L t ki kj}
      (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
      (hj : (Project.FirstOrderSemantics.reduct M).mem j J)
      (bij : Before i j) (hL : Field 6 S j L)
      (ht : PureKuratowski.PairMember M i t L)
      (hki : PureKuratowski.PairMember M i ki NewOut)
      (hkj : PureKuratowski.PairMember M j kj NewOut) : NodeMap t kj ki := by
    obtain ⟨A,m,u,a,U,V,K,f,ri⟩ := hV.1.2 i hi
    obtain ⟨B,n,v,b,X,Y,L',g,rj⟩ := hV.1.2 j hj
    have eL := ConstructionTowerHistory.field_unique 6 hV.1.1 hL (row_field 6 rj)
    subst L
    have hm := (hV.2.2.1 i j A m u a U V K f B n v b X Y L' g t hi hj bij ri rj ht).1
    have htMaps : MapsTo A B t := hm.1.1.1
    obtain ⟨hA,_,_,_,_,_,_,_,_⟩ := ConstructionTowerHistory.charts_row hCharts hi ri
    obtain ⟨hB,_,_,_,_,_,_,_,_⟩ := ConstructionTowerHistory.charts_row hCharts hj rj
    have hkiOld := old_leg hi hki
    have hkjOld := old_leg hj hkj
    have kiMaps := hOut.2 i A ki hi hA hkiOld
    have kjMaps := hOut.2 j B kj hj hB hkjOld
    have hij := (hE.2 i j).mpr ⟨hi,hj,bij⟩
    have htF := (ConstructionTowerTransitions.matrix_at hV.1 hF hi hj bij (row_field 6 rj)).mpr ht
    have stable {x y z} (hxy : PureKuratowski.PairMember M x y t)
        (hxz : PureKuratowski.PairMember M x z ki) : PureKuratowski.PairMember M y z kj :=
      hStable i j x y z ki kj hij
        ⟨⟨hi,A,hA,ForcingConditionGraphs.function_input htMaps.1 hxy⟩,
          ⟨hj,B,hB,htMaps.2 x y hxy⟩,t,htF,hxy⟩ hkiOld hkjOld hxz
    intro x z
    constructor
    · intro hxz
      obtain ⟨y,hxy,_⟩ := htMaps.1.2 x (ForcingConditionGraphs.function_input kiMaps.1 hxz)
      exact ⟨y,hxy,stable hxy hxz⟩
    · rintro ⟨y,hxy,hyz⟩
      obtain ⟨z',hxz,_⟩ := kiMaps.1.2 x (ForcingConditionGraphs.function_input htMaps.1 hxy)
      exact (function_unique kjMaps.1 (stable hxy hxz) hyz) ▸ hxz
  refine ⟨records,?_,?_,?_,?_⟩
  · intro i hi A m u a U V K f ri
    rcases split hi with hi | hi
    · exact hV.2.1 i hi A m u a U V K f ((old_row hi).mp ri)
    · subst i
      obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,_⟩ :=
        ConstructionTowerHistory.row_unique hFn ri new_row
      exact ⟨hObj,hBase,hBaseProfiles,next,_,hSucc,hNewFn,hSelfEdge,hId⟩
  · intro i j A m u a U V K f B n v b X Y L g t hi hj bij ri rj ht
    rcases split hj with hj | hj
    · have hi0 := old_of_before hi hj bij
      exact hV.2.2.1 i j A m u a U V K f B n v b X Y L g t
        hi0 hj bij ((old_row hi0).mp ri) ((old_row hj).mp rj) ht
    · subst j
      obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,_⟩ :=
        ConstructionTowerHistory.row_unique hFn rj new_row
      rcases split hi with hi | hi
      · exact ⟨(full_at hi ((old_row hi).mp ri) ht).1,(full_at hi ((old_row hi).mp ri) ht).2.1⟩
      · subst i
        obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,_⟩ :=
          ConstructionTowerHistory.row_unique hFn ri new_row
        have et := self_leg ht
        subst t
        exact ⟨idFields,idProfiles⟩
  · intro i j k L K f g h hi hj hk bij bjk hL hK hf hg hh
    rcases split hk with hk | hk
    · have hj0 := old_of_before hj hk bjk
      have hi0 := old_of_before hi hj0 bij
      exact hV.2.2.2.1 i j k L K f g h hi0 hj0 hk bij bjk
        ((old_field 6 hj0).mp hL) ((old_field 6 hk).mp hK) hf hg hh
    · subst k
      have eK := new_field 6 hK
      subst K
      rcases split hj with hj | hj
      · have hi0 := old_of_before hi hj bij
        exact old_comp hi0 hj bij ((old_field 6 hj).mp hL) hf hh hg
      · subst j
        have eL := new_field 6 hL
        subst L
        have eg := self_leg hg
        subst g
        have efh := function_unique hNewFn hf hh
        subst h
        obtain ⟨A,hMaps⟩ := new_maps hi hf
        exact right_id hMaps
  · intro i j f g K t hi hj bij hf hg hK ht
    rcases split hj with hj | hj
    · have hi0 := old_of_before hi hj bij
      exact hV.2.2.2.2 i j f g K t hi0 hj bij
        ((old_field 7 hi0).mp hf) ((old_field 7 hj).mp hg) ((old_field 6 hj).mp hK) ht
    · subst j
      have eg := new_field 7 hg
      have eK := new_field 6 hK
      subst g; subst K
      rcases split hi with hi | hi
      · obtain ⟨A,m,u,a,U,V,L,fi,ri⟩ := hV.1.2 i hi
        have ef := ConstructionTowerHistory.field_unique 7 hV.1.1 ((old_field 7 hi).mp hf) (row_field 7 ri)
        subst f
        exact (full_at hi ri ht).2.2
      · subst i
        have ef := new_field 7 hf
        have et := self_leg ht
        subst f; subst t
        exact right_id hBase.1.1.1


def append {m : Nat} (J S output next S0 : Fin m) : Project.Formula 1 m :=
  (.conj (Project.Formula.isSuccessor (.bound next) (.bound J)) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.functionOn S0 next)) (.forallE (.forallE (.iff (ProjectSyntax.encode id
  (Source.SetLanguage.edge S0.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)))) (.disj (ProjectSyntax.encode id
  (Source.SetLanguage.edge S.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)))) (.conj
  (Project.Formula.extensionalEq (.bound (1 : Fin (m+2))) (.bound J.succ.succ))
  (Project.Formula.extensionalEq (.bound (0 : Fin (m+2))) (.bound output.succ.succ)))))))))

theorem append_freeClosed {m : Nat} (J S output next S0 : Fin m) :
    (append J S output next S0).FreeClosed := by
  simp -implicitDefEqProofs [append,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isSuccessor,Project.Formula.extensionalEq]

theorem append_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J S output next S0 : Fin m) :
    Project.Formula.satisfies env (append J S output next S0) ↔ Append (env.bound J) (env.bound S) (env.bound output) (env.bound next) (env.bound S0) := by
  simp only [append,Append,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingConditionGraphs.functionOn_semantics (M := M),Project.Formula.satisfies_isSuccessor_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl


end PPAC.Migration.ConstructionTowerAppend
