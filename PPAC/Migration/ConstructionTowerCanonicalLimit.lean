/- Pinned ConstructionIteration at limits: the ALREADY CONSTRUCTED canonical
Under-base limit determines ONE actual state packet. Use the retained
quotient/projection/function-graph equations; do not choose a different
isomorphic limit or introduce a second class-choice/recursion backend. -/
import PPAC.Migration.ConstructionTowerLimit

namespace PPAC.Migration.ConstructionTowerCanonicalLimit
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (FunctionOn function_unique)
open ConstructionProbeMappedPath (NodeMap)
open ConstructionDirectedSystem
open ConstructionDirectedMonoidData (Family HomLaws ConicalFamily)
open ConstructionDirectedConservativeData (ConservativeTransitions JoinsFamily)
open ConstructionDirectedWeightData (WeightFamily Stable HeightBounds CostBounds UniformFamily SupremumLaws)
open ConstructionRealCuts (CutCarrier Cut)
open ConstructionTowerLimit (ProfileTransitions OriginLegs OriginNatural OriginProfiles)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem table_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {J Domains Muls projection L B G H : M.Carrier .set}
    (hB : ConstructionProbeLetters.Representatives L L B)
    (hG : MapsTo B L G) (hH : MapsTo B L H)
    (hGG : ConstructionDirectedProduct.Graph J Domains Muls projection G)
    (hHG : ConstructionDirectedProduct.Graph J Domains Muls projection H) : G = H := by
  have forward {A B' : M.Carrier .set} (hA : MapsTo B L A)
      (ha : ConstructionDirectedProduct.Graph J Domains Muls projection A)
      (hb : ConstructionDirectedProduct.Graph J Domains Muls projection B')
      (q z) (hq : PureKuratowski.PairMember M q z A) : PureKuratowski.PairMember M q z B' := by
    obtain ⟨x,y,_,_,hc⟩ := (hB q).mp (ForcingConditionGraphs.function_input hA.1 hq)
    obtain ⟨q',hc',hz⟩ := (hb x y z).mpr ((ha x y z).mp ⟨q,hc,hq⟩)
    exact (KuratowskiZF.code_unique hM hc' hc) ▸ hz
  exact SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM B L G).mp hG).1.1
    ((ForcingSupportSize.native_mapsTo hM B L H).mp hH).1.1
    (fun q z => ⟨forward hG hGG hHG q z,forward hH hHG hGG q z⟩)

theorem cocone_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {J E Domains F L projection K K' : M.Carrier .set}
    (hD : FunctionOn J Domains)
    (hK : ConstructionDirectedCocone.Cocone J E Domains F L projection K)
    (hK' : ConstructionDirectedCocone.Cocone J E Domains F L projection K') : K = K' := by
  have rel {A} (hA : FunctionOn J A) :
      (Project.FirstOrderSemantics.reduct M).IsSetRelation (KuratowskiZF.interpretation hM) A := by
    intro p hp
    obtain ⟨x,y,_,hc⟩ := hA.1 p hp
    exact ⟨x,y,hc⟩
  have forward {A B} (hA : ConstructionDirectedCocone.Cocone J E Domains F L projection A)
      (hB : ConstructionDirectedCocone.Cocone J E Domains F L projection B)
      (i ki) (hki : PureKuratowski.PairMember M i ki A) : PureKuratowski.PairMember M i ki B := by
    have hi := ForcingConditionGraphs.function_input hA.1.1 hki
    obtain ⟨D,hDi,_⟩ := hD.2 i hi
    obtain ⟨kj,hkj,_⟩ := hB.1.1.2 i hi
    have heq := ConstructionDirectedCocone.stage_map_unique hM hD
      ⟨D,hDi,hA.1.2 i D ki hi hDi hki,hA.2.2 i D ki hi hDi hki⟩
      ⟨D,hDi,hB.1.2 i D kj hi hDi hkj,hB.2.2 i D kj hi hDi hkj⟩
    exact heq.symm ▸ hkj
  exact SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    (rel hK.1.1) (rel hK'.1.1)
    (fun i ki => ⟨forward hK hK' i ki,forward hK' hK i ki⟩)

/-- All EIGHT output fields are literally equal, not just isomorphic. -/
theorem result_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C
      L G unit markL HL LC K base L' G' unit' markL' HL' LC' K' base' : M.Carrier .set}
    (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i J)
    (hFam : ConstructionDirectedMonoidData.Family J Domains Muls Units)
    (h1 : ConstructionTowerLimit.Result hM J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C L G unit markL HL LC K base)
    (h2 : ConstructionTowerLimit.Result hM J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C L' G' unit' markL' HL' LC' K' base') :
    L = L' ∧ G = G' ∧ unit = unit' ∧ markL = markL' ∧ HL = HL' ∧ LC = LC' ∧ K = K' ∧ base = base' := by
  obtain ⟨rep,projection,B,hRep,hp,hCar,hProj,hB,hG,hGraph,hUnit,hMark,hWeights,hObj,hKC,hFull,_,hBase,hNat,_,_,_,hUnique⟩ := h1
  obtain ⟨rep',projection',B',hRep',hp',hCar',hProj',hB',hG',hGraph',hUnit',hMark',hWeights',hObj',hKC',hFull',_,hBase',hNat',_,_,_,_⟩ := h2
  have heRep := (ModelTransfer.extensionality hM).eq_of_same_members rep rep'
    (fun x => (hRep x).trans (hRep' x).symm)
  subst rep'
  have heL := (ModelTransfer.extensionality hM).eq_of_same_members L L'
    (fun x => (hCar x).trans (hCar' x).symm)
  subst L'
  have heProjection := SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM rep L projection).mp hp).1.1
    ((ForcingSupportSize.native_mapsTo hM rep L projection').mp hp').1.1
    (fun p c => (hProj p c).trans (hProj' p c).symm)
  subst projection'
  have heB := (ModelTransfer.extensionality hM).eq_of_same_members B B'
    (fun x => (hB x).trans (hB' x).symm)
  subst B'
  have heG := table_unique hM hB hG hG' hGraph hGraph'
  subst G'
  obtain ⟨i,hi⟩ := hne
  obtain ⟨ei,hei⟩ := ConstructionDirectedMonoidData.unit_total hFam hi
  have heUnit := ConstructionProbeHomEvaluation.product_unique hM hp (hUnit i ei hei) (hUnit' i ei hei)
  subst unit'
  obtain ⟨ai,hai,_⟩ := hFull.2.2.2.1.2 i hi
  have heMark := ConstructionProbeHomEvaluation.product_unique hM hp (hMark i ai hi hai) (hMark' i ai hi hai)
  subst markL'
  have heH := SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM L R HL).mp hWeights.1).1.1
    ((ForcingSupportSize.native_mapsTo hM L R HL').mp hWeights'.1).1.1
    (fun x y => (hWeights.2.1 x y).trans (hWeights'.2.1 x y).symm)
  subst HL'
  have heC := SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM L R LC).mp hWeights.2.2.1).1.1
    ((ForcingSupportSize.native_mapsTo hM L R LC').mp hWeights'.2.2.1).1.1
    (fun x y => (hWeights.2.2.2.1 x y).trans (hWeights'.2.2.2.1 x y).symm)
  subst LC'
  have heK := cocone_unique hM hFam.1 hKC hKC'
  subst K'
  have heBase := hUnique base' hBase'.1.1.1 hNat'
  subst base'
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem packet_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {W G e mark H C O base time x y : M.Carrier .set}
    (hx : ConstructionRoundSelection.Pack W G e mark H C O base time x)
    (hy : ConstructionRoundSelection.Pack W G e mark H C O base time y) : x = y := by
  obtain ⟨t1,t2,t3,t4,t5,t6,t7,h0,h1,h2,h3,h4,h5,h6,h7⟩ := hx
  obtain ⟨s1,s2,s3,s4,s5,s6,s7,g0,g1,g2,g3,g4,g5,g6,g7⟩ := hy
  have he := KuratowskiZF.code_unique hM h7 g7; subst s7
  have he := KuratowskiZF.code_unique hM h6 g6; subst s6
  have he := KuratowskiZF.code_unique hM h5 g5; subst s5
  have he := KuratowskiZF.code_unique hM h4 g4; subst s4
  have he := KuratowskiZF.code_unique hM h3 g3; subst s3
  have he := KuratowskiZF.code_unique hM h2 g2; subst s2
  have he := KuratowskiZF.code_unique hM h1 g1; subst s1
  exact KuratowskiZF.code_unique hM h0 g0

theorem self_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {J next Domains Out W identity NewDomains NewOut identity' NewDomains' NewOut' : M.Carrier .set}
    (h : ConstructionTowerSuccessor.SelfExtension J next Domains Out W identity NewDomains NewOut)
    (h' : ConstructionTowerSuccessor.SelfExtension J next Domains Out W identity' NewDomains' NewOut') :
    identity = identity' ∧ NewDomains = NewDomains' ∧ NewOut = NewOut' := by
  have heId := SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM W W identity).mp h.2.2.1).1.1
    ((ForcingSupportSize.native_mapsTo hM W W identity').mp h'.2.2.1).1.1
    (fun x y => (h.2.2.2.1 x y).trans (h'.2.2.2.1 x y).symm)
  subst identity'
  have rel {A} (hA : FunctionOn next A) :
      (Project.FirstOrderSemantics.reduct M).IsSetRelation (KuratowskiZF.interpretation hM) A := by
    intro p hp
    obtain ⟨a,b,_,hc⟩ := hA.1 p hp
    exact ⟨a,b,hc⟩
  have heD := SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    (rel h.1) (rel h'.1)
    (fun i D => (h.2.2.2.2.1 i D).trans (h'.2.2.2.2.1 i D).symm)
  subst NewDomains'
  have heK := SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    (rel h.2.1) (rel h'.2.1)
    (fun i k => (h.2.2.2.2.2.1 i k).trans (h'.2.2.2.2.2.1 i k).symm)
  subst NewOut'
  exact ⟨rfl,rfl,rfl⟩

/-- The existing fixed tuple codec: six Object fields, full incoming family,
fromBase, and actual internal stage index J. -/
def Value (hM : FirstOrder.Theory.Models M nativeZF)
    (J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C
      output : M.Carrier .set) : Prop :=
  ∃ L G unit markL HL LC K base next identity NewDomains NewOut,
    ConstructionTowerLimit.Result hM J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C L G unit markL HL LC K base ∧
    (Project.FirstOrderSemantics.reduct M).SuccessorOf next J ∧
    ConstructionTowerSuccessor.SelfExtension J next Domains K L identity NewDomains NewOut ∧
    ConstructionRoundSelection.Pack L G unit markL HL LC NewOut base J output

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C x y : M.Carrier .set}
    (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i J)
    (hFam : ConstructionDirectedMonoidData.Family J Domains Muls Units)
    (hx : Value hM J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C x)
    (hy : Value hM J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C y) : x = y := by
  obtain ⟨L,G,unit,markL,HL,LC,K,base,next,identity,NewDomains,NewOut,hResult,hSucc,hSelf,hPack⟩ := hx
  obtain ⟨L',G',unit',markL',HL',LC',K',base',next',identity',NewDomains',NewOut',hResult',hSucc',hSelf',hPack'⟩ := hy
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := result_unique hM hne hFam hResult hResult'
  have heNext := (ModelTransfer.extensionality hM).eq_of_same_members next next'
    (fun z => (hSucc z).trans (hSucc' z).symm)
  subst next'
  obtain ⟨rfl,rfl,rfl⟩ := self_unique hM hSelf hSelf'
  exact packet_unique hM hPack hPack'

theorem exists_value (hM : FirstOrder.Theory.Models M nativeZF)
    (J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C : M.Carrier .set)
    (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i J)
    (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hFam : Family J Domains Muls Units) (hHom : HomLaws J E Domains F Muls Units)
    (hCons : ConservativeTransitions J E Domains F Muls)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R) (hTop : Cut hM w Q top)
    (hWH : WeightFamily J Domains R Heights) (hWC : WeightFamily J Domains R Costs)
    (hStableH : Stable J E Domains F Heights) (hStableC : Stable J E Domains F Costs)
    (hHB : HeightBounds J Heights top) (hCB : CostBounds J Costs top)
    (hUniform : UniformFamily hM w Q J Domains Muls Heights Costs)
    (hSup : SupremumLaws J E Domains F Muls Costs)
    (hCon : ConicalFamily J Domains Muls Units) (hJoins : JoinsFamily J Domains Muls Units)
    (hMarks : ConstructionDirectedMarks.MarkFamily J Domains Units Marks)
    (hMarkStable : ConstructionDirectedMarks.Stable J E Domains F Marks)
    (hProfiles : ProfileTransitions w J E Domains F Muls)
    (hOrigins : OriginLegs hM w Q J Domains Muls Units Marks Heights Costs Origins D mul e mark H C)
    (hNat : OriginNatural J E F Origins) (hOP : OriginProfiles w J Domains Muls Origins D mul)
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J) :



    ∃ output, Value hM J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C output ∧
      ∀ other, Value hM J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C other → other = output := by
  obtain ⟨L,G,unit,markL,HL,LC,K,base,hResult⟩ :=
    ConstructionTowerLimit.exists_system hM J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C
      hne hE hT hFam hHom hCons hw hQ hR hTop hWH hWC hStableH hStableC hHB hCB hUniform hSup hCon hJoins hMarks hMarkStable hProfiles hOrigins hNat hOP
  have hCopy := hResult
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hKC,_,_,_,_,_,_,_,_⟩ := hCopy
  have hKP := ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)
  obtain ⟨next,hSucc⟩ := KP.exists_successor hKP J
  have hNext := KP.successor_isOrdinal hKP hJ hSucc
  obtain ⟨identity,NewDomains,NewOut,hSelf⟩ :=
    ConstructionTowerSuccessor.exists_self_extension hM hJ hNext hSucc hFam.1 hKC.1
  obtain ⟨output,hPack⟩ := ConstructionRoundSelection.pack_exists hM L G unit markL HL LC NewOut base J
  have hV : Value hM J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C output :=
    ⟨L,G,unit,markL,HL,LC,K,base,next,identity,NewDomains,NewOut,hResult,hSucc,hSelf,hPack⟩
  exact ⟨output,hV,fun other hOther => value_unique hM hne hFam hOther hV⟩


def value {m : Nat} (J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C output : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.conj (ConstructionTowerLimit.result
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  E.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Domains.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  F.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Muls.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Units.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Heights.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Costs.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Marks.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Origins.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (11 : Fin (m+12)) (10 : Fin (m+12)) (9 : Fin
  (m+12)) (8 : Fin (m+12)) (7 : Fin (m+12)) (6 : Fin (m+12)) (5 : Fin (m+12)) (4 : Fin (m+12))) (.conj
  (Project.Formula.isSuccessor (.bound (3 : Fin (m+12))) (.bound
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.conj
  (ConstructionTowerSuccessor.selfExtension J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3
  : Fin (m+12)) Domains.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin (m+12)) (11 :
  Fin (m+12)) (2 : Fin (m+12)) (1 : Fin (m+12)) (0 : Fin (m+12))) (ConstructionRoundSelection.pack (11 : Fin
  (m+12)) (10 : Fin (m+12)) (9 : Fin (m+12)) (8 : Fin (m+12)) (7 : Fin (m+12)) (6 : Fin (m+12)) (0 : Fin
  (m+12)) (4 : Fin (m+12)) J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  output.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))))))))))))))))

theorem value_freeClosed {m : Nat} (J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C output : Fin m) :
    (value J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C output).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,ConstructionTowerLimit.result_freeClosed,Project.Formula.isSuccessor,ConstructionTowerSuccessor.selfExtension_freeClosed,ConstructionRoundSelection.pack_freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C output : Fin m) :
    Project.Formula.satisfies env (value J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C output) ↔ Value hM (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) (env.bound Muls) (env.bound Units) (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound Heights) (env.bound Costs) (env.bound Marks) (env.bound Origins) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound output) := by
  simp only [value,Value,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Term.eval_bound,
    ConstructionTowerLimit.result_semantics hM,Project.Formula.satisfies_isSuccessor_iff,ConstructionTowerSuccessor.selfExtension_semantics hM,ConstructionRoundSelection.pack_semantics hM]
  rfl


def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 20 (.imp (.existsE (.mem (.bound (0 : Fin 21)) (.bound (0 : Fin 20).succ)))
    (.imp (ConstructionDirectedSystem.indexLaws (0 : Fin 20) (1 : Fin 20)) (.imp
    (ConstructionDirectedSystem.transitionLaws (0 : Fin 20) (1 : Fin 20) (2 : Fin 20) (3 : Fin 20)) (.imp
    (ConstructionDirectedMonoidData.family (0 : Fin 20) (2 : Fin 20) (4 : Fin 20) (5 : Fin 20)) (.imp
    (ConstructionDirectedMonoidData.homLaws (0 : Fin 20) (1 : Fin 20) (2 : Fin 20) (3 : Fin 20) (4 : Fin 20)
    (5 : Fin 20)) (.imp (ConstructionDirectedConservativeData.conservativeTransitions (0 : Fin 20) (1 : Fin
    20) (2 : Fin 20) (3 : Fin 20) (4 : Fin 20)) (.imp (Project.Formula.isOmega (.bound (6 : Fin 20))) (.imp
    (ConstructionFractionOrder.carrier (6 : Fin 20) (7 : Fin 20)) (.imp (ConstructionRealCuts.cutCarrier (6
    : Fin 20) (7 : Fin 20) (8 : Fin 20)) (.imp (ConstructionRealCuts.cut (6 : Fin 20) (7 : Fin 20) (9 : Fin
    20)) (.imp (ConstructionDirectedWeightData.weightFamily (0 : Fin 20) (2 : Fin 20) (8 : Fin 20) (10 : Fin
    20)) (.imp (ConstructionDirectedWeightData.weightFamily (0 : Fin 20) (2 : Fin 20) (8 : Fin 20) (11 : Fin
    20)) (.imp (ConstructionDirectedWeightData.stable (0 : Fin 20) (1 : Fin 20) (2 : Fin 20) (3 : Fin 20)
    (10 : Fin 20)) (.imp (ConstructionDirectedWeightData.stable (0 : Fin 20) (1 : Fin 20) (2 : Fin 20) (3 :
    Fin 20) (11 : Fin 20)) (.imp (ConstructionDirectedWeightData.heightBounds (0 : Fin 20) (10 : Fin 20) (9
    : Fin 20)) (.imp (ConstructionDirectedWeightData.costBounds (0 : Fin 20) (11 : Fin 20) (9 : Fin 20))
    (.imp (ConstructionDirectedWeightData.uniformFamily (6 : Fin 20) (7 : Fin 20) (0 : Fin 20) (2 : Fin 20)
    (4 : Fin 20) (10 : Fin 20) (11 : Fin 20)) (.imp (ConstructionDirectedWeightData.supremumLaws (0 : Fin
    20) (1 : Fin 20) (2 : Fin 20) (3 : Fin 20) (4 : Fin 20) (11 : Fin 20)) (.imp
    (ConstructionDirectedMonoidData.conicalFamily (0 : Fin 20) (2 : Fin 20) (4 : Fin 20) (5 : Fin 20)) (.imp
    (ConstructionDirectedConservativeData.joinsFamily (0 : Fin 20) (2 : Fin 20) (4 : Fin 20) (5 : Fin 20))
    (.imp (ConstructionDirectedMarks.markFamily (0 : Fin 20) (2 : Fin 20) (5 : Fin 20) (12 : Fin 20)) (.imp
    (ConstructionDirectedMarks.stable (0 : Fin 20) (1 : Fin 20) (2 : Fin 20) (3 : Fin 20) (12 : Fin 20))
    (.imp (ConstructionTowerLimit.profileTransitions (6 : Fin 20) (0 : Fin 20) (1 : Fin 20) (2 : Fin 20) (3
    : Fin 20) (4 : Fin 20)) (.imp (ConstructionTowerLimit.originLegs (6 : Fin 20) (7 : Fin 20) (0 : Fin 20)
    (2 : Fin 20) (4 : Fin 20) (5 : Fin 20) (12 : Fin 20) (10 : Fin 20) (11 : Fin 20) (13 : Fin 20) (14 : Fin
    20) (15 : Fin 20) (16 : Fin 20) (17 : Fin 20) (18 : Fin 20) (19 : Fin 20)) (.imp
    (ConstructionTowerLimit.originNatural (0 : Fin 20) (1 : Fin 20) (3 : Fin 20) (13 : Fin 20)) (.imp
    (ConstructionTowerLimit.originProfiles (6 : Fin 20) (0 : Fin 20) (2 : Fin 20) (4 : Fin 20) (13 : Fin 20)
    (14 : Fin 20) (15 : Fin 20)) (.imp (Project.Formula.isOrdinal (.bound (0 : Fin 20))) (.existsE (.conj
    (value (0 : Fin 20).succ (1 : Fin 20).succ (2 : Fin 20).succ (3 : Fin 20).succ (4 : Fin 20).succ (5 :
    Fin 20).succ (6 : Fin 20).succ (7 : Fin 20).succ (8 : Fin 20).succ (9 : Fin 20).succ (10 : Fin 20).succ
    (11 : Fin 20).succ (12 : Fin 20).succ (13 : Fin 20).succ (14 : Fin 20).succ (15 : Fin 20).succ (16 : Fin
    20).succ (17 : Fin 20).succ (18 : Fin 20).succ (19 : Fin 20).succ (0 : Fin 21)) (.forallE (.imp (value
    (0 : Fin 20).succ.succ (1 : Fin 20).succ.succ (2 : Fin 20).succ.succ (3 : Fin 20).succ.succ (4 : Fin
    20).succ.succ (5 : Fin 20).succ.succ (6 : Fin 20).succ.succ (7 : Fin 20).succ.succ (8 : Fin
    20).succ.succ (9 : Fin 20).succ.succ (10 : Fin 20).succ.succ (11 : Fin 20).succ.succ (12 : Fin
    20).succ.succ (13 : Fin 20).succ.succ (14 : Fin 20).succ.succ (15 : Fin 20).succ.succ (16 : Fin
    20).succ.succ (17 : Fin 20).succ.succ (18 : Fin 20).succ.succ (19 : Fin 20).succ.succ (0 : Fin 22))
    (Project.Formula.extensionalEq (.bound (0 : Fin 22)) (.bound (0 : Fin
    21).succ))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,Project.Formula.isOrdinal,Project.Formula.extensionalEq,ConstructionDirectedSystem.indexLaws_freeClosed,ConstructionDirectedSystem.transitionLaws_freeClosed,ConstructionDirectedMonoidData.family_freeClosed,ConstructionDirectedMonoidData.homLaws_freeClosed,ConstructionDirectedConservativeData.conservativeTransitions_freeClosed,ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,ConstructionRealCuts.cut_freeClosed,ConstructionDirectedWeightData.weightFamily_freeClosed,ConstructionDirectedWeightData.stable_freeClosed,ConstructionDirectedWeightData.heightBounds_freeClosed,ConstructionDirectedWeightData.costBounds_freeClosed,ConstructionDirectedWeightData.uniformFamily_freeClosed,ConstructionDirectedWeightData.supremumLaws_freeClosed,ConstructionDirectedMonoidData.conicalFamily_freeClosed,ConstructionDirectedConservativeData.joinsFamily_freeClosed,ConstructionDirectedMarks.markFamily_freeClosed,ConstructionDirectedMarks.stable_freeClosed,ConstructionTowerLimit.profileTransitions_freeClosed,ConstructionTowerLimit.originLegs_freeClosed,ConstructionTowerLimit.originNatural_freeClosed,ConstructionTowerLimit.originProfiles_freeClosed,value_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOrdinal_iff,Project.Formula.satisfies_isOmega_iff,ConstructionDirectedSystem.indexLaws_semantics hM,ConstructionDirectedSystem.transitionLaws_semantics hM,ConstructionDirectedMonoidData.family_semantics hM,ConstructionDirectedMonoidData.homLaws_semantics hM,ConstructionDirectedConservativeData.conservativeTransitions_semantics hM,ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,ConstructionRealCuts.cut_semantics hM,ConstructionDirectedWeightData.weightFamily_semantics hM,ConstructionDirectedWeightData.stable_semantics hM,ConstructionDirectedWeightData.heightBounds_semantics hM,ConstructionDirectedWeightData.costBounds_semantics hM,ConstructionDirectedWeightData.uniformFamily_semantics hM,ConstructionDirectedWeightData.supremumLaws_semantics hM,ConstructionDirectedMonoidData.conicalFamily_semantics hM,ConstructionDirectedConservativeData.joinsFamily_semantics hM,ConstructionDirectedMarks.markFamily_semantics hM,ConstructionDirectedMarks.stable_semantics hM,ConstructionTowerLimit.profileTransitions_semantics hM,ConstructionTowerLimit.originLegs_semantics hM,ConstructionTowerLimit.originNatural_semantics hM,ConstructionTowerLimit.originProfiles_semantics hM,value_semantics hM]
  exact fun hne hE hT hFam hHom hCons hw hQ hR hTop hWH hWC hStableH hStableC hHB hCB hUniform hSup hCon hJoins hMarks hMarkStable hProfiles hOrigins hNat hOP hJ =>
    exists_value hM (bound 0) (bound 1) (bound 2) (bound 3) (bound 4) (bound 5) (bound 6) (bound 7) (bound 8) (bound 9) (bound 10) (bound 11) (bound 12) (bound 13) (bound 14) (bound 15) (bound 16) (bound 17) (bound 18) (bound 19)
      hne hE hT hFam hHom hCons hw hQ hR hTop hWH hWC hStableH hStableC hHB hCB hUniform hSup hCon hJoins hMarks hMarkStable hProfiles hOrigins hNat hOP hJ

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionTowerCanonicalLimit
