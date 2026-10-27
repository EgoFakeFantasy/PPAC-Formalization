/- Pinned Round.step/fromBase/map_succ as ONE deterministic stage packet.
Consume the SAME selected complete successor and existing all-old-leg update;
append its OWN actual identity leg. The common codec has six Object fields,
full incoming family, fromBase and the ACTUAL new internal index J. -/
import PPAC.Migration.ConstructionTowerInitial

namespace PPAC.Migration.ConstructionTowerCanonicalSuccessor
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (FunctionOn)
open ConstructionRoundFields
open ConstructionDirectedWeightData (WeightFamily Stable)
open ConstructionTowerSuccessor (FullLegs ProfileLegs BaseNatural Extended)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Value (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request
      J E Domains F Muls Units Marks Heights Costs K Origins next output : M.Carrier .set) : Prop :=
  ∃ raw W G unitW markW HL LC O baseW roots Out identity NewDomains NewOut,
    Extended hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request
      J E Domains F Muls Units Marks Heights Costs K Origins raw ∧
    ConstructionRoundSelection.Pack W G unitW markW HL LC O baseW roots raw ∧
    ConstructionTowerSuccessor.Graph J Domains K O W Out ∧ WeightFamily J Domains W Out ∧
    ConstructionTowerSuccessor.SelfExtension J next Domains Out W identity NewDomains NewOut ∧
    ConstructionRoundSelection.Pack W G unitW markW HL LC NewOut baseW J output

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request
      J E Domains F Muls Units Marks Heights Costs K Origins next x y : M.Carrier .set}
    (hx : Value hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request J E Domains F Muls Units Marks Heights Costs K Origins next x)
    (hy : Value hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request J E Domains F Muls Units Marks Heights Costs K Origins next y) : x = y := by
  obtain ⟨raw,W,G,unitW,markW,HL,LC,O,baseW,roots,Out,identity,NewDomains,NewOut,hExt,hRaw,hGraph,hOut,hSelf,hPack⟩ := hx
  obtain ⟨raw',W',G',unitW',markW',HL',LC',O',baseW',roots',Out',identity',NewDomains',NewOut',hExt',hRaw',hGraph',hOut',hSelf',hPack'⟩ := hy
  have heRaw := ConstructionRoundSelection.picked_unique hM hOrder hExt.1 hExt'.1
  subst raw'
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := ConstructionRoundSelection.pack_injective hRaw hRaw'
  have hCopy := hExt
  obtain ⟨_,W0,G0,unit0,mark0,H0,C0,O0,base0,roots0,Out0,hRaw0,_,_,_,_,_,_,_,_,_,_,hUnique⟩ := hCopy
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := ConstructionRoundSelection.pack_injective hRaw0 hRaw
  have heOut := (hUnique Out hOut.1 hGraph).trans (hUnique Out' hOut'.1 hGraph').symm
  subst Out'
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionTowerCanonicalLimit.self_unique hM hSelf hSelf'
  exact ConstructionTowerCanonicalLimit.packet_unique hM hPack hPack'

theorem exists_value (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w Q R top zero one u D mul e mark H C N mulN eN markN HN CN f request
      J E Domains F Muls Units Marks Heights Costs K Origins next : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : ConstructionRealCuts.CutCarrier hM w Q R)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (htop : ConstructionRealCuts.Principal hM w Q u top)
    (hObjD : ObjectFields hM w Q R top D mul e mark H C)
    (hObjN : ObjectFields hM w Q R top N mulN eN markN HN CN)
    (hf : MapFields hM w Q D N mul mulN e eN mark markN H C HN CN f)
    (hq : ConstructionRequestSchedule.Request w D mul e zero one request)
    (hK : WeightFamily J Domains N K) (hStable : Stable J E Domains F K)
    (hFull : FullLegs hM w Q J Domains Muls Units Marks Heights Costs K N mulN eN markN HN CN)
    (hProfiles : ProfileLegs w J Domains Muls K N mulN)
    (hNatural : BaseNatural J Origins K f)
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hNext : (Project.FirstOrderSemantics.reduct M).IsOrdinal next)
    (hSucc : (Project.FirstOrderSemantics.reduct M).SuccessorOf next J) :

    ∃ output, Value hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request J E Domains F Muls Units Marks Heights Costs K Origins next output ∧
      ∀ other, Value hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request J E Domains F Muls Units Marks Heights Costs K Origins next other → other = output := by
  obtain ⟨raw,hExt,_⟩ := ConstructionTowerSuccessor.exists_extended hM hOrder
    hw hz hzw hQ hR hu hone htop hObjD hObjN hf hq hK hStable hFull hProfiles hNatural
  have hCopy := hExt
  obtain ⟨_,W,G,unitW,markW,HL,LC,O,baseW,roots,Out,hRaw,_,_,hGraph,hOut,_,_,hFullW,_,_,_,_⟩ := hCopy
  obtain ⟨identity,NewDomains,NewOut,hSelf⟩ :=
    ConstructionTowerSuccessor.exists_self_extension hM hJ hNext hSucc hFullW.1 hOut
  obtain ⟨output,hPack⟩ := ConstructionRoundSelection.pack_exists hM W G unitW markW HL LC NewOut baseW J
  have hV : Value hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request J E Domains F Muls Units Marks Heights Costs K Origins next output :=
    ⟨raw,W,G,unitW,markW,HL,LC,O,baseW,roots,Out,identity,NewDomains,NewOut,hExt,hRaw,hGraph,hOut,hSelf,hPack⟩
  exact ⟨output,hV,fun other hOther => value_unique hM hOrder hOther hV⟩

def value {m : Nat} (w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request J E Domains F Muls Units Marks Heights Costs K Origins next output : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionTowerSuccessor.extended
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  N.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mulN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  eN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  markN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  HN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  CN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  request.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  E.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Domains.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  F.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Muls.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Units.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Marks.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Heights.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Costs.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Origins.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (13 : Fin (m+14))) (.conj
  (ConstructionRoundSelection.pack (12 : Fin (m+14)) (11 : Fin (m+14)) (10 : Fin (m+14)) (9 : Fin (m+14)) (8
  : Fin (m+14)) (7 : Fin (m+14)) (6 : Fin (m+14)) (5 : Fin (m+14)) (4 : Fin (m+14)) (13 : Fin (m+14)))
  (.conj (ConstructionTowerSuccessor.graph
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Domains.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+14)) (12 : Fin (m+14))
  (3 : Fin (m+14))) (.conj (ConstructionDirectedWeightData.weightFamily
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Domains.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin (m+14)) (3 : Fin
  (m+14))) (.conj (ConstructionTowerSuccessor.selfExtension
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  next.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Domains.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin (m+14)) (12 : Fin
  (m+14)) (2 : Fin (m+14)) (1 : Fin (m+14)) (0 : Fin (m+14))) (ConstructionRoundSelection.pack (12 : Fin
  (m+14)) (11 : Fin (m+14)) (10 : Fin (m+14)) (9 : Fin (m+14)) (8 : Fin (m+14)) (7 : Fin (m+14)) (0 : Fin
  (m+14)) (5 : Fin (m+14)) J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  output.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))))))))))))))))))))

theorem value_freeClosed {m : Nat} (w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request J E Domains F Muls Units Marks Heights Costs K Origins next output : Fin m) :
    (value w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request J E Domains F Muls Units Marks Heights Costs K Origins next output).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,ConstructionTowerSuccessor.extended_freeClosed,ConstructionRoundSelection.pack_freeClosed,ConstructionTowerSuccessor.graph_freeClosed,ConstructionDirectedWeightData.weightFamily_freeClosed,ConstructionTowerSuccessor.selfExtension_freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request J E Domains F Muls Units Marks Heights Costs K Origins next output : Fin m) :
    Project.Formula.satisfies env (value w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request J E Domains F Muls Units Marks Heights Costs K Origins next output) ↔ Value hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound zero) (env.bound one) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound N) (env.bound mulN) (env.bound eN) (env.bound markN) (env.bound HN) (env.bound CN) (env.bound f) (env.bound request) (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) (env.bound Muls) (env.bound Units) (env.bound Marks) (env.bound Heights) (env.bound Costs) (env.bound K) (env.bound Origins) (env.bound next) (env.bound output) := by
  simp only [value,Value,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    
    ConstructionTowerSuccessor.extended_semantics hM,ConstructionRoundSelection.pack_semantics hM,ConstructionTowerSuccessor.graph_semantics hM,ConstructionDirectedWeightData.weightFamily_semantics hM,ConstructionTowerSuccessor.selfExtension_semantics hM]
  rfl


def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 33 (.imp (Project.Formula.isOmega (.bound (0 : Fin 33))) (.imp
    (Project.Formula.isEmpty (.bound (4 : Fin 33))) (.imp (.mem (.bound (4 : Fin 33)) (.bound (0 : Fin 33)))
    (.imp (ConstructionFractionOrder.carrier (0 : Fin 33) (1 : Fin 33)) (.imp
    (ConstructionRealCuts.cutCarrier (0 : Fin 33) (1 : Fin 33) (2 : Fin 33)) (.imp
    (ConstructionFractionOrder.coordinates (0 : Fin 33) (32 : Fin 33) (5 : Fin 33) (5 : Fin 33)) (.imp
    (Project.Formula.isOrdinalOne (.bound (5 : Fin 33))) (.imp (ConstructionRealCuts.principal (0 : Fin 33)
    (1 : Fin 33) (32 : Fin 33) (3 : Fin 33)) (.imp (ConstructionRoundStepSyntax.objectFields (0 : Fin 33) (1
    : Fin 33) (2 : Fin 33) (3 : Fin 33) (6 : Fin 33) (7 : Fin 33) (8 : Fin 33) (9 : Fin 33) (10 : Fin 33)
    (11 : Fin 33)) (.imp (ConstructionRoundStepSyntax.objectFields (0 : Fin 33) (1 : Fin 33) (2 : Fin 33) (3
    : Fin 33) (12 : Fin 33) (13 : Fin 33) (14 : Fin 33) (15 : Fin 33) (16 : Fin 33) (17 : Fin 33)) (.imp
    (ConstructionRoundStepSyntax.mapFields (0 : Fin 33) (1 : Fin 33) (6 : Fin 33) (12 : Fin 33) (7 : Fin 33)
    (13 : Fin 33) (8 : Fin 33) (14 : Fin 33) (9 : Fin 33) (15 : Fin 33) (10 : Fin 33) (11 : Fin 33) (16 :
    Fin 33) (17 : Fin 33) (18 : Fin 33)) (.imp (ConstructionRequestSchedule.request (0 : Fin 33) (6 : Fin
    33) (7 : Fin 33) (8 : Fin 33) (4 : Fin 33) (5 : Fin 33) (19 : Fin 33)) (.imp
    (ConstructionDirectedWeightData.weightFamily (20 : Fin 33) (22 : Fin 33) (12 : Fin 33) (29 : Fin 33))
    (.imp (ConstructionDirectedWeightData.stable (20 : Fin 33) (21 : Fin 33) (22 : Fin 33) (23 : Fin 33) (29
    : Fin 33)) (.imp (ConstructionTowerSuccessor.fullLegs (0 : Fin 33) (1 : Fin 33) (20 : Fin 33) (22 : Fin
    33) (24 : Fin 33) (25 : Fin 33) (26 : Fin 33) (27 : Fin 33) (28 : Fin 33) (29 : Fin 33) (12 : Fin 33)
    (13 : Fin 33) (14 : Fin 33) (15 : Fin 33) (16 : Fin 33) (17 : Fin 33)) (.imp
    (ConstructionTowerSuccessor.profileLegs (0 : Fin 33) (20 : Fin 33) (22 : Fin 33) (24 : Fin 33) (29 : Fin
    33) (12 : Fin 33) (13 : Fin 33)) (.imp (ConstructionTowerSuccessor.baseNatural (20 : Fin 33) (30 : Fin
    33) (29 : Fin 33) (18 : Fin 33)) (.imp (Project.Formula.isOrdinal (.bound (20 : Fin 33))) (.imp
    (Project.Formula.isOrdinal (.bound (31 : Fin 33))) (.imp (.forallE (.iff (.mem (.bound (0 : Fin 34))
    (.bound (31 : Fin 33).succ)) (.disj (.mem (.bound (0 : Fin 34)) (.bound (20 : Fin 33).succ))
    (Project.Formula.extensionalEq (.bound (0 : Fin 34)) (.bound (20 : Fin 33).succ))))) (.existsE (.conj
    (value (0 : Fin 33).succ (1 : Fin 33).succ (2 : Fin 33).succ (3 : Fin 33).succ (4 : Fin 33).succ (5 :
    Fin 33).succ (6 : Fin 33).succ (7 : Fin 33).succ (8 : Fin 33).succ (9 : Fin 33).succ (10 : Fin 33).succ
    (11 : Fin 33).succ (12 : Fin 33).succ (13 : Fin 33).succ (14 : Fin 33).succ (15 : Fin 33).succ (16 : Fin
    33).succ (17 : Fin 33).succ (18 : Fin 33).succ (19 : Fin 33).succ (20 : Fin 33).succ (21 : Fin 33).succ
    (22 : Fin 33).succ (23 : Fin 33).succ (24 : Fin 33).succ (25 : Fin 33).succ (26 : Fin 33).succ (27 : Fin
    33).succ (28 : Fin 33).succ (29 : Fin 33).succ (30 : Fin 33).succ (31 : Fin 33).succ (0 : Fin 34))
    (.forallE (.imp (value (0 : Fin 33).succ.succ (1 : Fin 33).succ.succ (2 : Fin 33).succ.succ (3 : Fin
    33).succ.succ (4 : Fin 33).succ.succ (5 : Fin 33).succ.succ (6 : Fin 33).succ.succ (7 : Fin
    33).succ.succ (8 : Fin 33).succ.succ (9 : Fin 33).succ.succ (10 : Fin 33).succ.succ (11 : Fin
    33).succ.succ (12 : Fin 33).succ.succ (13 : Fin 33).succ.succ (14 : Fin 33).succ.succ (15 : Fin
    33).succ.succ (16 : Fin 33).succ.succ (17 : Fin 33).succ.succ (18 : Fin 33).succ.succ (19 : Fin
    33).succ.succ (20 : Fin 33).succ.succ (21 : Fin 33).succ.succ (22 : Fin 33).succ.succ (23 : Fin
    33).succ.succ (24 : Fin 33).succ.succ (25 : Fin 33).succ.succ (26 : Fin 33).succ.succ (27 : Fin
    33).succ.succ (28 : Fin 33).succ.succ (29 : Fin 33).succ.succ (30 : Fin 33).succ.succ (31 : Fin
    33).succ.succ (0 : Fin 35)) (Project.Formula.extensionalEq (.bound (0 : Fin 35)) (.bound (0 : Fin
    34).succ)))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,Project.Formula.isEmpty,
      Project.Formula.isOrdinalOne,Project.Formula.isOrdinal,Project.Formula.extensionalEq,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,
      ConstructionFractionOrder.coordinates_freeClosed,ConstructionRealCuts.principal_freeClosed,
      ConstructionRoundStepSyntax.objectFields_freeClosed,ConstructionRoundStepSyntax.mapFields_freeClosed,
      ConstructionRequestSchedule.request_freeClosed,ConstructionDirectedWeightData.weightFamily_freeClosed,
      ConstructionDirectedWeightData.stable_freeClosed,ConstructionTowerSuccessor.fullLegs_freeClosed,
      ConstructionTowerSuccessor.profileLegs_freeClosed,ConstructionTowerSuccessor.baseNatural_freeClosed,value_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M))) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isOrdinal_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_disj_iff,
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    ConstructionFractionOrder.coordinates_semantics hM,Project.Formula.satisfies_isOrdinalOne_iff,
    ConstructionRealCuts.principal_semantics hM,ConstructionRoundStepSyntax.objectFields_semantics hM,
    ConstructionRoundStepSyntax.mapFields_semantics hM,ConstructionRequestSchedule.request_semantics hM,
    ConstructionDirectedWeightData.weightFamily_semantics hM,ConstructionDirectedWeightData.stable_semantics hM,
    ConstructionTowerSuccessor.fullLegs_semantics hM,ConstructionTowerSuccessor.profileLegs_semantics hM,
    ConstructionTowerSuccessor.baseNatural_semantics hM,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,value_semantics hM,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  intro hw hz hzw hQ hR hu hone htop hObjD hObjN hf hq hK hStable hFull hProfiles hNatural hJ hNext hSucc
  have hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf (bound 31) (bound 20) := by
    intro x
    have h := hSucc x
    change ((Project.FirstOrderSemantics.reduct M).mem x (bound 31) ↔
      (Project.FirstOrderSemantics.reduct M).mem x (bound 20) ∨ x = bound 20) at h
    exact h.trans (or_congr Iff.rfl ⟨(fun he => by subst x; exact fun _ => Iff.rfl),
      fun he => (ModelTransfer.extensionality hM).eq_of_same_members x (bound 20) he⟩)
  exact exists_value hM hOrder hw hz hzw hQ hR hu hone htop hObjD hObjN hf hq hK hStable hFull hProfiles hNatural hJ hNext hs

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative constructionSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  apply ConstructibleGround.relative_models hM constructionSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality (ConstructibleSource.model_zf hM)) constructionSentence).mp
    (construction_models (ConstructibleSource.model_zf hM) (ConstructionRoundSelection.l_order hM))

end PPAC.Migration.ConstructionTowerCanonicalSuccessor
