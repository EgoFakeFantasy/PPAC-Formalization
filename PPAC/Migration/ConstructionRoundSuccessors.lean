/- Pinned MonoidRounds.Request.target/inclusion/gates/preserves_profile
and Round.step. Execute BOTH accepted original weighted parent producers;
retain operation witnesses, actual full objects/maps, profiles and size bounds. -/
import PPAC.Migration.ConstructionRoundFields

namespace PPAC.Migration.ConstructionRoundSuccessors
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRoundFields
open ConstructionProbeMappedPath (NodeMap)
open ConstructionPersistentProfiles (ProbeProfile)
open ConstructionMergerRelations (Prescription Valid CopyRel)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def ProbeDone (w N mulN markN O a b node : M.Carrier .set) : Prop :=
  ∃ gen oa ob mapped, PureKuratowski.PairMember M a oa O ∧ PureKuratowski.PairMember M b ob O ∧
    NodeMap node O mapped ∧ ProbeProfile w N mulN oa ob markN gen mapped ∧
    ∀ x, ¬ PureKuratowski.PairMember M x gen O

def MergerDone (n D N mul mulN P O roots : M.Carrier .set) : Prop :=
  MapsTo n N roots ∧
    (∀ i j x y ri rj ox oy u v, PureKuratowski.PairMember M i ri roots → PureKuratowski.PairMember M j rj roots →
      PureKuratowski.PairMember M x ox O → PureKuratowski.PairMember M y oy O →
      Product mulN ri ox u → Product mulN rj oy v → (u = v ↔ CopyRel n D mul P i x j y)) ∧
    ∀ i r x, PureKuratowski.PairMember M i r roots → ¬ PureKuratowski.PairMember M x r O

theorem probe (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top zero one u D mul e mark H C a b node : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : ConstructionRealCuts.CutCarrier hM w Q R)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (htop : ConstructionRealCuts.Principal hM w Q u top)
    (hObj : ObjectFields hM w Q R top D mul e mark H C)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D) (hne : b ≠ e)
    (hPath : ConstructionProbePath.Path w D mul e zero a node) :
    ∃ W G unitW markW HL LC O,
      Successor hM w Q R top zero D mul e mark H C W G unitW markW HL LC O ∧
      ProbeDone w W G markW O a b node := by
  obtain ⟨hm,hCon,hJoins,hmark,hmarkNe,hH,hHB,hC,hCB,hUniform,_,_⟩ := hObj
  obtain ⟨S,A,E,Off,V,projection,W,unitW,J,G,O,markW,KG,P,gen,oa,ob,mapped,
    _,_,hJ,hG,_,hMon,hConW,hJoinsW,hO,hCons,hEmb,hGates,hMark,hMarkMem,hMarkNe,
    _,_,_,_,_,ha,hb',hMap,hProfile,hNotOld,hCard,hProfiles,HL,GateCap,LC,hFields,hValues⟩ :=
    ConstructionProbeParent.exists_probe hM hw hz hzw hQ hR hu hone htop hm hCon hb hne hH hHB hC hCB hUniform hJoins hmark hmarkNe hPath
  obtain ⟨hHL,_,hHBW,_,_,_,hLC,_,hCBW,hUniformW,hExactW,_,_,hSup⟩ := hFields
  have hProd : ConstructionProbeLiftHom.PreservesProducts mul G O :=
    fun x y z ox oy oz hxyz hx hy hz => hEmb.2.1 x y z ox oy oz hx hy hz hxyz
  refine ⟨W,G,unitW,markW,HL,LC,O,?_,gen,oa,ob,mapped,ha,hb',hMap,hProfile,hNotOld⟩
  exact ⟨⟨hMon,hConW,hJoinsW,hMarkMem,hMarkNe,hHL,hHBW,hLC,hCBW,hUniformW,hExactW,J,hJ,hG⟩,
    ⟨hCons,hProd,hEmb.1,hMark,fun x ox r hx => (hValues x ox r hx).1,
      fun x ox r hx => (hValues x ox r hx).2,hSup⟩,hO,hGates,hProfiles,hCard⟩

theorem merger (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top zero one u D mul e mark H C n P : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : ConstructionRealCuts.CutCarrier hM w Q R)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (htop : ConstructionRealCuts.Principal hM w Q u top)
    (hObj : ObjectFields hM w Q R top D mul e mark H C)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hnp : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i n)
    (hP : Prescription n D P) (hValid : Valid n D mul P) :
    ∃ W G unitW markW HL LC O roots,
      Successor hM w Q R top zero D mul e mark H C W G unitW markW HL LC O ∧
      MergerDone n D W mul G P O roots := by
  obtain ⟨hm,hCon,hJoins,hmark,hmarkNe,hH,hHB,hC,hCB,hUniform,_,_⟩ := hObj
  obtain ⟨Copies,L,projection,K,A,W,I,T,B,G,unitW,hParent,_,hMon,hConW,_,hJoinsW,
    O,hO,hCons,hProd,hGates,hOne,hProfiles,roots,hRoots,_,hRootLaws,Rest⟩ :=
    ConstructionMergerParent.exists_system hM hw hz hzw hm hCon hJoins hP hValid hQ hn hnp hu hone htop hR hH hHB hC hCB hUniform hmark hmarkNe
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hB,hG,_⟩ := hParent
  obtain ⟨J,CH,CC,_,_,_,_,_,_,unitHeight,Ka,add,Km,mulCut,Id,two,cap,FH,FC,
    _,_,hCard,twoW,threeW,fourW,fiveW,sixW,sevenW,eightW,quarterW,eighthW,OffW,ScaleW,FactorW,HL,LC,
    hWord,markW,hMark,hMarkMem,hMarkNe,_,hValues⟩ := Rest
  obtain ⟨hActual,hUniformW,hExactW,hSup⟩ := hWord
  obtain ⟨_,hHL,_,_,hHBW,hLC,_,hCBW,_,_⟩ := hActual
  have hOldSup : ConstructionDirectedHeightCost.OldSuprema hM w Q D W mul G C LC O := by
    intro x y ox oy hx hy
    obtain ⟨_,_,cap,hCut,hCap0,hCap1,hUnique⟩ := hSup x y ox oy ((hO x ox).mp hx) ((hO y oy).mp hy)
    obtain ⟨f0,hF0,hU0,hL0⟩ := hCap0
    obtain ⟨f1,hF1,hU1,hL1⟩ := hCap1
    exact ⟨f0,f1,cap,hF0,hF1,hCut,⟨f0,hF0,hU0,hL0⟩,⟨f1,hF1,hU1,hL1⟩,hUnique⟩
  refine ⟨W,G,unitW,markW,HL,LC,O,roots,?_,hRoots,hRootLaws.2.1,hRootLaws.2.2⟩
  exact ⟨⟨hMon,hConW,hJoinsW,hMarkMem,hMarkNe,hHL,hHBW,hLC,hCBW,hUniformW,hExactW,B,hB,hG⟩,
    ⟨hCons,hProd,hOne,hMark,fun x ox r hx => (hValues x ox r hx).1,
      fun x ox r hx => (hValues x ox r hx).2,hOldSup⟩,hO,hGates,hProfiles,hCard⟩

end PPAC.Migration.ConstructionRoundSuccessors
