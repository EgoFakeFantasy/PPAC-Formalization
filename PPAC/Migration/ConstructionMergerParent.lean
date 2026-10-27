/- Pinned MonoidBase.MergerData.extension:235 / inclusion:245 / cardinal_le:271.
Execute the ORIGINAL weighted parent/prescription and distinguished nonunit.
Retain SAME actual copies/Word/monoid/inclusion/profiles/roots, construct
complete literal Word weights and actual old supremum preservation, and derive
all cardinal bounds conditionally in the OUTPUT, never as construction premises. -/
import PPAC.Migration.ConstructionMergerWordHeightCost
import PPAC.Migration.ConstructionMergerCardinality

namespace PPAC.Migration.ConstructionMergerParent
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts (Subset Cut CutCarrier)
open ConstructionCutAddition (SumCut)
open ConstructionProbeIntervals (Strict)
open ConstructionProbeLetters (Representatives)
open ConstructionMergerCopyCones (Reaches)
open ConstructionMergerFiniteWeights (HeightValue CostValue)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
open ConstructionProbeLetterIntervals (UniformMargins MissedBound)
open ConstructionMergerHeightCost (CopiesHeightCost)
open ConstructionBaseMonoid (Divides)
open ConstructionProbeRaw (Old Cons)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    {w n D mul e P zero Q R Height Cost top one u mark : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hc : ForcingDiagramPoset.Conical D mul e)
    (hJoins : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hP : ConstructionMergerRelations.Prescription n D P) (hValid : ConstructionMergerRelations.Valid n D mul P)
    (hQ : ConstructionFractionOrder.Carrier w Q)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hnp : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i n)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : ConstructionRealCuts.Principal hM w Q u top)
    (hR : CutCarrier hM w Q R) (hHeight : MapsTo D R Height)
    (hHB : ConstructionCutWeights.RangeBound top Height) (hCost : MapsTo D R Cost)
    (hCB : ConstructionProbeGateCap.Bounds top Cost)
    (hUniform : UniformMargins hM w Q D mul Height Cost)
    (hmark : (Project.FirstOrderSemantics.reduct M).mem mark D) (hmarkNe : mark ≠ e) :
    ∃ C L projection K A W I T B H unit, (Representatives n D C ∧ MapsTo C L projection ∧
      ConstructionMergerCopies.Copies n D mul P C L ∧ ConstructionMergerCopies.Projection n D mul P C projection ∧
      ConstructionMergerCopies.EqualityLaw n D mul P projection ∧ Representatives L D K ∧ MapsTo K L A ∧
      ConstructionMergerAction.ActionTable D mul projection A ∧ ConstructionMergerAction.RightFreeAction mul e L A ∧
      ConstructionMergerAction.CopyLaw D mul projection A ∧ ConstructionProbeRaw.Carrier w D L W ∧
      Representatives W D I ∧ MapsTo I W T ∧ ConstructionMergerWordAction.ActionTable w D L zero mul A T ∧
      ConstructionMergerAction.RightFreeAction mul e W T ∧ Representatives W W B ∧ MapsTo B W H ∧ ConstructionMergerWordProduct.Laws w D L zero T H) ∧
      ConstructionProbeRaw.Old zero D e unit ∧ LeftCancelMonoid W H unit ∧ ForcingDiagramPoset.Conical W H unit ∧ ConstructionMergerCopyCones.HasConeJoins D L A ∧ ConstructionProbeSharedIntersections.ConditionalJoins W H ∧ ∃ O, ConstructionProbeOldEmbedding.OldGraph zero D O ∧ ConstructionProbeConservative.Conservative D W mul H O ∧
      ConstructionProbeLiftHom.PreservesProducts mul H O ∧ ConstructionPersistentProfiles.HasOldGates D W mul H O ∧ PureKuratowski.PairMember M e unit O ∧
      (∀ a b d p node, ConstructionPersistentProfiles.ProbeProfile w D mul a b d p node →
        ∃ mapped fa fb fd fp, ConstructionProbeMappedPath.NodeMap node O mapped ∧
          PureKuratowski.PairMember M a fa O ∧ PureKuratowski.PairMember M b fb O ∧
          PureKuratowski.PairMember M d fd O ∧ PureKuratowski.PairMember M p fp O ∧
          ConstructionPersistentProfiles.ProbeProfile w W H fa fb fd fp mapped) ∧ ∃ F, MapsTo n W F ∧ ConstructionMergerRoots.RootGraph w D L e projection unit F ∧ ConstructionMergerRoots.RootLaws w D L n mul P projection unit H O F ∧ ∃ J CH CC, Representatives n L J ∧ MapsTo J R CH ∧ MapsTo J R CC ∧
      ConstructionMergerCoordinates.Graph n L projection Height zero CH ∧ ConstructionMergerCoordinates.Graph n L projection Cost top CC ∧
      ConstructionMergerCoordinateLaws.Laws n D L A projection Height Cost zero top CH CC ∧
      ∃ unitHeight Ka add Km mulCut Id two cap FH FC, (
      PureKuratowski.PairMember M e unitHeight Height ∧
      Representatives R R Ka ∧ MapsTo Ka R add ∧ ConstructionCutArithmetic.Graph hM w Q R add ∧
      Representatives R R Km ∧ MapsTo Km R mulCut ∧ ConstructionCutProduct.Graph hM w Q R mulCut ∧
      MapsTo R R Id ∧ ForcingConditionGraphs.IdentityGraph R Id ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf two one ∧ (Project.FirstOrderSemantics.reduct M).mem two w ∧
      (Project.FirstOrderSemantics.reduct M).mem cap R ∧ ConstructionCutDivision.Value hM w Q two unitHeight cap ∧
      MapsTo L R FH ∧ (∀ z a, PureKuratowski.PairMember M z a FH ↔
        (Project.FirstOrderSemantics.reduct M).mem z L ∧ HeightValue hM w Q n R add Id zero CH z a) ∧
      MapsTo L R FC ∧ (∀ z a, PureKuratowski.PairMember M z a FC ↔
        (Project.FirstOrderSemantics.reduct M).mem z L ∧ CostValue hM w Q n R mulCut Id top cap CC z a) ∧
      (∀ a, (Project.FirstOrderSemantics.reduct M).mem a R → Product mulCut a top a) ∧
      (∀ a, (Project.FirstOrderSemantics.reduct M).mem a R → Product add zero a a)) ∧
      CopiesHeightCost hM w Q R D L A top FH FC ∧
      (∀ mu, (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu →
        ForcingSupportSize.Small D mu → ForcingSupportSize.Small W mu) ∧
      ∃ twoW threeW fourW fiveW sixW sevenW eightW quarterW eighthW OffW ScaleW FactorW HL CL, ( ((
      ConstructionBaseWeights.Digits w one twoW threeW ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf fourW threeW ∧ (Project.FirstOrderSemantics.reduct M).mem fourW w ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf fiveW fourW ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf sixW fiveW ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf sevenW sixW ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf eightW sevenW ∧ (Project.FirstOrderSemantics.reduct M).mem eightW w ∧
      ConstructionCutDivision.Value hM w Q fourW top quarterW ∧ ConstructionCutDivision.Value hM w Q eightW top eighthW ∧
      (Project.FirstOrderSemantics.reduct M).mem quarterW R ∧ (Project.FirstOrderSemantics.reduct M).mem eighthW R ∧
      MapsTo L R OffW ∧ MapsTo L R ScaleW ∧ MapsTo L R FactorW ∧
      ConstructionMergerWordParameters.Graph 0 hM w Q fourW top quarterW eighthW L FH FC OffW ∧
      ConstructionMergerWordParameters.Graph 1 hM w Q fourW top quarterW eighthW L FH FC ScaleW ∧
      ConstructionMergerWordParameters.Graph 2 hM w Q fourW top quarterW eighthW L FH FC FactorW ∧
      (∀ s theta sigma factor, PureKuratowski.PairMember M s theta OffW →
        PureKuratowski.PairMember M s sigma ScaleW → PureKuratowski.PairMember M s factor FactorW →
        ConstructionMergerWordParameters.Recipe hM w Q fourW top quarterW eighthW FH FC s theta sigma factor) ∧
      ConstructionCutWeights.RangeBound top OffW ∧
      (∀ s sigma, PureKuratowski.PairMember M s sigma ScaleW → ∃ p, (Project.FirstOrderSemantics.reduct M).mem p sigma) ∧
      ConstructionProbeGateCap.Bounds eighthW FactorW) ∧
      MapsTo W R HL ∧ ConstructionProbeHeightFold.Laws hM w D L zero W Q Height OffW ScaleW HL ∧
      ConstructionMergerWordHeights.LiteralLaws hM w Q D L zero top Height OffW HL ∧
      ConstructionCutWeights.RangeBound top HL ∧ MapsTo W R CL ∧
      (∀ q y, PureKuratowski.PairMember M q y CL ↔ (Project.FirstOrderSemantics.reduct M).mem q W ∧ ConstructionMergerWordCosts.Value hM w Q D L zero top HL Cost FactorW q y) ∧
      ConstructionProbeGateCap.Bounds top CL ∧
      (∀ x q y, Old zero D x q → (PureKuratowski.PairMember M q y CL ↔ PureKuratowski.PairMember M x y Cost)) ∧
      (∀ letter pref q y, Cons w D L letter pref q →
        (PureKuratowski.PairMember M q y CL ↔ ∃ h room factor, PureKuratowski.PairMember M pref h HL ∧
          ConstructionCutDifference.Value hM w Q h top room ∧ SumCut hM w Q h room top ∧
          PureKuratowski.PairMember M letter factor FactorW ∧ ConstructionCutProduct.Value hM w Q room factor y))) ∧
      UniformMargins hM w Q W H HL CL ∧
      (∀ x y a b, PureKuratowski.PairMember M x a HL → PureKuratowski.PairMember M y b HL →
        Divides W H x y → ¬ Divides W H y x → ∃ cap total,
        Cut hM w Q cap ∧ ConstructionProbeCostSupremum.Cap W H CL x y cap ∧
        SumCut hM w Q a cap total ∧ Strict total b ∧ MissedBound W H CL x y cap) ∧
      (∀ x y ox oy, Old zero D x ox → Old zero D y oy →
        (∀ cd, ConstructionProbeCostSupremum.CostMember W H CL ox oy cd ↔ ConstructionProbeCostSupremum.CostMember D mul Cost x y cd) ∧
        (∀ cap, ConstructionProbeCostSupremum.Cap W H CL ox oy cap ↔ ConstructionProbeCostSupremum.Cap D mul Cost x y cap) ∧
        ∃ cap, Cut hM w Q cap ∧ ConstructionProbeCostSupremum.Cap D mul Cost x y cap ∧
          ConstructionProbeCostSupremum.Cap W H CL ox oy cap ∧
          ∀ c0 c1, ConstructionProbeCostSupremum.Cap D mul Cost x y c0 →
            ConstructionProbeCostSupremum.Cap W H CL ox oy c1 → c0 = c1)) ∧
      ∃ markN, PureKuratowski.PairMember M mark markN O ∧
        (Project.FirstOrderSemantics.reduct M).mem markN W ∧ markN ≠ unit ∧
        ConstructionProbeRaw.Old zero D mark markN ∧
        ∀ x ox value, PureKuratowski.PairMember M x ox O →
          (PureKuratowski.PairMember M ox value HL ↔ PureKuratowski.PairMember M x value Height) ∧
          (PureKuratowski.PairMember M ox value CL ↔ PureKuratowski.PairMember M x value Cost) := by
  obtain ⟨C,L,projection,K,A,W,I,T,B,H,unit,hParent,hUnit,hMonoid,hCon,hCone,hJoinsW,O,hO,hCons,hPres,hGates,hEdge,hProfiles,F,hF,hRoots,hRootLaws,J,CH,CC,hJ,hCH,hCC,hCoordH,hCoordC,hCoordLaws,
    unitHeight,Ka,add,Km,mulCut,Id,two,cap,FH,FC,hWeights,hCopyHC⟩ :=
    ConstructionMergerHeightCost.exists_system hM hw hz hzw hm hc hJoins hP hValid hQ hn hnp hu hone hunit hR hHeight hHB hCost hCB hUniform
  have hRetained := hParent
  obtain ⟨hC,hp,hL,hProjection,_,_,_,_,_,_,hW,_,_,hWordTable,_,hB,hH,hLaws⟩ := hParent
  have hCard : ∀ mu, (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu →
      ForcingSupportSize.Small D mu → ForcingSupportSize.Small W mu :=
    fun _ hmu hD => ConstructionMergerCardinality.merger_cardinal_le hM hw hmu hn hD hC hL hp hProjection hW
  obtain ⟨twoW,threeW,fourW,fiveW,sixW,sevenW,eightW,quarterW,eighthW,OffW,ScaleW,FactorW,HL,CL,hWordFields⟩ :=
    ConstructionMergerWordHeightCost.exists_heightCost hM hw hz hzw hQ hR hu hone hunit hW hHeight hCost hHB hCB hCopyHC
      hWordTable hLaws hB hH hMonoid hCon hUniform hm.1.1
  have hWordRetained := hWordFields
  obtain ⟨hActual,_,_,_⟩ := hWordFields
  obtain ⟨_,_,_,hLiteral,_,_,hCostGraph,_,_,_⟩ := hActual
  obtain ⟨markN,hMarkEdge,_⟩ := hCons.1.1.1.2 mark hmark
  have hMarkNe : markN ≠ unit := by
    intro heq
    exact hmarkNe (hCons.1.2 mark e unit (heq ▸ hMarkEdge) hEdge)
  refine ⟨C,L,projection,K,A,W,I,T,B,H,unit,hRetained,hUnit,hMonoid,hCon,hCone,hJoinsW,
    O,hO,hCons,hPres,hGates,hEdge,hProfiles,F,hF,hRoots,hRootLaws,J,CH,CC,hJ,hCH,hCC,hCoordH,hCoordC,hCoordLaws,
    unitHeight,Ka,add,Km,mulCut,Id,two,cap,FH,FC,hWeights,hCopyHC,hCard,
    twoW,threeW,fourW,fiveW,sixW,sevenW,eightW,quarterW,eighthW,OffW,ScaleW,FactorW,HL,CL,hWordRetained,
    markN,hMarkEdge,hCons.1.1.2 mark markN hMarkEdge,hMarkNe,(hO mark markN).mp hMarkEdge,?_⟩
  intro x ox value hxo
  have hOld := (hO x ox).mp hxo
  exact ⟨hLiteral.1 x ox value hOld,ConstructionMergerWordCosts.cost_old_iff hM hz hzw hW hCostGraph hOld⟩

end PPAC.Migration.ConstructionMergerParent
