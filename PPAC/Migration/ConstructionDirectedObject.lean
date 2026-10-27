/- Pinned MonoidTowers.DirectedColimit.object:63 / inclusion:74.
Construct SAME complete weighted pointed monoid from original stage Object
fields, retaining ALL original stage maps, profiles and exact old suprema.
Cardinality is a conditional OUTPUT with explicit original object Choice. -/
import PPAC.Migration.ConstructionDirectedMarks
import PPAC.Migration.ConstructionDirectedCardinality

namespace PPAC.Migration.ConstructionDirectedObject
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionDirectedSystem
open ConstructionDirectedMonoidData (Family HomLaws ConicalFamily)
open ConstructionDirectedConservativeData
open ConstructionDirectedLimitCarrier (Representatives Carrier Projection EqualityLaw)
open ConstructionDirectedMonoid (UnitImage)
open ConstructionDirectedWeightData
open ConstructionRealCuts (Cut CutCarrier)
open ForcingSupportSize (MapsTo)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    (J E Domains F Muls Units w Q R top Heights Costs Marks : M.Carrier .set)
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
    (hMarkStable : ConstructionDirectedMarks.Stable J E Domains F Marks) :
    ∃ C L projection B G unit mark, Representatives J Domains C ∧ MapsTo C L projection ∧ Carrier J E Domains F C L ∧
      Projection J E Domains F C projection ∧ EqualityLaw J E Domains F projection ∧
      ConstructionProbeLetters.Representatives L L B ∧ MapsTo B L G ∧ ConstructionDirectedProduct.Graph J Domains Muls projection G ∧
      (Project.FirstOrderSemantics.reduct M).mem unit L ∧ UnitImage J Domains Units projection unit ∧
      LeftCancelMonoid L G unit ∧ Conical L G unit ∧
      ConstructionProbeSharedIntersections.ConditionalJoins L G ∧
      (Project.FirstOrderSemantics.reduct M).mem mark L ∧ mark ≠ unit ∧
      ConstructionDirectedMarks.MarkImage J Marks projection mark ∧
      (∀ i D mul e, (Project.FirstOrderSemantics.reduct M).mem i J → PureKuratowski.PairMember M i D Domains →
        PureKuratowski.PairMember M i mul Muls → PureKuratowski.PairMember M i e Units →
        ∃ f, MapsTo D L f ∧ (∀ x z, PureKuratowski.PairMember M x z f ↔
          (Project.FirstOrderSemantics.reduct M).mem x D ∧ Product projection i x z) ∧
          ConstructionProbeLiftHom.PreservesProducts mul G f ∧ PureKuratowski.PairMember M e unit f ∧
          ConstructionProbeConservative.Conservative D L mul G f ∧ ConstructionDirectedProfiles.ProfileTransport J E Domains F Muls i D L G f ∧
          ∀ a, PureKuratowski.PairMember M i a Marks → PureKuratowski.PairMember M a mark f) ∧
      ∃ HL LC, ConstructionDirectedHeightCost.Laws hM w Q R top J Domains Muls Heights Costs L projection G HL LC ∧ ConstructionDirectedCardinality.Bound hM J Domains L := by
  obtain ⟨C,L,projection,B,G,unit,hC,hp,hL,hP,hEq,hB,hG,hGraph,hu,hImage,hMon,hConL,hJoinsL,hStages,HL,LC,hWeights⟩ :=
    ConstructionDirectedHeightCost.exists_system hM J E Domains F Muls Units w Q R top Heights Costs hne hE hT hFam hHom hCons hw hQ hR hTop hWH hWC hStableH hStableC hHB hCB hUniform hSup
  obtain ⟨mark,hmark,hneMark,hMarkImage⟩ := ConstructionDirectedMarks.exists_mark hM hne hFam hE hT hCons hC hp hEq hImage hMarks hMarkStable
  have hCard := ConstructionDirectedCardinality.bound hM hFam.1 hC hp hL hP
  refine ⟨C,L,projection,B,G,unit,mark,hC,hp,hL,hP,hEq,hB,hG,hGraph,hu,hImage,hMon,hConL hCon,hJoinsL hJoins,hmark,hneMark,hMarkImage,?_,HL,LC,hWeights,hCard⟩
  intro i D mul e hi hD hm he
  obtain ⟨f,hf,hFG,hProd,hOne,hCov,hProfile⟩ := hStages i D mul e hi hD hm he
  refine ⟨f,hf,hFG,hProd,hOne,hCov,hProfile,?_⟩
  intro a hia
  exact (hFG a mark).mpr ⟨(hMarks.2 i D e a hi hD he hia).1,hMarkImage i a hi hia⟩

end PPAC.Migration.ConstructionDirectedObject
