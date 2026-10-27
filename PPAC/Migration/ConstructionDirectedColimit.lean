/- Pinned MonoidTowers.DirectedColimit.cocone/lift/isColimit.
Retain the SAME complete actual weighted pointed object, every profile and
all canonical inclusions; construct its actual internal cocone leg family
and prove the full universal property for every internal target cocone. -/
import PPAC.Migration.ConstructionDirectedCocone

namespace PPAC.Migration.ConstructionDirectedColimit
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

def Colimit (J E Domains F Muls Units Heights Costs Marks L projection G unit mark HL LC : M.Carrier .set) : Prop :=
  ∃ K, ConstructionDirectedCocone.Cocone J E Domains F L projection K ∧
    ConstructionDirectedLift.Legs J Domains Muls Units K L G unit ∧
    ConstructionDirectedLift.MarkLegs J Marks K mark ∧
    ConstructionDirectedLift.WeightedLegs J Domains Muls Heights Costs K HL LC L G ∧
    ConstructionDirectedLift.Universal J E Domains F Muls Units Heights Costs Marks L projection G unit mark HL LC


def colimit {m : Nat} (J E Domains F Muls Units Heights Costs Marks L projection G unit mark HL LC : Fin m) : Project.Formula 1 m :=
  (.existsE (.conj (ConstructionDirectedCocone.cocone J.succ E.succ Domains.succ F.succ L.succ projection.succ
  (0 : Fin (m+1))) (.conj (ConstructionDirectedLiftSyntax.legs J.succ Domains.succ Muls.succ Units.succ (0 :
  Fin (m+1)) L.succ G.succ unit.succ) (.conj (ConstructionDirectedLiftSyntax.markLegs J.succ Marks.succ (0 :
  Fin (m+1)) mark.succ) (.conj (ConstructionDirectedLiftSyntax.weightedLegs J.succ Domains.succ Muls.succ
  Heights.succ Costs.succ (0 : Fin (m+1)) HL.succ LC.succ L.succ G.succ)
  (ConstructionDirectedLiftSyntax.universalProperty J.succ E.succ Domains.succ F.succ Muls.succ Units.succ
  Heights.succ Costs.succ Marks.succ L.succ projection.succ G.succ unit.succ mark.succ HL.succ LC.succ))))))

theorem colimit_freeClosed {m : Nat} (J E Domains F Muls Units Heights Costs Marks L projection G unit mark HL LC : Fin m) :
    (colimit J E Domains F Muls Units Heights Costs Marks L projection G unit mark HL LC).FreeClosed := by
  simp -implicitDefEqProofs [colimit,Definitional.Formula.FreeClosed,ConstructionDirectedCocone.cocone_freeClosed,ConstructionDirectedLiftSyntax.legs_freeClosed,ConstructionDirectedLiftSyntax.markLegs_freeClosed,ConstructionDirectedLiftSyntax.weightedLegs_freeClosed,ConstructionDirectedLiftSyntax.universalProperty_freeClosed]

theorem colimit_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E Domains F Muls Units Heights Costs Marks L projection G unit mark HL LC : Fin m) :
    Project.Formula.satisfies env (colimit J E Domains F Muls Units Heights Costs Marks L projection G unit mark HL LC) ↔ Colimit (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) (env.bound Muls) (env.bound Units) (env.bound Heights) (env.bound Costs) (env.bound Marks) (env.bound L) (env.bound projection) (env.bound G) (env.bound unit) (env.bound mark) (env.bound HL) (env.bound LC) := by
  simp only [colimit,Colimit,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    
    ConstructionDirectedCocone.cocone_semantics hM,ConstructionDirectedLiftSyntax.legs_semantics hM,ConstructionDirectedLiftSyntax.markLegs_semantics hM,ConstructionDirectedLiftSyntax.weightedLegs_semantics hM,ConstructionDirectedLiftSyntax.universalProperty_semantics hM]
  rfl

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
      ∃ HL LC, ConstructionDirectedHeightCost.Laws hM w Q R top J Domains Muls Heights Costs L projection G HL LC ∧ ConstructionDirectedCardinality.Bound hM J Domains L ∧ Colimit J E Domains F Muls Units Heights Costs Marks L projection G unit mark HL LC := by
  obtain ⟨C,L,projection,B,G,unit,mark,hC,hp,hL,hP,hEq,hB,hG,hGraph,hu,hImage,hMon,hConL,hJoinsL,hmark,hneMark,hMarkImage,hStages,HL,LC,hWeights,hCard⟩ :=
    ConstructionDirectedObject.exists_system hM J E Domains F Muls Units w Q R top Heights Costs Marks hne hE hT hFam hHom hCons hw hQ hR hTop hWH hWC hStableH hStableC hHB hCB hUniform hSup hCon hJoins hMarks hMarkStable
  obtain ⟨K,hK⟩ := ConstructionDirectedCocone.exists_cocone hM hFam.1 hC hp hE hT hEq
  obtain ⟨hLegs,hMarkLegs,hWeighted⟩ := ConstructionDirectedCocone.hom_fields hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hMarks hMarkImage hWeights hK
  have hUniversal := ConstructionDirectedLift.universal hM hne hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hMarks hMarkImage hWH hWC hWeights
  exact ⟨C,L,projection,B,G,unit,mark,hC,hp,hL,hP,hEq,hB,hG,hGraph,hu,hImage,hMon,hConL,hJoinsL,hmark,hneMark,hMarkImage,hStages,HL,LC,hWeights,hCard,K,hK,hLegs,hMarkLegs,hWeighted,hUniversal⟩

end PPAC.Migration.ConstructionDirectedColimit
