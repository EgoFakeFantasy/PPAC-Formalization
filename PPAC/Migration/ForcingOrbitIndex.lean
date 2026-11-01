/- Fixed OrbitAssignments.orbitAssignment_index:450-455.
An actual orbit assignment at a chosen representative has the same internal
quotient index as its vertex. Reuse the full quotient and representative roundtrip. -/
import PPAC.Migration.ForcingOrbitRepresentatives

namespace PPAC.Migration.ForcingOrbitIndex
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingConditionGraphs (Permutation CompositionGraph InverseGraph)
open ForcingSupportSize (MapsTo Injection)
open ForcingOrbitAssignment (OrbitAssignment orbitAssignment orbitAssignment_orbit orbitAssignment_freeClosed orbitAssignment_semantics)
open ForcingComponentMove (Move)
open ConstructionComponentCofinal (EncodedCommon Chain)
open ForcingComponentFibers (VertexFiber)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem orbitAssignment_index (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices orbitQuotient orbitProjection orbitReps orbitIndex vertexIndex : Fin k) (d vertex label tau : M.Carrier .set)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hq : Injection (env (rho 0)) (env I) (env q))
    (hGerm : ConstructionGermCosets.Carrier (env (rho 0)) (env I) (env mul) (env q) (env root) (env germGroup))
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hQuotient : ForcingOrbitQuotient.Classes (env (rho 0)) (env I) (env mul) (env q) (env vertices) (env orbitQuotient))
    (hProjection : ForcingOrbitQuotient.Projection (env (rho 0)) (env I) (env mul) (env q) (env vertices) (env orbitProjection))
    (hReps : ConstructionGermDetectors.Representatives (env vertices) (env orbitQuotient) (env orbitReps))
    (hRep : PureKuratowski.PairMember M (env orbitIndex) (env root) (env orbitReps))
    (hVertexIndex : PureKuratowski.PairMember M vertex (env vertexIndex) (env orbitProjection))
    (h : OrbitAssignment hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder d vertex label tau) :
    env orbitIndex = env vertexIndex := by
  have hOrbit := orbitAssignment_orbit hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices d vertex label tau hm hJ hw hChain hq hGerm h
  have hRoundTrip := ForcingOrbitRepresentatives.representative_roundtrip hM hm hJ hq hVertices hQuotient hProjection hReps
  have hLaws := ForcingOrbitQuotient.quotient_laws hM hm hJ hq hVertices hProjection
  exact (hLaws (env root) vertex (env orbitIndex) (env vertexIndex) (hRoundTrip _ _ hRep) hVertexIndex).1.mpr hOrbit

def indexSentence {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices orbitQuotient orbitProjection orbitReps orbitIndex vertexIndex d vertex label tau : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ConstructionGermCosets.carrier (rho 0) I mul q root germGroup)
    (.imp (ConstructionComponentCarrier.carrier (rho 0) I mul q vertices)
    (.imp (ForcingOrbitQuotient.classes (rho 0) I mul q vertices orbitQuotient)
    (.imp (ForcingOrbitQuotient.projection (rho 0) I mul q vertices orbitProjection)
    (.imp (ConstructionGermDetectors.representatives vertices orbitQuotient orbitReps)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge orbitReps orbitIndex root))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge orbitProjection vertex vertexIndex))
    (.imp (orbitAssignment rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id d vertex label tau)
    (Project.Formula.extensionalEq (.bound orbitIndex) (.bound vertexIndex)))))))))
))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionComponentCofinal.chain_freeClosed,ConstructionGermCosets.carrier_freeClosed,orbitAssignment_freeClosed,Project.Formula.extensionalEq,ConstructionComponentCarrier.carrier_freeClosed,ForcingOrbitQuotient.classes_freeClosed,ForcingOrbitQuotient.projection_freeClosed,ConstructionGermDetectors.representatives_freeClosed]

theorem index_models {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices orbitQuotient orbitProjection orbitReps orbitIndex vertexIndex d vertex label tau : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (indexSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices orbitQuotient orbitProjection orbitReps orbitIndex vertexIndex d vertex label tau)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionComponentCofinal.chain_semantics hM,ConstructionGermCosets.carrier_semantics hM,orbitAssignment_semantics hM,ForcingSupportSize.injection_semantics (M := M),ConstructionComponentCarrier.carrier_semantics hM,ForcingOrbitQuotient.classes_semantics hM,ForcingOrbitQuotient.projection_semantics hM,ConstructionGermDetectors.representatives_semantics hM,KuratowskiZF.source_edge,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  exact orbitAssignment_index hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices orbitQuotient orbitProjection orbitReps orbitIndex vertexIndex (env d) (env vertex) (env label) (env tau)

theorem index_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices orbitQuotient orbitProjection orbitReps orbitIndex vertexIndex d vertex label tau : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (indexSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices orbitQuotient orbitProjection orbitReps orbitIndex vertexIndex d vertex label tau)) := by
  apply ModelTransfer.derives
  intro M hM
  exact index_models rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices orbitQuotient orbitProjection orbitReps orbitIndex vertexIndex d vertex label tau hM

end PPAC.Migration.ForcingOrbitIndex
