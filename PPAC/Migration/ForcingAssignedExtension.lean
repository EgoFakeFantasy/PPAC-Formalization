/- Fixed OrbitAssignments.assigned_at_extension:585-593. Compose the existing
assigned_label, assigned_mono, literal labelVertex_arrow, and assigned_restrict.
The target is the unique actual label-availability vertex, not an arbitrary
identification of enlarged fibers. Consumers: assigned_compatible_one/inj. -/
import PPAC.Migration.ForcingAssignedLaws
import PPAC.Migration.ForcingAssignedTransport
import PPAC.Migration.ForcingLabelVertices

namespace PPAC.Migration.ForcingAssignedExtension
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingOrbitAssignment (OrbitAssignment orbitAssignment)
open ForcingGermCorrectedStable (stable_reindex)
open ForcingStableAt (StableAt stableAt)
open ForcingProductSymmetry (orderFormula)
open ConstructionComponentCofinal (Chain)
open ForcingTailCodes (Entry)
open ForcingSupportSize (Injection)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

open ForcingAssigned (Assigned assigned assigned_freeClosed assigned_semantics Fields Functions Germs fields functions germs fields_freeClosed functions_freeClosed germs_freeClosed fields_semantics functions_semantics germs_semantics)
open ForcingSupportSize (MapsTo)
open ForcingComponentFibers (VertexFiber)

theorem assigned_at_extension (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau Q pr a diagrams objImage objects arrows mapImage maps vertexLabels targetRoot targetObjects targetIndex targetVertex oldRoot oldIndex oldIdeal : Fin k) (families : Fin 16 → Fin k)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hRoot : ConstructionComponentCarrier.Code (env root) (env r) (env idx) (env U))
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal (env K))
    (hResult : ConstructionConcreteSelector.Result hM (env w) (env (rho 0)) (env I) (env mul) (env q) (env root) (env chain) (env K) (env zero) (env germGroup) (env quotient) (env projection) (env reps) (env nonidentity) (env detectorDomain) (env detector) (env detectorSites) (env high) (env B) (env (rho 1)) (env (rho 2)) (env patternCarrier) (env patternOrder) (env selectorDomain) (env selector))
    (he : (Project.FirstOrderSemantics.reduct M).mem (env e) (env (rho 3)))
    (hde : ForcingPowerName.Subset (env d) (env e))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hq : ForcingSupportSize.Injection (env (rho 0)) (env I) (env q))
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hQuotient : ForcingOrbitQuotient.Classes (env (rho 0)) (env I) (env mul) (env q) (env vertices) (env Q))
    (hProjection : ForcingOrbitQuotient.Projection (env (rho 0)) (env I) (env mul) (env q) (env vertices) (env pr))
    (hReps : ConstructionGermDetectors.Representatives (env vertices) (env Q) (env (families 0)))
    (hChains : ForcingOrbitChains.Family (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env vertices) (env Q) (env (families 0)) (env (families 1)))
    (hFunctions : Functions env families (env Q))
    (hGerms : Germs (env (rho 0)) (env I) (env mul) (env q) (env (families 0)) (env (families 10)))
    (hIndex : PureKuratowski.PairMember M (env vertex) (env a) (env pr))
    (hFields : Fields env families (env a) (env root) (env chain) (env codes) (env order) (env ranks) (env selection) (env rankBound) (env labelSet) (env tab) (env r) (env germGroup) (env quotient) (env nonidentity) (env high) (env detector) (env patternOrder))
    (h : Assigned hM env rho I G F mul q bound labels E w top K B zero Q families (env d) (env vertex) (env label) (env tau))
    (hDiagrams : ForcingDiagramCarrier.Carrier (env (rho 0)) (env I) (env diagrams))
    (hObj : MapsTo (env diagrams) (env objImage) (env objects))
    (hObjects : ForcingLabelSystem.Objects (env (rho 0)) (env diagrams) (env objects))
    (hArrows : ForcingEligibleMapFamily.Arrows (env (rho 0)) (env mul) (env diagrams) (env arrows))
    (hMaps : MapsTo (env arrows) (env mapImage) (env maps))
    (hMapFamily : ForcingLabelSystem.Maps (env objects) (env arrows) (env maps))
    (hFibers : ForcingConcreteLabels.CommonFibers (env (rho 0)) (env I) (env mul) (env objects) (env maps))
    (hRootFiber : VertexFiber (env (rho 0)) (env mul) (env objects) (env maps) (env root) (env labelSet))
    (hVertexFiber : VertexFiber (env (rho 0)) (env mul) (env objects) (env maps) (env vertex) (env vertexLabels))
    (hTargetObjects : PureKuratowski.PairMember M (env targetRoot) (env targetObjects) (env objects))
    (hTarget : ForcingLabelVertices.LabelVertex (env (rho 0)) (env I) (env mul) (env q) (env objects) (env maps) (env targetRoot) (env targetIndex) (env label) (env targetVertex))
    (hOldCode : ConstructionComponentCarrier.Code (env vertex) (env oldRoot) (env oldIndex) (env oldIdeal))
    (hOldVertex : ConstructionComponentVertices.Vertex (env (rho 0)) (env I) (env mul) (env q) (env oldRoot) (env oldIndex) (env oldIdeal))
    (hExtension : ForcingDiagramOrder.Le (env (rho 0)) (env mul) (env targetRoot) (env oldRoot)) :
    Assigned hM env rho I G F mul q bound labels E w top K B zero Q families (env e) (env targetVertex) (env label) (env tau) := by
  have hGerm := hGerms (env a) (env root) (env germGroup) hFields.1 hFields.2.2.2.2.2.2.2.2.2.2.1
  have hSys := ForcingLabelSystem.system_of_families hObj hObjects hMapFamily
  have hLabel := ForcingAssignedLaws.assigned_label hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices diagrams objImage objects arrows mapImage maps vertexLabels d vertex label tau Q pr a families
    hm hJ hw hChain hGerm hDiagrams hObj hObjects hArrows hMaps hMapFamily hSys hFibers hRootFiber hVertexFiber hq hVertices hQuotient hProjection hReps hChains hFunctions hGerms hIndex hFields h
  have hMono := ForcingAssignedLaws.assigned_mono hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau Q pr a families
    hm hp hChain hRoot hK hResult he hde hJ hw hq hVertices hQuotient hProjection hReps hChains hFunctions hGerms hIndex hFields h
  obtain ⟨n,hArrow⟩ := ForcingLabelVertices.labelVertex_arrow hM hm hDiagrams hObj hObjects hArrows hMaps hMapFamily hTargetObjects hTarget hOldCode hOldVertex hVertexFiber hLabel hExtension
  let other : Fin (k+1) → M.Carrier .set := Fin.cases n env
  have hInput := (ForcingAssigned.assigned_reindex hM env other Fin.succ (fun _ => rfl) rho I G F mul q bound labels E w top K B zero Q families (env e) (env vertex) (env label) (env tau)).mpr hMono
  have hOutput := ForcingAssignedTransport.assigned_restrict hM other (fun j => (rho j).succ) I.succ G.succ F.succ mul.succ q.succ bound.succ labels.succ E.succ w.succ top.succ K.succ B.succ zero.succ Q.succ one.succ e.succ vertex.succ targetVertex.succ 0 label.succ tau.succ (fun j => (families j).succ)
    hm hp hq hGerms hArrow hInput
  exact (ForcingAssigned.assigned_reindex hM env other Fin.succ (fun _ => rfl) rho I G F mul q bound labels E w top K B zero Q families (env e) (env targetVertex) (env label) (env tau)).mp hOutput

def extensionSentence {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau Q pr a diagrams objImage objects arrows mapImage maps vertexLabels targetRoot targetObjects targetIndex targetVertex oldRoot oldIndex oldIdeal : Fin k) (families : Fin 16 → Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ConstructionComponentCarrier.code root r idx U)
    (.imp (Project.Formula.isOrdinal (.bound K))
    (.imp (ConstructionConcreteSelector.resultFormula w (rho 0) I mul q root chain K zero germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high B (rho 1) (rho 2) patternCarrier patternOrder selectorDomain selector)
    (.imp ( .mem (.bound e) (.bound (rho 3)))
    (.imp (Project.Formula.subset (.bound d) (.bound e))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ConstructionComponentCarrier.carrier (rho 0) I mul q vertices)
    (.imp (ForcingOrbitQuotient.classes (rho 0) I mul q vertices Q)
    (.imp (ForcingOrbitQuotient.projection (rho 0) I mul q vertices pr)
    (.imp (ConstructionGermDetectors.representatives vertices Q (families 0))
    (.imp (ForcingOrbitChains.family w (rho 0) I mul q zero vertices Q (families 0) (families 1))
    (.imp (functions families Q)
    (.imp (germs (rho 0) I mul q (families 0) (families 10))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge pr vertex a))
    (.imp (fields families a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder)
    (.imp (assigned rho I G F mul q bound labels E w top K B zero Q families d vertex label tau)
    (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier (rho 0) I diagrams))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage))
    (.imp (ForcingLabelSystem.objectFamily (rho 0) diagrams objects)
    (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows (rho 0) mul diagrams arrows))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps arrows mapImage))
    (.imp (ForcingLabelSystem.mapFamily objects arrows maps)
    (.imp (ForcingConcreteLabels.commonFibers (rho 0) I mul objects maps)
    (.imp (ForcingComponentFibers.vertexFiber (rho 0) mul objects maps root labelSet)
    (.imp (ForcingComponentFibers.vertexFiber (rho 0) mul objects maps vertex vertexLabels)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge objects targetRoot targetObjects))
    (.imp (ForcingLabelVertices.labelVertex (rho 0) I mul q objects maps targetRoot targetIndex label targetVertex)
    (.imp (ConstructionComponentCarrier.code vertex oldRoot oldIndex oldIdeal)
    (.imp (ConstructionComponentVertices.vertex (rho 0) I mul q oldRoot oldIndex oldIdeal)
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.le (rho 0) mul targetRoot oldRoot))
    (assigned rho I G F mul q bound labels E w top K B zero Q families e targetVertex label tau))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionComponentCofinal.chain_freeClosed,ConstructionComponentCarrier.code_freeClosed,Project.Formula.isOrdinal,ConstructionConcreteSelector.resultFormula_freeClosed,Project.Formula.subset,assigned_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionComponentCarrier.carrier_freeClosed,ForcingOrbitQuotient.classes_freeClosed,ForcingOrbitQuotient.projection_freeClosed,ConstructionGermDetectors.representatives_freeClosed,ForcingOrbitChains.family_freeClosed,functions_freeClosed,germs_freeClosed,fields_freeClosed,ForcingLabelSystem.objectFamily_freeClosed,ForcingLabelSystem.mapFamily_freeClosed,ForcingConcreteLabels.commonFibers_freeClosed,ForcingComponentFibers.vertexFiber_freeClosed,ForcingLabelVertices.labelVertex_freeClosed,ConstructionComponentVertices.vertex_freeClosed]

theorem extension_models {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau Q pr a diagrams objImage objects arrows mapImage maps vertexLabels targetRoot targetObjects targetIndex targetVertex oldRoot oldIndex oldIdeal : Fin k) (families : Fin 16 → Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (extensionSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau Q pr a diagrams objImage objects arrows mapImage maps vertexLabels targetRoot targetObjects targetIndex targetVertex oldRoot oldIndex oldIdeal families)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),ConstructionComponentCofinal.chain_semantics hM,ConstructionComponentCarrier.code_semantics hM,Project.Formula.satisfies_isOrdinal_iff,ConstructionConcreteSelector.resultFormula_semantics hM,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,assigned_semantics hM,ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,Project.Formula.satisfies_isOmega_iff,ForcingSupportSize.injection_semantics (M := M),ConstructionComponentCarrier.carrier_semantics hM,ForcingOrbitQuotient.classes_semantics hM,ForcingOrbitQuotient.projection_semantics hM,ConstructionGermDetectors.representatives_semantics hM,ForcingOrbitChains.family_semantics hM,functions_semantics hM,germs_semantics hM,KuratowskiZF.source_edge,fields_semantics hM,ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),ForcingLabelSystem.objectFamily_semantics hM,ForcingEligibleMapFamily.arrows_semantics (M := M),ForcingLabelSystem.mapFamily_semantics hM,ForcingConcreteLabels.commonFibers_semantics hM,ForcingComponentFibers.vertexFiber_semantics hM,ForcingLabelVertices.labelVertex_semantics hM,ConstructionComponentVertices.vertex_semantics hM,ForcingDiagramOrder.le_semantics (M := M)]
  exact assigned_at_extension hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau Q pr a diagrams objImage objects arrows mapImage maps vertexLabels targetRoot targetObjects targetIndex targetVertex oldRoot oldIndex oldIdeal families

theorem extension_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau Q pr a diagrams objImage objects arrows mapImage maps vertexLabels targetRoot targetObjects targetIndex targetVertex oldRoot oldIndex oldIdeal : Fin k) (families : Fin 16 → Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (extensionSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau Q pr a diagrams objImage objects arrows mapImage maps vertexLabels targetRoot targetObjects targetIndex targetVertex oldRoot oldIndex oldIdeal families)) := by
  apply ModelTransfer.derives
  intro M hM
  exact extension_models rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau Q pr a diagrams objImage objects arrows mapImage maps vertexLabels targetRoot targetObjects targetIndex targetVertex oldRoot oldIndex oldIdeal families hM

end PPAC.Migration.ForcingAssignedExtension
