/- Fixed OrbitAssignments.assigned_ideal:574-581. Consume the already completed
Assigned stable proof at the SAME actual condition and align the vertex code.
No new local-name/ideal backend or cardinality substitute. -/
import PPAC.Migration.ForcingAssignedStable

namespace PPAC.Migration.ForcingAssignedIdeal
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
set_option maxHeartbeats 500000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

open ForcingAssigned (Assigned assigned assigned_freeClosed assigned_semantics Fields Functions Germs fields functions germs fields_freeClosed functions_freeClosed germs_freeClosed fields_semantics functions_semantics germs_semantics)
open ForcingSupportSize (MapsTo)
open ForcingComponentFibers (VertexFiber)

theorem assigned_ideal (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d tau codes order ranks selection rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder Q pr a currentRoot currentIndex currentIdeal : Fin k) (families : Fin 16 → Fin k)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G)) (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hq : Injection (env (rho 0)) (env I) (env q))
    (hAq : ForcingSupportedNames.Range (env (rho 0)) (env q) (env Aq))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env Aq) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hEntry : Entry (fun j => env (rho j)) (env G) (env F) (env bound) (env vertex) (env tau))
    (hGerm : ConstructionGermCosets.Carrier (env (rho 0)) (env I) (env mul) (env q) (env root) (env germGroup))
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hQuotient : ForcingOrbitQuotient.Classes (env (rho 0)) (env I) (env mul) (env q) (env vertices) (env Q))
    (hProjection : ForcingOrbitQuotient.Projection (env (rho 0)) (env I) (env mul) (env q) (env vertices) (env pr))
    (hReps : ConstructionGermDetectors.Representatives (env vertices) (env Q) (env (families 0)))
    (hChains : ForcingOrbitChains.Family (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env vertices) (env Q) (env (families 0)) (env (families 1)))
    (hFunctions : Functions env families (env Q))
    (hGerms : Germs (env (rho 0)) (env I) (env mul) (env q) (env (families 0)) (env (families 10)))
    (hIndex : PureKuratowski.PairMember M (env vertex) (env a) (env pr))
    (hFields : Fields env families (env a) (env root) (env chain) (env codes) (env order) (env ranks) (env selection) (env rankBound) (env labelSet) (env tab) (env initialRoot) (env germGroup) (env quotient) (env nonidentity) (env high) (env detector) (env patternOrder))
    (h : Assigned hM env rho I G F mul q bound labels E w top K B zero Q families (env d) (env vertex) (env label) (env tau))
    (hVertexCode : ConstructionComponentCarrier.Code (env vertex) (env currentRoot) (env currentIndex) (env currentIdeal))
    (hd : (Project.FirstOrderSemantics.reduct M).mem (env d) (env (rho 3))) :
    ForcingForcedAvailability.Carrier (orderFormula (rho 0) mul) env (fun j => env (rho j))
      (env G) (env F) (env mul) (env bound) (env d) (env currentRoot) (env currentIndex) (env tau) (env currentIdeal) := by
  have hs := ForcingAssignedStable.assigned_stable hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d tau codes order ranks selection rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder Q pr a families
    hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hChain hCarrier hEntry hGerm
    hVertices hQuotient hProjection hReps hChains hFunctions hGerms hIndex hFields h
  obtain ⟨s,index,U,A,H,z,hCode,_,_,_,_,_,hStable⟩ := hs
  obtain ⟨er,ea,eU⟩ := ConstructionComponentCarrier.code_injective hCode hVertexCode
  simpa only [er,ea,eU] using hStable (env d) hd (fun _ hx => hx)

def idealSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d tau codes order ranks selection rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder Q pr a currentRoot currentIndex currentIdeal : Fin k) (families : Fin 16 → Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul one mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn labelMap K))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K labelMap top bit labels))
    (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K labelMap top bit bound))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q Aq))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Aq Hq))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq E))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
    (.imp (ForcingTailCodes.entry rho G F bound vertex tau)
    (.imp (ConstructionGermCosets.carrier (rho 0) I mul q root germGroup)
    (.imp (ConstructionComponentCarrier.carrier (rho 0) I mul q vertices)
    (.imp (ForcingOrbitQuotient.classes (rho 0) I mul q vertices Q)
    (.imp (ForcingOrbitQuotient.projection (rho 0) I mul q vertices pr)
    (.imp (ConstructionGermDetectors.representatives vertices Q (families 0))
    (.imp (ForcingOrbitChains.family w (rho 0) I mul q zero vertices Q (families 0) (families 1))
    (.imp (functions families Q)
    (.imp (germs (rho 0) I mul q (families 0) (families 10))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge pr vertex a))
    (.imp (fields families a root chain codes order ranks selection rankBound labelSet tab initialRoot germGroup quotient nonidentity high detector patternOrder)
    (.imp (assigned rho I G F mul q bound labels E w top K B zero Q families d vertex label tau)
    (.imp (ConstructionComponentCarrier.code vertex currentRoot currentIndex currentIdeal)
      (.imp (.mem (.bound d) (.bound (rho 3)))
        (ForcingForcedAvailability.carrier (orderFormula (rho 0) mul) id rho G F mul bound d currentRoot currentIndex tau currentIdeal))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,ForcingTailCodes.carrier_freeClosed,
      ForcingTailCodes.entry_freeClosed,ConstructionGermCosets.carrier_freeClosed,
      assigned_freeClosed,ForcingForcedAvailability.carrier_freeClosed,ConstructionComponentCarrier.code_freeClosed,ConstructionComponentCarrier.carrier_freeClosed,ForcingOrbitQuotient.classes_freeClosed,ForcingOrbitQuotient.projection_freeClosed,ConstructionGermDetectors.representatives_freeClosed,ForcingOrbitChains.family_freeClosed,functions_freeClosed,germs_freeClosed,fields_freeClosed]

theorem ideal_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d tau codes order ranks selection rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder Q pr a currentRoot currentIndex currentIdeal : Fin k) (families : Fin 16 → Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (idealSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d tau codes order ranks selection rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder Q pr a currentRoot currentIndex currentIdeal families)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,ForcingSupportSize.small_semantics (M := M),
    ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ConstructionComponentCofinal.chain_semantics hM,
    ForcingTailCodes.carrier_semantics hM,ForcingTailCodes.entry_semantics hM,
    ConstructionGermCosets.carrier_semantics hM,assigned_semantics hM,ForcingForcedAvailability.carrier_semantics hM,ConstructionComponentCarrier.code_semantics hM,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,ConstructionComponentCarrier.carrier_semantics hM,ForcingOrbitQuotient.classes_semantics hM,ForcingOrbitQuotient.projection_semantics hM,ConstructionGermDetectors.representatives_semantics hM,ForcingOrbitChains.family_semantics hM,functions_semantics hM,germs_semantics hM,KuratowskiZF.source_edge,fields_semantics hM]
  exact assigned_ideal hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d tau codes order ranks selection rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder Q pr a currentRoot currentIndex currentIdeal families

theorem ideal_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d tau codes order ranks selection rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder Q pr a currentRoot currentIndex currentIdeal : Fin k) (families : Fin 16 → Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative (idealSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d tau codes order ranks selection rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder Q pr a currentRoot currentIndex currentIdeal families))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let witness := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    {bound := Fin.elim0,free := fun _ => witness}
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (idealSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d tau codes order ranks selection rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder Q pr a currentRoot currentIndex currentIdeal families)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (idealSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d tau codes order ranks selection rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder Q pr a currentRoot currentIndex currentIdeal families)).mp
      (ideal_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d tau codes order ranks selection rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder Q pr a currentRoot currentIndex currentIdeal families hL hChoice)


end PPAC.Migration.ForcingAssignedIdeal
