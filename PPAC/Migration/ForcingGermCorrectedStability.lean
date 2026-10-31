/- Fixed source StableSelectors.corrected_mono:438 and corrected_restrict:511.
Reuse the concrete selector result, the same inverse action and the established
Preliminary laws. Consumer: StableAt and OrbitAssignments, with all conditions
and name witnesses internal to the original pure set language. -/
import PPAC.Migration.ForcingGermCorrected
import PPAC.Migration.ConstructionConcreteSelector

namespace PPAC.Migration.ForcingGermCorrectedStability
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingGermCorrected (Corrected corrected)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem corrected_mono (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau : Fin k)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hRoot : ConstructionComponentCarrier.Code (env root) (env r) (env idx) (env U))
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal (env K))
    (hResult : ConstructionConcreteSelector.Result hM (env w) (env (rho 0)) (env I) (env mul) (env q) (env root) (env chain) (env K) (env zero) (env germGroup) (env quotient) (env projection) (env reps) (env nonidentity) (env detectorDomain) (env detector) (env detectorSites) (env high) (env B) (env (rho 1)) (env (rho 2)) (env patternCarrier) (env patternOrder) (env selectorDomain) (env selector))
    (he : (Project.FirstOrderSemantics.reduct M).mem (env e) (env (rho 3)))
    (hde : ForcingPowerName.Subset (env d) (env e))
    (h : Corrected hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (env d) (env vertex) (env label) (env tau)) :
    Corrected hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (env e) (env vertex) (env label) (env tau) := by
  obtain ⟨pi,cls,hpi,hClass,hSelected,inv,act,ac,movedD,movedVertex,movedLabel,movedTau,
    hPi,hInv,hInverse,hAct,hCohen,hdd,hMove,hLabel,hTau,hPreliminary⟩ := h
  have hac := ForcingLocalTransport.part_permutation hCohen
  have hd := ForcingConditionGraphs.function_input hac.1.1 hdd
  obtain ⟨movedE,hee,_⟩ := hac.1.1.2 (env e) he
  have hMovedE := hac.1.2 (env e) movedE hee
  have hOrder : ForcingCohenOrderAction.OrderPreserving ac := by
    obtain ⟨f,t,hf,hfg,ht,htg,_,hacg⟩ := hCohen
    exact ForcingCohenOrderAction.graph_order hp.2.2.1 ht hacg
  have hMovedSubset := (hOrder (env e) (env d) movedE movedD hee hdd).mpr hde
  obtain ⟨hGerm,_,_,hX,hDet,_,_,_,_,hZero,hHigh,hBits,hCoords,hS,hCover,hWO,_,_⟩ := hResult
  have hSelectedE := ConstructionGermSelected.selected_mono hM hGerm.1 hDet.1 hX hCoords hS hK hCover hWO
    hZero hHigh hBits ((hp.2.2.1 (env d)).mp hd) ((hp.2.2.1 (env e)).mp he) hde hSelected
  have hRootInjection : ForcingSupportSize.Injection (env (rho 0)) (env I) (env r) := by
    obtain ⟨r0,a0,U0,s,b,V,hRoot0,_,hr0,_,_⟩ := hChain.2.2.2.1 (env zero) (env root) hChain.2.1
    obtain ⟨er,_,_⟩ := ConstructionComponentCarrier.code_injective hRoot0 hRoot
    exact er ▸ hr0.1
  exact ⟨pi,cls,hpi,hClass,hSelectedE,inv,act,ac,movedE,movedVertex,movedLabel,movedTau,
    hPi,hInv,hInverse,hAct,hCohen,hee,hMove,hLabel,hTau,
    ForcingGermPreliminary.preliminary_mono hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r hm hp hMovedE hRootInjection hMovedSubset hPreliminary⟩

def monoSentence {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ConstructionComponentCarrier.code root r idx U)
    (.imp (Project.Formula.isOrdinal (.bound K))
    (.imp (ConstructionConcreteSelector.resultFormula w (rho 0) I mul q root chain K zero germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high B (rho 1) (rho 2) patternCarrier patternOrder selectorDomain selector)
    (.imp ( .mem (.bound e) (.bound (rho 3)))
    (.imp (Project.Formula.subset (.bound d) (.bound e))
    (.imp (corrected rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id d vertex label tau)
    (corrected rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id e vertex label tau))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,ConstructionComponentCarrier.code_freeClosed,
      Project.Formula.isOrdinal,ConstructionConcreteSelector.resultFormula_freeClosed,
      Project.Formula.subset,ForcingGermCorrected.corrected_freeClosed]

theorem mono_models {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (monoSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingProductFamily.presentation_semantics (M := M),ConstructionComponentCofinal.chain_semantics hM,
    ConstructionComponentCarrier.code_semantics hM,Project.Formula.satisfies_isOrdinal_iff,
    ConstructionConcreteSelector.resultFormula_semantics hM,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_subset_iff,ForcingGermCorrected.corrected_semantics hM]
  exact corrected_mono hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau

theorem mono_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (monoSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau)) := by
  apply ModelTransfer.derives
  intro M hM
  exact mono_models rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau hM

/-- Pullback retains the literal selected representative and name action. -/
theorem corrected_restrict (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one d vertex vertexT n label tau : Fin k)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hq : ForcingSupportSize.Injection (env (rho 0)) (env I) (env q))
    (hGerm : ConstructionGermCosets.Carrier (env (rho 0)) (env I) (env mul) (env q) (env root) (env germGroup))
    (hf : ConstructionComponentCofinal.EncodedArrow (env (rho 0)) (env I) (env mul) (env q) (env vertexT) (env vertex) (env n))
    (h : Corrected hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (env d) (env vertex) (env label) (env tau)) :
    Corrected hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (env d) (env vertexT) (env label) (env tau) := by
  obtain ⟨pi,cls,hpi,hClass,hSelected,inv,act,ac,movedD,movedVertex,movedLabel,movedTau,
    hPi,hInv,hInverse,hAct,hCohen,hdd,hMove,hLabel,hTau,hPreliminary⟩ := h
  have hFix := ForcingDiagramCarrier.reverse hPi hq hInverse ((hGerm pi).mp hpi).2.1
  have hVertexT : ConstructionComponentCarrier.EncodedVertex (env (rho 0)) (env I) (env mul) (env q) (env vertexT) := by
    obtain ⟨rt,atIdx,Ut,rv,av,Uv,ht,_,hvt,_,_⟩ := hf
    exact ⟨rt,atIdx,Ut,ht,hvt⟩
  obtain ⟨movedT,hMoveT⟩ := ForcingComponentMove.exists_move hM hInv hFix hVertexT
  have hArrow := ForcingComponentMove.move_arrow hMoveT hMove hf
  have hMovedD := (ForcingLocalTransport.part_permutation hCohen).1.2 (env d) movedD hdd
  exact ⟨pi,cls,hpi,hClass,hSelected,inv,act,ac,movedD,movedT,movedLabel,movedTau,
    hPi,hInv,hInverse,hAct,hCohen,hdd,hMoveT,hLabel,hTau,
    ForcingGermPreliminary.preliminary_restrict hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r hm hp hMovedD hArrow hPreliminary⟩

def restrictSentence {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one d vertex vertexT n label tau : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ConstructionGermCosets.carrier (rho 0) I mul q root germGroup)
    (.imp (ConstructionComponentCofinal.encodedArrow (rho 0) I mul q vertexT vertex n)
    (.imp (corrected rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id d vertex label tau)
    (corrected rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id d vertexT label tau)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionGermCosets.carrier_freeClosed,ConstructionComponentCofinal.encodedArrow_freeClosed,
      ForcingGermCorrected.corrected_freeClosed]

theorem restrict_models {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one d vertex vertexT n label tau : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (restrictSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one d vertex vertexT n label tau)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingProductFamily.presentation_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ConstructionGermCosets.carrier_semantics hM,ConstructionComponentCofinal.encodedArrow_semantics hM,
    ForcingGermCorrected.corrected_semantics hM]
  exact corrected_restrict hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one d vertex vertexT n label tau

theorem restrict_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one d vertex vertexT n label tau : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (restrictSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one d vertex vertexT n label tau)) := by
  apply ModelTransfer.derives
  intro M hM
  exact restrict_models rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one d vertex vertexT n label tau hM

end PPAC.Migration.ForcingGermCorrectedStability
