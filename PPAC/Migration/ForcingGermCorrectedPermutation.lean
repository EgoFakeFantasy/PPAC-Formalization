/- Fixed StableSelectors.corrected_permute:491. Construct the actual product
representative, its inverse and selected quotient class. Cancel the same outer
permutation on all four coordinates using existing action-composition laws. -/
import PPAC.Migration.ForcingGermCorrected
import PPAC.Migration.ConstructionConcreteSelector

namespace PPAC.Migration.ForcingGermCorrectedPermutation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingGermCorrected (Corrected corrected)
open ForcingConditionGraphs (Permutation InverseGraph CompositionGraph function_input function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem corrected_permute (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices projection reps detectorDomain detectorSites patternCarrier selectorDomain selector s sAct sAc d e vertex movedVertex label movedLabel tau movedTau : Fin k)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hq : ForcingSupportSize.Injection (env (rho 0)) (env I) (env q))
    (hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal (env K))
    (hResult : ConstructionConcreteSelector.Result hM (env w) (env (rho 0)) (env I) (env mul) (env q) (env root) (env chain) (env K) (env zero) (env germGroup) (env quotient) (env projection) (env reps) (env nonidentity) (env detectorDomain) (env detector) (env detectorSites) (env high) (env B) (env (rho 1)) (env (rho 2)) (env patternCarrier) (env patternOrder) (env selectorDomain) (env selector))
    (hsGerm : (Project.FirstOrderSemantics.reduct M).mem (env s) (env germGroup))
    (hsAct : ForcingProductFamily.Action (env (rho 0)) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)) (env s) (env sAct))
    (hsCohen : ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) (env s) (env sAc))
    (hsD : PureKuratowski.PairMember M (env d) (env e) (env sAc))
    (hsVertex : ForcingComponentMove.Move (env (rho 0)) (env I) (env mul) (env q) (env s) (env vertex) (env movedVertex))
    (hsLabel : PureKuratowski.PairMember M (env label) (env movedLabel) (env s))
    (hsTau : ForcingStabilizer.Action (env (rho 6)) (env sAct) (env tau) (env movedTau))
    (h : Corrected hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (env d) (env vertex) (env label) (env tau)) :
    Corrected hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (env e) (env movedVertex) (env movedLabel) (env movedTau) := by
  obtain ⟨pi,cls,hpi,hClass,hSelected,inv,act,ac,oldD,oldVertex,oldLabel,oldTau,
    hPi,hInv,hInverse,hAct,hCohen,hdd,hMove,hLabel,hTau,hPreliminary⟩ := h
  obtain ⟨hGerm,_,_,hNX,hDet,_,_,_,_,_,hHigh,hBits,hCoords,_,hCover,hOrder,_,_⟩ := hResult
  have hsStab := (hGerm.1 (env s)).mp hsGerm
  have hpiStab := (hGerm.1 pi).mp hpi
  obtain ⟨product,hProduct,hProductGraph⟩ := ForcingConditionGraphs.exists_composition hM hsStab.1 hPi
  have hProductStab := ConstructionGermSeparation.stabilizes_composition hM hm hJ hq hsStab hpiStab hProduct hProductGraph
  have hProductGerm := (hGerm.1 product).mpr hProductStab
  obtain ⟨productInv,hProductInv,hProductInverse⟩ := ForcingConditionGraphs.exists_inverse hM hProduct
  have hProductInvStab := ConstructionGermSeparation.stabilizes_inverse hM hq hProductStab hProductInv hProductInverse
  have hCancel : CompositionGraph (env I) productInv (env s) inv := by
    intro x z
    constructor
    · intro hxz
      have hx := function_input hInv.1.1 hxz
      obtain ⟨y,hxy,_⟩ := hsStab.1.1.1.2 x hx
      have hzx := (hInverse z x).mpr hxz
      exact ⟨hx,y,hxy,(hProductInverse z y).mp ((hProductGraph z y).mpr ⟨function_input hPi.1.1 hzx,x,hzx,hxy⟩)⟩
    · rintro ⟨_,y,hxy,hyz⟩
      obtain ⟨_,t,hzt,hty⟩ := (hProductGraph z y).mp ((hProductInverse z y).mpr hyz)
      have htx := hsStab.1.2.1 t x y hty hxy
      exact (hInverse z x).mp (htx ▸ hzt)
  obtain ⟨newClass,hNewClass⟩ := ConstructionGermCosets.exists_class hM (env w) (env (rho 0)) (env chain) (env germGroup) product
  obtain ⟨quotAct,hQuotAct⟩ := ConstructionGermLeftAction.construction hM hw hm hJ hq hChain hGerm.1 hGerm.2.2.1 hsGerm
  have hClassEdge := (hQuotAct.2 cls newClass).mpr ⟨ConstructionGermSelected.selected_mem hSelected,pi,product,hpi,hProductGerm,hClass,hNewClass,hProductGraph⟩
  have hsMoved : ConstructionCohenCompatibility.Moved (env s) (env d) (env e) := by
    obtain ⟨f,t,_,hf,_,ht,_,hGraph⟩ := hsCohen
    obtain ⟨hd,_,hImage⟩ := (hGraph (env d) (env e)).mp hsD
    exact ConstructionCohenCompatibility.moved_of_image hM hp.1 hp.2.1 hf ht ((hp.2.2.1 (env d)).mp hd) hImage
  have hSelectedE := ConstructionGermSelected.selected_permute hM hw hm hJ hq hChain hGerm.1 hGerm.2.2.1 hDet hNX hCoords hK
    hCover hOrder ((hBits (env zero)).mpr (Or.inl hHigh.predecessor_mem)) hBits.predecessor_mem hsGerm hsMoved hQuotAct hSelected hClassEdge
  obtain ⟨newAct,hNewAct⟩ := ForcingProductFamily.exists_action hM hp hProductInv
  obtain ⟨newAc,hNewCohen⟩ := ForcingLocalTransport.part_of_action hNewAct
  have hCancelCohen := ForcingAssignmentCosets.cohen_composition hM hp hsStab.1 hCancel hNewCohen hsCohen hCohen
  have hNewD : PureKuratowski.PairMember M (env e) oldD newAc := by
    obtain ⟨_,mid,hMid,hOut⟩ := (hCancelCohen (env d) oldD).mp hdd
    exact (function_unique (ForcingLocalTransport.part_permutation hsCohen).1.1 hMid hsD) ▸ hOut
  obtain ⟨newVertex,hNewVertex⟩ := ForcingComponentMove.exists_move hM hProductInv hProductInvStab.2.1 (ForcingComponentMove.target_vertex hsVertex)
  have hVertexEq := ForcingComponentMove.move_unique hM (ConstructionGermSeparation.move_composition hCancel hsVertex hNewVertex) hMove
  have hNewMove : ForcingComponentMove.Move (env (rho 0)) (env I) (env mul) (env q) productInv (env movedVertex) oldVertex := hVertexEq ▸ hNewVertex
  have hNewLabel : PureKuratowski.PairMember M (env movedLabel) oldLabel productInv := by
    obtain ⟨_,mid,hMid,hOut⟩ := (hCancel (env label) oldLabel).mp hLabel
    exact (function_unique hsStab.1.1.1 hMid hsLabel) ▸ hOut
  have hCancelAct := ForcingProductFamily.multiplication hM hp hsStab.1 hCancel hNewAct hsAct hAct
  obtain ⟨newTau,hNewTau⟩ := ForcingNameConjugacy.exists_action hM (ForcingProductFamily.action_permutation hNewAct).1 (env movedTau)
  have hCompositeTau := ForcingNameConjugacy.composition hM (ForcingProductFamily.action_permutation hNewAct).1
    (ForcingProductFamily.action_permutation hsAct).1 hCancelAct hsTau hNewTau
  have hTauEq := ForcingNameConjugacy.unique hM (ForcingProductFamily.action_permutation hAct).1 hCompositeTau hTau
  have hNewName : ForcingStabilizer.Action (env (rho 6)) newAct (env movedTau) oldTau := hTauEq ▸ hNewTau
  exact ⟨product,newClass,hProductGerm,hNewClass,hSelectedE,productInv,newAct,newAc,oldD,oldVertex,oldLabel,oldTau,
    hProduct,hProductInv,hProductInverse,hNewAct,hNewCohen,hNewD,hNewMove,hNewLabel,hNewName,hPreliminary⟩

def permutationSentence {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices projection reps detectorDomain detectorSites patternCarrier selectorDomain selector s sAct sAc d e vertex movedVertex label movedLabel tau movedTau : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (Project.Formula.isOmega (.bound w))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (Project.Formula.isOrdinal (.bound K))
    (.imp (ConstructionConcreteSelector.resultFormula w (rho 0) I mul q root chain K zero germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high B (rho 1) (rho 2) patternCarrier patternOrder selectorDomain selector)
    (.imp (.mem (.bound s) (.bound germGroup))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.action (rho 0) (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6) s sAct))
    (.imp (ProjectSyntax.encode id (ForcingLocalTransport.cohenPart (rho 1) (rho 2) (rho 3) s sAc))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge sAc d e))
    (.imp (ForcingComponentMove.move (rho 0) I mul q s vertex movedVertex)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge s label movedLabel))
    (.imp (ProjectSyntax.encode id (ForcingStabilizer.action (rho 6) sAct tau movedTau))
    (.imp (corrected rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id d vertex label tau)
    (corrected rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id e movedVertex movedLabel movedTau)))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,Project.Formula.isOrdinal,
      ConstructionConcreteSelector.resultFormula_freeClosed,ForcingComponentMove.move_freeClosed,
      ForcingGermCorrected.corrected_freeClosed]

theorem permutation_models {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices projection reps detectorDomain detectorSites patternCarrier selectorDomain selector s sAct sAc d e vertex movedVertex label movedLabel tau movedTau : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (permutationSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices projection reps detectorDomain detectorSites patternCarrier selectorDomain selector s sAct sAc d e vertex movedVertex label movedLabel tau movedTau)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductFamily.presentation_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ConstructionComponentCofinal.chain_semantics hM,Project.Formula.satisfies_isOrdinal_iff,
    ConstructionConcreteSelector.resultFormula_semantics hM,Project.Formula.satisfies_mem_iff,
    ForcingProductFamily.action_semantics (M := M),ForcingLocalTransport.cohenPart_semantics (M := M),
    KuratowskiZF.source_edge,ForcingComponentMove.move_semantics hM,
    ForcingStabilizer.action_semantics (M := M),ForcingGermCorrected.corrected_semantics hM]
  exact corrected_permute hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices projection reps detectorDomain detectorSites patternCarrier selectorDomain selector s sAct sAc d e vertex movedVertex label movedLabel tau movedTau

theorem permutation_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices projection reps detectorDomain detectorSites patternCarrier selectorDomain selector s sAct sAc d e vertex movedVertex label movedLabel tau movedTau : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (permutationSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices projection reps detectorDomain detectorSites patternCarrier selectorDomain selector s sAct sAc d e vertex movedVertex label movedLabel tau movedTau)) := by
  apply ModelTransfer.derives
  intro M hM
  exact permutation_models rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices projection reps detectorDomain detectorSites patternCarrier selectorDomain selector s sAct sAc d e vertex movedVertex label movedLabel tau movedTau hM

end PPAC.Migration.ForcingGermCorrectedPermutation
