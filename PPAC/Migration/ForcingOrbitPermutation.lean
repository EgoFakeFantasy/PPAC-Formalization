/- Pinned OrbitAssignments.orbitAssignment_permute:232-238.
Reuse the exact inverse-product cancellation of CorrectedPermutation and the
existing action composition laws; keep the SAME inner Corrected witness. -/
import PPAC.Migration.ForcingOrbitAssignment
import PPAC.Migration.ForcingGermCorrectedPermutation

namespace PPAC.Migration.ForcingOrbitPermutation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingConditionGraphs (Permutation CompositionGraph function_input function_unique)
open ForcingOrbitAssignment (OrbitAssignment orbitAssignment)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem orbitAssignment_permute (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder s sAct sAc d e vertex movedVertex label movedLabel tau movedTau : Fin k)
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hq : ForcingSupportSize.Injection (env (rho 0)) (env I) (env q))
    (hs : Permutation (env I) (env s))
    (hsFix : CompositionGraph (env (rho 0)) (env s) (env q) (env q))
    (hsAct : ForcingProductFamily.Action (env (rho 0)) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)) (env s) (env sAct))
    (hsCohen : ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) (env s) (env sAc))
    (hsD : PureKuratowski.PairMember M (env d) (env e) (env sAc))
    (hsVertex : ForcingComponentMove.Move (env (rho 0)) (env I) (env mul) (env q) (env s) (env vertex) (env movedVertex))
    (hsLabel : PureKuratowski.PairMember M (env label) (env movedLabel) (env s))
    (hsTau : ForcingStabilizer.Action (env (rho 6)) (env sAct) (env tau) (env movedTau))
    (h : OrbitAssignment hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (env d) (env vertex) (env label) (env tau)) :
    OrbitAssignment hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (env e) (env movedVertex) (env movedLabel) (env movedTau) := by
  obtain ⟨pi,inv,act,ac,oldD,oldVertex,oldTau,oldLabel,hPi,hFix,hInv,hInverse,hAct,hCohen,hdd,hMove,hTau,hk,hLabel,hCorrected⟩ := h
  obtain ⟨product,hProduct,hProductGraph⟩ := ForcingConditionGraphs.exists_composition hM hs hPi
  have hProductFix := ConstructionGermSeparation.compose_diagrams hq hProductGraph hFix hsFix
  obtain ⟨productInv,hProductInv,hProductInverse⟩ := ForcingConditionGraphs.exists_inverse hM hProduct
  have hProductInvFix := ForcingDiagramCarrier.reverse hProduct hq hProductInverse hProductFix
  have hCancel : CompositionGraph (env I) productInv (env s) inv := by
    intro x z
    constructor
    · intro hxz
      have hx := function_input hInv.1.1 hxz
      obtain ⟨y,hxy,_⟩ := hs.1.1.2 x hx
      have hzx := (hInverse z x).mpr hxz
      exact ⟨hx,y,hxy,(hProductInverse z y).mp ((hProductGraph z y).mpr ⟨function_input hPi.1.1 hzx,x,hzx,hxy⟩)⟩
    · rintro ⟨_,y,hxy,hyz⟩
      obtain ⟨_,t,hzt,hty⟩ := (hProductGraph z y).mp ((hProductInverse z y).mpr hyz)
      have htx := hs.2.1 t x y hty hxy
      exact (hInverse z x).mp (htx ▸ hzt)
  obtain ⟨newAct,hNewAct⟩ := ForcingProductFamily.exists_action hM hp hProductInv
  obtain ⟨newAc,hNewCohen⟩ := ForcingLocalTransport.part_of_action hNewAct
  have hCancelCohen := ForcingAssignmentCosets.cohen_composition hM hp hs hCancel hNewCohen hsCohen hCohen
  have hNewD : PureKuratowski.PairMember M (env e) oldD newAc := by
    obtain ⟨_,mid,hMid,hOut⟩ := (hCancelCohen (env d) oldD).mp hdd
    exact (function_unique (ForcingLocalTransport.part_permutation hsCohen).1.1 hMid hsD) ▸ hOut
  obtain ⟨newVertex,hNewVertex⟩ := ForcingComponentMove.exists_move hM hProductInv hProductInvFix (ForcingComponentMove.target_vertex hsVertex)
  have hVertexEq := ForcingComponentMove.move_unique hM (ConstructionGermSeparation.move_composition hCancel hsVertex hNewVertex) hMove
  have hNewMove : ForcingComponentMove.Move (env (rho 0)) (env I) (env mul) (env q) productInv (env movedVertex) oldVertex := hVertexEq ▸ hNewVertex
  have hNewLabel : PureKuratowski.PairMember M oldLabel (env movedLabel) product :=
    (hProductGraph oldLabel (env movedLabel)).mpr ⟨function_input hPi.1.1 hLabel,env label,hLabel,hsLabel⟩
  have hCancelAct := ForcingProductFamily.multiplication hM hp hs hCancel hNewAct hsAct hAct
  obtain ⟨newTau,hNewTau⟩ := ForcingNameConjugacy.exists_action hM (ForcingProductFamily.action_permutation hNewAct).1 (env movedTau)
  have hCompositeTau := ForcingNameConjugacy.composition hM (ForcingProductFamily.action_permutation hNewAct).1
    (ForcingProductFamily.action_permutation hsAct).1 hCancelAct hsTau hNewTau
  have hTauEq := ForcingNameConjugacy.unique hM (ForcingProductFamily.action_permutation hAct).1 hCompositeTau hTau
  have hNewName : ForcingStabilizer.Action (env (rho 6)) newAct (env movedTau) oldTau := hTauEq ▸ hNewTau
  exact ⟨product,productInv,newAct,newAc,oldD,oldVertex,oldTau,oldLabel,hProduct,hProductFix,
    hProductInv,hProductInverse,hNewAct,hNewCohen,hNewD,hNewMove,hNewName,hk,hNewLabel,hCorrected⟩

def permutationSentence {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder s sAct sAc d e vertex movedVertex label movedLabel tau movedTau : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I s))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph (rho 0) s q q))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.action (rho 0) (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6) s sAct))
    (.imp (ProjectSyntax.encode id (ForcingLocalTransport.cohenPart (rho 1) (rho 2) (rho 3) s sAc))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge sAc d e))
    (.imp (ForcingComponentMove.move (rho 0) I mul q s vertex movedVertex)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge s label movedLabel))
    (.imp (ProjectSyntax.encode id (ForcingStabilizer.action (rho 6) sAct tau movedTau))
    (.imp (orbitAssignment rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id d vertex label tau)
    (orbitAssignment rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id e movedVertex movedLabel movedTau))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ForcingComponentMove.move_freeClosed,ForcingOrbitAssignment.orbitAssignment_freeClosed]

theorem permutation_models {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder s sAct sAc d e vertex movedVertex label movedLabel tau movedTau : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (permutationSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder s sAct sAc d e vertex movedVertex label movedLabel tau movedTau)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingProductFamily.presentation_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),
    ForcingProductFamily.action_semantics (M := M),ForcingLocalTransport.cohenPart_semantics (M := M),
    KuratowskiZF.source_edge,ForcingComponentMove.move_semantics hM,ForcingStabilizer.action_semantics (M := M),
    ForcingOrbitAssignment.orbitAssignment_semantics hM]
  exact orbitAssignment_permute hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder s sAct sAc d e vertex movedVertex label movedLabel tau movedTau

theorem permutation_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder s sAct sAc d e vertex movedVertex label movedLabel tau movedTau : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (permutationSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder s sAct sAc d e vertex movedVertex label movedLabel tau movedTau)) := by
  apply ModelTransfer.derives
  intro M hM
  exact permutation_models rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder s sAct sAc d e vertex movedVertex label movedLabel tau movedTau hM

end PPAC.Migration.ForcingOrbitPermutation
