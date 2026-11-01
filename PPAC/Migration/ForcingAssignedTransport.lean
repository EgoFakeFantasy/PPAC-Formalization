/- Fixed OrbitAssignments.assigned_permute:421-427 and assigned_restrict:436-442.
Keep the same internal orbit and all sixteen field values. Consumers: AssignedGraphs.graphWitness_move and OrbitAssignments graph restriction. -/
import PPAC.Migration.ForcingAssigned
import PPAC.Migration.ForcingOrbitPermutation
import PPAC.Migration.ForcingOrbitAssignment
import PPAC.Migration.ForcingGermCorrectedPermutation

namespace PPAC.Migration.ForcingAssignedTransport
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

open ForcingAssigned (Assigned assigned assigned_freeClosed assigned_semantics context Germs germs germs_freeClosed germs_semantics)

theorem assigned_permute (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E w top K B zero Q s sAct sAc d e vertex movedVertex label movedLabel tau movedTau : Fin k) (families : Fin 16 → Fin k)
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
    (h : Assigned hM env rho I G F mul q bound labels E w top K B zero Q families (env d) (env vertex) (env label) (env tau)) :
    Assigned hM env rho I G F mul q bound labels E w top K B zero Q families (env e) (env movedVertex) (env movedLabel) (env movedTau) := by
  obtain ⟨a,root,chain,codes,order,ranks,selection,rankBound,labelSet,tab,r,germGroup,quotient,nonidentity,high,detector,patternOrder,ha,hFields,hOrbit⟩ := h
  let other := context env a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder
  let up : Fin k → Fin (k+17) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  have hOutput := ForcingOrbitPermutation.orbitAssignment_permute hM other (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) 15 (up w) 14 13 12 11 10 (up top) 9 8 7 6 (up K) (up B) (up zero) 5 4 3 2 1 0 (up s) (up sAct) (up sAc) (up d) (up e) (up vertex) (up movedVertex) (up label) (up movedLabel) (up tau) (up movedTau)
    hp hq hs hsFix hsAct hsCohen hsD hsVertex hsLabel hsTau hOrbit
  exact ⟨a,root,chain,codes,order,ranks,selection,rankBound,labelSet,tab,r,germGroup,quotient,nonidentity,high,detector,patternOrder,ha,hFields,hOutput⟩

def permutationSentence {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q s sAct sAc d e vertex movedVertex label movedLabel tau movedTau : Fin k) (families : Fin 16 → Fin k) : Project.Sentence where
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
    (.imp (assigned rho I G F mul q bound labels E w top K B zero Q families d vertex label tau)
    (assigned rho I G F mul q bound labels E w top K B zero Q families e movedVertex movedLabel movedTau))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ForcingComponentMove.move_freeClosed,assigned_freeClosed]

theorem permutation_models {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q s sAct sAc d e vertex movedVertex label movedLabel tau movedTau : Fin k) (families : Fin 16 → Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (permutationSentence rho I G F mul q bound labels E w top K B zero Q s sAct sAc d e vertex movedVertex label movedLabel tau movedTau families)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingProductFamily.presentation_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),
    ForcingProductFamily.action_semantics (M := M),ForcingLocalTransport.cohenPart_semantics (M := M),
    KuratowskiZF.source_edge,ForcingComponentMove.move_semantics hM,ForcingStabilizer.action_semantics (M := M),
    assigned_semantics hM]
  exact assigned_permute hM env rho I G F mul q bound labels E w top K B zero Q s sAct sAc d e vertex movedVertex label movedLabel tau movedTau families

theorem permutation_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q s sAct sAc d e vertex movedVertex label movedLabel tau movedTau : Fin k) (families : Fin 16 → Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (permutationSentence rho I G F mul q bound labels E w top K B zero Q s sAct sAc d e vertex movedVertex label movedLabel tau movedTau families)) := by
  apply ModelTransfer.derives
  intro M hM
  exact permutation_models rho I G F mul q bound labels E w top K B zero Q s sAct sAc d e vertex movedVertex label movedLabel tau movedTau families hM

theorem assigned_restrict (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q one d vertex vertexT n label tau : Fin k) (families : Fin 16 → Fin k)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hq : ForcingSupportSize.Injection (env (rho 0)) (env I) (env q))
    (hGerms : Germs (env (rho 0)) (env I) (env mul) (env q) (env (families 0)) (env (families 10)))
    (hf : ConstructionComponentCofinal.EncodedArrow (env (rho 0)) (env I) (env mul) (env q) (env vertexT) (env vertex) (env n))
    (h : Assigned hM env rho I G F mul q bound labels E w top K B zero Q families (env d) (env vertex) (env label) (env tau)) :
    Assigned hM env rho I G F mul q bound labels E w top K B zero Q families (env d) (env vertexT) (env label) (env tau) := by
  obtain ⟨a,root,chain,codes,order,ranks,selection,rankBound,labelSet,tab,r,germGroup,quotient,nonidentity,high,detector,patternOrder,ha,hFields,hOrbit⟩ := h
  let other := context env a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder
  let up : Fin k → Fin (k+17) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  have hGerm := hGerms a root germGroup hFields.1 hFields.2.2.2.2.2.2.2.2.2.2.1
  have hOutput := ForcingOrbitAssignment.orbitAssignment_restrict hM other (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) 15 (up w) 14 13 12 11 10 (up top) 9 8 7 6 (up K) (up B) (up zero) 5 4 3 2 1 0 (up one) (up d) (up vertex) (up vertexT) (up n) (up label) (up tau)
    hm hp hq hGerm hf hOrbit
  exact ⟨a,root,chain,codes,order,ranks,selection,rankBound,labelSet,tab,r,germGroup,quotient,nonidentity,high,detector,patternOrder,ha,hFields,hOutput⟩

def restrictSentence {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q one d vertex vertexT n label tau : Fin k) (families : Fin 16 → Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (germs (rho 0) I mul q (families 0) (families 10))
    (.imp (ConstructionComponentCofinal.encodedArrow (rho 0) I mul q vertexT vertex n)
    (.imp (assigned rho I G F mul q bound labels E w top K B zero Q families d vertex label tau)
    (assigned rho I G F mul q bound labels E w top K B zero Q families d vertexT label tau)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      germs_freeClosed,ConstructionComponentCofinal.encodedArrow_freeClosed,
      assigned_freeClosed]

theorem restrict_models {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q one d vertex vertexT n label tau : Fin k) (families : Fin 16 → Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (restrictSentence rho I G F mul q bound labels E w top K B zero Q one d vertex vertexT n label tau families)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingProductFamily.presentation_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    germs_semantics hM,ConstructionComponentCofinal.encodedArrow_semantics hM,
    assigned_semantics hM]
  exact assigned_restrict hM env rho I G F mul q bound labels E w top K B zero Q one d vertex vertexT n label tau families

theorem restrict_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q one d vertex vertexT n label tau : Fin k) (families : Fin 16 → Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (restrictSentence rho I G F mul q bound labels E w top K B zero Q one d vertex vertexT n label tau families)) := by
  apply ModelTransfer.derives
  intro M hM
  exact restrict_models rho I G F mul q bound labels E w top K B zero Q one d vertex vertexT n label tau families hM


end PPAC.Migration.ForcingAssignedTransport
