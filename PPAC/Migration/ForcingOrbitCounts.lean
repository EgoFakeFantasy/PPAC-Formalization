/- Fixed OrbitAssignments.assigned_total:485-488 and assigned_onto:504-507.
The full-root count hypothesis at d implies every component inverse count after
an actual full-root move of d, using the existing Cohen action multiplication. -/
import PPAC.Migration.ForcingOrbitDensity

namespace PPAC.Migration.ForcingOrbitCounts
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingConditionGraphs (Permutation CompositionGraph)
open ForcingGermDensity (OrdinalCount)
open ForcingGermCorrectedDensity (InverseCounts inverseCounts)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def RootCounts (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I mul q w top selection r labelSet : Fin k) (d : M.Carrier .set) : Prop :=
  ∀ pi ac movedD, Permutation (env I) pi →
    CompositionGraph (env (rho 0)) pi (env q) (env q) →
    ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) pi ac →
    PureKuratowski.PairMember M d movedD ac →
    OrdinalCount hM env rho mul w top selection r labelSet movedD

def rootCounts {k : Nat} (rho : Fin 7 → Fin k)
    (I mul q w top selection r labelSet d : Fin k) : Project.Formula 1 k :=
  let up : Fin k → Fin (k+3) := fun i => i.succ.succ.succ
  .forallE (.forallE (.forallE
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.permutation (up I) 2))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph (up (rho 0)) 2 (up q) (up q)))
    (.imp (ProjectSyntax.encode id (ForcingLocalTransport.cohenPart (up (rho 1)) (up (rho 2)) (up (rho 3)) 2 1))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 1 (up d) 0))
      (ForcingGermDensity.ordinalCount rho mul w top selection r labelSet up 0)))))))

theorem rootCounts_freeClosed {k : Nat} (rho : Fin 7 → Fin k)
    (I mul q w top selection r labelSet d : Fin k) :
    (rootCounts rho I mul q w top selection r labelSet d).FreeClosed := by
  simp -implicitDefEqProofs [rootCounts,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ForcingGermDensity.ordinalCount_freeClosed]

theorem rootCounts_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k) (rho : Fin 7 → Fin k)
    (I mul q w top selection r labelSet d : Fin k) :
    Project.Formula.satisfies env (rootCounts rho I mul q w top selection r labelSet d) ↔
      RootCounts hM env.bound rho I mul q w top selection r labelSet (env.bound d) := by
  simp only [rootCounts,RootCounts,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),
    ForcingLocalTransport.cohenPart_semantics (M := M),KuratowskiZF.source_edge,
    ForcingGermDensity.ordinalCount_semantics hM]
  rfl

theorem rootCounts_reindex (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (other : Fin n → M.Carrier .set)
    (base : Fin k → Fin n) (he : ∀ i, other (base i) = env i) (rho : Fin 7 → Fin k)
    (I mul q w top selection r labelSet : Fin k) (d : M.Carrier .set) :
    RootCounts hM other (fun j => base (rho j)) (base I) (base mul) (base q) (base w)
      (base top) (base selection) (base r) (base labelSet) d ↔
    RootCounts hM env rho I mul q w top selection r labelSet d := by
  have hR (x y : M.Carrier .set) :
      ForcingMapConditions.MapRel (ForcingProductSymmetry.orderFormula (base (rho 0)) (base mul)) other x y ↔
      ForcingMapConditions.MapRel (ForcingProductSymmetry.orderFormula (rho 0) mul) env x y := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,he]
  simp only [RootCounts,OrdinalCount,ForcingPrincipalFilter.EqF,
    ForcingEquivariantMix.forces_order_congr hR,he]

theorem inverseCounts_of_rootCounts (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B mul q w top selection r labelSet root germGroup s ac d movedD : Fin k)
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hq : ForcingSupportSize.Injection (env (rho 0)) (env I) (env q))
    (hGerm : ConstructionGermCosets.Carrier (env (rho 0)) (env I) (env mul) (env q) (env root) (env germGroup))
    (hs : Permutation (env I) (env s))
    (hsFix : CompositionGraph (env (rho 0)) (env s) (env q) (env q))
    (hsCohen : ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) (env s) (env ac))
    (hdd : PureKuratowski.PairMember M (env d) (env movedD) (env ac))
    (hCount : RootCounts hM env rho I mul q w top selection r labelSet (env d)) :
    InverseCounts hM env rho I mul w top selection r labelSet germGroup (env movedD) := by
  intro pi inv ai target hPi hInv hInverse hInvCohen hMoved
  have hStab := (hGerm pi).mp hPi
  have hInvFix := ForcingDiagramCarrier.reverse hStab.1 hq hInverse hStab.2.1
  obtain ⟨product,hProduct,hProductGraph⟩ := ForcingConditionGraphs.exists_composition hM hInv hs
  have hProductFix := ConstructionGermSeparation.compose_diagrams hq hProductGraph hsFix hInvFix
  obtain ⟨act,hAct⟩ := ForcingProductFamily.exists_action hM hp hProduct
  obtain ⟨productCohen,hProductCohen⟩ := ForcingLocalTransport.part_of_action hAct
  have hComposition := ForcingAssignmentCosets.cohen_composition hM hp hs hProductGraph hInvCohen hsCohen hProductCohen
  have hTarget : PureKuratowski.PairMember M (env d) target productCohen :=
    (hComposition (env d) target).mpr ⟨ForcingConditionGraphs.function_input (ForcingLocalTransport.part_permutation hsCohen).1.1 hdd,env movedD,hdd,hMoved⟩
  exact hCount product productCohen target hProduct hProductFix hProductCohen hTarget

def countSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B mul q w top selection r labelSet root germGroup s ac d movedD : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ConstructionGermCosets.carrier (rho 0) I mul q root germGroup)
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I s))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph (rho 0) s q q))
    (.imp (ProjectSyntax.encode id (ForcingLocalTransport.cohenPart (rho 1) (rho 2) (rho 3) s ac))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge ac d movedD))
    (.imp (rootCounts rho I mul q w top selection r labelSet d)
      (inverseCounts rho I mul w top selection r labelSet germGroup movedD)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionGermCosets.carrier_freeClosed,rootCounts_freeClosed,ForcingGermCorrectedDensity.inverseCounts_freeClosed]

theorem count_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B mul q w top selection r labelSet root germGroup s ac d movedD : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (countSentence rho I K B mul q w top selection r labelSet root germGroup s ac d movedD)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingProductFamily.presentation_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ConstructionGermCosets.carrier_semantics hM,ForcingConditionGraphs.permutation_semantics (M := M),
    ForcingConditionGraphs.compositionGraph_semantics (M := M),ForcingLocalTransport.cohenPart_semantics (M := M),
    KuratowskiZF.source_edge,rootCounts_semantics hM,ForcingGermCorrectedDensity.inverseCounts_semantics hM]
  exact inverseCounts_of_rootCounts hM env rho I K B mul q w top selection r labelSet root germGroup s ac d movedD

theorem count_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B mul q w top selection r labelSet root germGroup s ac d movedD : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (countSentence rho I K B mul q w top selection r labelSet root germGroup s ac d movedD)) := by
  apply ModelTransfer.derives
  intro M hM
  exact count_models rho I K B mul q w top selection r labelSet root germGroup s ac d movedD hM

end PPAC.Migration.ForcingOrbitCounts
