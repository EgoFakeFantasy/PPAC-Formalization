/- Fixed StableSelectors.forcedAvailable_permute_iff:550 and
forcedAvailability_permute:568. Transport the actual normalized local witness
and the exact ideal, using existing subdiagram, support and EqF covariance.
Direct consumer: StableSelectors.stableAt_permute:589. -/
import PPAC.Migration.ForcingForcedAvailability
import PPAC.Migration.ForcingPersistentCovariance
import PPAC.Migration.ForcingLocalNameTransport

namespace PPAC.Migration.ForcingForcedAvailabilityTransport
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingForcedAvailability (Available Carrier)
open ForcingProductSymmetry (orderFormula)
open ForcingConditionGraphs (CompositionGraph)
open ForcingSupportSize (Injection)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem available_permute_iff (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul act : Fin k)
    {I K B w G F mu pi inv c ai one bound ac d movedD r movedRoot tau movedTau n : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hData : ForcingProductCovariance.SystemData (fun j => env (rho j)) I K B w G F mu pi inv c (env act) ai)
    (hBound : ForcingSupportedNames.Supported (fun j => env (rho j)) G bound)
    (hCohen : ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) pi ac)
    (hdd : PureKuratowski.PairMember M d movedD ac)
    (hr : Injection (env (rho 0)) I r) (hMovedRoot : Injection (env (rho 0)) I movedRoot)
    (hComp : CompositionGraph (env (rho 0)) pi r movedRoot)
    (hTau : ForcingStabilizer.Action (env (rho 6)) (env act) tau movedTau) :
    Available (orderFormula (rho 0) mul) env (fun j => env (rho j)) G F (env mul) bound movedD movedRoot movedTau n ↔
      Available (orderFormula (rho 0) mul) env (fun j => env (rho j)) G F (env mul) bound d r tau n := by
  obtain ⟨hp,hG,hPi,hInv,hInverse,hConj,hConjGraph,hAct,hAI,hF⟩ := hData
  have hData : ForcingProductCovariance.SystemData (fun j => env (rho j)) I K B w G F mu pi inv c (env act) ai :=
    ⟨hp,hG,hPi,hInv,hInverse,hConj,hConjGraph,hAct,hAI,hF⟩
  have hActEnd := (ForcingProductFamily.action_permutation hAct).1
  have hAIEnd := (ForcingProductFamily.action_permutation hAI).1
  constructor
  · rintro ⟨s,A,H,sigma,hs,hSub,hRange,hFix,hLocal,hEq⟩
    have hsI := (hp.2.2.2.1 s).mp hs
    obtain ⟨back,hBackI,hBack⟩ := ForcingDiagramAction.exists_permute hM hInv hsI
    have hBackSub := ForcingDiagramOrder.permute_sub
      (ForcingDiagramCarrier.reverse hPi hr hInverse hComp) hBack hSub
    obtain ⟨backRange,hImage,_⟩ := ForcingLabelConjugacy.exists_image hM hInv.1 (J := A)
    obtain ⟨backFix,hBackFix⟩ := ForcingLabelPermutations.exists_fixing hM G backRange
    obtain ⟨reverseConj,hReverse⟩ := ForcingLocalNameTransport.reverse_data hM hData
    obtain ⟨nu,hNu⟩ := ForcingNameConjugacy.exists_action hM hAIEnd sigma
    have hSubset : ForcingPowerName.Subset A I := by
      intro x hx
      obtain ⟨j,_,hjx⟩ := (hRange x).mp hx
      exact hsI.1.2 j x hjx
    have hNuLocal := ForcingLocalNameTransport.local_name_move hM hReverse hBound hSubset hImage hFix hBackFix hLocal hNu
    have hInverseAction := ForcingProductCovariance.inverse hM hp hPi hInverse hAct hAI
    have hForwardNu := ForcingNameConjugacy.inverse_action hM hAIEnd hActEnd
      (fun x y => (hInverseAction y x).symm) (ForcingHS.isName hLocal.1.1) hNu
    exact ⟨back,backRange,backFix,nu,(hp.2.2.2.1 back).mpr hBackI,hBackSub,
      ForcingLocalNameTransport.range_image hRange hBack hImage,hBackFix,hNuLocal,
      (ForcingPersistentCovariance.eqF_transport_iff hM env rho mul act hm hp hPi hAct hCohen hdd hr hMovedRoot hComp hForwardNu hTau).mp hEq⟩
  · rintro ⟨s,A,H,sigma,hs,hSub,hRange,hFix,hLocal,hEq⟩
    have hsI := (hp.2.2.2.1 s).mp hs
    obtain ⟨movedSub,hMovedSubI,hMovedSub⟩ := ForcingDiagramAction.exists_permute hM hPi hsI
    obtain ⟨movedRange,hImage,_⟩ := ForcingLabelConjugacy.exists_image hM hPi.1 (J := A)
    obtain ⟨movedFix,hMovedFix⟩ := ForcingLabelPermutations.exists_fixing hM G movedRange
    obtain ⟨movedSigma,hSigma⟩ := ForcingNameConjugacy.exists_action hM hActEnd sigma
    have hSubset : ForcingPowerName.Subset A I := by
      intro x hx
      obtain ⟨j,_,hjx⟩ := (hRange x).mp hx
      exact hsI.1.2 j x hjx
    exact ⟨movedSub,movedRange,movedFix,movedSigma,(hp.2.2.2.1 movedSub).mpr hMovedSubI,
      ForcingDiagramOrder.permute_sub hComp hMovedSub hSub,
      ForcingLocalNameTransport.range_image hRange hMovedSub hImage,hMovedFix,
      ForcingLocalNameTransport.local_name_move hM hData hBound hSubset hImage hFix hMovedFix hLocal hSigma,
      (ForcingPersistentCovariance.eqF_transport_iff hM env rho mul act hm hp hPi hAct hCohen hdd hr hMovedRoot hComp hSigma hTau).mpr hEq⟩

theorem carrier_permute_iff (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul act : Fin k)
    {I K B w G F mu pi inv c ai one bound ac d movedD r movedRoot tau movedTau index U : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hData : ForcingProductCovariance.SystemData (fun j => env (rho j)) I K B w G F mu pi inv c (env act) ai)
    (hBound : ForcingSupportedNames.Supported (fun j => env (rho j)) G bound)
    (hCohen : ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) pi ac)
    (hdd : PureKuratowski.PairMember M d movedD ac)
    (hr : Injection (env (rho 0)) I r) (hMovedRoot : Injection (env (rho 0)) I movedRoot)
    (hComp : CompositionGraph (env (rho 0)) pi r movedRoot)
    (hTau : ForcingStabilizer.Action (env (rho 6)) (env act) tau movedTau) :
    Carrier (orderFormula (rho 0) mul) env (fun j => env (rho j)) G F (env mul) bound movedD movedRoot index movedTau U ↔
      Carrier (orderFormula (rho 0) mul) env (fun j => env (rho j)) G F (env mul) bound d r index tau U := by
  have hAvailable (n : M.Carrier .set) := available_permute_iff hM env rho mul act hm hData hBound hCohen hdd hr hMovedRoot hComp hTau (n := n)
  simp only [Carrier,hAvailable]

def availableSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mu pi inv c ai one bound ac d movedD r movedRoot tau movedTau mul act n : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductCovariance.systemData rho I K B w G F mu pi inv c act ai))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho G bound))
    (.imp (ProjectSyntax.encode id (ForcingLocalTransport.cohenPart (rho 1) (rho 2) (rho 3) pi ac))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge ac d movedD))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection r (rho 0) I))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection movedRoot (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph (rho 0) pi r movedRoot))
    (.imp (ProjectSyntax.encode id (ForcingStabilizer.action (rho 6) act tau movedTau))
    (.iff (ForcingForcedAvailability.available (orderFormula (rho 0) mul) id rho G F mul bound movedD movedRoot movedTau n) (ForcingForcedAvailability.available (orderFormula (rho 0) mul) id rho G F mul bound d r tau n)))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ForcingForcedAvailability.available_freeClosed]

theorem available_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mu pi inv c ai one bound ac d movedD r movedRoot tau movedTau mul act n : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (availableSentence rho I K B w G F mu pi inv c ai one bound ac d movedD r movedRoot tau movedTau mul act n)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingProductCovariance.systemData_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ForcingLocalTransport.cohenPart_semantics (M := M),
    KuratowskiZF.source_edge,ForcingSupportSize.injection_semantics (M := M),
    ForcingConditionGraphs.compositionGraph_semantics (M := M),ForcingStabilizer.action_semantics (M := M),
    ForcingForcedAvailability.available_semantics hM]
  exact available_permute_iff hM env rho mul act

theorem available_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mu pi inv c ai one bound ac d movedD r movedRoot tau movedTau mul act n : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (availableSentence rho I K B w G F mu pi inv c ai one bound ac d movedD r movedRoot tau movedTau mul act n)) := by
  apply ModelTransfer.derives
  intro M hM
  exact available_models rho I K B w G F mu pi inv c ai one bound ac d movedD r movedRoot tau movedTau mul act n hM

def carrierSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mu pi inv c ai one bound ac d movedD r movedRoot tau movedTau mul act index U : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductCovariance.systemData rho I K B w G F mu pi inv c act ai))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho G bound))
    (.imp (ProjectSyntax.encode id (ForcingLocalTransport.cohenPart (rho 1) (rho 2) (rho 3) pi ac))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge ac d movedD))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection r (rho 0) I))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection movedRoot (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph (rho 0) pi r movedRoot))
    (.imp (ProjectSyntax.encode id (ForcingStabilizer.action (rho 6) act tau movedTau))
    (.iff (ForcingForcedAvailability.carrier (orderFormula (rho 0) mul) id rho G F mul bound movedD movedRoot index movedTau U) (ForcingForcedAvailability.carrier (orderFormula (rho 0) mul) id rho G F mul bound d r index tau U)))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ForcingForcedAvailability.carrier_freeClosed]

theorem carrier_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mu pi inv c ai one bound ac d movedD r movedRoot tau movedTau mul act index U : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (carrierSentence rho I K B w G F mu pi inv c ai one bound ac d movedD r movedRoot tau movedTau mul act index U)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingProductCovariance.systemData_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ForcingLocalTransport.cohenPart_semantics (M := M),
    KuratowskiZF.source_edge,ForcingSupportSize.injection_semantics (M := M),
    ForcingConditionGraphs.compositionGraph_semantics (M := M),ForcingStabilizer.action_semantics (M := M),
    ForcingForcedAvailability.carrier_semantics hM]
  exact carrier_permute_iff hM env rho mul act

theorem carrier_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mu pi inv c ai one bound ac d movedD r movedRoot tau movedTau mul act index U : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (carrierSentence rho I K B w G F mu pi inv c ai one bound ac d movedD r movedRoot tau movedTau mul act index U)) := by
  apply ModelTransfer.derives
  intro M hM
  exact carrier_models rho I K B w G F mu pi inv c ai one bound ac d movedD r movedRoot tau movedTau mul act index U hM

end PPAC.Migration.ForcingForcedAvailabilityTransport
