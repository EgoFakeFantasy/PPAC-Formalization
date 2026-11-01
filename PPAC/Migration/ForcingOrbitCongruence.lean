/- Pinned OrbitAssignments.orbitAssignment_congr:240-245.
S.Name is the existing HS subtype (SymmetricNames:49); preserve that domain.
Consume existing EqF transport and corrected_congr on the same inverse witness. -/
import PPAC.Migration.ForcingOrbitAssignment
import PPAC.Migration.ForcingGermCorrectedCongruence

namespace PPAC.Migration.ForcingOrbitCongruence
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingOrbitAssignment (OrbitAssignment orbitAssignment)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem orbitAssignment_congr (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one mu d vertex localRoot index U label tau sigma : Fin k)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hCode : ConstructionComponentCarrier.Code (env vertex) (env localRoot) (env index) (env U))
    (hs : ForcingClassEvaluation.Predicate (ForcingPairUnion.domain rho G F) env (env sigma))
    (he : ForcingPrincipalFilter.EqF (ForcingProductSymmetry.orderFormula (rho 0) mul) env (env (rho 6)) (env d) (env localRoot) (env tau) (env sigma))
    (h : OrbitAssignment hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (env d) (env vertex) (env label) (env tau)) :
    OrbitAssignment hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (env d) (env vertex) (env label) (env sigma) := by
  obtain ⟨pi,inv,act,ac,movedD,movedVertex,movedTau,movedLabel,hPi,hFix,hInv,hInverse,hAct,hCohen,hdd,hMove,hTau,hk,hLabel,hCorrected⟩ := h
  have hReverse : ForcingConditionGraphs.InverseGraph inv pi := fun x y => (hInverse y x).symm
  obtain ⟨conj,hConjPerm,hConj⟩ := ForcingConjugationGraph.exists_graph hM hG hInv hPi hReverse
  obtain ⟨forward,hForward⟩ := ForcingProductFamily.exists_action hM hp hPi
  have hData : ForcingProductCovariance.SystemData (fun j => env (rho j))
      (env I) (env K) (env B) (env w) (env G) (env F) (env mu) inv pi conj act forward :=
    ⟨hp,hG,hInv,hPi,hReverse,hConjPerm,hConj,hAct,hForward,hF⟩
  obtain ⟨movedSigma,hSigma⟩ := ForcingNameConjugacy.exists_action hM (ForcingProductFamily.action_permutation hAct).1 (env sigma)
  have hMovedHS := (ForcingPairUnion.domain_semantics env rho G F movedSigma).mpr
    (ForcingProductCovariance.hs_action hM hData (env sigma)
      ((ForcingPairUnion.domain_semantics env rho G F (env sigma)).mp hs) movedSigma hSigma)
  obtain ⟨r0,a0,U0,movedRoot,hCode0,hMovedCode,hr0,hMovedRoot,hComp⟩ := hMove
  obtain ⟨er,_,_⟩ := ConstructionComponentCarrier.code_injective hCode0 hCode
  have hOriginal : ForcingPrincipalFilter.EqF (ForcingProductSymmetry.orderFormula (rho 0) mul) env (env (rho 6)) (env d) r0 (env tau) (env sigma) := er.symm ▸ he
  let other : Fin (k+1) → M.Carrier .set := Fin.cases act env
  let up : Fin k → Fin (k+1) := Fin.succ
  have hOrder (x y : M.Carrier .set) :
      ForcingMapConditions.MapRel (ForcingProductSymmetry.orderFormula (up (rho 0)) (up mul)) other x y ↔
      ForcingMapConditions.MapRel (ForcingProductSymmetry.orderFormula (rho 0) mul) env x y := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,other,up,Fin.cases_succ]
  have hReindex (dd rr tt ss : M.Carrier .set) :
      ForcingPrincipalFilter.EqF (ForcingProductSymmetry.orderFormula (up (rho 0)) (up mul)) other (env (rho 6)) dd rr tt ss ↔
      ForcingPrincipalFilter.EqF (ForcingProductSymmetry.orderFormula (rho 0) mul) env (env (rho 6)) dd rr tt ss := by
    simp only [ForcingPrincipalFilter.EqF,ForcingEquivariantMix.forces_order_congr hOrder]
  have hTransport := ForcingPersistentCovariance.eqF_transport_iff hM other (fun j => up (rho j)) (up mul) 0
    hm hp hInv hAct hCohen hdd hr0.1 hMovedRoot.1 hComp hTau hSigma
  have hEqMoved := (hReindex movedD movedRoot movedTau movedSigma).mp
    (hTransport.mpr ((hReindex (env d) r0 (env tau) (env sigma)).mpr hOriginal))
  let targetEnv : Fin (k+8) → M.Carrier .set := Fin.cases movedD (Fin.cases movedVertex (Fin.cases movedLabel
    (Fin.cases movedTau (Fin.cases movedSigma (Fin.cases movedRoot (Fin.cases a0 (Fin.cases U0 env)))))))
  let lift : Fin k → Fin (k+8) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ
  have henv (i : Fin k) : targetEnv (lift i) = env i := rfl
  have hTargetOrder (x y : M.Carrier .set) :
      ForcingMapConditions.MapRel (ForcingProductSymmetry.orderFormula (lift (rho 0)) (lift mul)) targetEnv x y ↔
      ForcingMapConditions.MapRel (ForcingProductSymmetry.orderFormula (rho 0) mul) env x y := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,henv]
  have hTargetHS : ForcingClassEvaluation.Predicate (ForcingPairUnion.domain (fun j => lift (rho j)) (lift G) (lift F)) targetEnv movedSigma :=
    (ForcingPairUnion.domain_semantics targetEnv (fun j => lift (rho j)) (lift G) (lift F) movedSigma).mpr
      ((ForcingPairUnion.domain_semantics env rho G F movedSigma).mp hMovedHS)
  have hTargetEq : ForcingPrincipalFilter.EqF (ForcingProductSymmetry.orderFormula (lift (rho 0)) (lift mul)) targetEnv (env (rho 6)) movedD movedRoot movedTau movedSigma := by
    simpa only [ForcingPrincipalFilter.EqF,ForcingEquivariantMix.forces_order_congr hTargetOrder] using hEqMoved
  have hInput := (ForcingOrbitAssignment.corrected_reindex hM env targetEnv lift henv rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder movedD movedVertex movedLabel movedTau).mpr hCorrected
  have hOutput := ForcingGermCorrectedCongruence.corrected_congr hM targetEnv (fun j => lift (rho j)) (lift I) (lift G) (lift F) (lift mul) (lift q) (lift bound) (lift labels) (lift E) (lift root) (lift w) (lift chain) (lift codes) (lift order) (lift ranks) (lift selection) (lift top) (lift rankBound) (lift labelSet) (lift tab) (lift r) (lift K) (lift B) (lift zero) (lift germGroup) (lift quotient) (lift nonidentity) (lift high) (lift detector) (lift patternOrder) (lift one) (lift mu) 0 1 5 6 7 2 3 4
    hm hp hG hF hMovedCode hTargetHS hTargetEq hInput
  refine ⟨pi,inv,act,ac,movedD,movedVertex,movedSigma,movedLabel,hPi,hFix,hInv,hInverse,hAct,hCohen,hdd,?_,hSigma,hk,hLabel,?_⟩
  · exact ⟨r0,a0,U0,movedRoot,hCode0,hMovedCode,hr0,hMovedRoot,hComp⟩
  · exact (ForcingOrbitAssignment.corrected_reindex hM env targetEnv lift henv rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder movedD movedVertex movedLabel movedSigma).mp hOutput

def congrSentence {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one mu d vertex localRoot index U label tau sigma : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.imp (ConstructionComponentCarrier.code vertex localRoot index U)
    (.imp (ProjectSyntax.encode id (MinimalPredicates.pred (ForcingPairUnion.domain rho G F) id sigma))
    (.imp (ForcingPrincipalFilter.eqF (ForcingProductSymmetry.orderFormula (rho 0) mul) id (rho 6) d localRoot tau sigma)
    (.imp (orbitAssignment rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id d vertex label tau)
    (orbitAssignment rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id d vertex label sigma)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionComponentCarrier.code_freeClosed,ForcingPrincipalFilter.eqF_freeClosed,
      ForcingOrbitAssignment.orbitAssignment_freeClosed]

theorem congr_models {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one mu d vertex localRoot index U label tau sigma : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (congrSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one mu d vertex localRoot index U label tau sigma)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ConstructionComponentCarrier.code_semantics hM,
    ForcingClassEvaluation.predicate_semantics (M := M),ForcingPrincipalFilter.eqF_semantics hM,
    ForcingOrbitAssignment.orbitAssignment_semantics hM]
  exact orbitAssignment_congr hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one mu d vertex localRoot index U label tau sigma

theorem congr_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one mu d vertex localRoot index U label tau sigma : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (congrSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one mu d vertex localRoot index U label tau sigma)) := by
  apply ModelTransfer.derives
  intro M hM
  exact congr_models rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one mu d vertex localRoot index U label tau sigma hM

end PPAC.Migration.ForcingOrbitCongruence
