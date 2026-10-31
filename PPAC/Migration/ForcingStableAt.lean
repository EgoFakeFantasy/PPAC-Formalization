/- Fixed StableSelectors.StableAt:581 / stableAt_permute:589 / stableAt_permute_iff:619.
Keep the literal normalized local name and the SAME ideal at every stronger
internal Cohen condition. Direct consumer: OrbitAssignments.corrected_stable:30.
Reuse existing name/support/forcing symmetry and exact availability transport. -/
import PPAC.Migration.ForcingForcedAvailabilityTransport
import PPAC.Migration.ForcingEligibleTransport
import PPAC.Migration.ForcingAssignmentInvariant

namespace PPAC.Migration.ForcingStableAt
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args3)
open ForcingProductSymmetry (orderFormula)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def StableAt {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (env : Fin k → M.Carrier .set) (v : Fin 7 → M.Carrier .set)
    (G F mul bound labels E d vertex tau : M.Carrier .set) : Prop :=
  ∃ r index U A H z, ConstructionComponentCarrier.Code vertex r index U ∧
    ForcingSupportedNames.Range (v 0) r A ∧ ForcingLabelPermutations.Fixing G A H ∧
    ForcingLocalNames.LocalName v G F bound H tau ∧ ForcingSupportingRoot.Code z d r ∧
    ForcingFormula.Force R Hdom env (args3 tau labels E) (v 6) z (ForcingEligibility.isClass 0 1 2) ∧
    ∀ e, (Project.FirstOrderSemantics.reduct M).mem e (v 3) → ForcingPowerName.Subset d e →
      ForcingForcedAvailability.Carrier R env v G F mul bound e r index tau U

def stableAt {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (G F mul bound labels E d vertex tau : Fin m) : Project.Formula 1 m :=
  let up : Fin m → Fin (m+6) := fun i => i.succ.succ.succ.succ.succ.succ
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionComponentCarrier.code (up vertex) 5 4 3)
      (.conj (ProjectSyntax.encode id (ForcingSupportedNames.range (up (rho 0)) 5 2))
      (.conj (ProjectSyntax.encode id (ForcingLabelPermutations.fixing (up G) 2 1))
      (.conj (ProjectSyntax.encode id (ForcingLocalNames.localName (fun j => up (rho j)) (up G) (up F) (up bound) 1 (up tau)))
      (.conj (ProjectSyntax.encode id (ForcingSupportingRoot.code 0 (up d) 5))
      (.conj (ProjectSyntax.encode id (ForcingFormula.formula R Hdom (fun j => up (base j)) (args3 (up tau) (up labels) (up E)) (up (rho 6)) 0 (ForcingEligibility.isClass 0 1 2)))
      (.forallE (.imp (.mem (.bound 0) (.bound (up (rho 3)).succ))
      (.imp (Project.Formula.subset (.bound (up d).succ) (.bound 0))
        (ForcingForcedAvailability.carrier R (fun j => (up (base j)).succ) (fun j => (up (rho j)).succ)
          (up G).succ (up F).succ (up mul).succ (up bound).succ 0 6 5 (up tau).succ 4)))))))))))))))

theorem stableAt_freeClosed {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m) (G F mul bound labels E d vertex tau : Fin m) :
    (stableAt R Hdom base rho G F mul bound labels E d vertex tau).FreeClosed := by
  simp -implicitDefEqProofs [stableAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionComponentCarrier.code_freeClosed,ForcingForcedAvailability.carrier_freeClosed]

theorem stableAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m) (G F mul bound labels E d vertex tau : Fin m) :
    Project.Formula.satisfies env (stableAt R Hdom base rho G F mul bound labels E d vertex tau) ↔
      StableAt R Hdom (fun j => env.bound (base j)) (fun j => env.bound (rho j))
        (env.bound G) (env.bound F) (env.bound mul) (env.bound bound) (env.bound labels) (env.bound E)
        (env.bound d) (env.bound vertex) (env.bound tau) := by
  simp only [stableAt,StableAt,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    ConstructionComponentCarrier.code_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingLocalNames.localName_semantics (M := M),ForcingSupportingRoot.code_semantics (M := M),
    ForcingFormula.formula_semantics (M := M),ForcingForcedAvailability.carrier_semantics hM]
  rfl

theorem permute (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul act : Fin k)
    {I K B w mu pi inv c ai one bound labels E q ac d movedD vertex movedVertex tau movedTau : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hData : ForcingProductCovariance.SystemData (fun j => env (rho j)) I K B w (env G) (env F) mu pi inv c (env act) ai)
    (hNormal : ForcingNormalFilter.Normal I (env G) (env F))
    (hBound : ForcingSupportedNames.Supported (fun j => env (rho j)) (env G) bound)
    (hLabels : ForcingStabilizer.Action (env (rho 6)) (env act) labels labels)
    (hE : ForcingStabilizer.Action (env (rho 6)) (env act) E E)
    (hCohen : ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) pi ac)
    (hdd : PureKuratowski.PairMember M d movedD ac)
    (hMove : ForcingComponentMove.Move (env (rho 0)) I (env mul) q pi vertex movedVertex)
    (hTau : ForcingStabilizer.Action (env (rho 6)) (env act) tau movedTau)
    (h : StableAt (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) bound labels E d vertex tau) :
    StableAt (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) bound labels E movedD movedVertex movedTau := by
  obtain ⟨r,index,U,A,H,z,hCode,hRange,hFix,hLocal,hz,hForce,hStable⟩ := h
  obtain ⟨r0,index0,U0,movedRoot,hCode0,hMovedCode,hr,hMovedRoot,hComp⟩ := hMove
  obtain ⟨er,ei,eU⟩ := ConstructionComponentCarrier.code_injective hCode hCode0
  subst r0; subst index0; subst U0
  have hp := hData.1
  have hG := hData.2.1
  have hPi := hData.2.2.1
  have hAct := hData.2.2.2.2.2.2.2.1
  have hSubset : ForcingPowerName.Subset A I := by
    intro x hx
    obtain ⟨j,_,hjx⟩ := (hRange x).mp hx
    exact hr.1.1.2 j x hjx
  obtain ⟨movedRange,hImage,_⟩ := ForcingLabelConjugacy.exists_image hM hPi.1 (J := A)
  obtain ⟨movedFix,hMovedFix⟩ := ForcingLabelPermutations.exists_fixing hM (env G) movedRange
  obtain ⟨movedZ,hMovedZ⟩ := ForcingSupportingRoot.exists_code hM movedD movedRoot
  have hac := ForcingLocalTransport.part_permutation hCohen
  have hd := ForcingConditionGraphs.function_input hac.1.1 hdd
  have hTuple : ∀ j : Fin 3, ForcingStabilizer.Action (env (rho 6)) (env act)
      (args3 tau labels E j) (args3 movedTau labels E j) := by
    intro j
    exact Fin.cases hTau (fun j => Fin.cases hLabels (fun j => Fin.cases hE (fun j => Fin.elim0 j) j) j) j
  have hzW := ForcingSupportingRoot.code_mem hp ((hp.2.2.1 d).mp hd) hr.1 hz
  have hForceMoved := (ForcingSeparation.symmetry hM env rho G F mul hp hG hNormal hPi
    ((ForcingProductFamily.mapRel_action (fun j => env (rho j)) pi (env act)).mpr hAct)
    (ForcingEligibility.isClass 0 1 2) (args3 tau labels E) (args3 movedTau labels E) hTuple hzW
    (ForcingLocalTransport.moved_code hM hp hAct hCohen hdd hr.1 hMovedRoot.1 hComp hz hMovedZ)).mp hForce
  refine ⟨movedRoot,index,U,movedRange,movedFix,movedZ,hMovedCode,
    ForcingLocalNameTransport.range_image hRange hComp hImage,hMovedFix,
    ForcingLocalNameTransport.local_name_move hM hData hBound hSubset hImage hFix hMovedFix hLocal hTau,
    hMovedZ,hForceMoved,?_⟩
  intro e he hde
  obtain ⟨back,hBackMem,hBack⟩ := hac.2.2 e he
  have ho : ForcingCohenOrderAction.OrderPreserving ac := by
    obtain ⟨f,t,_,_,ht,_,_,hGraph⟩ := hCohen
    exact ForcingCohenOrderAction.graph_order hp.2.2.1 ht hGraph
  have hBackLe := (ho back d e movedD hBack hdd).mp hde
  exact (ForcingForcedAvailabilityTransport.carrier_permute_iff hM env rho mul act
    hm hData hBound hCohen hBack hr.1 hMovedRoot.1 hComp hTau).mpr (hStable back hBackMem hBackLe)

theorem permute_iff (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul act ai : Fin k)
    {I K B w mu pi inv c one bound labels E q ac d movedD vertex movedVertex tau movedTau : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hData : ForcingProductCovariance.SystemData (fun j => env (rho j)) I K B w (env G) (env F) mu pi inv c (env act) (env ai))
    (hNormal : ForcingNormalFilter.Normal I (env G) (env F))
    (hBound : ForcingSupportedNames.Supported (fun j => env (rho j)) (env G) bound)
    (hLabels : ForcingStabilizer.Action (env (rho 6)) (env act) labels labels)
    (hE : ForcingStabilizer.Action (env (rho 6)) (env act) E E)
    (hLabelsName : ForcingNames.IsName (env (rho 6)) labels)
    (hEName : ForcingNames.IsName (env (rho 6)) E)
    (hTauName : ForcingNames.IsName (env (rho 6)) tau)
    (hCohen : ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) pi ac)
    (hdd : PureKuratowski.PairMember M d movedD ac)
    (hMove : ForcingComponentMove.Move (env (rho 0)) I (env mul) q pi vertex movedVertex)
    (hTau : ForcingStabilizer.Action (env (rho 6)) (env act) tau movedTau) :
    StableAt (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) bound labels E movedD movedVertex movedTau ↔
    StableAt (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) bound labels E d vertex tau := by
  constructor
  · intro h
    obtain ⟨reverseConj,hReverse⟩ := ForcingLocalNameTransport.reverse_data hM hData
    have hPi := hData.2.2.1
    have hInverse := hData.2.2.2.2.1
    have hAct := hData.2.2.2.2.2.2.2.1
    have hAI := hData.2.2.2.2.2.2.2.2.1
    have hActEnd := (ForcingProductFamily.action_permutation hAct).1
    have hAIEnd := (ForcingProductFamily.action_permutation hAI).1
    have hInverseAction := ForcingProductCovariance.inverse hM hData.1 hPi hInverse hAct hAI
    have hLabelsBack := ForcingNameConjugacy.inverse_action hM hActEnd hAIEnd hInverseAction hLabelsName hLabels
    have hEBack := ForcingNameConjugacy.inverse_action hM hActEnd hAIEnd hInverseAction hEName hE
    have hTauBack := ForcingNameConjugacy.inverse_action hM hActEnd hAIEnd hInverseAction hTauName hTau
    obtain ⟨backCohen,hBackCohen⟩ := ForcingLocalTransport.part_of_action hAI
    have hBackD := ForcingAssignmentInvariant.cohen_inverse hData.1 hInverse hCohen hBackCohen hdd
    exact permute hM env rho G F mul ai hm hReverse hNormal hBound hLabelsBack hEBack
      hBackCohen hBackD (ForcingComponentMove.move_inverse hPi hInverse hMove) hTauBack h
  · exact permute hM env rho G F mul act hm hData hNormal hBound hLabels hE hCohen hdd hMove hTau

theorem literal_permute_iff (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul act ai I K B w mu pi inv c one bound labels E q ac d movedD vertex movedVertex tau movedTau labelMap top bit Hq : Fin k)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hData : ForcingProductCovariance.SystemData (fun j => env (rho j)) (env I) (env K) (env B) (env w)
      (env G) (env F) (env mu) (env pi) (env inv) (env c) (env act) (env ai))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hBound : ForcingPowerName.Bound (env (rho 6)) (env labels) (env bound))
    (hPiHq : (Project.FirstOrderSemantics.reduct M).mem (env pi) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hEName : ForcingNames.IsName (env (rho 6)) (env E))
    (hTauName : ForcingNames.IsName (env (rho 6)) (env tau))
    (hCohen : ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) (env pi) (env ac))
    (hdd : PureKuratowski.PairMember M (env d) (env movedD) (env ac))
    (hMove : ForcingComponentMove.Move (env (rho 0)) (env I) (env mul) (env q) (env pi) (env vertex) (env movedVertex))
    (hTau : ForcingStabilizer.Action (env (rho 6)) (env act) (env tau) (env movedTau)) :
    StableAt (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) (env bound) (env labels) (env E) (env movedD) (env movedVertex) (env movedTau) ↔
    StableAt (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) (env bound) (env labels) (env E) (env d) (env vertex) (env tau) := by
  have hSmall := (ForcingSupportSize.native_small hM (env w) (env mu)).mpr hMu.2
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hData.2.1 hData.2.2.2.2.2.2.2.2.2
  obtain ⟨hLabelsHS,hLabelsFix⟩ := ForcingLabelSet.HS_and_fixed hM (fun j => env (rho j)) hData.1 hData.2.1 hNormal
    hData.2.2.2.2.2.2.2.2.2 hw hSmall hLabelMap hTop hLabels
  have hAct := (ForcingProductFamily.mapRel_action (fun j => env (rho j)) (env pi) (env act)).mpr hData.2.2.2.2.2.2.2.1
  exact permute_iff hM env rho G F mul act ai hm hData hNormal
    (ForcingLocalNameTransport.bound_supported hM hData.1 hData.2.1 hLabelsHS hLabelsFix hBound)
    (hLabelsFix (env pi) ((hData.2.1 (env pi)).mpr hData.2.2.1) (env act) hAct)
    (hE (env pi) hPiHq (env act) hAct) (ForcingHS.isName hLabelsHS) hEName hTauName hCohen hdd hMove hTau

def permutationSentence {k : Nat} (rho : Fin 7 → Fin k) (G F mul act ai I K B w mu pi inv c one bound labels E q ac d movedD vertex movedVertex tau movedTau labelMap top bit Hq : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductCovariance.systemData rho I K B w G F mu pi inv c act ai))
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn labelMap K))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K labelMap top bit labels))
    (.imp (ProjectSyntax.encode id (ForcingLabelBound.bound (rho 6) labels bound))
    (.imp (.mem (.bound pi) (.bound Hq))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq E))
    (.imp (ProjectSyntax.encode id (ForcingNames.isName (rho 6) E))
    (.imp (ProjectSyntax.encode id (ForcingNames.isName (rho 6) tau))
    (.imp (ProjectSyntax.encode id (ForcingLocalTransport.cohenPart (rho 1) (rho 2) (rho 3) pi ac))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge ac d movedD))
    (.imp (ForcingComponentMove.move (rho 0) I mul q pi vertex movedVertex)
    (.imp (ProjectSyntax.encode id (ForcingStabilizer.action (rho 6) act tau movedTau))
    (.iff (stableAt (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul bound labels E movedD movedVertex movedTau)
      (stableAt (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul bound labels E d vertex tau))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ForcingComponentMove.move_freeClosed,stableAt_freeClosed]

theorem permutation_models {k : Nat} (rho : Fin 7 → Fin k) (G F mul act ai I K B w mu pi inv c one bound labels E q ac d movedD vertex movedVertex tau movedTau labelMap top bit Hq : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (permutationSentence rho G F mul act ai I K B w mu pi inv c one bound labels E q ac d movedD vertex movedVertex tau movedTau labelMap top bit Hq)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductCovariance.systemData_semantics (M := M),
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.functionOn_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingLabelSet.labelSet_semantics (M := M),ForcingLabelBound.bound_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ForcingNames.isName_semantics (M := M),
    ForcingLocalTransport.cohenPart_semantics (M := M),KuratowskiZF.source_edge,
    ForcingComponentMove.move_semantics hM,ForcingStabilizer.action_semantics (M := M),stableAt_semantics hM]
  exact literal_permute_iff hM env rho G F mul act ai I K B w mu pi inv c one bound labels E q ac d movedD vertex movedVertex tau movedTau labelMap top bit Hq

theorem permutation_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (G F mul act ai I K B w mu pi inv c one bound labels E q ac d movedD vertex movedVertex tau movedTau labelMap top bit Hq : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (permutationSentence rho G F mul act ai I K B w mu pi inv c one bound labels E q ac d movedD vertex movedVertex tau movedTau labelMap top bit Hq)) := by
  apply ModelTransfer.derives
  intro M hM
  exact permutation_models rho G F mul act ai I K B w mu pi inv c one bound labels E q ac d movedD vertex movedVertex tau movedTau labelMap top bit Hq hM

end PPAC.Migration.ForcingStableAt
