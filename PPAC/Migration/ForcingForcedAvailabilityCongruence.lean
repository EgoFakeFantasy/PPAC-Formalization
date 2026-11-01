/- Fixed GraphFusion.forcedAvailability_congr:587-602, consumed by
OrbitAssignments.assigned_compatible_inj. Retain the SAME actual availability
ideals; reuse existing EqF transitivity/symmetry and native extensionality. -/
import PPAC.Migration.ForcingForcedAvailability

namespace PPAC.Migration.ForcingForcedAvailabilityCongruence
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingProductSymmetry (orderFormula)
open ForcingForcedAvailability (Available Carrier available carrier)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem available_congr (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w mul one G F bound d r tau sigma : Fin k)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hd : (Project.FirstOrderSemantics.reduct M).mem (env d) (env (rho 3)))
    (hr : ForcingSupportSize.Injection (env (rho 0)) (env I) (env r))
    (heq : ForcingPrincipalFilter.EqF (orderFormula (rho 0) mul) env (env (rho 6)) (env d) (env r) (env tau) (env sigma)) (n : M.Carrier .set) :
    Available (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) (env F) (env mul) (env bound) (env d) (env r) (env tau) n ↔
      Available (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) (env F) (env mul) (env bound) (env d) (env r) (env sigma) n := by
  constructor
  · rintro ⟨s,A,H,nu,hs,hSub,hA,hH,hLocal,hEq⟩
    exact ⟨s,A,H,nu,hs,hSub,hA,hH,hLocal,ForcingPrincipalFilter.eqF_trans hM env rho mul hm hp hd hr hEq heq⟩
  · rintro ⟨s,A,H,nu,hs,hSub,hA,hH,hLocal,hEq⟩
    exact ⟨s,A,H,nu,hs,hSub,hA,hH,hLocal,ForcingPrincipalFilter.eqF_trans hM env rho mul hm hp hd hr hEq (ForcingPrincipalFilter.eqF_symm hM heq)⟩

theorem carrier_congr (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w mul one G F bound d r tau sigma a U V : Fin k)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hd : (Project.FirstOrderSemantics.reduct M).mem (env d) (env (rho 3)))
    (hr : ForcingSupportSize.Injection (env (rho 0)) (env I) (env r))
    (heq : ForcingPrincipalFilter.EqF (orderFormula (rho 0) mul) env (env (rho 6)) (env d) (env r) (env tau) (env sigma))
    (hU : Carrier (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) (env F) (env mul) (env bound) (env d) (env r) (env a) (env tau) (env U))
    (hV : Carrier (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) (env F) (env mul) (env bound) (env d) (env r) (env a) (env sigma) (env V)) : env U = env V := by
  apply (ModelTransfer.extensionality hM).eq_of_same_members
  intro n
  exact (hU n).trans ((and_congr_right fun _ => and_congr_right fun _ =>
    available_congr hM env rho I K B w mul one G F bound d r tau sigma hm hp hd hr heq n).trans (hV n).symm)

def congrSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w mul one G F bound d r tau sigma a U V : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (.mem (.bound d) (.bound (rho 3)))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection r (rho 0) I))
    (.imp (ForcingPrincipalFilter.eqF (orderFormula (rho 0) mul) id (rho 6) d r tau sigma)
    (.imp (carrier (orderFormula (rho 0) mul) id rho G F mul bound d r a tau U)
    (.imp (carrier (orderFormula (rho 0) mul) id rho G F mul bound d r a sigma V)
      (Project.Formula.extensionalEq (.bound U) (.bound V)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ForcingPrincipalFilter.eqF_freeClosed,ForcingForcedAvailability.carrier_freeClosed,Project.Formula.extensionalEq]

theorem congr_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w mul one G F bound d r tau sigma a U V : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (congrSentence rho I K B w mul one G F bound d r tau sigma a U V)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingPrincipalFilter.eqF_semantics hM,
    ForcingForcedAvailability.carrier_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  exact carrier_congr hM env rho I K B w mul one G F bound d r tau sigma a U V

theorem congr_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w mul one G F bound d r tau sigma a U V : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (congrSentence rho I K B w mul one G F bound d r tau sigma a U V)) := by
  apply ModelTransfer.derives
  intro M hM
  exact congr_models rho I K B w mul one G F bound d r tau sigma a U V hM

end PPAC.Migration.ForcingForcedAvailabilityCongruence
