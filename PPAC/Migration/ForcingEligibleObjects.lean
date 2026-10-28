/- Pinned AvailableRecords.eligibleSystem.Obj:272. Construct the actual
ground set of eligible local quotient classes below q by existing Separation.
Outside the cone the object set is empty by the same exact membership equation. -/
import PPAC.Migration.ForcingEligibilityReflection

namespace PPAC.Migration.ForcingEligibleObjects
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args1 args2 args3)
open ForcingMapConditions (MapRel)
open ForcingEligibility (Eligible eligible)
open ForcingLocalQuotient (Projection)
open ForcingLocalRestriction (Restriction)
open ForcingSupportingRoot (Code exists_code code_mem code_le)
open ForcingFormula (Force)
open ForcingProductSymmetry (orderFormula_semantics)
open ForcingSupportSize (MapsTo)
open ForcingProductFamily (Presentation)
open ForcingProductSymmetry (orderFormula)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}



def Carrier {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (D mul W g r q labels E pr Q V : M.Carrier .set) : Prop :=
  ∀ x, (Project.FirstOrderSemantics.reduct M).mem x V ↔
    (Project.FirstOrderSemantics.reduct M).mem x Q ∧ ForcingDiagramOrder.Le D mul r q ∧
      Eligible R H env W g r labels E pr x

def carrier {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (rho : Fin k → Fin m)
    (D mul W g r q labels E pr Q V : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) V.castSucc).iff
    ((Formula.mem (Fin.last m) Q.castSucc).conj
      ((ForcingDiagramOrder.le D.castSucc mul.castSucc r.castSucc q.castSucc).conj
        (eligible R H (paramsUp rho) W.castSucc g.castSucc r.castSucc labels.castSucc E.castSucc pr.castSucc (Fin.last m)))))

theorem carrier_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (rho : Fin k → Fin m)
    (D mul W g r q labels E pr Q V : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (carrier R H rho D mul W g r q labels E pr Q V) ↔
      Carrier R H (fun j => env (rho j)) (env D) (env mul) (env W) (env g) (env r) (env q)
        (env labels) (env E) (env pr) (env Q) (env V) := by
  simp only [carrier,Carrier,Source.Formula.iff,Formula.Realize,ForcingDiagramOrder.le_semantics (M := M),
    ForcingEligibility.eligible_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h x => ⟨(h x).1,(h x).2⟩,fun h x => ⟨(h x).mp,(h x).mpr⟩⟩

theorem exists_carrier (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul g r q labels E pr Q : Fin k) :
    ∃ V, Carrier (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (env (rho 0)) (env mul) (env (rho 6)) (env g) (env r) (env q) (env labels) (env E) (env pr) (env Q) V := by
  let test : Formula (k+1) :=
    (ForcingDiagramOrder.le (rho 0).castSucc mul.castSucc r.castSucc q.castSucc).conj
      (eligible (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) Fin.castSucc
        (rho 6).castSucc g.castSucc r.castSucc labels.castSucc E.castSucc pr.castSucc (Fin.last k))
  have sep := (GodelDefOutput.separation_semantics (Project.FirstOrderSemantics.reduct M).mem test).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation test).semantically_entails M hM))
  obtain ⟨V,hV⟩ := sep env (env Q)
  refine ⟨V,fun x => (hV x).trans ?_⟩
  apply and_congr Iff.rfl
  simp only [test,Formula.Realize,ForcingDiagramOrder.le_semantics (M := M),
    ForcingEligibility.eligible_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]

theorem empty_outside_cone {k : Nat} {R : Formula (k+2)} {H : Formula (k+1)}
    {env : Fin k → M.Carrier .set} {D mul W g r q labels E pr Q V : M.Carrier .set}
    (hV : Carrier R H env D mul W g r q labels E pr Q V)
    (hn : ¬ ForcingDiagramOrder.Le D mul r q) : ForcingWithTopCarrier.Empty V :=
  fun x hx => hn ((hV x).mp hx).2.1

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k) (G F mul g r q labels E pr Q : Fin k) : Source.Sentence :=
  (Formula.ex (carrier (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) Fin.castSucc
    (rho 0).castSucc mul.castSucc (rho 6).castSucc g.castSucc r.castSucc q.castSucc
    labels.castSucc E.castSucc pr.castSucc Q.castSucc (Fin.last k))).close

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k) (G F mul g r q labels E pr Q : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (constructionSentence rho G F mul g r q labels E pr Q)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env
  obtain ⟨V,hV⟩ := exists_carrier hM env rho G F mul g r q labels E pr Q
  refine ⟨V,?_⟩
  apply (carrier_semantics (M := M) (Fin.lastCases V env) (orderFormula (rho 0) mul)
    (ForcingPairUnion.domain rho G F) Fin.castSucc
    (rho 0).castSucc mul.castSucc (rho 6).castSucc g.castSucc r.castSucc q.castSucc
    labels.castSucc E.castSucc pr.castSucc Q.castSucc (Fin.last k)).mpr
  simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hV

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (G F mul g r q labels E pr Q : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (constructionSentence rho G F mul g r q labels E pr Q)) :=
  ModelTransfer.derives (fun _ hM => construction_models rho G F mul g r q labels E pr Q hM)

end PPAC.Migration.ForcingEligibleObjects
