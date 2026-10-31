/- Pinned BlockTowers.Cell.rangeAttachment's f.rangeEquiv base change.
The range S is the existing literal stage, never a replacement carrier.
Reuse range_closed, exists_submonoid, inverse_hom and maps_requests. The
only new transport here is corestriction of the SAME actual leg f. -/
import PPAC.Migration.ConstructionCellSimulationEquiv
import PPAC.Migration.ConstructionRequestMapsSyntax

namespace PPAC.Migration.ConstructionRangeObject
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionConservativeHull (Closure ProductGraph)
open ConstructionProbePushout (Hom)
open ConstructionProbeConservative (Conservative)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ConstructionProbeMappedPath (NodeMap)
open ForcingSupportSize (MapsTo)
open ForcingSupportedNames (Range)
open ForcingConditionGraphs (IdentityGraph InverseGraph function_input)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Same graph and exact domain; only its codomain is changed to its range. -/
theorem corestrict_maps {D V f S : M.Carrier .set}
    (hf : MapsTo D V f) (hRange : Range D f S) : MapsTo D S f :=
  ⟨hf.1,fun x y hxy => (hRange y).mpr ⟨x,function_input hf.1 hxy,hxy⟩⟩

/-- The original four conservative fields survive the existing range's
restricted multiplication. Reuse join_reflect/divides_iff for that subobject. -/
theorem corestrict_conservative
    {D V mul G unit f S GS : M.Carrier .set}
    (hf : Conservative D V mul G f) (hRange : Range D f S)
    (hClosed : Closure V G unit S) (hGS : ProductGraph S G GS) :
    Conservative D S mul GS f := by
  have hfS := corestrict_maps hf.1.1 hRange
  refine ⟨⟨hfS,hf.1.2⟩,?_,?_,?_⟩
  · intro x y z fx fy hfx hfy hz hp
    exact hf.2.1 x y z fx fy hfx hfy (hClosed.1 z hz) ((hGS fx z fy).mp hp).2.2
  · intro x y j fx fy fj hfx hfy hfj hJoin
    exact ConstructionConservativeHull.join_reflect hClosed hGS
      (hfS.2 x fx hfx) (hfS.2 y fy hfy) (hfS.2 j fj hfj)
      (hf.2.2.1 x y j fx fy fj hfx hfy hfj hJoin)
  · intro x y fx fy hfx hfy hCommon
    obtain ⟨z,hz,hxz,hyz⟩ := hCommon
    exact hf.2.2.2 x y fx fy hfx hfy ⟨z,hClosed.1 z hz,
      (ConstructionConservativeHull.divides_iff hClosed hGS (hfS.2 x fx hfx) hz).mpr hxz,
      (ConstructionConservativeHull.divides_iff hClosed hGS (hfS.2 y fy hfy) hz).mpr hyz⟩

/-- The literal range subobject, the SAME leg as a conservative bijection
onto it, its internal inverse, and BOTH original request mapping branches. -/
def Data (w zero D V mul G e unit f S B GS inc inv : M.Carrier .set) : Prop :=
  Closure V G unit S ∧ ConstructionProbeLetters.Representatives S S B ∧ MapsTo B S GS ∧
    ProductGraph S G GS ∧ LeftCancelMonoid S GS unit ∧ Conical S GS unit ∧
    ConditionalJoins S GS ∧ IdentityGraph S inc ∧ Hom S V GS G unit unit inc ∧
    Conservative S V GS G inc ∧ Hom D S mul GS e unit f ∧ Conservative D S mul GS f ∧
    Range D f S ∧ Hom S D GS mul unit e inv ∧ InverseGraph f inv ∧ NodeMap f inc f ∧
    ConstructionRequestMaps.MapsRequests w D mul e zero S GS unit f

/-- Source rangeEquiv and ofMulEquiv, at the actual supplied range S.
No subobject, inverse or mapped request contract is an extra premise. -/
theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero D V mul G e unit f S : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hJ : ConditionalJoins D mul)
    (hv : LeftCancelMonoid V G unit) (hc : Conical V G unit) (hJV : ConditionalJoins V G)
    (hf : Hom D V mul G e unit f) (hCons : Conservative D V mul G f) (hRange : Range D f S) :
    ∃ B GS inc inv, Data w zero D V mul G e unit f S B GS inc inv := by
  have hClosed := ConstructionBlockStages.range_closed hm hJ hv hc hf hCons hRange
  obtain ⟨B,GS,inc,hB,hGS,hProduct,hmS,hcS,hId,hInc,hConsInc,hJS⟩ :=
    ConstructionConservativeHull.exists_submonoid hM hv hc hJV hClosed
  have hfS := corestrict_maps hf.1 hRange
  have hHomS := ConstructionCellGeneration.hom_restrict hf hfS hProduct
  have hConsS := corestrict_conservative hCons hRange hClosed hProduct
  obtain ⟨inv,hInv,hInverse⟩ := ConstructionCellSimulationEquiv.inverse_hom hM hm hmS hHomS hConsS.1 hRange
  exact ⟨B,GS,inc,inv,hClosed,hB,hGS,hProduct,hmS,hcS,hJS,hId,hInc,hConsInc,hHomS,hConsS,hRange,
    hInv,hInverse,ConstructionPushoutIdentification.right_identity hfS hId,
    ConstructionRequestMaps.maps_requests hM hm hmS hConsS hHomS.2.2 hHomS.2.1 hJ⟩

/-- Pure membership syntax for the exact range object and its retained maps. -/
def data {m : Nat} (w zero D V mul G e unit f S B GS inc inv : Fin m) : Project.Formula 1 m :=
  .conj (ConstructionConservativeHull.closure V G unit S)
    (.conj (ConstructionProbeLetters.representatives S S B)
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo GS B S))
    (.conj (ConstructionConservativeHull.productGraph S G GS)
    (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid S GS unit))
    (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.conical S GS unit))
    (.conj (ConstructionProbeSharedIntersections.conditionalJoins S GS)
    (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph S inc))
    (.conj (ConstructionProbePushoutSyntax.hom S V GS G unit unit inc)
    (.conj (ConstructionProbeConservativeSyntax.conservative S V GS G inc)
    (.conj (ConstructionProbePushoutSyntax.hom D S mul GS e unit f)
    (.conj (ConstructionProbeConservativeSyntax.conservative D S mul GS f)
    (.conj (ProjectSyntax.encode id (ForcingSupportedNames.range D f S))
    (.conj (ConstructionProbePushoutSyntax.hom S D GS mul unit e inv)
    (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.inverseGraph f inv))
    (.conj (ConstructionProbeMappedPathSyntax.nodeMap f inc f)
    (ConstructionRequestMapsSyntax.mapsRequests w D mul e zero S GS unit f))))))))))))))))

theorem data_freeClosed {m : Nat} (w zero D V mul G e unit f S B GS inc inv : Fin m) :
    (data w zero D V mul G e unit f S B GS inc inv).FreeClosed := by
  simp -implicitDefEqProofs [data,Definitional.Formula.FreeClosed,
    ProjectSyntax.freeClosed,
    ConstructionConservativeHull.closure_freeClosed,
    ConstructionProbeLetters.representatives_freeClosed,
    ConstructionConservativeHull.productGraph_freeClosed,
    ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
    ConstructionProbePushoutSyntax.hom_freeClosed,
    ConstructionProbeConservativeSyntax.conservative_freeClosed,
    ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,
    ConstructionRequestMapsSyntax.mapsRequests_freeClosed]

theorem data_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero D V mul G e unit f S B GS inc inv : Fin m) :
    Project.Formula.satisfies env (data w zero D V mul G e unit f S B GS inc inv) ↔
      Data (env.bound w) (env.bound zero) (env.bound D) (env.bound V) (env.bound mul) (env.bound G) (env.bound e) (env.bound unit) (env.bound f) (env.bound S) (env.bound B) (env.bound GS) (env.bound inc) (env.bound inv) := by
  simp only [data,Data,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionConservativeHull.closure_semantics hM,
    ConstructionProbeLetters.representatives_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionConservativeHull.productGraph_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingDiagramPoset.conical_semantics (M := M),
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingConditionGraphs.identityGraph_semantics (M := M),
    ConstructionProbePushoutSyntax.hom_semantics hM,
    ConstructionProbeConservativeSyntax.conservative_semantics hM,
    ForcingSupportedNames.range_semantics (M := M),
    ForcingConditionGraphs.inverseGraph_semantics (M := M),
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,
    ConstructionRequestMapsSyntax.mapsRequests_semantics hM]
  rfl

/-- All sets and all internally coded requests; no range-equivalence premise. -/
def constructionSentence {m : Nat} (w zero D V mul G e unit f S : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul)
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V G unit))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical V G unit))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins V G)
    (.imp (ConstructionProbePushoutSyntax.hom D V mul G e unit f)
    (.imp (ConstructionProbeConservativeSyntax.conservative D V mul G f)
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range D f S))
    (.existsE (.existsE (.existsE (.existsE (data w.succ.succ.succ.succ zero.succ.succ.succ.succ D.succ.succ.succ.succ V.succ.succ.succ.succ mul.succ.succ.succ.succ G.succ.succ.succ.succ e.succ.succ.succ.succ unit.succ.succ.succ.succ f.succ.succ.succ.succ S.succ.succ.succ.succ 3 2 1 0)))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      data_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionProbePushoutSyntax.hom_freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed]

theorem construction_models {m : Nat} (w zero D V mul G e unit f S : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence w zero D V mul G e unit f S)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w zero D V mul G e unit f S)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingDiagramPoset.conical_semantics (M := M),
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ConstructionProbePushoutSyntax.hom_semantics hM,
    ConstructionProbeConservativeSyntax.conservative_semantics hM,
    ForcingSupportedNames.range_semantics (M := M),data_semantics hM]
  exact construction hM

theorem construction_kernel_certificate {m : Nat} (w zero D V mul G e unit f S : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence w zero D V mul G e unit f S)) :=
  ModelTransfer.derives (fun _ hM => construction_models w zero D V mul G e unit f S hM)

end PPAC.Migration.ConstructionRangeObject
