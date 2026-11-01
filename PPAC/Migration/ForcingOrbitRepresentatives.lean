/- Fixed OrbitAssignments.orbitRep/orbit_rep:159-162. Reuse the existing
internal membership uniformization from ConstructionGermDetectors; the chosen
representatives are an actual set function on the full internal orbit quotient. -/
import PPAC.Migration.ForcingOrbitQuotient
import PPAC.Migration.ForcingOrbitDescent

namespace PPAC.Migration.ForcingOrbitRepresentatives
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingOrbitQuotient (Class Classes Projection)
open ConstructionGermDetectors (Representatives representatives)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem exists_representatives (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {D I mul one q V Q : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul one)
    (hq : ForcingSupportSize.Injection D I q)
    (hV : ConstructionComponentCarrier.Carrier D I mul q V) (hQ : Classes D I mul q V Q) :
    ∃ reps, Representatives V Q reps := by
  let schema : Project.BinarySchema 0 := { body := .mem (.bound 0) (.bound 1), freeClosed := by simp [Definitional.Formula.FreeClosed] }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 0 := { bound := Fin.elim0, free := fun _ => D }
  have he C pi : schema.denote env C pi ↔ (Project.FirstOrderSemantics.reduct M).mem pi C := by
    simp [Project.BinarySchema.denote,schema,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,SetTheory.Env.push]
    rfl
  obtain ⟨reps,hr,hmem⟩ := ExistingSmallUnion.uniformize_formula_l (KuratowskiZF.interpretation hM)
    (ConstructionDirectedCardinality.models_zfc hM hChoice) schema env (X := Q) (Y := V) (by
      intro C hCQ
      obtain ⟨pi,hpi,hClass⟩ := (hQ C).mp hCQ
      exact ⟨pi,hpi,(he C pi).mpr ((hClass pi).mpr ⟨hpi,ForcingOrbitQuotient.orbit_refl hM hm hq ((hV pi).mp hpi)⟩)⟩)
  exact ⟨reps,(ForcingSupportSize.native_mapsTo hM Q V reps).mpr hr,fun C pi hp => (he C pi).mp (hmem C pi hp)⟩

def RoundTrip (pr reps : M.Carrier .set) : Prop := ∀ C v,
  PureKuratowski.PairMember M C v reps → PureKuratowski.PairMember M v C pr

theorem representative_roundtrip (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul one q V Q pr reps : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul one)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul) (hq : ForcingSupportSize.Injection D I q)
    (hV : ConstructionComponentCarrier.Carrier D I mul q V) (hQ : Classes D I mul q V Q)
    (hPr : Projection D I mul q V pr) (hReps : Representatives V Q reps) : RoundTrip pr reps := by
  intro C v hv
  have hCQ := ForcingConditionGraphs.function_input hReps.1.1 hv
  obtain ⟨w,hw,hC⟩ := (hQ C).mp hCQ
  obtain ⟨hvV,hOrbit⟩ := (hC v).mp (hReps.2 C v hv)
  obtain ⟨E,hE⟩ := ForcingOrbitQuotient.exists_class hM D I mul q V v
  have he := (ForcingOrbitQuotient.class_eq_iff hM hm hJ hq hV hvV hC hE).mpr hOrbit
  exact (hPr v C).mpr ⟨hvV,he.symm ▸ hE⟩

def roundTrip {m : Nat} (pr reps : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge reps.succ.succ 1 0))
    (ProjectSyntax.encode id (Source.SetLanguage.edge pr.succ.succ 0 1))))

theorem roundTrip_freeClosed {m : Nat} (pr reps : Fin m) : (roundTrip pr reps).FreeClosed := by
  simp -implicitDefEqProofs [roundTrip,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem roundTrip_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (pr reps : Fin m) :
    Project.Formula.satisfies env (roundTrip pr reps) ↔ RoundTrip (env.bound pr) (env.bound reps) := by
  simp only [roundTrip,RoundTrip,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def representativeSentence {k : Nat} (D I mul one q V Q pr : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul one))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q D I))
    (.imp (ConstructionComponentCarrier.carrier D I mul q V)
    (.imp (ForcingOrbitQuotient.classes D I mul q V Q)
    (.imp (ForcingOrbitQuotient.projection D I mul q V pr)
    (.existsE (.conj (representatives V.succ Q.succ 0) (roundTrip pr.succ 0)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionComponentCarrier.carrier_freeClosed,
      ForcingOrbitQuotient.classes_freeClosed,ForcingOrbitQuotient.projection_freeClosed,
      ConstructionGermDetectors.representatives_freeClosed,roundTrip_freeClosed]

theorem representative_models {k : Nat} (D I mul one q V Q pr : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (representativeSentence D I mul one q V Q pr)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingSupportSize.injection_semantics (M := M),ConstructionComponentCarrier.carrier_semantics hM,
    ForcingOrbitQuotient.classes_semantics hM,ForcingOrbitQuotient.projection_semantics hM,
    ConstructionGermDetectors.representatives_semantics hM,roundTrip_semantics hM]
  intro hm hJ hq hV hQ hPr
  obtain ⟨reps,hReps⟩ := exists_representatives hM hChoice hm hq hV hQ
  exact ⟨reps,hReps,representative_roundtrip hM hm hJ hq hV hQ hPr hReps⟩

theorem representative_kernel_certificate {k : Nat} (D I mul one q V Q pr : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (representativeSentence D I mul one q V Q pr))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let witness := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    {bound := Fin.elim0,free := fun _ => witness}
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (representativeSentence D I mul one q V Q pr)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (representativeSentence D I mul one q V Q pr)).mp
      (representative_models D I mul one q V Q pr hL hChoice)


end PPAC.Migration.ForcingOrbitRepresentatives
