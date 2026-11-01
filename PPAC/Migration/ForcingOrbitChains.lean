/- Fixed OrbitAssignments.orbitChain:173-175. Select one actual internal
cofinal chain for every chosen orbit representative, using the existing native
function space and component_cofinal_chain; no new recursion or chain backend. -/
import PPAC.Migration.ForcingOrbitRepresentatives
import YesMetaZFC.SetTheory.FunctionSpaceConstruction

namespace PPAC.Migration.ForcingOrbitChains
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionComponentCofinal (Chain)
open ConstructionGermDetectors (Representatives)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Family (w D I mul q zero V Q reps chains : M.Carrier .set) : Prop :=
  ForcingConditionGraphs.FunctionOn Q chains ∧ ∀ C f,
    PureKuratowski.PairMember M C f chains →
      ∃ v, PureKuratowski.PairMember M C v reps ∧ Chain w D I mul q zero v V f

def family {m : Nat} (w D I mul q zero V Q reps chains : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn chains Q))
    (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge chains.succ.succ 1 0))
      (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge reps.succ.succ.succ 2 0))
        (ConstructionComponentCofinal.chain w.succ.succ.succ D.succ.succ.succ I.succ.succ.succ mul.succ.succ.succ
          q.succ.succ.succ zero.succ.succ.succ 0 V.succ.succ.succ 1))))))

theorem family_freeClosed {m : Nat} (w D I mul q zero V Q reps chains : Fin m) :
    (family w D I mul q zero V Q reps chains).FreeClosed := by
  simp -implicitDefEqProofs [family,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionComponentCofinal.chain_freeClosed]

theorem family_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D I mul q zero V Q reps chains : Fin m) :
    Project.Formula.satisfies env (family w D I mul q zero V Q reps chains) ↔
      Family (env.bound w) (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound zero)
        (env.bound V) (env.bound Q) (env.bound reps) (env.bound chains) := by
  simp only [family,Family,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingConditionGraphs.functionOn_semantics (M := M),ConstructionComponentCofinal.chain_semantics hM]
  rfl

theorem exists_family (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w rationals reals top D I mul one mark H cells q zero V Q reps : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : ConstructionFractionOrder.Carrier w rationals)
    (hR : ConstructionRealCuts.CutCarrier hM w rationals reals)
    (hTop : ConstructionRealCuts.Cut hM w rationals top)
    (hObj : ConstructionRoundFields.ObjectFields hM w rationals reals top D mul one mark H cells)
    (hV : ConstructionComponentCarrier.Carrier D I mul q V)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hReps : Representatives V Q reps) : ∃ chains, Family w D I mul q zero V Q reps chains := by
  obtain ⟨space,hSpace⟩ := ZF.exists_functionSpace (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) w V
  let schema : Project.BinarySchema 8 := {
    body := .existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 10 2 0))
      (ConstructionComponentCofinal.chain 3 4 5 6 7 8 0 9 1))
    freeClosed := by
      simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
        ConstructionComponentCofinal.chain_freeClosed] }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 8 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases I (Fin.cases mul (Fin.cases q (Fin.cases zero (Fin.cases V (fun _ => reps))))))),
    free := fun _ => V }
  have he C f : schema.denote env C f ↔
      ∃ v, PureKuratowski.PairMember M C v reps ∧ Chain w D I mul q zero v V f := by
    simp only [Project.BinarySchema.denote,schema,Project.Formula.satisfies_exists_iff,
      Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
      KuratowskiZF.source_edge,ConstructionComponentCofinal.chain_semantics hM]
    rfl
  obtain ⟨chains,hFunction,hValue⟩ := ExistingSmallUnion.uniformize_formula_l (KuratowskiZF.interpretation hM)
    (ConstructionDirectedCardinality.models_zfc hM hChoice) schema env (X := Q) (Y := space) (by
      intro C hC
      obtain ⟨v,hCv,_⟩ := hReps.1.1.2 C hC
      obtain ⟨r,a,U,hCode,hVertex⟩ := (hV v).mp (hReps.1.2 C v hCv)
      obtain ⟨f,hChain⟩ := ConstructionComponentCofinal.component_cofinal_chain hM hChoice
        hw hQ hR hTop hObj hVertex hCode hV hz
      exact ⟨f,(hSpace f).mpr ((ForcingSupportSize.native_mapsTo hM w V f).mp hChain.1),
        (he C f).mpr ⟨v,hCv,hChain⟩⟩)
  exact ⟨chains,((ForcingSupportSize.native_mapsTo hM Q space chains).mpr hFunction).1,
    fun C f hf => (he C f).mp (hValue C f hf)⟩

def constructionSentence {k : Nat} (w rationals reals top D I mul one mark H cells q zero V Q reps : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (Project.Formula.isOmega (.bound w))
    (.imp (ConstructionFractionOrder.carrier w rationals)
    (.imp (ConstructionRealCuts.cutCarrier w rationals reals)
    (.imp (ConstructionRealCuts.cut w rationals top)
    (.imp (ConstructionRoundStepSyntax.objectFields w rationals reals top D mul one mark H cells)
    (.imp (ConstructionComponentCarrier.carrier D I mul q V)
    (.imp (Project.Formula.isEmpty (.bound zero))
    (.imp (ConstructionGermDetectors.representatives V Q reps)
    (.existsE (family w.succ D.succ I.succ mul.succ q.succ zero.succ V.succ Q.succ reps.succ 0))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,Project.Formula.isEmpty,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,
      ConstructionRealCuts.cut_freeClosed,ConstructionRoundStepSyntax.objectFields_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,ConstructionGermDetectors.representatives_freeClosed,
      family_freeClosed]

theorem construction_models {k : Nat} (w rationals reals top D I mul one mark H cells q zero V Q reps : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence w rationals reals top D I mul one mark H cells q zero V Q reps)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,Project.Term.eval_bound,
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    ConstructionRealCuts.cut_semantics hM,ConstructionRoundStepSyntax.objectFields_semantics hM,
    ConstructionComponentCarrier.carrier_semantics hM,ConstructionGermDetectors.representatives_semantics hM,
    family_semantics hM]
  exact exists_family hM hChoice

theorem construction_kernel_certificate {k : Nat} (w rationals reals top D I mul one mark H cells q zero V Q reps : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative
        (constructionSentence w rationals reals top D I mul one mark H cells q zero V Q reps))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence w rationals reals top D I mul one mark H cells q zero V Q reps)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence w rationals reals top D I mul one mark H cells q zero V Q reps)).mp
      (construction_models w rationals reals top D I mul one mark H cells q zero V Q reps hL hChoice)


end PPAC.Migration.ForcingOrbitChains
