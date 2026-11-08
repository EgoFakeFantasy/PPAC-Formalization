/- Fixed Main.forces_target:156-163. Combine the ALREADY COMPLETED
ZF forcing schemas and actual PP/ACwo/notAC on ONE constructed Core.
External source-schema indices are retained; no all-internal Proof/Con claim. -/
import PPAC.Migration.ForcingReverseInjection
import PPAC.Migration.ForcingActualOrdinalChoice
import PPAC.Migration.ForcingZFAxioms

namespace PPAC.Migration.ForcingTargetTheory
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingFormula (Force)
open ForcingProductSymmetry (orderFormula)
open ForcingPairUnion (domain)
open ForcingConcreteSystem (forcingRho)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Exact source targetTheory membership split, retaining every ZF schema. -/
theorem forces_target (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (env : Fin 40 → M.Carrier .set) (hCore : ForcingConcreteSystem.Core hM env)
    {p : M.Carrier .set} (hp : (Project.FirstOrderSemantics.reduct M).mem p (env 33))
    (phi : Source.Sentence) (hphi : Source.SetLanguage.targetTheory phi) :
    Force (orderFormula (forcingRho 0) 18) (domain forcingRho 34 35)
      env Fin.elim0 (env 33) p phi := by
  rcases hphi with hZF | hPP | hACwo | hNotAC
  · obtain ⟨_,hm,_,hPres,hG,hFilter,hw,hMu,_⟩ := hCore
    have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hFilter
    have hpre := ForcingProductPoset.preorder env (forcingRho 0) 18 (forcingRho 6) hm
      hPres.2.2.2.2.1 hPres.2.2.2.1 hPres.2.2.2.2.2
    exact ForcingZFAxioms.forces_ZF hM env forcingRho 34 35 18 hPres hG hNormal hpre hp phi hZF
  · subst phi
    exact ForcingReverseInjection.forces_PP hM hOrder hChoice env id hCore hp
  · subst phi
    exact ForcingActualOrdinalChoice.on_core hM hChoice env hCore p hp
  · subst phi
    exact ForcingChoiceFailure.on_core hM hChoice env hCore p hp

/-- All internal conditions of the SAME unbounded HS interpretation. -/
def allForces (phi : Source.Sentence) : Project.Formula 1 40 :=
  .forallE (.imp (.mem (.bound 0) (.bound (33 : Fin 40).succ))
    (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (forcingRho 0) 18)
      (domain forcingRho 34 35) Fin.succ Fin.elim0 (33 : Fin 40).succ 0 phi)))

theorem allForces_freeClosed (phi : Source.Sentence) : (allForces phi).FreeClosed := by
  simp -implicitDefEqProofs [allForces,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem allForces_semantics (hM : FirstOrder.Theory.Models M nativeZF)
    (env : Env (Project.FirstOrderSemantics.reduct M) 40) (phi : Source.Sentence) :
    Project.Formula.satisfies env (allForces phi) ↔
      ∀ p, (Project.FirstOrderSemantics.reduct M).mem p (env.bound 33) →
        Force (orderFormula (forcingRho 0) 18) (domain forcingRho 34 35)
          env.bound Fin.elim0 (env.bound 33) p phi := by
  simp only [allForces,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingFormula.formula_semantics,id_eq]
  have hz (p : M.Carrier .set) :
      (fun i : Fin 0 => (env.push p).bound (Fin.elim0 i)) = (Fin.elim0 : Fin 0 → M.Carrier .set) :=
    funext (fun i => Fin.elim0 i)
  simp only [hz]
  rfl

/-- Actual same-system existence, including PP/ACwo/notAC AND the complete
chosen source target axiom. The source schema index remains external. -/
def sentence (phi : Source.Sentence) : Project.Sentence where
  formula := .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE ((.conj ForcingConcreteSystem.coreFormula (.conj (allForces phi) (.conj (allForces Source.SetLanguage.PP) (.conj (allForces Source.SetLanguage.ACwo) (allForces Source.SetLanguage.AC.neg)))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ForcingConcreteSystem.coreFormula_freeClosed,allForces_freeClosed]

theorem models (phi : Source.Sentence) (hphi : Source.SetLanguage.targetTheory phi)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (sentence phi)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  change Project.Formula.satisfies ({bound := Fin.elim0,free := free} :
    Env (Project.FirstOrderSemantics.reduct M) 0) (sentence phi).formula
  obtain ⟨w,hw⟩ := ZF.exists_omega (ModelTransfer.project_models_iff.mp hM)
  obtain ⟨bound,labels,labelMap,F,G,W,Product,Y,X,CS,CC,I,outerF,P,base,incoming,C,H,mark,one,mul,D,history,stageBound,K,mu,continuum,Power,groundTop,u,seedC,seedH,values,Q,three,B,high,zero,seedMul,hCore,_hOutcome⟩ :=
    ForcingConcreteSystem.construct hM hOrder hChoice hw
  have hTarget := fun (p : M.Carrier .set) (hp : (Project.FirstOrderSemantics.reduct M).mem p W) => forces_target hM hOrder hChoice _ hCore hp phi hphi
  have hPP := fun (p : M.Carrier .set) (hp : (Project.FirstOrderSemantics.reduct M).mem p W) => forces_target hM hOrder hChoice _ hCore hp Source.SetLanguage.PP (Or.inr (Or.inl rfl))
  have hACwo := fun (p : M.Carrier .set) (hp : (Project.FirstOrderSemantics.reduct M).mem p W) => forces_target hM hOrder hChoice _ hCore hp Source.SetLanguage.ACwo (Or.inr (Or.inr (Or.inl rfl)))
  have hNotAC := fun (p : M.Carrier .set) (hp : (Project.FirstOrderSemantics.reduct M).mem p W) => forces_target hM hOrder hChoice _ hCore hp Source.SetLanguage.AC.neg (Or.inr (Or.inr (Or.inr rfl)))
  simp only [sentence,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ForcingConcreteSystem.coreFormula_semantics hM,allForces_semantics hM]
  exact ⟨w,bound,labels,labelMap,F,G,W,Product,Y,X,CS,CC,I,outerF,P,base,incoming,C,H,mark,one,mul,D,history,stageBound,K,mu,continuum,Power,groundTop,u,seedC,seedH,values,Q,three,B,high,zero,seedMul,hCore,hTarget,hPP,hACwo,hNotAC⟩

/-- Ordinary original nativeZF derivation of EACH source target axiom/schema
on an ACTUAL common system. Existing L discharges source helper Choice/order;
this is not yet the quantified internal proof-code consistency implication. -/
theorem kernel_certificate (phi : Source.Sentence) (hphi : Source.SetLanguage.targetTheory phi) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative (sentence phi))) := by
  apply ModelTransfer.derives
  intro N hN
  have hL := ConstructibleSource.model_zf hN
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hN)
  obtain ⟨witness,_⟩ := ZF.exists_omega (ModelTransfer.project_models_iff.mp hL)
  let env : Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hN)) 0 := ⟨Fin.elim0,fun _ => witness⟩
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hN
  exact (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hL) _).mp
    (models phi hphi hL (ConstructionRoundSelection.l_order hN) hChoice)

end PPAC.Migration.ForcingTargetTheory
