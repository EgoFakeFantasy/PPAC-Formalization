/- Pinned Models.ConcreteSystem: actual mu=(2^omega)^+ and K=mu.
Consume actual cardinal witnesses and existing full IdealTower; no supplied
mu, mu^omega=mu, regularity, omega1 bound, or independently chosen K remains.
The source Base geometry/countable carrier contract stays explicit here. -/
import PPAC.Migration.ConstructionConcreteCardinals

namespace PPAC.Migration.ConstructionConcreteTower
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Tower (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one u P c mu kappa B : M.Carrier .set) : Prop :=
  ConstructionConcreteCardinals.Parameters hM w P c mu ∧
    ConstructionIdealProbes.IdealTower hM w Q R top D mul e mark H C zero one u mu mu kappa B

theorem exists_tower (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top D mul e mark H C zero one u : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : ConstructionRealCuts.CutCarrier hM w Q R)
    (hCoordinates : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hTop : ConstructionRealCuts.Principal hM w Q u top)
    (hObj : ConstructionRoundFields.ObjectFields hM w Q R top D mul e mark H C)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hD : ForcingSupportSize.Small D w) :
    ∃ P c mu kappa B, Tower hM w Q R top D mul e mark H C zero one u P c mu kappa B := by
  obtain ⟨P,c,mu,hParams⟩ := ConstructionConcreteCardinals.parameters_exists hM hChoice hw
  have hCopy := hParams
  obtain ⟨_,_,_,_,_,_,hMu,hPow,hOmegaOne⟩ := hCopy
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨wToMu,hWToMu⟩ := hMu.2
  obtain ⟨fromD,hFromD⟩ := (ForcingSupportSize.native_small hM D w).mp hD
  have hDmu := (ForcingSupportSize.native_small hM D mu).mpr
    (ZF.exists_compositionInjection hZF I hFromD hWToMu)
  obtain ⟨id,hId⟩ := ZF.exists_identityBijection hZF I mu
  have hKSmall := (ForcingSupportSize.native_small hM mu mu).mpr ⟨id,hId.1⟩
  obtain ⟨k,hk,_⟩ := hWToMu.1.2.2 zero hzw
  obtain ⟨kappa,B,hTower⟩ := ConstructionIdealProbes.exists_ideal_tower hM hOrder hChoice
    hw hQ hR hCoordinates hone hTop hObj hz hzw ⟨k,hk⟩ hMu hPow hDmu hKSmall hOmegaOne
  exact ⟨P,c,mu,kappa,B,hParams,hTower⟩


def tower {m : Nat} (w Q R top D mul e mark H C zero one u P c mu kappa B : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionConcreteCardinals.parameters w P c mu) (ConstructionIdealProbes.idealTower w Q R top D
  mul e mark H C zero one u mu mu kappa B))

theorem tower_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one u P c mu kappa B : Fin m) :
    (tower w Q R top D mul e mark H C zero one u P c mu kappa B).FreeClosed := by
  simp -implicitDefEqProofs [tower,Definitional.Formula.FreeClosed,ConstructionConcreteCardinals.parameters_freeClosed,ConstructionIdealProbes.idealTower_freeClosed]

theorem tower_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one u P c mu kappa B : Fin m) :
    Project.Formula.satisfies env (tower w Q R top D mul e mark H C zero one u P c mu kappa B) ↔ Tower hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound u) (env.bound P) (env.bound c) (env.bound mu) (env.bound kappa) (env.bound B) := by
  simp only [tower,Tower,
    Project.Formula.satisfies_conj_iff,
    
    ConstructionConcreteCardinals.parameters_semantics hM,ConstructionIdealProbes.idealTower_semantics hM]

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 13
    (.imp (Project.Formula.isOmega (.bound (12 : Fin 13))) (.imp (ConstructionFractionOrder.carrier (12 : Fin
    13) (11 : Fin 13)) (.imp (ConstructionRealCuts.cutCarrier (12 : Fin 13) (11 : Fin 13) (10 : Fin 13))
    (.imp (ConstructionFractionOrder.coordinates (12 : Fin 13) (0 : Fin 13) (1 : Fin 13) (1 : Fin 13)) (.imp
    (Project.Formula.isOrdinalOne (.bound (1 : Fin 13))) (.imp (ConstructionRealCuts.principal (12 : Fin 13)
    (11 : Fin 13) (0 : Fin 13) (9 : Fin 13)) (.imp (ConstructionRoundStepSyntax.objectFields (12 : Fin 13)
    (11 : Fin 13) (10 : Fin 13) (9 : Fin 13) (8 : Fin 13) (7 : Fin 13) (6 : Fin 13) (5 : Fin 13) (4 : Fin
    13) (3 : Fin 13)) (.imp (Project.Formula.isEmpty (.bound (2 : Fin 13))) (.imp (.mem (.bound (2 : Fin
    13)) (.bound (12 : Fin 13))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (8 : Fin 13) (12 :
    Fin 13))) (.existsE (.existsE (.existsE (.existsE (.existsE (tower (12 : Fin
    13).succ.succ.succ.succ.succ (11 : Fin 13).succ.succ.succ.succ.succ (10 : Fin
    13).succ.succ.succ.succ.succ (9 : Fin 13).succ.succ.succ.succ.succ (8 : Fin 13).succ.succ.succ.succ.succ
    (7 : Fin 13).succ.succ.succ.succ.succ (6 : Fin 13).succ.succ.succ.succ.succ (5 : Fin
    13).succ.succ.succ.succ.succ (4 : Fin 13).succ.succ.succ.succ.succ (3 : Fin 13).succ.succ.succ.succ.succ
    (2 : Fin 13).succ.succ.succ.succ.succ (1 : Fin 13).succ.succ.succ.succ.succ (0 : Fin
    13).succ.succ.succ.succ.succ (4 : Fin (13+5)) (3 : Fin (13+5)) (2 : Fin (13+5)) (1 : Fin (13+5)) (0 :
    Fin (13+5))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,ConstructionFractionOrder.carrier_freeClosed,
      ConstructionRealCuts.cutCarrier_freeClosed,ConstructionFractionOrder.coordinates_freeClosed,
      Project.Formula.isOrdinalOne,ConstructionRealCuts.principal_freeClosed,
      ConstructionRoundStepSyntax.objectFields_freeClosed,Project.Formula.isEmpty,tower_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isOrdinalOne_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    ConstructionFractionOrder.coordinates_semantics hM,ConstructionRealCuts.principal_semantics hM,
    ConstructionRoundStepSyntax.objectFields_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),tower_semantics hM]
  exact fun hw hQ hR hCoordinates hone hTop hObj hz hzw hD =>
    exists_tower hM hOrder hChoice hw hQ hR hCoordinates hone hTop hObj hz hzw hD

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative constructionSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let z := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => z }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM constructionSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) constructionSentence).mp
    (construction_models hL (ConstructionRoundSelection.l_order hM) hChoice)




end PPAC.Migration.ConstructionConcreteTower
