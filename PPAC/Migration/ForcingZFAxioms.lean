/- Pinned SymmetricChoice.forces_ZF: seven fixed axioms and the full
Separation/Replacement schemas, in the same all-rank internal HS domain.
This is an external schema of native derivations, not internal code induction. -/
import PPAC.Migration.ForcingReplacementAxiom
import PPAC.Migration.ForcingPowerAxiom
import PPAC.Migration.ForcingFoundation
import PPAC.Migration.ForcingInfinity

namespace PPAC.Migration.ForcingZFAxioms
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingAtomicBasic (PreorderOn)
open ForcingFormula (Force)
open ForcingProductFamily (Presentation)
open ForcingProductSymmetry (orderFormula)
open ForcingPairUnion (domain)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem forces_ZF (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w p : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpre : PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hcond : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (phi : Source.Sentence) (hphi : Source.SetLanguage.ZF phi) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env Fin.elim0 (env (rho 6)) p phi := by
  cases hphi with
  | extensionality => exact ForcingBasicSetAxioms.forces_extensionality hM env rho G F mul hpre hcond
  | emptySet => exact ForcingBasicSetAxioms.forces_emptySet hM env rho G F mul hp hG hF hpre
  | pairing => exact ForcingPairUnion.forces_pairing hM env rho G F mul hp hG hF hpre hcond
  | union => exact ForcingPairUnion.forces_union hM env rho G F mul hp hG hF hpre hcond
  | powerSet => exact ForcingPowerAxiom.forces_powerSet hM env rho G F mul hp hG hF hpre hcond
  | infinity => exact ForcingInfinity.forces_infinity hM env rho G F mul hp hG hF hpre
  | foundation => exact ForcingFoundation.forces_foundation hM env rho G F mul hpre hcond
  | separation phi => exact ForcingSeparationAxiom.forces_separation hM env rho G F mul hp hG hF hpre hcond phi
  | replacement phi => exact ForcingReplacementAxiom.forces_replacement hM env rho G F mul hp hG hF hpre hcond phi

def sentence (phi : Source.Sentence) : Source.Sentence :=
  let rho : Fin 7 → Fin 16 := fun i => ⟨i.val,Nat.lt_trans i.isLt (by decide)⟩
  let R := orderFormula (0 : Fin 16) 13
  let H := domain rho 11 12
  ((ForcingDiagramPoset.leftCancelMonoid (0 : Fin 16) 13 14).imp
    ((ForcingProductFamily.presentation (0 : Fin 16) 7 8 9 10 1 2 3 4 5 6).imp
      ((ForcingLabelPermutations.carrier (7 : Fin 16) 11).imp
        ((ForcingNormalFilter.normal (7 : Fin 16) 11 12).imp
          ((Formula.mem (15 : Fin 16) 6).imp (ForcingFormula.formula R H id Fin.elim0 6 15 phi)))))).close

theorem models (phi : Source.Sentence) (hphi : Source.SetLanguage.ZF phi)
    (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence (sentence phi)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hm hp hG hF hc
  let rho : Fin 7 → Fin 16 := fun i => ⟨i.val,Nat.lt_trans i.isLt (by decide)⟩
  let R := orderFormula (0 : Fin 16) 13
  let H := domain rho 11 12
  have hm' := (ForcingDiagramPoset.leftCancelMonoid_semantics (M := M) env 0 13 14).mp hm
  have hp' := (ForcingProductFamily.presentation_semantics (M := M) env 0 7 8 9 10 1 2 3 4 5 6).mp hp
  have hG' := (ForcingLabelPermutations.carrier_semantics (M := M) env 7 11).mp hG
  have hF' := (ForcingNormalFilter.normal_semantics (M := M) env 7 11 12).mp hF
  have hpre := ForcingProductPoset.preorder env 0 13 6 hm' hp'.2.2.2.2.1 hp'.2.2.2.1 hp'.2.2.2.2.2
  apply (ForcingFormula.formula_semantics (M := M) env R H id Fin.elim0 6 15 phi).mpr
  have hz : (fun i : Fin 0 => env (Fin.elim0 i)) = (Fin.elim0 : Fin 0 → M.Carrier .set) :=
    funext (fun i => Fin.elim0 i)
  rw [hz]
  exact forces_ZF hM env rho 11 12 13 hp' hG' hF' hpre hc phi hphi

theorem kernel_certificate (phi : Source.Sentence) (hphi : Source.SetLanguage.ZF phi) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (sentence phi)) :=
  ModelTransfer.derives (fun _ hM => models phi hphi hM)

end PPAC.Migration.ForcingZFAxioms
