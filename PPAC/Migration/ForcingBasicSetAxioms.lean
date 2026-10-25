/- Pinned SymmetricNames.eq_of_same_members/not_mem_empty and their forced
Extensionality/Empty Set axioms. Exact recursive equality, actual all-rank HS
and already constructed condition system; no forcing axiom is assumed. -/
import PPAC.Migration.ForcingPairUnion

namespace PPAC.Migration.ForcingBasicSetAxioms
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
open ForcingAtomicBasic (PreorderOn)
open ForcingFormula (Force)
open ForcingHS (HS)
open ForcingProductFamily (Presentation)
open ForcingProductSymmetry (orderFormula)
open ForcingPairUnion (domain domain_semantics)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem eq_of_same_members (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {A : Formula (k+2)} {aenv : Fin k → M.Carrier .set}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {G P F sigma tau p : M.Carrier .set}
    (hpre : PreorderOn R params P) (hs : HS A aenv G P F sigma) (ht : HS A aenv G P F tau)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P)
    (h : ∀ nu, HS A aenv G P F nu → ∀ q,
      (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R params q p →
      (Forces false R params P nu sigma q ↔ Forces false R params P nu tau q)) :
    Forces true R params P sigma tau p := by
  apply (ForcingAtomicRelations.eq_iff hM R params P sigma tau p).mpr
  refine ⟨hp,?_,?_⟩
  · intro nu c hc he q hq hqp hqc
    exact (h nu (ForcingHS.child hs he) q hq hqp).mp
      (ForcingAtomicBasic.mem_of_edge_eq hM hpre hc hqc he (ForcingAtomicBasic.eq_refl hM hpre nu q hq))
  · intro nu c hc he q hq hqp hqc
    exact (h nu (ForcingHS.child ht he) q hq hqp).mpr
      (ForcingAtomicBasic.mem_of_edge_eq hM hpre hc hqc he (ForcingAtomicBasic.eq_refl hM hpre nu q hq))

theorem not_mem_empty (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P empty nu p : M.Carrier .set}
    (hpre : PreorderOn R params P) (he : ForcingWithTopCarrier.Empty empty) :
    ¬Forces false R params P nu empty p := by
  intro hm
  obtain ⟨hp,hcl⟩ := (ForcingAtomicRelations.mem_iff hM R params P nu empty p).mp hm
  obtain ⟨_,_,_,_,_,_,⟨z,_,hz⟩,_,_⟩ := hcl p hp (hpre.1 p hp)
  exact he z hz

theorem forces_extensionality (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Fin n → M.Carrier .set) (rho : Fin 7 → Fin n) (G F mul : Fin n)
    {p : M.Carrier .set}
    (hpre : PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env Fin.elim0 (env (rho 6)) p Source.SetLanguage.extensionality := by
  unfold Source.SetLanguage.extensionality
  apply (ForcingFormula.force_all hM hpre hp _ _).mpr
  intro sigma hs
  apply (ForcingFormula.force_all hM hpre hp _ _).mpr
  intro tau ht
  apply (ForcingFormula.force_imp hM hpre hp _ _ _).mpr
  intro q hq _ hsame
  apply eq_of_same_members hM hpre ((domain_semantics env rho G F sigma).mp hs)
    ((domain_semantics env rho G F tau).mp ht) hq
  intro nu hnu r hr hrq
  have hpoint := (ForcingFormula.force_all hM hpre hq _ _).mp hsame nu
    ((domain_semantics env rho G F nu).mpr hnu)
  exact ⟨(ForcingFormula.force_imp hM hpre hq _ _ _).mp hpoint.1 r hr hrq,
    (ForcingFormula.force_imp hM hpre hq _ _ _).mp hpoint.2 r hr hrq⟩

theorem forces_emptySet (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Fin n → M.Carrier .set) (rho : Fin 7 → Fin n) (G F mul : Fin n)
    {I K B w p : M.Carrier .set}
    (hpresentation : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpre : PreorderOn (orderFormula (rho 0) mul) env (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env Fin.elim0 (env (rho 6)) p Source.SetLanguage.emptySet := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  unfold Source.SetLanguage.emptySet
  apply (ForcingFormula.force_ex R H env Fin.elim0 W p _).mpr
  intro q hq hqp
  obtain ⟨empty,he⟩ := ForcingWithTopCarrier.exists_empty hM
  have hf := ForcingProductFamily.family hM (fun j => env (rho j)) hpresentation hG
  have hHS := ForcingHS.empty_hs hM ForcingProductFamily.actionFormula (fun j => env (rho j))
    (env G) W (env F) empty (by
      intro g hg
      obtain ⟨a,ha⟩ := hf.1 g hg
      exact ⟨a,ha,(hf.2 g a hg ha).1⟩) hF.1 he
  refine ⟨q,hq,hpre.1 q hq,empty,(domain_semantics env rho G F empty).mpr hHS,?_⟩
  change Force R H env (Fin.lastCases empty Fin.elim0) W q (.all (Formula.mem (1 : Fin 2) 0).neg)
  apply (ForcingFormula.force_all hM hpre hq _ _).mpr
  intro nu hnu
  apply (ForcingFormula.force_neg hM hpre hq _ _).mpr
  intro r hr hrq hm
  exact not_mem_empty hM hpre he hm

def sentence : Source.Sentence :=
  let rho : Fin 7 → Fin 16 := fun i => ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  let R := orderFormula (0 : Fin 16) 13
  let H := domain rho 11 12
  ((ForcingDiagramPoset.leftCancelMonoid (0 : Fin 16) 13 14).imp
    ((ForcingProductFamily.presentation (0 : Fin 16) 7 8 9 10 1 2 3 4 5 6).imp
      ((ForcingLabelPermutations.carrier (7 : Fin 16) 11).imp
        ((ForcingNormalFilter.normal (7 : Fin 16) 11 12).imp
          ((Formula.mem (15 : Fin 16) 6).imp
            ((ForcingFormula.formula R H id Fin.elim0 6 15 Source.SetLanguage.extensionality).conj
              (ForcingFormula.formula R H id Fin.elim0 6 15 Source.SetLanguage.emptySet))))))).close

theorem models (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence sentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hm hp hG hF hc
  let rho : Fin 7 → Fin 16 := fun i => ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  let R := orderFormula (0 : Fin 16) 13
  let H := domain rho 11 12
  have hm' := (ForcingDiagramPoset.leftCancelMonoid_semantics (M := M) env 0 13 14).mp hm
  have hp' := (ForcingProductFamily.presentation_semantics (M := M) env 0 7 8 9 10 1 2 3 4 5 6).mp hp
  have hG' := (ForcingLabelPermutations.carrier_semantics (M := M) env 7 11).mp hG
  have hF' := (ForcingNormalFilter.normal_semantics (M := M) env 7 11 12).mp hF
  have hpre := ForcingProductPoset.preorder env 0 13 6 hm' hp'.2.2.2.2.1 hp'.2.2.2.1 hp'.2.2.2.2.2
  have hzero : (fun i : Fin 0 => env (Fin.elim0 i)) = (Fin.elim0 : Fin 0 → M.Carrier .set) :=
    funext (fun i => Fin.elim0 i)
  constructor
  · apply (ForcingFormula.formula_semantics (M := M) env R H id Fin.elim0 6 15 Source.SetLanguage.extensionality).mpr
    rw [hzero]
    exact forces_extensionality hM env rho 11 12 13 hpre hc
  · apply (ForcingFormula.formula_semantics (M := M) env R H id Fin.elim0 6 15 Source.SetLanguage.emptySet).mpr
    rw [hzero]
    exact forces_emptySet hM env rho 11 12 13 hp' hG' hF' hpre

theorem kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence sentence) :=
  ModelTransfer.derives (fun _ hM => models hM)

end PPAC.Migration.ForcingBasicSetAxioms
