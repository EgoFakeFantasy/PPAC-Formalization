/- Pinned SymmetricChoice.singleValued_of_totalFunctional/forces_replacement.
The Collection/orbit witness construction is consumed, not postulated. -/
import PPAC.Migration.ForcingReplacementImage

namespace PPAC.Migration.ForcingReplacementAxiom
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
open ForcingAtomicBasic (PreorderOn)
open ForcingClassEvaluation (Predicate)
open ForcingFormula (Force)
open ForcingProductFamily (Presentation actionFormula)
open ForcingProductSymmetry (orderFormula)
open ForcingPairUnion (domain domain_semantics)
open ForcingHS (HS)
open ForcingReplacementWitness (RelF)
open ForcingReplacementImage (SingleValuedF ImageF forces_relation)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def TotalFunctionalF {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (v : Fin n → M.Carrier .set) (P sigma p : M.Carrier .set) (phi : Formula (n+2)) : Prop :=
  ∀ x, Predicate H env x → ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
    Forces false R env P x sigma q → ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P → MapRel R env r q →
      ∃ s, (Definitional.Project.FirstOrderSemantics.reduct M).mem s P ∧ MapRel R env s r ∧
        ∃ y, Predicate H env y ∧ RelF R H env v P s x y phi ∧
          ∀ z, Predicate H env z → ∀ t, (Definitional.Project.FirstOrderSemantics.reduct M).mem t P → MapRel R env t s →
            RelF R H env v P t x z phi → Forces true R env P z y t

theorem singleValued_of_totalFunctional (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {v : Fin n → M.Carrier .set} {P sigma p : M.Carrier .set} {phi : Formula (n+2)}
    (hpre : PreorderOn R env P) (h : TotalFunctionalF R H env v P sigma p phi) :
    SingleValuedF R H env v P sigma p phi := by
  intro x hx y hy z hz q hq hqp hmem hxy hxz
  apply ForcingAtomicBasic.eq_of_dense hM hpre hq
  intro r hr hrq
  obtain ⟨s,hs,hsr,eta,_,_,heta⟩ := h x hx q hq hqp hmem r hr hrq
  have hsq := hpre.2 s r q hs hr hq hsr hrq
  have hyeta := heta y hy s hs (hpre.1 s hs) (ForcingFormula.mono hM hpre phi _ hq hs hsq hxy)
  have hzeta := heta z hz s hs (hpre.1 s hs) (ForcingFormula.mono hM hpre phi _ hq hs hsq hxz)
  exact ⟨s,hs,hsr,ForcingAtomicLaws.eq_trans hM hpre hyeta (ForcingAtomicBasic.eq_symm hM hzeta)⟩

theorem forces_replacement (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w p : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpre : PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hcond : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) (phi : Formula (n+2)) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env Fin.elim0 (env (rho 6)) p (Source.SetLanguage.replacement phi) := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let P := env (rho 6)
  unfold Source.SetLanguage.replacement
  apply (ForcingSeparationAxiom.force_close hM hpre hcond _).mpr
  intro v hv
  apply (ForcingFormula.force_all hM hpre hcond _ _).mpr
  intro sigma hs
  apply (ForcingFormula.force_imp hM hpre hcond _ _ _).mpr
  intro q hq _ hant
  have htot : TotalFunctionalF R H env v P sigma q phi := by
    intro x hx a ha haq hmem b hb hba
    have hxa := (ForcingFormula.force_all hM hpre hq _ _).mp hant x hx
    have hex := (ForcingFormula.force_imp hM hpre hq _ _ _).mp hxa a ha haq (by
      simpa only [ForcingFormula.force_mem,Fin.lastCases_last,Fin.lastCases_castSucc] using hmem)
    obtain ⟨c,hc,hcb,y,hy,hboth⟩ := (ForcingFormula.force_ex R H env _ P a _).mp hex b hb hba
    obtain ⟨hrel,huniq⟩ := (ForcingFormula.force_conj _ _ _ _ _ _ _ _).mp hboth
    refine ⟨c,hc,hcb,y,hy,?_,?_⟩
    · have hh := (forces_relation hM hpre hc phi (fun i => i.castSucc.castSucc.castSucc)
        (Fin.last (n+1)).castSucc (Fin.last (n+2)) (Fin.lastCases y (Fin.lastCases x (Fin.lastCases sigma v)))).mp hrel
      simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hh
    · intro z hz t ht htc hrelz
      have hzuniq := (ForcingFormula.force_all hM hpre hc _ _).mp huniq z hz
      have himp := (ForcingFormula.force_imp hM hpre hc _ _ _).mp hzuniq t ht htc
      have hh : Force R H env (Fin.lastCases z (Fin.lastCases y (Fin.lastCases x (Fin.lastCases sigma v)))) P t
          (Source.SetLanguage.relation phi (fun i => i.castSucc.castSucc.castSucc.castSucc)
            (Fin.last (n+1)).castSucc.castSucc (Fin.last (n+3))) := by
        apply (forces_relation hM hpre ht phi _ _ _ _).mpr
        simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hrelz
      simpa only [ForcingFormula.force_equal,Fin.lastCases_last,Fin.lastCases_castSucc] using himp hh
  have hfunc := singleValued_of_totalFunctional hM hpre htot
  obtain ⟨name,hn,he⟩ := ForcingReplacementImage.exists_image hM env rho G F mul hp hG hF hpre
    ((domain_semantics env rho G F sigma).mp hs) v
    (fun j => (domain_semantics env rho G F (v j)).mp (hv j)) phi hq hfunc
  apply (ForcingFormula.force_ex R H env _ P q _).mpr
  intro r hr hrq
  refine ⟨r,hr,hpre.1 r hr,name,(domain_semantics env rho G F name).mpr hn,?_⟩
  apply (ForcingFormula.force_all hM hpre hr _ _).mpr
  intro nu hnu
  have himage : ∀ t, (Definitional.Project.FirstOrderSemantics.reduct M).mem t P →
      (Force R H env (Fin.lastCases nu (Fin.lastCases name (Fin.lastCases sigma v))) P t
        (.ex ((Formula.mem (Fin.last (n+3)) (Fin.last n).castSucc.castSucc.castSucc).conj
          (Source.SetLanguage.relation phi (fun i => i.castSucc.castSucc.castSucc.castSucc)
            (Fin.last (n+3)) (Fin.last (n+2)).castSucc))) ↔ ImageF R H env v P sigma t nu phi) := by
    intro t ht
    rw [ForcingFormula.force_ex]
    unfold ImageF
    apply forall_congr'
    intro a
    apply forall_congr'
    intro ha
    apply forall_congr'
    intro hat
    apply exists_congr
    intro b
    apply and_congr Iff.rfl
    constructor
    · rintro ⟨hba,x,hx,hboth⟩
      obtain ⟨hmem,hrel⟩ := (ForcingFormula.force_conj _ _ _ _ _ _ _ _).mp hboth
      simp only [ForcingFormula.force_mem,Fin.lastCases_last,Fin.lastCases_castSucc] at hmem
      have hb := ForcingAtomicBasic.condition hM hmem
      have hh := (forces_relation hM hpre hb phi _ _ _ _).mp hrel
      simp only [Fin.lastCases_last,Fin.lastCases_castSucc] at hh
      exact ⟨hba,x,hx,hmem,hh⟩
    · rintro ⟨hba,x,hx,hmem,hrel⟩
      have hb := ForcingAtomicBasic.condition hM hmem
      refine ⟨hba,x,hx,(ForcingFormula.force_conj _ _ _ _ _ _ _ _).mpr ⟨?_,?_⟩⟩
      · simpa only [ForcingFormula.force_mem,Fin.lastCases_last,Fin.lastCases_castSucc] using hmem
      · apply (forces_relation hM hpre hb phi _ _ _ _).mpr
        simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hrel
  simp only [Source.Formula.iff,ForcingFormula.force_conj,ForcingFormula.force_imp hM hpre hr,
    ForcingFormula.force_mem,Fin.lastCases_last,Fin.lastCases_castSucc]
  constructor
  · intro t ht htr hmem
    exact (himage t ht).mpr ((he t ht (hpre.2 t r q ht hr hq htr hrq) nu hnu).mp hmem)
  · intro t ht htr hforce
    exact (he t ht (hpre.2 t r q ht hr hq htr hrq) nu hnu).mpr ((himage t ht).mp hforce)

def sentence {n : Nat} (phi : Formula (n+2)) : Source.Sentence :=
  let rho : Fin 7 → Fin 16 := fun i => ⟨i.val,Nat.lt_trans i.isLt (by decide)⟩
  let R := orderFormula (0 : Fin 16) 13
  let H := domain rho 11 12
  ((ForcingDiagramPoset.leftCancelMonoid (0 : Fin 16) 13 14).imp
    ((ForcingProductFamily.presentation (0 : Fin 16) 7 8 9 10 1 2 3 4 5 6).imp
      ((ForcingLabelPermutations.carrier (7 : Fin 16) 11).imp
        ((ForcingNormalFilter.normal (7 : Fin 16) 11 12).imp
          ((Formula.mem (15 : Fin 16) 6).imp
            (ForcingFormula.formula R H id Fin.elim0 6 15 (Source.SetLanguage.replacement phi))))))).close

theorem models {n : Nat} (phi : Formula (n+2)) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (sentence phi)).TrueIn M := by
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
  apply (ForcingFormula.formula_semantics (M := M) env R H id Fin.elim0 6 15 (Source.SetLanguage.replacement phi)).mpr
  have hz : (fun i : Fin 0 => env (Fin.elim0 i)) = (Fin.elim0 : Fin 0 → M.Carrier .set) :=
    funext (fun i => Fin.elim0 i)
  rw [hz]
  exact forces_replacement hM env rho 11 12 13 hp' hG' hF' hpre hc phi

theorem kernel_certificate {n : Nat} (phi : Formula (n+2)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (sentence phi)) :=
  ModelTransfer.derives (fun _ hM => models phi hM)

end PPAC.Migration.ForcingReplacementAxiom
