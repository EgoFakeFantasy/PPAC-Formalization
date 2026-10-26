/- Pinned SymmetricChoice: RelF, ImageF, image_in_bound, replacementImage.
The actual Collection/orbit bound supplies every local witness. -/
import PPAC.Migration.ForcingReplacementWitness

namespace PPAC.Migration.ForcingReplacementImage
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
open ForcingReplacementWitness (RelF LocalBound)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem forces_relation (hM : FirstOrder.Theory.Models M nativeZF) {k n m : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set} {P p : M.Carrier .set}
    (hpre : PreorderOn R env P) (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P)
    (phi : Formula (n+2)) (r : Fin n → Fin m) (x y : Fin m) (v : Fin m → M.Carrier .set) :
    Force R H env v P p (Source.SetLanguage.relation phi r x y) ↔
      RelF R H env (fun j => v (r j)) P p (v x) (v y) phi := by
  unfold Source.SetLanguage.relation
  rw [ForcingSound.rename hM hpre _ _ _ _ hp]
  have he : (fun j => v (Fin.lastCases y (Fin.lastCases x r) j)) =
      Fin.lastCases (v y) (Fin.lastCases (v x) (fun j => v (r j))) := by
    funext j
    refine Fin.lastCases ?_ (fun l => ?_) j
    · simp only [Fin.lastCases_last]
    · refine Fin.lastCases ?_ (fun t => ?_) l <;> simp only [Fin.lastCases_castSucc,Fin.lastCases_last]
  rw [he]
  rfl

theorem rel_left_congr (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set} {P p x x' y : M.Carrier .set}
    (hpre : PreorderOn R env P) (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P)
    (v : Fin n → M.Carrier .set) (phi : Formula (n+2)) (heq : Forces true R env P x x' p) :
    RelF R H env v P p x y phi ↔ RelF R H env v P p x' y phi := by
  apply ForcingFormula.tuple_congr hM hpre phi _ _ p hp
  intro j
  refine Fin.lastCases ?_ (fun l => ?_) j
  · simpa only [Fin.lastCases_last] using ForcingAtomicBasic.eq_refl hM hpre y p hp
  · refine Fin.lastCases ?_ (fun t => ?_) l
    · simpa only [Fin.lastCases_castSucc,Fin.lastCases_last] using heq
    · simpa only [Fin.lastCases_castSucc] using ForcingAtomicBasic.eq_refl hM hpre (v t) p hp

def ImageF {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (v : Fin n → M.Carrier .set) (P sigma p nu : M.Carrier .set) (phi : Formula (n+2)) : Prop :=
  ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
    ∃ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧
      ∃ x, Predicate H env x ∧ Forces false R env P x sigma r ∧ RelF R H env v P r x nu phi

def SingleValuedF {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (v : Fin n → M.Carrier .set) (P sigma p : M.Carrier .set) (phi : Formula (n+2)) : Prop :=
  ∀ x, Predicate H env x → ∀ y, Predicate H env y → ∀ z, Predicate H env z →
    ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
      Forces false R env P x sigma q → RelF R H env v P q x y phi → RelF R H env v P q x z phi → Forces true R env P y z q

theorem image_in_bound (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {v : Fin n → M.Carrier .set} {sigma bound p nu : M.Carrier .set} {phi : Formula (n+2)}
    (hpre : PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hs : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) sigma)
    (hcond : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hnu : Predicate (domain rho G F) env nu)
    (hb : LocalBound (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) sigma bound phi)
    (hfunc : SingleValuedF (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) sigma p phi)
    (himage : ImageF (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) sigma p nu phi) :
    Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nu bound p := by
  apply ForcingAtomicBasic.mem_of_dense hM hpre hcond
  intro q hq hqp
  obtain ⟨r,hr,hrq,x,_,hx,hphi⟩ := himage q hq hqp
  obtain ⟨s,child,c,hscnd,hsr,hc,he,hsc,heq⟩ :=
    ((ForcingAtomicRelations.mem_iff hM _ env _ x sigma r).mp hx).2 r hr (hpre.1 r hr)
  have hchild := (domain_semantics env rho G F child).mpr (ForcingHS.child hs he)
  have hphi' := (rel_left_congr hM hpre hscnd v phi heq).mp
    (ForcingFormula.mono hM hpre phi _ hr hscnd hsr hphi)
  obtain ⟨eta,heta,hetaphi,hetaB⟩ := ForcingReplacementWitness.bounded_local_witness hb he hscnd ⟨nu,hnu,hphi'⟩
  have hsp := hpre.2 s r p hscnd hr hcond hsr (hpre.2 r q p hr hq hcond hrq hqp)
  have hmem := ForcingAtomicBasic.mem_of_edge_eq hM hpre hc hsc he (ForcingAtomicBasic.eq_refl hM hpre child s hscnd)
  have hneq := hfunc child hchild nu hnu eta heta s hscnd hsp hmem hphi' hetaphi
  exact ⟨s,hscnd,hpre.2 s r q hscnd hr hq hsr hrq,(ForcingAtomicLaws.mem_congr_left hM hpre hneq).mpr hetaB⟩

/-- Exactly the original source image predicate and binder positions. -/
def imageFormula {n : Nat} (phi : Formula (n+2)) : Formula (n+2) :=
  .ex ((Formula.mem (Fin.last (n+2)) (Fin.last n).castSucc.castSucc).conj
    (Source.SetLanguage.relation phi (fun i => i.castSucc.castSucc.castSucc)
      (Fin.last (n+2)) (Fin.last (n+1)).castSucc))

theorem forces_imageFormula (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set} {P sigma p nu : M.Carrier .set}
    (hpre : PreorderOn R env P) (v : Fin n → M.Carrier .set) (phi : Formula (n+2)) :
    Force R H env (Fin.lastCases nu (Fin.lastCases sigma v)) P p (imageFormula phi) ↔ ImageF R H env v P sigma p nu phi := by
  unfold imageFormula ImageF
  rw [ForcingFormula.force_ex]
  apply forall_congr'
  intro q
  apply forall_congr'
  intro hq
  apply forall_congr'
  intro hqp
  apply exists_congr
  intro r
  apply and_congr Iff.rfl
  constructor
  · rintro ⟨hrq,x,hx,hforce⟩
    obtain ⟨hmem,hrel⟩ := (ForcingFormula.force_conj _ _ _ _ _ _ _ _).mp hforce
    simp only [ForcingFormula.force_mem,Fin.lastCases_last,Fin.lastCases_castSucc] at hmem
    have hr := ForcingAtomicBasic.condition hM hmem
    have hh := (forces_relation hM hpre hr phi (fun i => i.castSucc.castSucc.castSucc)
      (Fin.last (n+2)) (Fin.last (n+1)).castSucc (Fin.lastCases x (Fin.lastCases nu (Fin.lastCases sigma v)))).mp hrel
    simp only [Fin.lastCases_last,Fin.lastCases_castSucc] at hh
    exact ⟨hrq,x,hx,hmem,hh⟩
  · rintro ⟨hrq,x,hx,hmem,hrel⟩
    have hr := ForcingAtomicBasic.condition hM hmem
    refine ⟨hrq,x,hx,(ForcingFormula.force_conj _ _ _ _ _ _ _ _).mpr ⟨?_,?_⟩⟩
    · simpa only [ForcingFormula.force_mem,Fin.lastCases_last,Fin.lastCases_castSucc] using hmem
    · apply (forces_relation hM hpre hr phi (fun i => i.castSucc.castSucc.castSucc)
        (Fin.last (n+2)) (Fin.last (n+1)).castSucc (Fin.lastCases x (Fin.lastCases nu (Fin.lastCases sigma v)))).mpr
      simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hrel

/-- Source replacementImage is Separation of the orbit bound by imageFormula. -/
theorem exists_image (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w sigma p : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpre : PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hs : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) sigma)
    (v : Fin n → M.Carrier .set)
    (hv : ∀ j, HS actionFormula (fun l => env (rho l)) (env G) (env (rho 6)) (env F) (v j))
    (phi : Formula (n+2))
    (hcond : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hfunc : SingleValuedF (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) sigma p phi) :
    ∃ name, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧
      ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
        MapRel (orderFormula (rho 0) mul) env q p → ∀ nu, Predicate (domain rho G F) env nu →
        (Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nu name q ↔
          ImageF (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) sigma q nu phi) := by
  obtain ⟨bound,hb,hw⟩ := ForcingReplacementWitness.exists_at_values hM env rho G F mul hp hG hF hpre sigma v phi
  have hv' : ∀ j, HS actionFormula (fun l => env (rho l)) (env G) (env (rho 6)) (env F) (Fin.lastCases sigma v j) := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [Fin.lastCases_last] using hs
    · simpa only [Fin.lastCases_castSucc] using hv i
  obtain ⟨name,hn,hsep⟩ := ForcingSeparationAxiom.exists_at_values hM env rho G F mul hp hG hF hb
    (Fin.lastCases sigma v) hv' (imageFormula phi)
  refine ⟨name,hn,?_⟩
  intro q hq hqp nu hnu
  rw [ForcingSeparationAxiom.mem_separate hM hpre hsep hq,forces_imageFormula hM hpre v phi]
  refine ⟨And.right,fun hi => ⟨?_,hi⟩⟩
  exact image_in_bound hM env rho G F mul hpre hs hq hnu hw
    (fun x hx y hy z hz r hr hrq => hfunc x hx y hy z hz r hr (hpre.2 r q p hr hq hcond hrq hqp)) hi

end PPAC.Migration.ForcingReplacementImage
