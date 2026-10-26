/- Pinned SymmetricNames.mem_separate/forces_separation.
Reuse the literal collected HS name and source regular-forcing arguments. -/
import PPAC.Migration.ForcingSeparation

namespace PPAC.Migration.ForcingSeparationAxiom
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
open ForcingAtomicBasic (PreorderOn)
open ForcingFormula (Force)
open ForcingSeparation (Separated)
open ForcingProductFamily (Presentation actionFormula)
open ForcingProductSymmetry (orderFormula)
open ForcingPairUnion (domain domain_semantics)
open ForcingClassEvaluation (Predicate)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem snoc_congr (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p x y : M.Carrier .set} (hpre : PreorderOn R env P)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P)
    (he : Forces true R env P x y p) (v : Fin n → M.Carrier .set) (phi : Formula (n+1)) :
    Force R H env (Fin.lastCases x v) P p phi ↔ Force R H env (Fin.lastCases y v) P p phi := by
  apply ForcingFormula.tuple_congr hM hpre phi _ _ p hp
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa only [Fin.lastCases_last] using he
  · simpa only [Fin.lastCases_castSucc] using ForcingAtomicBasic.eq_refl hM hpre (v i) p hp

theorem mem_separate (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {v : Fin n → M.Carrier .set} {P sigma name nu p : M.Carrier .set} {phi : Formula (n+1)}
    (hpre : PreorderOn R env P) (hn : Separated R H env v P sigma name phi)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P) :
    Forces false R env P nu name p ↔
      Forces false R env P nu sigma p ∧ Force R H env (Fin.lastCases nu v) P p phi := by
  constructor
  · intro h
    have hd : ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
        ∃ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧
          Forces false R env P nu sigma r ∧ Force R H env (Fin.lastCases nu v) P r phi := by
      intro q hq hqp
      obtain ⟨r,child,c,hr,hrq,hc,he,hrc,heq⟩ := ((ForcingAtomicRelations.mem_iff hM R env P nu name p).mp h).2 q hq hqp
      obtain ⟨_,_,hm,hforce⟩ := (hn child c).mp he
      exact ⟨r,hr,hrq,(ForcingAtomicLaws.mem_congr_left hM hpre heq).mpr
        (ForcingAtomicBasic.mem_mono hM hpre hr hrc hm),
        (snoc_congr hM hpre hr heq v phi).mpr (ForcingFormula.mono hM hpre phi _ hc hr hrc hforce)⟩
    constructor
    · apply ForcingAtomicBasic.mem_of_dense hM hpre hp
      intro q hq hqp
      obtain ⟨r,hr,hrq,hm,_⟩ := hd q hq hqp
      exact ⟨r,hr,hrq,hm⟩
    · apply ForcingFormula.of_dense hM hpre phi _ hp
      intro q hq hqp
      obtain ⟨r,hr,hrq,_,hf⟩ := hd q hq hqp
      exact ⟨r,hr,hrq,hf⟩
  · rintro ⟨hm,hforce⟩
    apply (ForcingAtomicRelations.mem_iff hM R env P nu name p).mpr
    refine ⟨hp,?_⟩
    intro q hq hqp
    obtain ⟨r,child,c,hr,hrq,hc,he,hrc,heq⟩ := ((ForcingAtomicRelations.mem_iff hM R env P nu sigma p).mp hm).2 q hq hqp
    have hmem := ForcingAtomicBasic.mem_of_edge_eq hM hpre hc hrc he
      (ForcingAtomicBasic.eq_refl hM hpre child r hr)
    have hphi := (snoc_congr hM hpre hr heq v phi).mp
      (ForcingFormula.mono hM hpre phi _ hp hr (hpre.2 r q p hr hq hp hrq hqp) hforce)
    exact ⟨r,child,r,hr,hrq,hr,(hn child r).mpr ⟨⟨c,he⟩,hr,hmem,hphi⟩,hpre.1 r hr,heq⟩

/-- Instantiate the constructed name at arbitrary internal parameter values;
Fin.addCases merely supplies slots for the existing pure object formula. -/
theorem exists_at_values (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w sigma : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hs : ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) sigma)
    (v : Fin n → M.Carrier .set)
    (hv : ∀ j, ForcingHS.HS actionFormula (fun l => env (rho l)) (env G) (env (rho 6)) (env F) (v j))
    (phi : Formula (n+1)) :
    ∃ name, ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧
      Separated (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) sigma name phi := by
  let ext : Fin (k+(n+1)) → M.Carrier .set := Fin.addCases env (Fin.lastCases sigma v)
  let up : Fin k → Fin (k+(n+1)) := Fin.castAdd (n+1)
  let ra := fun j => up (rho j)
  let vv : Fin n → Fin (k+(n+1)) := fun j => Fin.natAdd k j.castSucc
  let ss := Fin.natAdd k (Fin.last n)
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let S := orderFormula (up (rho 0)) (up mul)
  let J := domain ra (up G) (up F)
  have hp' : Presentation (ext (ra 0)) I K B w (ext (ra 1)) (ext (ra 2))
      (ext (ra 3)) (ext (ra 4)) (ext (ra 5)) (ext (ra 6)) := by
    simpa only [ext,ra,up,Fin.addCases_left] using hp
  have hG' : ForcingLabelPermutations.Carrier I (ext (up G)) := by
    simpa only [ext,up,Fin.addCases_left] using hG
  have hF' : ForcingNormalFilter.Normal I (ext (up G)) (ext (up F)) := by
    simpa only [ext,up,Fin.addCases_left] using hF
  have hs' : ForcingHS.HS actionFormula (fun j => ext (ra j)) (ext (up G)) (ext (ra 6)) (ext (up F)) (ext ss) := by
    simpa only [ext,ra,up,ss,Fin.addCases_left,Fin.addCases_right,Fin.lastCases_last] using hs
  have hv' : ∀ j, ForcingHS.HS actionFormula (fun l => ext (ra l)) (ext (up G)) (ext (ra 6)) (ext (up F)) (ext (vv j)) := by
    intro j
    simpa only [ext,ra,up,vv,Fin.addCases_left,Fin.addCases_right,Fin.lastCases_castSucc] using hv j
  obtain ⟨f,name,hf,hn,hname⟩ := ForcingSeparation.exists_separate hM ext ra (up G) (up F) (up mul) ss hp' hG' hF' hs' vv hv' phi
  have hR : ∀ x y, MapRel R env x y ↔ MapRel S ext x y := by
    intro x y
    simp only [R,S,ForcingProductSymmetry.orderFormula_semantics,ext,up,Fin.addCases_left]
  have hH : ∀ x, Predicate H env x ↔ Predicate J ext x := by
    intro x
    simp only [H,J,domain_semantics,ext,ra,up,Fin.addCases_left]
  refine ⟨name,?_,?_⟩
  · simpa only [ext,ra,up,Fin.addCases_left] using hname
  · intro child p
    have he : PureKuratowski.PairMember M child p name ↔
        (∃ c, PureKuratowski.PairMember M child c sigma) ∧
        (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) ∧
        Forces false S ext (env (rho 6)) child sigma p ∧
        Force S J ext (Fin.lastCases child v) (env (rho 6)) p phi := by
      simpa only [ext,ra,up,vv,ss,Fin.addCases_left,Fin.addCases_right,Fin.lastCases_last,Fin.lastCases_castSucc]
        using ForcingSeparation.edge_separate hM hf hn child p
    rw [← ForcingSeparation.atomic_congr hR false, ← ForcingSeparation.force_congr hR hH phi] at he
    exact he

/-- Source forceFormula_close, with all parameters ranging over the actual H. -/
theorem force_close (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set} {P p : M.Carrier .set}
    (hpre : PreorderOn R env P) (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P)
    (phi : Formula n) : Force R H env Fin.elim0 P p phi.close ↔
      ∀ v, (∀ j, Predicate H env (v j)) → Force R H env v P p phi := by
  induction n with
  | zero =>
    constructor
    · intro h v _
      have he : (Fin.elim0 : Fin 0 → M.Carrier .set) = v := funext (fun i => Fin.elim0 i)
      exact he ▸ h
    · intro h
      exact h Fin.elim0 (fun i => Fin.elim0 i)
  | succ n ih =>
    rw [Source.Formula.close, ih]
    constructor
    · intro h v hv
      have hf := (ForcingFormula.force_all hM hpre hp _ _).mp
        (h (fun j => v j.castSucc) (fun j => hv j.castSucc)) (v (Fin.last n)) (hv (Fin.last n))
      have he : (Fin.lastCases (v (Fin.last n)) (fun j => v j.castSucc)) = v := by
        funext j
        refine Fin.lastCases ?_ (fun i => ?_) j <;> simp only [Fin.lastCases_last,Fin.lastCases_castSucc]
      exact he ▸ hf
    · intro h v hv
      apply (ForcingFormula.force_all hM hpre hp _ _).mpr
      intro x hx
      apply h (Fin.lastCases x v)
      intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa only [Fin.lastCases_last] using hx
      · simpa only [Fin.lastCases_castSucc] using hv i

theorem forces_separation (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w p : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpre : PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hcond : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (phi : Formula (n+1)) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env Fin.elim0 (env (rho 6)) p
      (Source.SetLanguage.separation phi) := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let P := env (rho 6)
  unfold Source.SetLanguage.separation
  apply (force_close hM hpre hcond _).mpr
  intro v hv
  apply (ForcingFormula.force_all hM hpre hcond _ _).mpr
  intro sigma hs
  obtain ⟨name,hname,hn⟩ := exists_at_values hM env rho G F mul hp hG hF
    ((domain_semantics env rho G F sigma).mp hs) v
    (fun j => (domain_semantics env rho G F (v j)).mp (hv j)) phi
  apply (ForcingFormula.force_ex R H env _ P p _).mpr
  intro q hq _
  refine ⟨q,hq,hpre.1 q hq,name,(domain_semantics env rho G F name).mpr hname,?_⟩
  apply (ForcingFormula.force_all hM hpre hq _ _).mpr
  intro nu _
  let vv : Fin (n+3) → M.Carrier .set := Fin.lastCases nu (Fin.lastCases name (Fin.lastCases sigma v))
  let ren : Fin (n+1) → Fin (n+3) := Fin.lastCases (Fin.last (n+2)) (fun i => i.castSucc.castSucc.castSucc)
  have hvec : (fun i => vv (ren i)) = Fin.lastCases nu v := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [vv,ren,Fin.lastCases_last,Fin.lastCases_castSucc]
  have hrn : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P →
      (Force R H env vv P r (phi.rename ren) ↔ Force R H env (Fin.lastCases nu v) P r phi) := by
    intro r hr
    rw [ForcingSound.rename hM hpre phi ren vv r hr,hvec]
  simp only [Source.Formula.iff,ForcingFormula.force_conj,ForcingFormula.force_imp hM hpre hq,
    ForcingFormula.force_mem,Fin.lastCases_last,Fin.lastCases_castSucc]
  constructor
  · intro r hr _ hm
    have hh := (mem_separate hM hpre hn hr).mp hm
    exact ⟨hh.1,(hrn r hr).mpr hh.2⟩
  · intro r hr _ hh
    exact (mem_separate hM hpre hn hr).mpr ⟨hh.1,(hrn r hr).mp hh.2⟩

/-- Every source Separation instance, in the actual HS interpretation. The
preorder follows from the source algebra contract, not an extra forcing axiom. -/
def sentence {n : Nat} (phi : Formula (n+1)) : Source.Sentence :=
  let rho : Fin 7 → Fin 16 := fun i => ⟨i.val,Nat.lt_trans i.isLt (by decide)⟩
  let R := orderFormula (0 : Fin 16) 13
  let H := domain rho 11 12
  ((ForcingDiagramPoset.leftCancelMonoid (0 : Fin 16) 13 14).imp
    ((ForcingProductFamily.presentation (0 : Fin 16) 7 8 9 10 1 2 3 4 5 6).imp
      ((ForcingLabelPermutations.carrier (7 : Fin 16) 11).imp
        ((ForcingNormalFilter.normal (7 : Fin 16) 11 12).imp
          ((Formula.mem (15 : Fin 16) 6).imp
            (ForcingFormula.formula R H id Fin.elim0 6 15 (Source.SetLanguage.separation phi))))))).close

theorem models {n : Nat} (phi : Formula (n+1)) (hM : FirstOrder.Theory.Models M nativeZF) :
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
  apply (ForcingFormula.formula_semantics (M := M) env R H id Fin.elim0 6 15 (Source.SetLanguage.separation phi)).mpr
  have hz : (fun i : Fin 0 => env (Fin.elim0 i)) = (Fin.elim0 : Fin 0 → M.Carrier .set) :=
    funext (fun i => Fin.elim0 i)
  rw [hz]
  exact forces_separation hM env rho 11 12 13 hp' hG' hF' hpre hc phi

theorem kernel_certificate {n : Nat} (phi : Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (sentence phi)) :=
  ModelTransfer.derives (fun _ hM => models phi hM)

end PPAC.Migration.ForcingSeparationAxiom
