/- Internal adaptation of SymmetricChoice.WitnessIndex/chosenWitness.
Use existing native Collection on the exact valid entry/condition indices.
A set of witnesses suffices for the original bounded_local_witness consumer;
no object choice function or global name-rank cutoff is introduced. -/
import PPAC.Migration.ForcingReplacementOrbit

namespace PPAC.Migration.ForcingReplacementWitness
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
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def RelF {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (v : Fin n → M.Carrier .set) (P p x y : M.Carrier .set) (phi : Formula (n+2)) : Prop :=
  Force R H env (Fin.lastCases y (Fin.lastCases x v)) P p phi

def relF {k n m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (rho : Fin k → Fin m)
    (v : Fin n → Fin m) (P p x y : Fin m) (phi : Formula (n+2)) : Formula m :=
  ForcingFormula.formula R H rho (Fin.lastCases y (Fin.lastCases x v)) P p phi

theorem relF_semantics {k n m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (rho : Fin k → Fin m)
    (v : Fin n → Fin m) (P p x y : Fin m) (phi : Formula (n+2)) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (relF R H rho v P p x y phi) ↔
      RelF R H (fun j => env (rho j)) (fun j => env (v j)) (env P) (env p) (env x) (env y) phi := by
  unfold relF RelF
  rw [ForcingFormula.formula_semantics]
  have he : (fun j => env (Fin.lastCases y (Fin.lastCases x v) j)) =
      Fin.lastCases (env y) (Fin.lastCases (env x) (fun j => env (v j))) := by
    funext j
    refine Fin.lastCases ?_ (fun l => ?_) j
    · simp only [Fin.lastCases_last]
    · refine Fin.lastCases ?_ (fun t => ?_) l <;> simp only [Fin.lastCases_castSucc,Fin.lastCases_last]
  rw [he]

def Local {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (v : Fin n → M.Carrier .set) (P sigma i p eta : M.Carrier .set) (phi : Formula (n+2)) : Prop :=
  (Definitional.Project.FirstOrderSemantics.reduct M).mem i sigma ∧
  (Definitional.Project.FirstOrderSemantics.reduct M).mem p P ∧ Predicate H env eta ∧
  ∃ child c, PureKuratowski.Code M i child c ∧ RelF R H env v P p child eta phi

def localWitness {k n m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (rho : Fin k → Fin m)
    (v : Fin n → Fin m) (P sigma i p eta : Fin m) (phi : Formula (n+2)) : Formula m :=
  (Formula.mem i sigma).conj ((Formula.mem p P).conj ((MinimalPredicates.pred H rho eta).conj
    (.ex (.ex ((PairSyntax.ordered i.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
      (relF R H (paramsUp (paramsUp rho)) (paramsUp (paramsUp v)) P.castSucc.castSucc p.castSucc.castSucc
        (Fin.last m).castSucc eta.castSucc.castSucc phi))))))

theorem localWitness_semantics {k n m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (rho : Fin k → Fin m)
    (v : Fin n → Fin m) (P sigma i p eta : Fin m) (phi : Formula (n+2)) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (localWitness R H rho v P sigma i p eta phi) ↔
      Local R H (fun j => env (rho j)) (fun j => env (v j)) (env P) (env sigma) (env i) (env p) (env eta) phi := by
  simp only [localWitness,Local,Formula.Realize,ForcingClassEvaluation.predicate_semantics (M := M),
    KuratowskiZF.source_code,relF_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def Witness {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (v : Fin n → M.Carrier .set) (P sigma z eta : M.Carrier .set) (phi : Formula (n+2)) : Prop :=
  ∃ i p, PureKuratowski.Code M z i p ∧ Local R H env v P sigma i p eta phi

def witness {k n m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (rho : Fin k → Fin m)
    (v : Fin n → Fin m) (P sigma z eta : Fin m) (phi : Formula (n+2)) : Formula m :=
  .ex (.ex ((PairSyntax.ordered z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    (localWitness R H (paramsUp (paramsUp rho)) (paramsUp (paramsUp v)) P.castSucc.castSucc sigma.castSucc.castSucc
      (Fin.last m).castSucc (Fin.last (m+1)) eta.castSucc.castSucc phi)))

theorem witness_semantics {k n m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (rho : Fin k → Fin m)
    (v : Fin n → Fin m) (P sigma z eta : Fin m) (phi : Formula (n+2)) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (witness R H rho v P sigma z eta phi) ↔
      Witness R H (fun j => env (rho j)) (fun j => env (v j)) (env P) (env sigma) (env z) (env eta) phi := by
  simp only [witness,Witness,Formula.Realize,KuratowskiZF.source_code,localWitness_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- Collection replaces only the source's host choice, preserving every
valid index and its original relation witness. All collected seeds are HS. -/
theorem exists_seeds (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (v : Fin n → Fin k) (P sigma : Fin k) (phi : Formula (n+2)) :
    ∃ W, (∀ eta, (Definitional.Project.FirstOrderSemantics.reduct M).mem eta W → Predicate H env eta) ∧
      ∀ i p, (∃ eta, Local R H env (fun j => env (v j)) (env P) (env sigma) i p eta phi) →
        ∃ eta, (Definitional.Project.FirstOrderSemantics.reduct M).mem eta W ∧
          Local R H env (fun j => env (v j)) (env P) (env sigma) i p eta phi := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  obtain ⟨J,hJ⟩ := ForcingCohenCoordinates.exists_cartesian hM (env sigma) (env P)
  let matrix := witness R H (paramsUp (paramsUp id)) (paramsUp (paramsUp v)) P.castSucc.castSucc
    sigma.castSucc.castSucc (Fin.last k).castSucc (Fin.last (k+1)) phi
  have hm : ∀ z eta, MapRel matrix env z eta ↔
      Witness R H env (fun j => env (v j)) (env P) (env sigma) z eta phi := by
    intro z eta
    simpa only [MapRel,paramsUp,id_eq,Fin.lastCases_last,Fin.lastCases_castSucc] using
      witness_semantics (M := M) (Fin.lastCases eta (Fin.lastCases z env)) R H
        (paramsUp (paramsUp id)) (paramsUp (paramsUp v)) P.castSucc.castSucc sigma.castSucc.castSucc
          (Fin.last k).castSucc (Fin.last (k+1)) phi
  have sep := (GodelDefOutput.separation_semantics E (.ex matrix)).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation (.ex matrix)).semantically_entails M hM))
  obtain ⟨valid,hvalid⟩ := sep env J
  have hv : ∀ z, E z valid ↔ E z J ∧ ∃ eta, Witness R H env (fun j => env (v j)) (env P) (env sigma) z eta phi := by
    intro z
    rw [hvalid z]
    apply and_congr Iff.rfl
    constructor
    · rintro ⟨eta,he⟩
      exact ⟨eta,(hm z eta).mp he⟩
    · rintro ⟨eta,he⟩
      exact ⟨eta,(hm z eta).mpr he⟩
  let penv : SetTheory.Env (Definitional.Project.FirstOrderSemantics.reduct M) k :=
    { bound := fun j => env j.rev, free := fun _ => J }
  have hrel := ForcingMapConditions.binary_semantics hM matrix env J
  obtain ⟨family,hfamily⟩ := SetTheory.ZF.collection_exists_d (ModelTransfer.project_models_iff.mp hM)
    (ProjectSyntax.binary matrix) penv valid (by
      intro z hz
      obtain ⟨eta,he⟩ := ((hv z).mp hz).2
      exact ⟨eta,(hrel z eta).mpr ((hm z eta).mpr he)⟩)
  have filter := (GodelDefOutput.separation_semantics E H).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation H).semantically_entails M hM))
  obtain ⟨W,hW⟩ := filter env family
  refine ⟨W,fun eta he => ((hW eta).mp he).2,?_⟩
  intro i p he
  obtain ⟨eta,hi,hp,hHS,hloc⟩ := he
  obtain ⟨z,hz⟩ := KuratowskiZF.exists_code hM i p
  have hzi := (hv z).mpr ⟨(hJ z).mpr ⟨i,hi,p,hp,hz⟩,eta,i,p,hz,hi,hp,hHS,hloc⟩
  obtain ⟨out,ho,hout⟩ := hfamily z hzi
  obtain ⟨i',p',hcode,hl⟩ := (hm z out).mp ((hrel z out).mp hout)
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hcode
  exact ⟨out,(hW out).mpr ⟨ho,hl.2.2.1⟩,hl⟩


def LocalBound {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (v : Fin n → M.Carrier .set) (P sigma bound : M.Carrier .set) (phi : Formula (n+2)) : Prop :=
  ∀ i p, (∃ eta, Local R H env v P sigma i p eta phi) →
    ∃ eta, Local R H env v P sigma i p eta phi ∧ Forces false R env P eta bound p

/-- Discharge the original replacementBound local-witness contract using
native Collection and exactly the source whole-group orbit argument. -/
theorem exists_bound (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul sigma : Fin k)
    {I K B w : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpre : PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (v : Fin n → Fin k) (phi : Formula (n+2)) :
    ∃ bound, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) bound ∧
      LocalBound (orderFormula (rho 0) mul) (domain rho G F) env (fun j => env (v j)) (env (rho 6)) (env sigma) bound phi := by
  obtain ⟨W,hW,hwit⟩ := exists_seeds hM (orderFormula (rho 0) mul) (domain rho G F) env v (rho 6) sigma phi
  have hseed : ∀ eta, (Definitional.Project.FirstOrderSemantics.reduct M).mem eta W →
      HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) eta :=
    fun eta he => (domain_semantics env rho G F eta).mp (hW eta he)
  obtain ⟨bound,hb,he,_⟩ := ForcingReplacementOrbit.exists_bound hM (fun j => env (rho j)) hp hG hF hseed
  refine ⟨bound,hb,?_⟩
  intro i p hi
  obtain ⟨eta,heta,hloc⟩ := hwit i p hi
  have horbit := ForcingReplacementOrbit.orbit_contains hM (fun j => env (rho j)) hp hG
    (ForcingHS.isName (hseed eta heta)) heta
  have hedge := (he eta p).mpr ⟨hloc.2.1,horbit⟩
  exact ⟨eta,hloc,ForcingAtomicBasic.mem_of_edge_eq hM hpre hloc.2.1 (hpre.1 p hloc.2.1) hedge
    (ForcingAtomicBasic.eq_refl hM hpre eta p hloc.2.1)⟩

/-- Exact consumer of source bounded_local_witness: every valid raw entry
and condition with a local HS witness has one in the constructed bound. -/
theorem bounded_local_witness {k n : Nat} {R : Formula (k+2)} {H : Formula (k+1)}
    {env : Fin k → M.Carrier .set} {v : Fin n → M.Carrier .set} {P sigma bound child c p : M.Carrier .set}
    {phi : Formula (n+2)} (hb : LocalBound R H env v P sigma bound phi)
    (he : PureKuratowski.PairMember M child c sigma)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P)
    (h : ∃ eta, Predicate H env eta ∧ RelF R H env v P p child eta phi) :
    ∃ eta, Predicate H env eta ∧ RelF R H env v P p child eta phi ∧ Forces false R env P eta bound p := by
  obtain ⟨i,hcode,hi⟩ := he
  obtain ⟨eta,heta,hrel⟩ := h
  obtain ⟨out,hloc,hm⟩ := hb i p ⟨eta,hi,hp,heta,child,c,hcode,hrel⟩
  obtain ⟨_,_,hout,child',c',hcode',hrel'⟩ := hloc
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
  exact ⟨out,hout,hrel',hm⟩


/-- Parameter extension does not change the source local-witness relation. -/
theorem local_congr {k l n : Nat} {R : Formula (k+2)} {H : Formula (k+1)}
    {S : Formula (l+2)} {J : Formula (l+1)}
    {env : Fin k → M.Carrier .set} {ext : Fin l → M.Carrier .set}
    (hR : ∀ x y, MapRel R env x y ↔ MapRel S ext x y)
    (hH : ∀ x, Predicate H env x ↔ Predicate J ext x)
    (v : Fin n → M.Carrier .set) (P sigma i p eta : M.Carrier .set) (phi : Formula (n+2)) :
    Local R H env v P sigma i p eta phi ↔ Local S J ext v P sigma i p eta phi := by
  simp only [Local,RelF,← hH,← ForcingSeparation.force_congr hR hH phi]

theorem exists_at_values (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpre : PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (sigma : M.Carrier .set) (v : Fin n → M.Carrier .set) (phi : Formula (n+2)) :
    ∃ bound, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) bound ∧
      LocalBound (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) sigma bound phi := by
  let ext : Fin (k+(n+1)) → M.Carrier .set := Fin.addCases env (Fin.lastCases sigma v)
  let up : Fin k → Fin (k+(n+1)) := Fin.castAdd (n+1)
  let ra := fun j => up (rho j)
  let vv : Fin n → Fin (k+(n+1)) := fun j => Fin.natAdd k j.castSucc
  let ss := Fin.natAdd k (Fin.last n)
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let S := orderFormula (up (rho 0)) (up mul)
  let J := domain ra (up G) (up F)
  have hR : ∀ x y, MapRel R env x y ↔ MapRel S ext x y := by
    intro x y
    simp only [R,S,ForcingProductSymmetry.orderFormula_semantics,ext,up,Fin.addCases_left]
  have hH : ∀ x, Predicate H env x ↔ Predicate J ext x := by
    intro x
    simp only [H,J,domain_semantics,ext,ra,up,Fin.addCases_left]
  have hp' : Presentation (ext (ra 0)) I K B w (ext (ra 1)) (ext (ra 2))
      (ext (ra 3)) (ext (ra 4)) (ext (ra 5)) (ext (ra 6)) := by
    simpa only [ext,ra,up,Fin.addCases_left] using hp
  have hG' : ForcingLabelPermutations.Carrier I (ext (up G)) := by
    simpa only [ext,up,Fin.addCases_left] using hG
  have hF' : ForcingNormalFilter.Normal I (ext (up G)) (ext (up F)) := by
    simpa only [ext,up,Fin.addCases_left] using hF
  have hpre' : PreorderOn S ext (ext (ra 6)) := by
    have hh : PreorderOn S ext (env (rho 6)) := by
      refine ⟨fun p hp => (hR p p).mp (hpre.1 p hp),?_⟩
      intro p q r hp hq hr hpq hqr
      exact (hR p r).mp (hpre.2 p q r hp hq hr ((hR p q).mpr hpq) ((hR q r).mpr hqr))
    simpa only [ext,ra,up,Fin.addCases_left] using hh
  obtain ⟨bound,hb,hw⟩ := exists_bound hM ext ra (up G) (up F) (up mul) ss hp' hG' hF' hpre' vv phi
  refine ⟨bound,?_,?_⟩
  · simpa only [ext,ra,up,Fin.addCases_left] using hb
  · have hh : LocalBound S J ext v (env (rho 6)) sigma bound phi := by
      simpa only [LocalBound,ext,ra,up,vv,ss,Fin.addCases_left,Fin.addCases_right,Fin.lastCases_last,Fin.lastCases_castSucc] using hw
    intro i p hi
    obtain ⟨eta,he⟩ := hi
    obtain ⟨eta',he',hm⟩ := hh i p ⟨eta,(local_congr hR hH v _ _ _ _ _ phi).mp he⟩
    exact ⟨eta',(local_congr hR hH v _ _ _ _ _ phi).mpr he',
      (ForcingSeparation.atomic_congr hR false _ _ _ _).mpr hm⟩

end PPAC.Migration.ForcingReplacementWitness


