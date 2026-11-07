/- Pinned OrderedSections.LeastOccurrence.relation/exists_injection.
Actual checked-index forcing families used by indexedImage and slices. Reuse
relationOf, internal minimum, literal check names and the existing graph collector. -/
import PPAC.Migration.ForcingOrderedSections

namespace PPAC.Migration.ForcingLeastRelation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args2 args3)
open ForcingMapConditions (MapRel)
open ForcingFormula (Force)
open ForcingAtomicRelations (Forces)
open ForcingClassEvaluation (Predicate)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingPairUnion (domain domain_semantics)
open ForcingRelationGraphForcing (Holds)
open ForcingCheckName (Checked)
open ForcingLeastOccurrence (At)
open ForcingRawRank (Ordinal)
open ForcingHS (HS)
open ForcingSupportedNames (Supported)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Finite SOURCE formula parameters, followed by check(i) and the name.
The set of ground indices remains INTERNAL and has no size/rank restriction. -/
def values {k n : Nat} (env : Fin k → M.Carrier .set) (names : Fin n → Fin k)
    (checked x : M.Carrier .set) : Fin (n+2) → M.Carrier .set :=
  Fin.lastCases x (Fin.lastCases checked (fun j => env (names j)))

def Occurrence {k n : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul top : Fin k) (names : Fin n → Fin k) (phi : Formula (n+2))
    (p x i : M.Carrier .set) : Prop :=
  ∃ checked, Checked (env top) i checked ∧
    Force (orderFormula (rho 0) mul) (domain rho G F) env (values env names checked x) (env (rho 6)) p phi

def occurrence {k n : Nat} (rho : Fin 7 → Fin k) (G F mul top : Fin k)
    (names : Fin n → Fin k) (phi : Formula (n+2)) : Formula (k+3) :=
  let up : Fin k → Fin (k+4) := fun j => j.castSucc.castSucc.castSucc.castSucc
  .ex ((ForcingCheckName.checkName (up top) (Fin.last (k+2)).castSucc (Fin.last (k+3))).conj
    (ForcingRelationGraphSupport.relation (ForcingMapCalculus.relationOf rho G F mul names phi) up
      (Fin.last k).castSucc.castSucc.castSucc (Fin.last (k+3)) (Fin.last (k+1)).castSucc.castSucc))

theorem occurrence_semantics {k n : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul top : Fin k) (names : Fin n → Fin k) (phi : Formula (n+2)) (p x i : M.Carrier .set) :
    Holds (occurrence rho G F mul top names phi) env p x i ↔ Occurrence env rho G F mul top names phi p x i := by
  simp only [occurrence,Holds,Formula.Realize,ForcingCheckName.checkName_semantics (M := M),
    ForcingRelationGraphSupport.relation_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  change (∃ checked, Checked (env top) i checked ∧
    Holds (ForcingMapCalculus.relationOf rho G F mul names phi) env p checked x) ↔ _
  simp only [Occurrence,ForcingMapCalculus.relationOf_semantics]
  rfl

theorem occurrence_mono (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top : Fin k)
    (names : Fin n → Fin k) (phi : Formula (n+2))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    {p q x i : M.Carrier .set} (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hq : (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)))
    (hqp : MapRel (orderFormula (rho 0) mul) env q p)
    (h : Occurrence env rho G F mul top names phi p x i) : Occurrence env rho G F mul top names phi q x i := by
  obtain ⟨checked,hChecked,hForce⟩ := h
  exact ⟨checked,hChecked,ForcingFormula.mono hM hpre phi _ hp hq hqp hForce⟩

theorem occurrence_congr (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top : Fin k)
    (names : Fin n → Fin k) (phi : Formula (n+2))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    {p x x' i : M.Carrier .set} (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (he : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) x x' p) :
    Occurrence env rho G F mul top names phi p x i ↔ Occurrence env rho G F mul top names phi p x' i := by
  have step {x x'} (he : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) x x' p)
      (h : Occurrence env rho G F mul top names phi p x i) : Occurrence env rho G F mul top names phi p x' i := by
    obtain ⟨checked,hChecked,hForce⟩ := h
    refine ⟨checked,hChecked,(ForcingFormula.tuple_congr hM hpre phi
      (values env names checked x) (values env names checked x') p hp ?_).mp hForce⟩
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [values,Fin.lastCases_last] using he
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [values,Fin.lastCases_castSucc,Fin.lastCases_last] using
          ForcingAtomicBasic.eq_refl hM hpre checked p hp
      · simpa only [values,Fin.lastCases_castSucc] using
          ForcingAtomicBasic.eq_refl hM hpre (env (names j)) p hp
  exact ⟨step he,step (ForcingAtomicBasic.eq_symm hM he)⟩

theorem occurrence_regular (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top : Fin k)
    (names : Fin n → Fin k) (phi : Formula (n+2))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    {p x i : M.Carrier .set} (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (h : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) → MapRel (orderFormula (rho 0) mul) env q p →
      ∃ r, (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) ∧ MapRel (orderFormula (rho 0) mul) env r q ∧
        Occurrence env rho G F mul top names phi r x i) : Occurrence env rho G F mul top names phi p x i := by
  obtain ⟨checked,hChecked⟩ := ForcingCheckName.exists_checked hM (env top) i
  refine ⟨checked,hChecked,ForcingFormula.of_dense hM hpre phi (values env names checked x) hp ?_⟩
  intro q hq hqp
  obtain ⟨r,hr,hrq,other,hOther,hForce⟩ := h q hq hqp
  have he := ForcingCheckName.unique hM hOther hChecked
  cases he
  exact ⟨r,hr,hrq,hForce⟩

/-- Exact source least-index relation, with actual check witnesses. -/
def Least {k : Nat} (L : Formula (k+2)) (Q : Formula (k+3)) (env : Fin k → M.Carrier .set)
    (P O top p x y : M.Carrier .set) : Prop :=
  ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L env q p → ∃ r,
    (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel L env r q ∧ ∃ i,
      (Project.FirstOrderSemantics.reduct M).mem i O ∧ ∃ checked, Checked top i checked ∧
        Forces true L env P y checked r ∧ At L Q env P O r x i

def relFormula {k m : Nat} (L : Formula (k+2)) (Q : Formula (k+3)) (base : Fin k → Fin m)
    (P O top p x y : Fin m) : Formula m :=
  let up : Fin m → Fin (m+4) := fun j => j.castSucc.castSucc.castSucc.castSucc
  let b : Fin k → Fin (m+4) := fun j => up (base j)
  let q := (Fin.last m).castSucc.castSucc.castSucc
  let r := (Fin.last (m+1)).castSucc.castSucc
  let i := (Fin.last (m+2)).castSucc
  let checked := Fin.last (m+3)
  .all ((Formula.mem (Fin.last m) P.castSucc).imp
    ((ReplacementPredicates.rel L (fun j => (base j).castSucc) (Fin.last m) p.castSucc).imp
      (.ex (.ex (.ex ((Formula.mem r (up P)).conj
        ((ReplacementPredicates.rel L b r q).conj ((Formula.mem i (up O)).conj
          ((ForcingCheckName.checkName (up top) i checked).conj
            ((ForcingAtomicRelations.forces true L b (up P) (up y) checked r).conj
              (ForcingLeastOccurrence.atFormula L Q b (up P) (up O) r (up x) i)))))))))))

theorem relFormula_semantics {k m : Nat} (v : Fin m → M.Carrier .set)
    (L : Formula (k+2)) (Q : Formula (k+3)) (base : Fin k → Fin m) (P O top p x y : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v (relFormula L Q base P O top p x y) ↔
      Least L Q (fun j => v (base j)) (v P) (v O) (v top) (v p) (v x) (v y) := by
  simp only [relFormula,Least,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    ForcingCheckName.checkName_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    ForcingLeastOccurrence.at_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  constructor
  · intro h q hq hqp
    obtain ⟨r,i,checked,hr,hrq,hi,hChecked,hEq,hAt⟩ := h q hq hqp
    exact ⟨r,hr,hrq,i,hi,checked,hChecked,hEq,hAt⟩
  · intro h q hq hqp
    obtain ⟨r,hr,hrq,i,hi,checked,hChecked,hEq,hAt⟩ := h q hq hqp
    exact ⟨r,i,checked,hr,hrq,hi,hChecked,hEq,hAt⟩

def relation {k : Nat} (L : Formula (k+2)) (Q : Formula (k+3)) (P O top : Fin k) : Formula (k+3) :=
  relFormula L Q (fun j => j.castSucc.castSucc.castSucc) P.castSucc.castSucc.castSucc
    O.castSucc.castSucc.castSucc top.castSucc.castSucc.castSucc (Fin.last k).castSucc.castSucc
    (Fin.last (k+1)).castSucc (Fin.last (k+2))

theorem relation_semantics {k : Nat} (env : Fin k → M.Carrier .set)
    (L : Formula (k+2)) (Q : Formula (k+3)) (P O top : Fin k) (p x y : M.Carrier .set) :
    Holds (relation L Q P O top) env p x y ↔ Least L Q env (env P) (env O) (env top) p x y := by
  simp only [relation,Holds,relFormula_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]

theorem rel_mono {k : Nat} {L : Formula (k+2)} {Q : Formula (k+3)} {env : Fin k → M.Carrier .set}
    {P O top p q x y : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn L env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) (hq : (Project.FirstOrderSemantics.reduct M).mem q P)
    (hqp : MapRel L env q p) (h : Least L Q env P O top p x y) : Least L Q env P O top q x y := by
  intro r hr hrq
  exact h r hr (hpre.2 r q p hr hq hp hrq hqp)

theorem rel_regular {k : Nat} {L : Formula (k+2)} {Q : Formula (k+3)} {env : Fin k → M.Carrier .set}
    {P O top p x y : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn L env P)
    (h : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L env q p → ∃ r,
      (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel L env r q ∧ Least L Q env P O top r x y) :
    Least L Q env P O top p x y := by
  intro q hq hqp
  obtain ⟨r,hr,hrq,hRel⟩ := h q hq hqp
  obtain ⟨s,hs,hsr,i,hi,checked,hChecked,hEq,hAt⟩ := hRel r hr (hpre.1 r hr)
  exact ⟨s,hs,hpre.2 s r q hs hr hq hsr hrq,i,hi,checked,hChecked,hEq,hAt⟩

theorem rel_congr (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {L : Formula (k+2)} {Q : Formula (k+3)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P O top p x x' y y' : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn L env P)
    (hCongr : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i O → ∀ p,
      (Project.FirstOrderSemantics.reduct M).mem p P → ∀ x y, Predicate H env x → Predicate H env y →
      Forces true L env P x y p → (Holds Q env p x i ↔ Holds Q env p y i))
    (hx : Predicate H env x) (hx' : Predicate H env x') (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hxx : Forces true L env P x x' p) (hyy : Forces true L env P y y' p) :
    Least L Q env P O top p x y ↔ Least L Q env P O top p x' y' := by
  have step {x x' y y'} (hx : Predicate H env x) (hx' : Predicate H env x')
      (hxx : Forces true L env P x x' p) (hyy : Forces true L env P y y' p)
      (h : Least L Q env P O top p x y) : Least L Q env P O top p x' y' := by
    intro q hq hqp
    obtain ⟨r,hr,hrq,i,hi,checked,hChecked,hEq,hAt⟩ := h q hq hqp
    have hrp := hpre.2 r q p hr hq hp hrq hqp
    exact ⟨r,hr,hrq,i,hi,checked,hChecked,
      ForcingAtomicLaws.eq_trans hM hpre (ForcingAtomicBasic.eq_symm hM
        (ForcingAtomicBasic.eq_mono hM hpre hr hrp hyy)) hEq,
      (ForcingLeastOccurrence.congr hM hpre hCongr hx hx' hr
        (ForcingAtomicBasic.eq_mono hM hpre hr hrp hxx)).mp hAt⟩
  exact ⟨step hx hx' hxx hyy,step hx' hx (ForcingAtomicBasic.eq_symm hM hxx) (ForcingAtomicBasic.eq_symm hM hyy)⟩

def Cover {k : Nat} (L : Formula (k+2)) (Q : Formula (k+3)) (H : Formula (k+1))
    (env : Fin k → M.Carrier .set) (P O Y p : M.Carrier .set) : Prop :=
  ∀ x, Predicate H env x → ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L env q p →
    Forces false L env P x Y q → ForcingLeastOccurrence.Dense false L Q env P O q x

def OneAt {k : Nat} (L : Formula (k+2)) (Q : Formula (k+3)) (H : Formula (k+1))
    (env : Fin k → M.Carrier .set) (P O p : M.Carrier .set) : Prop :=
  ∀ i, (Project.FirstOrderSemantics.reduct M).mem i O → ∀ q,
    (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L env q p → ∀ x y,
      Predicate H env x → Predicate H env y → Holds Q env q x i → Holds Q env q y i → Forces true L env P x y q

/-- Source relation_one: two minimum witnesses have the SAME literal index,
and the actual check names are unique. -/
theorem rel_one (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {L : Formula (k+2)} {Q : Formula (k+3)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P O top p x y z : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn L env P) (hO : Ordinal O)
    (hMono : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i O → ∀ p q,
      (Project.FirstOrderSemantics.reduct M).mem p P → (Project.FirstOrderSemantics.reduct M).mem q P →
      MapRel L env q p → ∀ x, Predicate H env x → Holds Q env p x i → Holds Q env q x i)
    (hx : Predicate H env x) (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hy : Least L Q env P O top p x y) (hz : Least L Q env P O top p x z) : Forces true L env P y z p := by
  apply ForcingAtomicBasic.eq_of_dense hM hpre hp
  intro q hq hqp
  obtain ⟨r,hr,hrq,i,_hi,ci,hci,hEqY,hAtI⟩ := hy q hq hqp
  obtain ⟨s,hs,hsr,j,_hj,cj,hcj,hEqZ,hAtJ⟩ := hz r hr (hpre.2 r q p hr hq hp hrq hqp)
  have hAtI' := ForcingLeastOccurrence.mono hpre hMono hx hr hs hsr hAtI
  have hij := ForcingLeastOccurrence.unique hM hO hpre hs hAtI' hAtJ
  cases hij
  have hc := ForcingCheckName.unique hM hci hcj
  cases hc
  exact ⟨s,hs,hpre.2 s r q hs hr hq hsr hrq,ForcingAtomicLaws.eq_trans hM hpre
    (ForcingAtomicBasic.eq_mono hM hpre hs hsr hEqY) (ForcingAtomicBasic.eq_symm hM hEqZ)⟩

/-- Source relation_inj: equality of the common check-index value reflects
literal index equality; source OneAt then identifies the two names. -/
theorem rel_injective (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {L : Formula (k+2)} {Q : Formula (k+3)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P O top p q x y z : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn L env P)
    (hMono : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i O → ∀ p q,
      (Project.FirstOrderSemantics.reduct M).mem p P → (Project.FirstOrderSemantics.reduct M).mem q P →
      MapRel L env q p → ∀ x, Predicate H env x → Holds Q env p x i → Holds Q env q x i)
    (ht : (Project.FirstOrderSemantics.reduct M).mem top P)
    (hTop : ∀ r, (Project.FirstOrderSemantics.reduct M).mem r P → MapRel L env r top)
    (hOne : OneAt L Q H env P O p) (hx : Predicate H env x) (hy : Predicate H env y)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) (hq : (Project.FirstOrderSemantics.reduct M).mem q P)
    (hqp : MapRel L env q p) (hX : Least L Q env P O top q x z) (hY : Least L Q env P O top q y z) :
    Forces true L env P x y q := by
  apply ForcingAtomicBasic.eq_of_dense hM hpre hq
  intro r hr hrq
  obtain ⟨s,hs,hsr,i,hi,ci,hci,hEqI,hAtI⟩ := hX r hr hrq
  obtain ⟨t,htP,hts,j,_hj,cj,hcj,hEqJ,hAtJ⟩ := hY s hs (hpre.2 s r q hs hr hq hsr hrq)
  have hciEq := ForcingAtomicLaws.eq_trans hM hpre
    (ForcingAtomicBasic.eq_symm hM (ForcingAtomicBasic.eq_mono hM hpre htP hts hEqI)) hEqJ
  have hij := (ForcingCheckReflection.eq_check_iff hM hpre ht hTop htP hci hcj).mp hciEq
  cases hij
  have hAtI' := ForcingLeastOccurrence.mono hpre hMono hx hs htP hts hAtI
  have htr := hpre.2 t s r htP hs hr hts hsr
  exact ⟨t,htP,htr,hOne i hi t htP (hpre.2 t q p htP hq hp
    (hpre.2 t r q htP hr hq htr hrq) hqp) x y hx hy hAtI'.2.1 hAtJ.2.1⟩

/-- Source totality constructs the actual check witness at the least index;
all members of the given check(O) remain available. -/
theorem rel_total (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {L : Formula (k+2)} {Q : Formula (k+3)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P O top Y checkedO p x q r : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn L env P)
    (hMono : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i O → ∀ p q,
      (Project.FirstOrderSemantics.reduct M).mem p P → (Project.FirstOrderSemantics.reduct M).mem q P →
      MapRel L env q p → ∀ x, Predicate H env x → Holds Q env p x i → Holds Q env q x i)
    (hO : Ordinal O) (hCheckedO : Checked top O checkedO)
    (ht : (Project.FirstOrderSemantics.reduct M).mem top P)
    (hTop : ∀ r, (Project.FirstOrderSemantics.reduct M).mem r P → MapRel L env r top)
    (hCheck : ∀ i checked, Checked top i checked → Predicate H env checked)
    (hCover : Cover L Q H env P O Y p) (hx : Predicate H env x)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel L env q p)
    (hMem : Forces false L env P x Y q) (hr : (Project.FirstOrderSemantics.reduct M).mem r P)
    (hrq : MapRel L env r q) : ∃ s, (Project.FirstOrderSemantics.reduct M).mem s P ∧ MapRel L env s r ∧
      ∃ y, Predicate H env y ∧ Forces false L env P y checkedO s ∧ Least L Q env P O top s x y := by
  obtain ⟨s,hs,hsr,i,hAt⟩ := ForcingLeastOccurrence.dense hM L Q env P O q x hO hpre
    (hCover x hx q hq hqp hMem) r hr hrq
  obtain ⟨checked,hChecked⟩ := ForcingCheckName.exists_checked hM top i
  refine ⟨s,hs,hsr,checked,hCheck i checked hChecked,
    ForcingInfinity.check_mem_of_mem hM hpre hCheckedO hChecked hAt.1 ht hTop hs,?_⟩
  intro t htP hts
  refine ⟨t,htP,hpre.1 t htP,i,hAt.1,checked,hChecked,ForcingAtomicBasic.eq_refl hM hpre checked t htP,?_⟩
  exact ForcingLeastOccurrence.mono hpre hMono hx hs htP hts hAt

/-- Covariance is proved from the EXISTING actual formula symmetry, not
assumed as a movement oracle for the least-index relation. -/
theorem occurrence_move (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top : Fin k)
    (names : Fin n → Fin k) (phi : Formula (n+2)) {I K B w pi act p q x x' i : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top)) (hpi : ForcingConditionGraphs.Permutation I pi)
    (hAct : MapRel actionFormula (fun j => env (rho j)) pi act)
    (hFixed : ∀ j, ForcingStabilizer.Action (env (rho 6)) act (env (names j)) (env (names j)))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hpq : PureKuratowski.PairMember M p q act) (hxx : ForcingStabilizer.Action (env (rho 6)) act x x') :
    Occurrence env rho G F mul top names phi p x i ↔ Occurrence env rho G F mul top names phi q x' i := by
  have hPhi (checked : M.Carrier .set) (hc : Checked (env top) i checked) :
      Force (orderFormula (rho 0) mul) (domain rho G F) env (values env names checked x) (env (rho 6)) p phi ↔
      Force (orderFormula (rho 0) mul) (domain rho G F) env (values env names checked x') (env (rho 6)) q phi := by
    have hCI := ForcingLabelNames.checked_fixed hM (fun j => env (rho j)) hPres ht
      ((mapRel_action _ _ _).mp hAct) hc
    apply ForcingSeparation.symmetry hM env rho G F mul hPres hG hF hpi hAct phi
      (values env names checked x) (values env names checked x') ?_ hp hpq
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [values,Fin.lastCases_last] using hxx
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [values,Fin.lastCases_castSucc,Fin.lastCases_last] using hCI
      · simpa only [values,Fin.lastCases_castSucc] using hFixed j
  exact ⟨fun ⟨checked,hc,h⟩ => ⟨checked,hc,(hPhi checked hc).mp h⟩,
    fun ⟨checked,hc,h⟩ => ⟨checked,hc,(hPhi checked hc).mpr h⟩⟩

theorem at_move (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top O : Fin k)
    (names : Fin n → Fin k) (phi : Formula (n+2)) {I K B w pi act p q x x' i : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top)) (hpi : ForcingConditionGraphs.Permutation I pi)
    (hAct : MapRel actionFormula (fun j => env (rho j)) pi act)
    (hFixed : ∀ j, ForcingStabilizer.Action (env (rho 6)) act (env (names j)) (env (names j)))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hpq : PureKuratowski.PairMember M p q act) (hxx : ForcingStabilizer.Action (env (rho 6)) act x x')
    (h : At (orderFormula (rho 0) mul) (occurrence rho G F mul top names phi) env
      (env (rho 6)) (env O) p x i) :
    At (orderFormula (rho 0) mul) (occurrence rho G F mul top names phi) env (env (rho 6)) (env O) q x' i := by
  have ha := (mapRel_action (fun j => env (rho j)) pi act).mp hAct
  have hPerm := ForcingProductFamily.action_permutation ha
  have hOrder := ForcingProductFamily.order hM (env mul) hPres hpi ha
  refine ⟨h.1,(occurrence_semantics env rho G F mul top names phi q x' i).mpr
    ((occurrence_move hM env rho G F mul top names phi hPres hG hF ht hpi hAct hFixed hp hpq hxx).mp
      ((occurrence_semantics env rho G F mul top names phi p x i).mp h.2.1)),?_⟩
  intro j hj hji r hr hrq hRj
  obtain ⟨r0,hr0,hr0r⟩ := hPerm.2.2 r hr
  have hr0p := (orderFormula_semantics env (rho 0) mul r0 p).mpr
    ((hOrder r0 p r q hr0r hpq).mpr ((orderFormula_semantics env (rho 0) mul r q).mp hrq))
  apply h.2.2 j hj hji r0 hr0 hr0p
  apply (occurrence_semantics env rho G F mul top names phi r0 x j).mpr
  apply (occurrence_move hM env rho G F mul top names phi hPres hG hF ht hpi hAct hFixed hr0 hr0r hxx).mpr
  exact (occurrence_semantics env rho G F mul top names phi r x' j).mp hRj

/-- Exact source relation_move: pull a condition back through the ACTUAL
permutation, choose an existing dense witness, then move it forward. -/
theorem rel_move (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top O : Fin k)
    (names : Fin n → Fin k) (phi : Formula (n+2)) {I K B w pi act p q x x' y y' : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top)) (hpi : ForcingConditionGraphs.Permutation I pi)
    (hAct : MapRel actionFormula (fun j => env (rho j)) pi act)
    (hFixed : ∀ j, ForcingStabilizer.Action (env (rho 6)) act (env (names j)) (env (names j)))
    (_hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hpq : PureKuratowski.PairMember M p q act) (hxx : ForcingStabilizer.Action (env (rho 6)) act x x')
    (hyy : ForcingStabilizer.Action (env (rho 6)) act y y')
    (h : Least (orderFormula (rho 0) mul) (occurrence rho G F mul top names phi) env
      (env (rho 6)) (env O) (env top) p x y) :
    Least (orderFormula (rho 0) mul) (occurrence rho G F mul top names phi) env
      (env (rho 6)) (env O) (env top) q x' y' := by
  have ha := (mapRel_action (fun j => env (rho j)) pi act).mp hAct
  have hPerm := ForcingProductFamily.action_permutation ha
  have hOrder := ForcingProductFamily.order hM (env mul) hPres hpi ha
  intro t htP htq
  obtain ⟨t0,ht0,ht0t⟩ := hPerm.2.2 t htP
  have ht0p := (orderFormula_semantics env (rho 0) mul t0 p).mpr
    ((hOrder t0 p t q ht0t hpq).mpr ((orderFormula_semantics env (rho 0) mul t q).mp htq))
  obtain ⟨r,hr,hrt0,i,hi,checked,hChecked,hEq,hAt⟩ := h t0 ht0 ht0p
  obtain ⟨r',hrr',_⟩ := hPerm.1.1.2 r hr
  have hr' := hPerm.1.2 r r' hrr'
  have hr't := (orderFormula_semantics env (rho 0) mul r' t).mpr
    ((hOrder r t0 r' t hrr' ht0t).mp ((orderFormula_semantics env (rho 0) mul r t0).mp hrt0))
  have hCI := ForcingLabelNames.checked_fixed hM (fun j => env (rho j)) hPres ht ha hChecked
  have hEq' := (ForcingSeparation.symmetry hM env rho G F mul hPres hG hF hpi hAct (.equal (0 : Fin 2) 1)
    (args2 y checked) (args2 y' checked)
    (fun j => Fin.cases hyy (Fin.cases hCI (fun a => Fin.elim0 a)) j) hr hrr').mp hEq
  exact ⟨r',hr',hr't,i,hi,checked,hChecked,hEq',
    at_move hM env rho G F mul top O names phi hPres hG hF ht hpi hAct hFixed hr hrr' hxx hAt⟩

/-- Construct the ACTUAL collected least-index graph and prove the FULL
source injection. Coverage, per-index uniqueness, parameter support and the
actual check(O) are the original source inputs; no graph/laws/movement is given. -/
theorem construct (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F S mul top O Y checkedO p : Fin k) (names : Fin n → Fin k) (phi : Formula (n+2))
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hS : ForcingConjugationGraph.Subgroup (env I) (env G) (env S))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem (env S) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hO : Ordinal (env O)) (hCheckedO : Checked (env top) (env O) (env checkedO))
    (hY : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Y))
    (hFixY : Supported (fun j => env (rho j)) (env S) (env Y))
    (hParams : ∀ j, Supported (fun j => env (rho j)) (env S) (env (names j)))
    (hCover : Cover (orderFormula (rho 0) mul) (occurrence rho G F mul top names phi) (domain rho G F)
      env (env (rho 6)) (env O) (env Y) (env p))
    (hOne : OneAt (orderFormula (rho 0) mul) (occurrence rho G F mul top names phi) (domain rho G F)
      env (env (rho 6)) (env O) (env p))
    (hp : (Project.FirstOrderSemantics.reduct M).mem (env p) (env (rho 6))) :
    ∃ graph, ForcingRelationGraph.Graph (orderFormula (rho 0) mul)
      (relation (orderFormula (rho 0) mul) (occurrence rho G F mul top names phi) (rho 6) O top)
        env (rho 6) top Y checkedO graph ∧
      HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) graph ∧
      Supported (fun j => env (rho j)) (env S) graph ∧
      Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph (env Y) (env checkedO))
        (env (rho 6)) (env p) (Source.SetLanguage.injection 0 1 2) := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  let occ := occurrence rho G F mul top names phi
  let Q := relation R occ (rho 6) O top
  let v7 : Fin 7 → M.Carrier .set := fun j => env (rho j)
  have htW := (hPres.2.2.2.2.2 (env top)).mpr (Or.inl ht)
  have hTop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q W → MapRel R env q (env top) :=
    fun q _ => (orderFormula_semantics env (rho 0) mul q (env top)).mpr (Or.inl ht)
  have hCheck : ∀ i checked, Checked (env top) i checked → Predicate H env checked := by
    intro i checked hc
    apply (domain_semantics env rho G F checked).mpr
    apply ForcingHSCheck.check_hs hM actionFormula v7 (env G) W (env F) (env top) hF.1 htW ?_ i checked hc
    intro pi hpi
    obtain ⟨act,ha⟩ := ForcingProductFamily.exists_action hM hPres ((hG pi).mp hpi)
    exact ⟨act,(mapRel_action v7 pi act).mpr ha,(ForcingProductFamily.action_permutation ha).1,
      Or.inl ⟨htW,ForcingProductFamily.top_fixed hPres ht ha⟩⟩
  have hCO := (domain_semantics env rho G F (env checkedO)).mp (hCheck (env O) (env checkedO) hCheckedO)
  have hFixCO : Supported v7 (env S) (env checkedO) := by
    intro pi _hpi act hAct
    exact ForcingLabelNames.checked_fixed hM v7 hPres ht ((mapRel_action v7 pi act).mp hAct) hCheckedO
  have hMove : ForcingRelationGraphSupport.Moves Q env rho G F S := by
    intro pi hpi act hAct a b x y x' y' ha hab _hx _hy hxx hyy hRel
    apply (relation_semantics env R occ (rho 6) O top b x' y').mpr
    exact rel_move hM env rho G F mul top O names phi hPres hG hF ht
      ((hG pi).mp (hS.1 pi hpi)) hAct (fun j => hParams j pi hpi act hAct) ha hab hxx hyy
      ((relation_semantics env R occ (rho 6) O top a x y).mp hRel)
  obtain ⟨graph,hGraph,hGraphHS,hFixed⟩ := ForcingRelationGraphSupport.construct hM Q env rho
    I K B w G F S mul top Y checkedO hPres hG hF hS ht hY hCO hFixY hFixCO hMove hSF
  have hOMono : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i (env O) → ∀ a b,
      (Project.FirstOrderSemantics.reduct M).mem a W → (Project.FirstOrderSemantics.reduct M).mem b W →
      MapRel R env b a → ∀ x, Predicate H env x → Holds occ env a x i → Holds occ env b x i := by
    intro i _hi a b ha hb hba x _hx hh
    exact (occurrence_semantics env rho G F mul top names phi b x i).mpr
      (occurrence_mono hM env rho G F mul top names phi hpre ha hb hba
        ((occurrence_semantics env rho G F mul top names phi a x i).mp hh))
  have hOCongr : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i (env O) → ∀ a,
      (Project.FirstOrderSemantics.reduct M).mem a W → ∀ x y, Predicate H env x → Predicate H env y →
      Forces true R env W x y a → (Holds occ env a x i ↔ Holds occ env a y i) := by
    intro i _hi a ha x y _hx _hy he
    rw [occurrence_semantics,occurrence_semantics]
    exact occurrence_congr hM env rho G F mul top names phi hpre ha he
  have hDomain (x : M.Carrier .set)
      (hx : HS (ForcingRelationGraphApplication.actionAt rho) env (env G) W (env F) x) : Predicate H env x :=
    (domain_semantics env rho G F x).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hx)
  have hMono : ForcingRelationGraphForcing.Monotone R (ForcingRelationGraphApplication.actionAt rho) Q env W (env G) (env F) := by
    intro a b x y ha hb hba _hx _hy hRel
    exact (relation_semantics env R occ (rho 6) O top b x y).mpr
      (rel_mono hpre ha hb hba ((relation_semantics env R occ (rho 6) O top a x y).mp hRel))
  have hCongr : ForcingRelationGraphForcing.Congruent R (ForcingRelationGraphApplication.actionAt rho) Q env W (env G) (env F) := by
    intro a x y x' y' hx _hy hx' _hy' hxx hyy
    have ha := ForcingAtomicBasic.condition hM hxx
    rw [relation_semantics,relation_semantics]
    exact rel_congr hM hpre hOCongr (hDomain x hx) (hDomain x' hx') ha hxx hyy
  have hRegular : ForcingRelationGraphForcing.Regular R (ForcingRelationGraphApplication.actionAt rho) Q env W (env G) (env F) := by
    intro a x y _ha _hx _hy hDense
    apply (relation_semantics env R occ (rho 6) O top a x y).mpr
    apply rel_regular hpre
    intro b hb hba
    obtain ⟨c,hc,hcb,hRel⟩ := hDense b hb hba
    exact ⟨c,hc,hcb,(relation_semantics env R occ (rho 6) O top c x y).mp hRel⟩
  refine ⟨graph,hGraph,hGraphHS,hFixed,?_⟩
  apply ForcingRelationGraphFunctions.graph_injection hM env rho G F mul top Y checkedO Q
    (args3 graph (env Y) (env checkedO)) 0 1 2 hPres hG hF ht hpre hY hCO hMono hCongr hRegular
    hGraph rfl rfl ?_ ?_ ?_ hp
  · intro x hx q hq hqp hMY r hr hrq
    obtain ⟨s,hs,hsr,y,hy,hMem,hRel⟩ := rel_total hM hpre hOMono hO hCheckedO htW hTop hCheck
      hCover (hDomain x hx) hq hqp hMY hr hrq
    exact ⟨s,hs,hsr,y,(ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mpr
      ((domain_semantics env rho G F y).mp hy),hMem,(relation_semantics env R occ (rho 6) O top s x y).mpr hRel⟩
  · intro q hq _hqp x y z hx _hy _hz hXY hXZ
    exact rel_one hM hpre hO hOMono (hDomain x hx) hq
      ((relation_semantics env R occ (rho 6) O top q x y).mp hXY)
      ((relation_semantics env R occ (rho 6) O top q x z).mp hXZ)
  · intro q hq hqp x y z hx hy _hz hXZ hYZ
    exact rel_injective hM hpre hOMono htW hTop hOne (hDomain x hx) (hDomain y hy) hp hq hqp
      ((relation_semantics env R occ (rho 6) O top q x z).mp hXZ)
      ((relation_semantics env R occ (rho 6) O top q y z).mp hYZ)

def covering {k m : Nat} (L : Formula (k+2)) (Q : Formula (k+3)) (H : Formula (k+1))
    (base : Fin k → Fin m) (P O Y p : Fin m) : Formula m :=
  .all ((MinimalPredicates.pred H (fun j => (base j).castSucc) (Fin.last m)).imp (.all
    ((Formula.mem (Fin.last (m+1)) P.castSucc.castSucc).imp
      ((ReplacementPredicates.rel L (fun j => (base j).castSucc.castSucc) (Fin.last (m+1)) p.castSucc.castSucc).imp
        ((ForcingAtomicRelations.forces false L (fun j => (base j).castSucc.castSucc) P.castSucc.castSucc
          (Fin.last m).castSucc Y.castSucc.castSucc (Fin.last (m+1))).imp
            (ForcingLeastOccurrence.densely false L Q (fun j => (base j).castSucc.castSucc)
              P.castSucc.castSucc O.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc))))))

theorem covering_semantics {k m : Nat} (v : Fin m → M.Carrier .set) (L : Formula (k+2))
    (Q : Formula (k+3)) (H : Formula (k+1)) (base : Fin k → Fin m) (P O Y p : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v (covering L Q H base P O Y p) ↔
      Cover L Q H (fun j => v (base j)) (v P) (v O) (v Y) (v p) := by
  simp only [covering,Cover,Formula.Realize,ForcingClassEvaluation.predicate_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    ForcingLeastOccurrence.densely_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def oneAtFormula {k m : Nat} (L : Formula (k+2)) (Q : Formula (k+3)) (H : Formula (k+1))
    (base : Fin k → Fin m) (P O p : Fin m) : Formula m :=
  let up : Fin m → Fin (m+4) := fun j => j.castSucc.castSucc.castSucc.castSucc
  let b : Fin k → Fin (m+4) := fun j => up (base j)
  let i := (Fin.last m).castSucc.castSucc.castSucc
  let q := (Fin.last (m+1)).castSucc.castSucc
  let x := (Fin.last (m+2)).castSucc
  let y := Fin.last (m+3)
  .all ((Formula.mem (Fin.last m) O.castSucc).imp (.all
    ((Formula.mem (Fin.last (m+1)) P.castSucc.castSucc).imp
      ((ReplacementPredicates.rel L (fun j => (base j).castSucc.castSucc) (Fin.last (m+1)) p.castSucc.castSucc).imp
        (.all ((MinimalPredicates.pred H (fun j => (base j).castSucc.castSucc.castSucc) (Fin.last (m+2))).imp
          (.all ((MinimalPredicates.pred H b y).imp
            ((ForcingRelationGraphSupport.relation Q b q x i).imp
              ((ForcingRelationGraphSupport.relation Q b q y i).imp
                (ForcingAtomicRelations.forces true L b (up P) x y q)))))))))))

theorem oneAtFormula_semantics {k m : Nat} (v : Fin m → M.Carrier .set) (L : Formula (k+2))
    (Q : Formula (k+3)) (H : Formula (k+1)) (base : Fin k → Fin m) (P O p : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v (oneAtFormula L Q H base P O p) ↔
      OneAt L Q H (fun j => v (base j)) (v P) (v O) (v p) := by
  simp only [oneAtFormula,OneAt,Formula.Realize,ForcingClassEvaluation.predicate_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M),ForcingRelationGraphSupport.relation_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  constructor
  · intro h i hi q hq hqp x y hx hy hxi hyi
    exact h i hi q hq hqp x hx y hy hxi hyi
  · intro h i hi q hq hqp x hx y hy hxi hyi
    exact h i hi q hq hqp x y hx hy hxi hyi

def fixedParams {k n : Nat} (rho : Fin 7 → Fin k) (S : Fin k) (names : Fin n → Fin k) : Formula k :=
  ForcingSound.conjunction ((List.finRange n).map (fun j => ForcingEquivariantMix.fixedAll rho S (names j)))

theorem fixedParams_semantics {k n : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (S : Fin k) (names : Fin n → Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (fixedParams rho S names) ↔
      ∀ j, Supported (fun a => env (rho a)) (env S) (env (names j)) := by
  simp only [fixedParams,ForcingTupleStabilizer.finite_conjunction,ForcingEquivariantMix.fixedAll_semantics,Supported]

/-- Actual graph existence with all source functionOn/no-junk/injectivity
clauses. The check(O) is the original already-constructed check-name input. -/
def Built {k n : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F S mul top O Y checkedO p : Fin k) (names : Fin n → Fin k) (phi : Formula (n+2)) : Prop :=
  ∃ graph, ForcingRelationGraph.Graph (orderFormula (rho 0) mul)
    (relation (orderFormula (rho 0) mul) (occurrence rho G F mul top names phi) (rho 6) O top)
      env (rho 6) top Y checkedO graph ∧
    HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) graph ∧
    Supported (fun j => env (rho j)) (env S) graph ∧
    Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph (env Y) (env checkedO))
      (env (rho 6)) (env p) (Source.SetLanguage.injection 0 1 2)

def construction {k n : Nat} (rho : Fin 7 → Fin k) (G F S mul top O Y checkedO p : Fin k)
    (names : Fin n → Fin k) (phi : Formula (n+2)) : Formula k :=
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let Q := relation R (occurrence rho G F mul top names phi) (rho 6) O top
  let up : Fin k → Fin (k+1) := Fin.castSucc
  let rr : Fin 7 → Fin (k+1) := fun j => up (rho j)
  let graph := Fin.last k
  .ex ((ForcingRelationGraph.graph R Q up (rho 6) top Y checkedO graph).conj
    ((ForcingHS.hs actionFormula rr (up G) (up (rho 6)) (up F) graph).conj
      ((ForcingEquivariantMix.fixedAll rr (up S) graph).conj
        (ForcingFormula.formula R H up (args3 graph (up Y) (up checkedO)) (up (rho 6)) (up p)
          (Source.SetLanguage.injection 0 1 2)))))

theorem construction_semantics {k n : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F S mul top O Y checkedO p : Fin k) (names : Fin n → Fin k) (phi : Formula (n+2)) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (construction rho G F S mul top O Y checkedO p names phi) ↔
      Built env rho G F S mul top O Y checkedO p names phi := by
  simp only [construction,Built,Formula.Realize,ForcingRelationGraph.graph_semantics (M := M),
    ForcingHS.hs_semantics (M := M),ForcingEquivariantMix.fixedAll_semantics,ForcingFormula.formula_semantics,
    Supported,Fin.lastCases_last,Fin.lastCases_castSucc]
  have hV (graph : M.Carrier .set) :
      (fun j => Fin.lastCases graph env (args3 (Fin.last k) Y.castSucc checkedO.castSucc j)) =
        args3 graph (env Y) (env checkedO) := by
    funext j
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))) j
    · change Fin.lastCases graph env (Fin.last k) = graph
      rw [Fin.lastCases_last]
    · change Fin.lastCases graph env Y.castSucc = env Y
      rw [Fin.lastCases_castSucc]
    · change Fin.lastCases graph env checkedO.castSucc = env checkedO
      rw [Fin.lastCases_castSucc]
  constructor
  · rintro ⟨graph,hGraph,hHS,hFix,hForce⟩
    rw [hV] at hForce
    exact ⟨graph,hGraph,hHS,hFix,hForce⟩
  · rintro ⟨graph,hGraph,hHS,hFix,hForce⟩
    refine ⟨graph,hGraph,hHS,hFix,?_⟩
    rw [hV]
    exact hForce

def sentence {k n : Nat} (rho : Fin 7 → Fin k) (I K B w G F S mul top O Y checkedO p : Fin k)
    (names : Fin n → Fin k) (phi : Formula (n+2)) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ([ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
      ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
      ProjectSyntax.encode id (ForcingNormalFilter.normal I G F),
      ProjectSyntax.encode id (ForcingConjugationGraph.subgroup I G S),
      .mem (.bound S) (.bound F),
      ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
      ProjectSyntax.encode id (ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)),
      ProjectSyntax.encode id (OrdinalSyntax.ordinal O),
      ProjectSyntax.encode id (ForcingCheckName.checkName top O checkedO),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F Y),
      ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho S Y),
      ProjectSyntax.encode id (fixedParams rho S names),
      ProjectSyntax.encode id (covering (orderFormula (rho 0) mul) (occurrence rho G F mul top names phi)
        (domain rho G F) id (rho 6) O Y p),
      ProjectSyntax.encode id (oneAtFormula (orderFormula (rho 0) mul) (occurrence rho G F mul top names phi)
        (domain rho G F) id (rho 6) O p),
      .mem (.bound p) (.bound (rho 6))].foldr Definitional.Formula.imp
        (ProjectSyntax.encode id (construction rho G F S mul top O Y checkedO p names phi)))
  freeClosed := by
    simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem models {k n : Nat} (rho : Fin 7 → Fin k) (I K B w G F S mul top O Y checkedO p : Fin k)
    (names : Fin n → Fin k) (phi : Formula (n+2)) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sentence rho I K B w G F S mul top O Y checkedO p names phi)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductFamily.presentation_semantics,
    ForcingLabelPermutations.carrier_semantics,ForcingNormalFilter.normal_semantics,ForcingConjugationGraph.subgroup_semantics,
    ForcingWithTopCarrier.empty_semantics,ForcingAtomicBasic.preorder_semantics,ForcingRawRank.ordinal_semantics,
    ForcingCheckName.checkName_semantics,ForcingHS.hs_semantics,ForcingEquivariantMix.fixedAll_semantics,
    fixedParams_semantics,covering_semantics,oneAtFormula_semantics,construction_semantics,id_eq]
  exact construct hM env rho I K B w G F S mul top O Y checkedO p names phi

theorem kernel_certificate {k n : Nat} (rho : Fin 7 → Fin k) (I K B w G F S mul top O Y checkedO p : Fin k)
    (names : Fin n → Fin k) (phi : Formula (n+2)) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (sentence rho I K B w G F S mul top O Y checkedO p names phi)) :=
  ModelTransfer.derives (fun _ hM => models rho I K B w G F S mul top O Y checkedO p names phi hM)

end PPAC.Migration.ForcingLeastRelation
