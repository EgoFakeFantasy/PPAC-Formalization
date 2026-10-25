/- Pinned ForcingQuotient.BasicFormula / Formula.toBasic / AtomicData.Force,
and ForcingTruth.force_of_dense. Only the direct soundness dependency slice is
ported: no quotient, generic filter, decision family or maximum principle.
Each fixed source formula compiles to a pure object formula. The name domain
is an arbitrary parameter formula H, later instantiated by the actual HS class. -/
import PPAC.Migration.ForcingAtomicLaws
import PPAC.Migration.ForcingClassEvaluation

namespace PPAC.Migration.ForcingFormula
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingAtomicRelations (Forces forces)
open ForcingAtomicBasic (PreorderOn)
open ForcingMapConditions (MapRel)
open ForcingClassEvaluation (Predicate)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Literal six-constructor source basis; Countable is irrelevant to direct soundness. -/
inductive Basic : Nat → Type where
  | bot {n} : Basic n
  | mem {n} (x y : Fin n) : Basic n
  | equal {n} (x y : Fin n) : Basic n
  | conj {n} (p q : Basic n) : Basic n
  | neg {n} (p : Basic n) : Basic n
  | ex {n} (p : Basic (n+1)) : Basic n

def toBasic {n : Nat} : Formula n → Basic n
  | .bot => .bot
  | .mem x y => .mem x y
  | .equal x y => .equal x y
  | .imp p q => .neg (.conj (toBasic p) (.neg (toBasic q)))
  | .conj p q => .conj (toBasic p) (toBasic q)
  | .disj p q => .neg (.conj (.neg (toBasic p)) (.neg (toBasic q)))
  | .all p => .neg (.ex (.neg (toBasic p)))
  | .ex p => .ex (toBasic p)

def basic {k n m : Nat} (R : Formula (k+2)) (H : Formula (k+1))
    (rho : Fin k → Fin m) (v : Fin n → Fin m) (P p : Fin m) : Basic n → Formula m
  | .bot => .bot
  | .mem x y => forces false R rho P (v x) (v y) p
  | .equal x y => forces true R rho P (v x) (v y) p
  | .conj a b => (basic R H rho v P p a).conj (basic R H rho v P p b)
  | .neg a => .all ((Formula.mem (Fin.last m) P.castSucc).imp
      ((ReplacementPredicates.rel R (paramsUp rho) (Fin.last m) p.castSucc).imp
        (basic R H (paramsUp rho) (fun i => (v i).castSucc) P.castSucc (Fin.last m) a).neg))
  | .ex a =>
    let up : Fin m → Fin (m+3) := fun i => i.castSucc.castSucc.castSucc
    .all ((Formula.mem (Fin.last m) P.castSucc).imp
      ((ReplacementPredicates.rel R (paramsUp rho) (Fin.last m) p.castSucc).imp
        (.ex ((Formula.mem (Fin.last (m+1)) P.castSucc.castSucc).conj
          ((ReplacementPredicates.rel R (paramsUp (paramsUp rho)) (Fin.last (m+1)) (Fin.last m).castSucc).conj
            (.ex ((MinimalPredicates.pred H (fun i => up (rho i)) (Fin.last (m+2))).conj
              (basic R H (fun i => up (rho i)) (Fin.lastCases (Fin.last (m+2)) (fun i => up (v i)))
                (up P) (Fin.last (m+1)).castSucc a))))))))

def BasicForce {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1))
    (params : Fin k → M.Carrier .set) (v : Fin n → M.Carrier .set) (P p : M.Carrier .set) : Basic n → Prop
  | .bot => False
  | .mem x y => Forces false R params P (v x) (v y) p
  | .equal x y => Forces true R params P (v x) (v y) p
  | .conj a b => BasicForce R H params v P p a ∧ BasicForce R H params v P p b
  | .neg a => ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R params q p →
      ¬BasicForce R H params v P q a
  | .ex a => ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R params q p →
      ∃ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R params r q ∧
        ∃ x, Predicate H params x ∧ BasicForce R H params (Fin.lastCases x v) P r a

theorem basic_semantics {k n m : Nat} (env : Fin m → M.Carrier .set) (R : Formula (k+2)) (H : Formula (k+1))
    (rho : Fin k → Fin m) (v : Fin n → Fin m) (P p : Fin m) (phi : Basic n) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (basic R H rho v P p phi) ↔
      BasicForce R H (fun i => env (rho i)) (fun i => env (v i)) (env P) (env p) phi := by
  induction phi generalizing m with
  | bot => rfl
  | mem x y => exact ForcingAtomicRelations.forces_semantics env false R rho P (v x) (v y) p
  | equal x y => exact ForcingAtomicRelations.forces_semantics env true R rho P (v x) (v y) p
  | conj a b ia ib => exact and_congr (ia env rho v P p) (ib env rho v P p)
  | neg a ia =>
    simp only [basic,BasicForce,Source.Formula.neg,Formula.Realize,
      ForcingMapConditions.rel_semantics (M := M),ia,paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  | ex a ia =>
    simp only [basic,BasicForce,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
      ForcingClassEvaluation.predicate_semantics (M := M),ia,paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
    have he : ∀ x q r, (fun i => Fin.lastCases x (Fin.lastCases r (Fin.lastCases q env))
        (Fin.lastCases (Fin.last (m+2)) (fun j => (v j).castSucc.castSucc.castSucc) i)) =
        Fin.lastCases x (fun i => env (v i)) := by
      intro x q r
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [Fin.lastCases_last,Fin.lastCases_castSucc]
    simp only [he]
    rfl

def formula {k n m : Nat} (R : Formula (k+2)) (H : Formula (k+1))
    (rho : Fin k → Fin m) (v : Fin n → Fin m) (P p : Fin m) (phi : Formula n) : Formula m :=
  basic R H rho v P p (toBasic phi)

def Force {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (params : Fin k → M.Carrier .set)
    (v : Fin n → M.Carrier .set) (P p : M.Carrier .set) (phi : Formula n) : Prop :=
  BasicForce R H params v P p (toBasic phi)

theorem formula_semantics {k n m : Nat} (env : Fin m → M.Carrier .set) (R : Formula (k+2)) (H : Formula (k+1))
    (rho : Fin k → Fin m) (v : Fin n → Fin m) (P p : Fin m) (phi : Formula n) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (formula R H rho v P p phi) ↔
      Force R H (fun i => env (rho i)) (fun i => env (v i)) (env P) (env p) phi :=
  basic_semantics env R H rho v P p (toBasic phi)

theorem basic_mono (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {params : Fin k → M.Carrier .set}
    {P p q : M.Carrier .set}
    (hpre : PreorderOn R params P) (phi : Basic n) (v : Fin n → M.Carrier .set)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P)
    (hq : (Definitional.Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel R params q p)
    (h : BasicForce R H params v P p phi) : BasicForce R H params v P q phi := by
  induction phi with
  | bot => exact h
  | mem => exact ForcingAtomicBasic.mem_mono hM hpre hq hqp h
  | equal => exact ForcingAtomicBasic.eq_mono hM hpre hq hqp h
  | conj a b ia ib => exact ⟨ia v h.1,ib v h.2⟩
  | neg a _ => exact fun r hr hrq => h r hr (hpre.2 r q p hr hq hp hrq hqp)
  | ex a _ => exact fun r hr hrq => h r hr (hpre.2 r q p hr hq hp hrq hqp)

theorem basic_of_dense (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {params : Fin k → M.Carrier .set} {P : M.Carrier .set}
    (hpre : PreorderOn R params P) (phi : Basic n) (v : Fin n → M.Carrier .set) (p : M.Carrier .set)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P)
    (h : ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R params q p →
      ∃ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R params r q ∧ BasicForce R H params v P r phi) :
    BasicForce R H params v P p phi := by
  induction phi generalizing p with
  | bot => obtain ⟨_,_,_,hr⟩ := h p hp (hpre.1 p hp); exact hr
  | mem => exact ForcingAtomicBasic.mem_of_dense hM hpre hp h
  | equal => exact ForcingAtomicBasic.eq_of_dense hM hpre hp h
  | conj a b ia ib =>
    constructor
    · apply ia v p hp
      intro q hq hqp
      obtain ⟨r,hr,hrq,ha,hb⟩ := h q hq hqp
      exact ⟨r,hr,hrq,ha⟩
    · apply ib v p hp
      intro q hq hqp
      obtain ⟨r,hr,hrq,ha,hb⟩ := h q hq hqp
      exact ⟨r,hr,hrq,hb⟩
  | neg a _ =>
    intro q hq hqp hqa
    obtain ⟨r,hr,hrq,hra⟩ := h q hq hqp
    exact hra r hr (hpre.1 r hr) (basic_mono hM hpre a v hq hr hrq hqa)
  | ex a _ =>
    intro q hq hqp
    obtain ⟨r,hr,hrq,hra⟩ := h q hq hqp
    obtain ⟨s,hs,hsr,hx⟩ := hra r hr (hpre.1 r hr)
    exact ⟨s,hs,hpre.2 s r q hs hr hq hsr hrq,hx⟩

theorem exists_basic_neg (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {params : Fin k → M.Carrier .set} {P p : M.Carrier .set}
    (hpre : PreorderOn R params P) (phi : Basic n) (v : Fin n → M.Carrier .set)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P) (hn : ¬BasicForce R H params v P p phi) :
    ∃ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P ∧ MapRel R params q p ∧ BasicForce R H params v P q (.neg phi) := by
  apply Classical.byContradiction
  intro h
  apply hn
  apply basic_of_dense hM hpre phi v p hp
  intro q hq hqp
  apply Classical.byContradiction
  intro hnot
  exact h ⟨q,hq,hqp,fun r hr hrq hphi => hnot ⟨r,hr,hrq,hphi⟩⟩

theorem mono (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {params : Fin k → M.Carrier .set} {P p q : M.Carrier .set}
    (hpre : PreorderOn R params P) (phi : Formula n) (v : Fin n → M.Carrier .set)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P)
    (hq : (Definitional.Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel R params q p)
    (h : Force R H params v P p phi) : Force R H params v P q phi :=
  basic_mono hM hpre (toBasic phi) v hp hq hqp h

theorem of_dense (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {params : Fin k → M.Carrier .set} {P p : M.Carrier .set}
    (hpre : PreorderOn R params P) (phi : Formula n) (v : Fin n → M.Carrier .set)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P)
    (h : ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R params q p →
      ∃ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R params r q ∧ Force R H params v P r phi) :
    Force R H params v P p phi := basic_of_dense hM hpre (toBasic phi) v p hp h

theorem force_bot {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (params : Fin k → M.Carrier .set)
    (v : Fin n → M.Carrier .set) (P p : M.Carrier .set) : Force R H params v P p .bot ↔ False := Iff.rfl

theorem force_mem {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (params : Fin k → M.Carrier .set)
    (v : Fin n → M.Carrier .set) (P p : M.Carrier .set) (x y : Fin n) :
    Force R H params v P p (.mem x y) ↔ Forces false R params P (v x) (v y) p := Iff.rfl

theorem force_equal {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (params : Fin k → M.Carrier .set)
    (v : Fin n → M.Carrier .set) (P p : M.Carrier .set) (x y : Fin n) :
    Force R H params v P p (.equal x y) ↔ Forces true R params P (v x) (v y) p := Iff.rfl

theorem force_conj {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (params : Fin k → M.Carrier .set)
    (v : Fin n → M.Carrier .set) (P p : M.Carrier .set) (a b : Formula n) :
    Force R H params v P p (.conj a b) ↔ Force R H params v P p a ∧ Force R H params v P p b := Iff.rfl

theorem force_imp (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {params : Fin k → M.Carrier .set} {P p : M.Carrier .set}
    (hpre : PreorderOn R params P) (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P)
    (v : Fin n → M.Carrier .set) (a b : Formula n) :
    Force R H params v P p (.imp a b) ↔
      ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R params q p →
        Force R H params v P q a → Force R H params v P q b := by
  constructor
  · intro h q hq hqp hqa
    apply Classical.byContradiction
    intro hn
    obtain ⟨r,hr,hrq,hrb⟩ := exists_basic_neg hM hpre (toBasic b) v hq hn
    exact h r hr (hpre.2 r q p hr hq hp hrq hqp) ⟨mono hM hpre a v hq hr hrq hqa,hrb⟩
  · intro h q hq hqp hqab
    exact hqab.2 q hq (hpre.1 q hq) (h q hq hqp hqab.1)

theorem force_neg (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {params : Fin k → M.Carrier .set} {P p : M.Carrier .set}
    (hpre : PreorderOn R params P) (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P)
    (v : Fin n → M.Carrier .set) (a : Formula n) :
    Force R H params v P p a.neg ↔
      ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R params q p → ¬Force R H params v P q a :=
  force_imp hM hpre hp v a .bot

theorem force_disj {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (params : Fin k → M.Carrier .set)
    (v : Fin n → M.Carrier .set) (P p : M.Carrier .set) (a b : Formula n) :
    Force R H params v P p (.disj a b) ↔
      ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R params q p →
        ∃ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R params r q ∧
          (Force R H params v P r a ∨ Force R H params v P r b) := by
  constructor
  · intro h q hq hqp
    apply Classical.byContradiction
    intro hn
    apply h q hq hqp
    exact ⟨fun r hr hrq ha => hn ⟨r,hr,hrq,Or.inl ha⟩,fun r hr hrq hb => hn ⟨r,hr,hrq,Or.inr hb⟩⟩
  · intro h q hq hqp hab
    obtain ⟨r,hr,hrq,ha | hb⟩ := h q hq hqp
    · exact hab.1 r hr hrq ha
    · exact hab.2 r hr hrq hb

theorem force_ex {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (params : Fin k → M.Carrier .set)
    (v : Fin n → M.Carrier .set) (P p : M.Carrier .set) (a : Formula (n+1)) :
    Force R H params v P p (.ex a) ↔
      ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R params q p →
        ∃ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R params r q ∧
          ∃ x, Predicate H params x ∧ Force R H params (Fin.lastCases x v) P r a := Iff.rfl

theorem force_all (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {params : Fin k → M.Carrier .set} {P p : M.Carrier .set}
    (hpre : PreorderOn R params P) (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P)
    (v : Fin n → M.Carrier .set) (a : Formula (n+1)) :
    Force R H params v P p (.all a) ↔
      ∀ x, Predicate H params x → Force R H params (Fin.lastCases x v) P p a := by
  constructor
  · intro h x hx
    apply Classical.byContradiction
    intro hn
    let vx : Fin (n+1) → M.Carrier .set := Fin.lastCases x v
    have hn' : ¬BasicForce R H params vx P p (toBasic a) := hn
    obtain ⟨q,hq,hqp,hqa⟩ := exists_basic_neg hM (H := H) hpre (toBasic a) vx hp hn'
    apply h q hq hqp
    intro r hr hrq
    exact ⟨r,hr,hpre.1 r hr,x,hx,basic_mono hM hpre (.neg (toBasic a)) (Fin.lastCases x v) hq hr hrq hqa⟩
  · intro h q hq hqp hqex
    obtain ⟨r,hr,hrq,x,hx,hra⟩ := hqex q hq (hpre.1 q hq)
    let vx : Fin (n+1) → M.Carrier .set := Fin.lastCases x v
    have hv : Force R H params vx P p a := h x hx
    have hv' : Force R H params vx P r a := mono hM hpre a vx hp hr
      (hpre.2 r q p hr hq hp hrq hqp) hv
    exact hra r hr (hpre.1 r hr) hv'

/-- The original tuple substitution proof, with no invariance of H postulated. -/
theorem basic_tuple_congr (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {params : Fin k → M.Carrier .set} {P : M.Carrier .set}
    (hpre : PreorderOn R params P) (phi : Basic n) (v w : Fin n → M.Carrier .set) (p : M.Carrier .set)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P)
    (he : ∀ i, Forces true R params P (v i) (w i) p) :
    BasicForce R H params v P p phi ↔ BasicForce R H params w P p phi := by
  induction phi generalizing p with
  | bot => rfl
  | mem x y =>
    exact (ForcingAtomicLaws.mem_congr_left hM hpre (he x)).trans
      (ForcingAtomicLaws.mem_congr_right hM hpre (he y))
  | equal x y =>
    constructor
    · intro h
      exact ForcingAtomicLaws.eq_trans hM hpre (ForcingAtomicBasic.eq_symm hM (he x))
        (ForcingAtomicLaws.eq_trans hM hpre h (he y))
    · intro h
      exact ForcingAtomicLaws.eq_trans hM hpre (he x)
        (ForcingAtomicLaws.eq_trans hM hpre h (ForcingAtomicBasic.eq_symm hM (he y)))
  | conj a b ia ib => exact and_congr (ia v w p hp he) (ib v w p hp he)
  | neg a ia =>
    constructor
    · intro h q hq hqp ha
      exact h q hq hqp ((ia v w q hq (fun i => ForcingAtomicBasic.eq_mono hM hpre hq hqp (he i))).mpr ha)
    · intro h q hq hqp ha
      exact h q hq hqp ((ia v w q hq (fun i => ForcingAtomicBasic.eq_mono hM hpre hq hqp (he i))).mp ha)
  | @ex n a ia =>
    have step : ∀ v w : Fin n → M.Carrier .set, (∀ i, Forces true R params P (v i) (w i) p) →
        BasicForce R H params v P p (.ex a) → BasicForce R H params w P p (.ex a) := by
      intro v w he h q hq hqp
      obtain ⟨r,hr,hrq,x,hx,hra⟩ := h q hq hqp
      refine ⟨r,hr,hrq,x,hx,(ia (Fin.lastCases x v) (Fin.lastCases x w) r hr ?_).mp hra⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.lastCases_last] using ForcingAtomicBasic.eq_refl hM hpre x r hr
      · simpa only [Fin.lastCases_castSucc] using
          ForcingAtomicBasic.eq_mono hM hpre hr (hpre.2 r q p hr hq hp hrq hqp) (he j)
    exact ⟨step v w he,step w v (fun i => ForcingAtomicBasic.eq_symm hM (he i))⟩

theorem tuple_congr (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {params : Fin k → M.Carrier .set} {P : M.Carrier .set}
    (hpre : PreorderOn R params P) (phi : Formula n) (v w : Fin n → M.Carrier .set) (p : M.Carrier .set)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P)
    (he : ∀ i, Forces true R params P (v i) (w i) p) : Force R H params v P p phi ↔ Force R H params w P p phi :=
  basic_tuple_congr hM hpre (toBasic phi) v w p hp he

def dense {k n m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (rho : Fin k → Fin m)
    (v : Fin n → Fin m) (P p : Fin m) (phi : Formula n) : Formula m :=
  .all ((Formula.mem (Fin.last m) P.castSucc).imp
    ((ReplacementPredicates.rel R (paramsUp rho) (Fin.last m) p.castSucc).imp
      (.ex ((Formula.mem (Fin.last (m+1)) P.castSucc.castSucc).conj
        ((ReplacementPredicates.rel R (paramsUp (paramsUp rho)) (Fin.last (m+1)) (Fin.last m).castSucc).conj
          (formula R H (paramsUp (paramsUp rho)) (fun i => (v i).castSucc.castSucc)
            P.castSucc.castSucc (Fin.last (m+1)) phi))))))

theorem dense_semantics {k n m : Nat} (env : Fin m → M.Carrier .set) (R : Formula (k+2)) (H : Formula (k+1))
    (rho : Fin k → Fin m) (v : Fin n → Fin m) (P p : Fin m) (phi : Formula n) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (dense R H rho v P p phi) ↔
      ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q (env P) → MapRel R (fun i => env (rho i)) q (env p) →
        ∃ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r (env P) ∧ MapRel R (fun i => env (rho i)) r q ∧
          Force R H (fun i => env (rho i)) (fun i => env (v i)) (env P) r phi := by
  simp only [dense,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),formula_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]

def monotoneSentence {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (v : Fin n → Fin k)
    (P p q : Fin k) (phi : Formula n) : Source.Sentence :=
  ((ForcingAtomicBasic.preorder R id P).imp ((Formula.mem p P).imp ((Formula.mem q P).imp
    ((ReplacementPredicates.rel R id q p).imp ((formula R H id v P p phi).imp (formula R H id v P q phi)))))).close

def denseSentence {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (v : Fin n → Fin k)
    (P p : Fin k) (phi : Formula n) : Source.Sentence :=
  ((ForcingAtomicBasic.preorder R id P).imp ((Formula.mem p P).imp
    ((dense R H id v P p phi).imp (formula R H id v P p phi)))).close

theorem monotone_models {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (v : Fin n → Fin k)
    (P p q : Fin k) (phi : Formula n) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (monotoneSentence R H v P p q phi)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hpre hp hq hqp h
  exact (formula_semantics (M := M) env R H id v P q phi).mpr
    (mono hM ((ForcingAtomicBasic.preorder_semantics (M := M) env R id P).mp hpre) phi (fun i => env (v i)) hp hq
      ((ForcingMapConditions.rel_semantics (M := M) env R id q p).mp hqp)
      ((formula_semantics (M := M) env R H id v P p phi).mp h))

theorem dense_models {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (v : Fin n → Fin k)
    (P p : Fin k) (phi : Formula n) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (denseSentence R H v P p phi)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hpre hp h
  exact (formula_semantics (M := M) env R H id v P p phi).mpr
    (of_dense hM ((ForcingAtomicBasic.preorder_semantics (M := M) env R id P).mp hpre) phi (fun i => env (v i)) hp
      ((dense_semantics (M := M) env R H id v P p phi).mp h))

theorem monotone_kernel_certificate {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (v : Fin n → Fin k)
    (P p q : Fin k) (phi : Formula n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (monotoneSentence R H v P p q phi)) :=
  ModelTransfer.derives (fun _ hM => monotone_models R H v P p q phi hM)

theorem dense_kernel_certificate {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (v : Fin n → Fin k)
    (P p : Fin k) (phi : Formula n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (denseSentence R H v P p phi)) :=
  ModelTransfer.derives (fun _ hM => dense_models R H v P p phi hM)

end PPAC.Migration.ForcingFormula
