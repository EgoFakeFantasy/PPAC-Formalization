/- Pinned Models/OrdinalPresentation:50-145, consumed by completionRelation
and completionGraph_surjection. Keep the exact Boolean disjunction and the
all-stronger-condition NoValue clause. Reuse existing forcing/tuple/action
laws; no new graph collector, recursion or choice principle. -/
import PPAC.Migration.ForcingMapCalculus

namespace PPAC.Migration.ForcingDefaultRelation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args3)
open ForcingMapCalculus (five)
open ForcingFormula (Force)
open ForcingAtomicRelations (Forces)
open ForcingMapConditions (MapRel)
open ForcingClassEvaluation (Predicate)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
universe u v1 v2
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def defaultFormula : Formula 5 :=
  ((Source.SetLanguage.edge 0 3 4).conj (.mem 4 1)).disj
    ((Formula.ex ((Source.SetLanguage.edge 0 3 5).conj (.mem 5 1))).neg.conj (.equal 4 2))

def Default {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (P f X x0 a y p : M.Carrier .set) : Prop :=
  Force R H env (five f X x0 a y) P p defaultFormula

def NoValue {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (P f X a p : M.Carrier .set) : Prop :=
  ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
    ∀ y, Predicate H env y → Force R H env (args3 f a y) P q (Source.SetLanguage.edge 0 1 2) →
      Forces false R env P y X q → False

section Laws
variable (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
variable {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set} {P : M.Carrier .set}
variable (hpre : ForcingAtomicBasic.PreorderOn R env P)
include hM hpre

omit hM in
theorem noValue_mono {f X a p q : M.Carrier .set}
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) (hq : (Project.FirstOrderSemantics.reduct M).mem q P)
    (hqp : MapRel R env q p) (h : NoValue R H env P f X a p) : NoValue R H env P f X a q := by
  intro r hr hrq y hy ha hm
  exact h r hr (hpre.2 r q p hr hq hp hrq hqp) y hy ha hm

/-- Exact source defaultRelation_iff, with arbitrary internal conditions and
the actual quantifier domain in the fallback exclusion. -/
theorem default_iff {f X x0 a y p : M.Carrier .set}
    (_hp : (Project.FirstOrderSemantics.reduct M).mem p P) :
    Default R H env P f X x0 a y p ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
        ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧
          ((Force R H env (args3 f a y) P r (Source.SetLanguage.edge 0 1 2) ∧ Forces false R env P y X r) ∨
            (NoValue R H env P f X a r ∧ Forces true R env P y x0 r)) := by
  unfold Default defaultFormula
  rw [ForcingFormula.force_disj]
  constructor
  · intro h q hq hqp
    obtain ⟨r,hr,hrq,hLeft | hRight⟩ := h q hq hqp
    · exact ⟨r,hr,hrq,Or.inl ⟨(ForcingRelationClass.edge_formula hM hpre hr _ (0 : Fin 5) 3 4).mp hLeft.1,hLeft.2⟩⟩
    · refine ⟨r,hr,hrq,Or.inr ⟨?_,hRight.2⟩⟩
      intro t ht htr z hz ha hm
      have hn := (ForcingFormula.force_neg hM hpre hr _ _).mp hRight.1 t ht htr
      apply hn
      apply (ForcingFormula.force_ex R H env _ P t _).mpr
      intro b hb hbt
      refine ⟨b,hb,hpre.1 b hb,z,hz,?_,ForcingAtomicBasic.mem_mono hM hpre hb hbt hm⟩
      exact (ForcingRelationClass.edge_formula hM hpre hb _ (0 : Fin 6) 3 5).mpr
        (ForcingFormula.mono hM hpre _ _ ht hb hbt ha)
  · intro h q hq hqp
    obtain ⟨r,hr,hrq,hLeft | hRight⟩ := h q hq hqp
    · exact ⟨r,hr,hrq,Or.inl ⟨(ForcingRelationClass.edge_formula hM hpre hr _ (0 : Fin 5) 3 4).mpr hLeft.1,hLeft.2⟩⟩
    · refine ⟨r,hr,hrq,Or.inr ⟨?_,hRight.2⟩⟩
      apply (ForcingFormula.force_neg hM hpre hr _ _).mpr
      intro t ht htr hh
      obtain ⟨b,hb,hbt,z,hz,ha,hm⟩ := (ForcingFormula.force_ex R H env _ P t _).mp hh t ht (hpre.1 t ht)
      exact hRight.1 b hb (hpre.2 b t r hb ht hr hbt htr) z hz
        ((ForcingRelationClass.edge_formula hM hpre hb _ (0 : Fin 6) 3 5).mp ha) hm

theorem mono {f X x0 a y p q : M.Carrier .set}
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) (hq : (Project.FirstOrderSemantics.reduct M).mem q P)
    (hqp : MapRel R env q p) (h : Default R H env P f X x0 a y p) : Default R H env P f X x0 a y q :=
  ForcingFormula.mono hM hpre defaultFormula _ hp hq hqp h

theorem of_app {f X x0 a y p : M.Carrier .set}
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (ha : Force R H env (args3 f a y) P p (Source.SetLanguage.edge 0 1 2))
    (hy : Forces false R env P y X p) : Default R H env P f X x0 a y p := by
  apply (default_iff hM hpre hp).mpr
  intro q hq hqp
  exact ⟨q,hq,hpre.1 q hq,Or.inl ⟨ForcingFormula.mono hM hpre _ _ hp hq hqp ha,
    ForcingAtomicBasic.mem_mono hM hpre hq hqp hy⟩⟩

theorem total {f X x0 a p : M.Carrier .set}
    (_hp : (Project.FirstOrderSemantics.reduct M).mem p P) (hX0 : Predicate H env x0)
    (hx0 : Forces false R env P x0 X p) :
    ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
      ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧
        ∃ y, Predicate H env y ∧ Forces false R env P y X r ∧ Default R H env P f X x0 a y r := by
  intro q hq hqp
  by_cases hh : ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧
      ∃ y, Predicate H env y ∧ Force R H env (args3 f a y) P r (Source.SetLanguage.edge 0 1 2) ∧ Forces false R env P y X r
  · obtain ⟨r,hr,hrq,y,hy,ha,hm⟩ := hh
    exact ⟨r,hr,hrq,y,hy,hm,of_app hM hpre hr ha hm⟩
  · refine ⟨q,hq,hpre.1 q hq,x0,hX0,ForcingAtomicBasic.mem_mono hM hpre hq hqp hx0,?_⟩
    apply (default_iff hM hpre hq).mpr
    intro r hr hrq
    refine ⟨r,hr,hpre.1 r hr,Or.inr ⟨?_,ForcingAtomicBasic.eq_refl hM hpre x0 r hr⟩⟩
    intro t ht htr y hy ha hm
    exact hh ⟨t,ht,hpre.2 t r q ht hr hq htr hrq,y,hy,ha,hm⟩

omit hM hpre in
def PartialUnique (f : M.Carrier .set) : Prop :=
  ∀ p, (Project.FirstOrderSemantics.reduct M).mem p P → ∀ a, Predicate H env a →
    ∀ y, Predicate H env y → ∀ z, Predicate H env z →
      Force R H env (args3 f a y) P p (Source.SetLanguage.edge 0 1 2) →
      Force R H env (args3 f a z) P p (Source.SetLanguage.edge 0 1 2) → Forces true R env P y z p

theorem unique {f X x0 a y z p : M.Carrier .set}
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) (hf : PartialUnique (R := R) (H := H) (env := env) (P := P) f)
    (ha : Predicate H env a) (hy : Predicate H env y) (hz : Predicate H env z)
    (hY : Default R H env P f X x0 a y p) (hZ : Default R H env P f X x0 a z p) : Forces true R env P y z p := by
  apply ForcingAtomicBasic.eq_of_dense hM hpre hp
  intro q hq hqp
  obtain ⟨r,hr,hrq,hLeft | hRight⟩ := (default_iff hM hpre hp).mp hY q hq hqp
  · obtain ⟨s,hs,hsr,hLeft' | hRight'⟩ := (default_iff hM hpre hp).mp hZ r hr (hpre.2 r q p hr hq hp hrq hqp)
    · exact ⟨s,hs,hpre.2 s r q hs hr hq hsr hrq,hf s hs a ha y hy z hz
        (ForcingFormula.mono hM hpre _ _ hr hs hsr hLeft.1) hLeft'.1⟩
    · exact (hRight'.1 s hs (hpre.1 s hs) y hy (ForcingFormula.mono hM hpre _ _ hr hs hsr hLeft.1)
        (ForcingAtomicBasic.mem_mono hM hpre hs hsr hLeft.2)).elim
  · obtain ⟨s,hs,hsr,hLeft' | hRight'⟩ := (default_iff hM hpre hp).mp hZ r hr (hpre.2 r q p hr hq hp hrq hqp)
    · exact (hRight.1 s hs hsr z hz hLeft'.1 hLeft'.2).elim
    · exact ⟨s,hs,hpre.2 s r q hs hr hq hsr hrq,ForcingAtomicLaws.eq_trans hM hpre
        (ForcingAtomicBasic.eq_mono hM hpre hs hsr hRight.2) (ForcingAtomicBasic.eq_symm hM hRight'.2)⟩

theorem congr {f X x0 a a' y y' p : M.Carrier .set}
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (ha : Forces true R env P a a' p) (hy : Forces true R env P y y' p) :
    Default R H env P f X x0 a y p ↔ Default R H env P f X x0 a' y' p := by
  apply ForcingFormula.tuple_congr hM hpre defaultFormula _ _ p hp
  intro j
  exact Fin.cases (ForcingAtomicBasic.eq_refl hM hpre f p hp)
    (Fin.cases (ForcingAtomicBasic.eq_refl hM hpre X p hp)
      (Fin.cases (ForcingAtomicBasic.eq_refl hM hpre x0 p hp) (Fin.cases ha (Fin.cases hy (fun i => Fin.elim0 i))))) j

theorem regular {f X x0 a y p : M.Carrier .set}
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (h : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
      ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧ Default R H env P f X x0 a y r) :
    Default R H env P f X x0 a y p :=
  ForcingFormula.of_dense hM hpre defaultFormula _ hp h

end Laws

/-- Reuse the already accepted formula-to-binary-relation compiler. -/
def relation {k : Nat} (rho : Fin 7 → Fin k) (G F mul f X x0 : Fin k) : Formula (k+3) :=
  ForcingMapCalculus.relationOf rho G F mul (args3 f X x0) defaultFormula

theorem relation_semantics {k : Nat} (env : Fin k → M.Carrier .set)
    (rho : Fin 7 → Fin k) (G F mul f X x0 : Fin k) (p a y : M.Carrier .set) :
    ForcingRelationGraphForcing.Holds (relation rho G F mul f X x0) env p a y ↔
      Default (ForcingProductSymmetry.orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
        (env (rho 6)) (env f) (env X) (env x0) a y p := by
  rw [relation,ForcingMapCalculus.relationOf_semantics]
  have hv : (Fin.lastCases y (Fin.lastCases a (fun j => env (args3 f X x0 j))) : Fin 5 → M.Carrier .set) =
      five (env f) (env X) (env x0) a y := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))) j
  rw [hv]
  rfl

/-- Exact defaultRelation_symmetry, consuming the existing actual Product
formula symmetry theorem and literal actions fixing the three parameters. -/
theorem symmetry (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w pi act f X x0 a a' y y' p q : M.Carrier .set}
    (hPres : ForcingProductFamily.Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpi : ForcingConditionGraphs.Permutation I pi)
    (hAct : MapRel ForcingProductFamily.actionFormula (fun j => env (rho j)) pi act)
    (hf : ForcingStabilizer.Action (env (rho 6)) act f f)
    (hX : ForcingStabilizer.Action (env (rho 6)) act X X)
    (hx0 : ForcingStabilizer.Action (env (rho 6)) act x0 x0)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hpq : PureKuratowski.PairMember M p q act)
    (ha : ForcingStabilizer.Action (env (rho 6)) act a a')
    (hy : ForcingStabilizer.Action (env (rho 6)) act y y') :
    Default (ForcingProductSymmetry.orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (env (rho 6)) f X x0 a y p ↔
    Default (ForcingProductSymmetry.orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (env (rho 6)) f X x0 a' y' q := by
  apply ForcingSeparation.symmetry hM env rho G F mul hPres hG hF hpi hAct defaultFormula _ _ ?_ hp hpq
  intro j
  exact Fin.cases hf (Fin.cases hX (Fin.cases hx0 (Fin.cases ha (Fin.cases hy (fun i => Fin.elim0 i))))) j

private theorem args3_map {a : Type v1} {b : Type v2} (f : a → b) (x y z : a) :
    (fun j => f (args3 x y z j)) = args3 (f x) (f y) (f z) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))) j

private theorem five_map {a : Type v1} {b : Type v2} (f : a → b) (x y z r s : a) :
    (fun j => f (five x y z r s j)) = five (f x) (f y) (f z) (f r) (f s) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))) j

private def app {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (P f a y p : Fin m) : Formula m :=
  ForcingFormula.formula R H base (args3 f a y) P p (Source.SetLanguage.edge 0 1 2)

private def atFormula {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (P f X x0 a y p : Fin m) : Formula m :=
  ForcingFormula.formula R H base (five f X x0 a y) P p defaultFormula

private theorem app_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m) (P f a y p : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (app R H base P f a y p) ↔
      Force R H (fun j => env (base j)) (args3 (env f) (env a) (env y)) (env P) (env p) (Source.SetLanguage.edge 0 1 2) := by
  simp only [app,ForcingFormula.formula_semantics,args3_map]

private theorem atFormula_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m) (P f X x0 a y p : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (atFormula R H base P f X x0 a y p) ↔
      Default R H (fun j => env (base j)) (env P) (env f) (env X) (env x0) (env a) (env y) (env p) := by
  simp only [atFormula,Default,ForcingFormula.formula_semantics,five_map]

def noValue {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (P f X a p : Fin m) : Formula m :=
  let up : Fin m → Fin (m+2) := fun j => j.castSucc.castSucc
  let rr : Fin k → Fin (m+2) := fun j => up (base j)
  .all ((Formula.mem (Fin.last m) P.castSucc).imp
    ((ReplacementPredicates.rel R (fun j => (base j).castSucc) (Fin.last m) p.castSucc).imp
      (.all ((MinimalPredicates.pred H rr (Fin.last (m+1))).imp
        ((app R H rr (up P) (up f) (up a) (Fin.last (m+1)) (Fin.last m).castSucc).imp
          (ForcingAtomicRelations.forces false R rr (up P) (Fin.last (m+1)) (up X) (Fin.last m).castSucc).neg)))))

theorem noValue_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m) (P f X a p : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (noValue R H base P f X a p) ↔
      NoValue R H (fun j => env (base j)) (env P) (env f) (env X) (env a) (env p) := by
  simp only [noValue,NoValue,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    ForcingClassEvaluation.predicate_semantics (M := M),app_semantics,ForcingAtomicRelations.forces_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

private def casesFormula {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (P f X x0 a y p : Fin m) : Formula m :=
  let up : Fin m → Fin (m+2) := fun j => j.castSucc.castSucc
  let rr : Fin k → Fin (m+2) := fun j => up (base j)
  let r := Fin.last (m+1)
  .all ((Formula.mem (Fin.last m) P.castSucc).imp
    ((ReplacementPredicates.rel R (fun j => (base j).castSucc) (Fin.last m) p.castSucc).imp
      (.ex ((Formula.mem r (up P)).conj
        ((ReplacementPredicates.rel R rr r (Fin.last m).castSucc).conj
          (((app R H rr (up P) (up f) (up a) (up y) r).conj
            (ForcingAtomicRelations.forces false R rr (up P) (up y) (up X) r)).disj
            ((noValue R H rr (up P) (up f) (up X) (up a) r).conj
              (ForcingAtomicRelations.forces true R rr (up P) (up y) (up x0) r))))))))

private theorem casesFormula_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m) (P f X x0 a y p : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (casesFormula R H base P f X x0 a y p) ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env P) → MapRel R (fun j => env (base j)) q (env p) →
        ∃ r, (Project.FirstOrderSemantics.reduct M).mem r (env P) ∧ MapRel R (fun j => env (base j)) r q ∧
          ((Force R H (fun j => env (base j)) (args3 (env f) (env a) (env y)) (env P) r (Source.SetLanguage.edge 0 1 2) ∧
            Forces false R (fun j => env (base j)) (env P) (env y) (env X) r) ∨
            (NoValue R H (fun j => env (base j)) (env P) (env f) (env X) (env a) r ∧
              Forces true R (fun j => env (base j)) (env P) (env y) (env x0) r)) := by
  simp only [casesFormula,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),app_semantics,
    noValue_semantics,ForcingAtomicRelations.forces_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]

def pointFormula {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (P f X x0 : Fin m) : Formula m :=
  let up : Fin m → Fin (m+3) := fun j => j.castSucc.castSucc.castSucc
  let rr : Fin k → Fin (m+3) := fun j => up (base j)
  let p := (Fin.last m).castSucc.castSucc
  let a := (Fin.last (m+1)).castSucc
  let y := Fin.last (m+2)
  .all ((Formula.mem (Fin.last m) P.castSucc).imp (.all (.all
    ((atFormula R H rr (up P) (up f) (up X) (up x0) a y p).iff
      (casesFormula R H rr (up P) (up f) (up X) (up x0) a y p)))))

theorem pointFormula_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m) (P f X x0 : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (pointFormula R H base P f X x0) ↔
      ∀ p, (Project.FirstOrderSemantics.reduct M).mem p (env P) → ∀ a y,
        (Default R H (fun j => env (base j)) (env P) (env f) (env X) (env x0) a y p ↔
          ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env P) → MapRel R (fun j => env (base j)) q p →
            ∃ r, (Project.FirstOrderSemantics.reduct M).mem r (env P) ∧ MapRel R (fun j => env (base j)) r q ∧
              ((Force R H (fun j => env (base j)) (args3 (env f) a y) (env P) r (Source.SetLanguage.edge 0 1 2) ∧
                Forces false R (fun j => env (base j)) (env P) y (env X) r) ∨
                (NoValue R H (fun j => env (base j)) (env P) (env f) (env X) a r ∧
                  Forces true R (fun j => env (base j)) (env P) y (env x0) r))) := by
  simp only [pointFormula,Source.Formula.iff,Formula.Realize,atFormula_semantics,casesFormula_semantics,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  constructor
  · intro h p hp a y
    exact ⟨(h p hp a y).1,(h p hp a y).2⟩
  · intro h p hp a y
    exact ⟨(h p hp a y).mp,(h p hp a y).mpr⟩

private def totalAt {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (P f X x0 a p : Fin m) : Formula m :=
  let up : Fin m → Fin (m+3) := fun j => j.castSucc.castSucc.castSucc
  let rr : Fin k → Fin (m+3) := fun j => up (base j)
  let r := (Fin.last (m+1)).castSucc
  let y := Fin.last (m+2)
  .all ((Formula.mem (Fin.last m) P.castSucc).imp
    ((ReplacementPredicates.rel R (fun j => (base j).castSucc) (Fin.last m) p.castSucc).imp
      (.ex ((Formula.mem (Fin.last (m+1)) P.castSucc.castSucc).conj
        ((ReplacementPredicates.rel R (fun j => (base j).castSucc.castSucc) (Fin.last (m+1)) (Fin.last m).castSucc).conj
          (.ex ((MinimalPredicates.pred H rr y).conj
            ((ForcingAtomicRelations.forces false R rr (up P) y (up X) r).conj
              (atFormula R H rr (up P) (up f) (up X) (up x0) (up a) y r)))))))))

def totalFormula {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (P f X x0 : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) P.castSucc).imp
    ((ForcingAtomicRelations.forces false R (fun j => (base j).castSucc) P.castSucc x0.castSucc X.castSucc (Fin.last m)).imp
      (.all (totalAt R H (fun j => (base j).castSucc.castSucc) P.castSucc.castSucc f.castSucc.castSucc X.castSucc.castSucc
        x0.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc))))

theorem totalFormula_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m) (P f X x0 : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (totalFormula R H base P f X x0) ↔
      ∀ p, (Project.FirstOrderSemantics.reduct M).mem p (env P) →
        Forces false R (fun j => env (base j)) (env P) (env x0) (env X) p → ∀ a,
          ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env P) → MapRel R (fun j => env (base j)) q p →
            ∃ r, (Project.FirstOrderSemantics.reduct M).mem r (env P) ∧ MapRel R (fun j => env (base j)) r q ∧
              ∃ y, Predicate H (fun j => env (base j)) y ∧ Forces false R (fun j => env (base j)) (env P) y (env X) r ∧
                Default R H (fun j => env (base j)) (env P) (env f) (env X) (env x0) a y r := by
  simp only [totalFormula,totalAt,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    ForcingClassEvaluation.predicate_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    atFormula_semantics,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

private def uniqueApp {k m : Nat} (useDefault : Bool) (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (P f X x0 a y p : Fin m) : Formula m :=
  if useDefault then atFormula R H base P f X x0 a y p else app R H base P f a y p

def uniqueFormula {k m : Nat} (useDefault : Bool) (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (P f X x0 : Fin m) : Formula m :=
  let up : Fin m → Fin (m+4) := fun j => j.castSucc.castSucc.castSucc.castSucc
  let rr : Fin k → Fin (m+4) := fun j => up (base j)
  let p := (Fin.last m).castSucc.castSucc.castSucc
  let a := (Fin.last (m+1)).castSucc.castSucc
  let y := (Fin.last (m+2)).castSucc
  let z := Fin.last (m+3)
  .all ((Formula.mem (Fin.last m) P.castSucc).imp (.all
    ((MinimalPredicates.pred H (fun j => (base j).castSucc.castSucc) (Fin.last (m+1))).imp (.all
      ((MinimalPredicates.pred H (fun j => (base j).castSucc.castSucc.castSucc) (Fin.last (m+2))).imp (.all
        ((MinimalPredicates.pred H rr z).imp
          ((uniqueApp useDefault R H rr (up P) (up f) (up X) (up x0) a y p).imp
            ((uniqueApp useDefault R H rr (up P) (up f) (up X) (up x0) a z p).imp
              (ForcingAtomicRelations.forces true R rr (up P) y z p))))))))))

theorem uniqueFormula_semantics {k m : Nat} (useDefault : Bool) (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m) (P f X x0 : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (uniqueFormula useDefault R H base P f X x0) ↔
      ∀ p, (Project.FirstOrderSemantics.reduct M).mem p (env P) → ∀ a, Predicate H (fun j => env (base j)) a →
        ∀ y, Predicate H (fun j => env (base j)) y → ∀ z, Predicate H (fun j => env (base j)) z →
          (if useDefault then Default R H (fun j => env (base j)) (env P) (env f) (env X) (env x0) a y p
            else Force R H (fun j => env (base j)) (args3 (env f) a y) (env P) p (Source.SetLanguage.edge 0 1 2)) →
          (if useDefault then Default R H (fun j => env (base j)) (env P) (env f) (env X) (env x0) a z p
            else Force R H (fun j => env (base j)) (args3 (env f) a z) (env P) p (Source.SetLanguage.edge 0 1 2)) →
          Forces true R (fun j => env (base j)) (env P) y z p := by
  cases useDefault with
  | false =>
    simp only [uniqueFormula,uniqueApp,Formula.Realize,ForcingClassEvaluation.predicate_semantics (M := M),
      ForcingAtomicRelations.forces_semantics (M := M),Bool.false_eq_true,if_false,app_semantics,
      Fin.lastCases_last,Fin.lastCases_castSucc]
    rfl
  | true =>
    simp only [uniqueFormula,uniqueApp,Formula.Realize,ForcingClassEvaluation.predicate_semantics (M := M),
      ForcingAtomicRelations.forces_semantics (M := M),if_true,atFormula_semantics,
      Fin.lastCases_last,Fin.lastCases_castSucc]
    rfl


def sentence {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (P f X x0 : Fin k) : Source.Sentence :=
  ((ForcingAtomicBasic.preorder R id P).imp ((MinimalPredicates.pred H id x0).imp
    ((pointFormula R H id P f X x0).conj ((totalFormula R H id P f X x0).conj
      ((uniqueFormula false R H id P f X x0).imp (uniqueFormula true R H id P f X x0)))))).close

theorem models {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (P f X x0 : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence (sentence R H P f X x0)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hpre hX0
  have hpre := (ForcingAtomicBasic.preorder_semantics (M := M) env R id P).mp hpre
  have hX0 := (ForcingClassEvaluation.predicate_semantics (M := M) env H id x0).mp hX0
  refine ⟨(pointFormula_semantics env R H id P f X x0).mpr ?_,
    (totalFormula_semantics env R H id P f X x0).mpr ?_,?_⟩
  · intro p hp a y
    exact default_iff hM hpre hp
  · intro p hp hx0 a
    exact total hM hpre hp hX0 hx0
  · intro hf
    apply (uniqueFormula_semantics true env R H id P f X x0).mpr
    have hf := (uniqueFormula_semantics false env R H id P f X x0).mp hf
    intro p hp a ha y hy z hz hY hZ
    exact unique hM hpre hp hf ha hy hz hY hZ

/-- Ordinary ZF in the original pure membership kernel. Full source default
logic, totality and unique-value preservation; no Choice or L wrapper. -/
theorem kernel_certificate {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (P f X x0 : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (sentence R H P f X x0)) :=
  ModelTransfer.derives (fun _ hM => models R H P f X x0 hM)

end PPAC.Migration.ForcingDefaultRelation
