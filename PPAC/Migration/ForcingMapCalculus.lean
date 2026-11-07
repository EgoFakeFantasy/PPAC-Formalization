/- Fixed RelationCalculus boundedApp/compositionRelation/compositionGraph/
inverseGraph:200-361. Direct consumers UniformImages:243-276.
Specialize existing raw relation-graph collectors; retain complete forced
function formulas and the actual tuple stabilizers. -/
import PPAC.Migration.ForcingImageQuotient

namespace PPAC.Migration.ForcingMapCalculus
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args3)
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
open ForcingFormula (Force)
open ForcingProductFamily (Presentation actionFormula)
open ForcingProductSymmetry (orderFormula)
open ForcingHS (HS)
open ForcingPairUnion (domain domain_semantics)
open ForcingStabilizer (Action)
open ForcingRelationGraphForcing (Holds Monotone Congruent Regular)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000
universe u v v2
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Finite source parameter tuple, not a selected object-theory function. -/
def five {α : Type v} (f g X Y Z : α) : Fin 5 → α :=
  Fin.cases f (Fin.cases g (args3 X Y Z))

private theorem five_map {α : Type v} {β : Type v2} (f : α → β) (a b c d e : α) :
    (fun j => f (five a b c d e j)) = five (f a) (f b) (f c) (f d) (f e) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))) j

private theorem args3_map {α : Type v} {β : Type v2} (f : α → β) (a b c : α) :
    (fun j => f (args3 a b c j)) = args3 (f a) (f b) (f c) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))) j

/-- Reuse the existing forcing-formula front end for a finite parameter list. -/
def relationOf {k l : Nat} (rho : Fin 7 → Fin k) (G F mul : Fin k)
    (names : Fin l → Fin k) (phi : Formula (l+2)) : Formula (k+3) :=
  let up : Fin k → Fin (k+3) := fun j => j.castSucc.castSucc.castSucc
  ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) up
    (Fin.lastCases (Fin.last (k+2)) (Fin.lastCases (Fin.last (k+1)).castSucc (fun j => up (names j))))
    (up (rho 6)) (Fin.last k).castSucc.castSucc phi

theorem relationOf_semantics {k l : Nat} (env : Fin k → M.Carrier .set)
    (rho : Fin 7 → Fin k) (G F mul : Fin k) (names : Fin l → Fin k) (phi : Formula (l+2))
    (p x y : M.Carrier .set) :
    Holds (relationOf rho G F mul names phi) env p x y ↔
      Force (orderFormula (rho 0) mul) (domain rho G F) env
        (Fin.lastCases y (Fin.lastCases x (fun j => env (names j)))) (env (rho 6)) p phi := by
  simp only [relationOf,Holds,ForcingFormula.formula_semantics,Fin.lastCases_last,Fin.lastCases_castSucc]
  have hv : (fun j => Fin.lastCases y (Fin.lastCases x (Fin.lastCases p env))
      (Fin.lastCases (Fin.last (k+2)) (Fin.lastCases (Fin.last (k+1)).castSucc
        (fun j => (names j).castSucc.castSucc.castSucc)) j)) =
      Fin.lastCases y (Fin.lastCases x (fun j => env (names j))) := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Fin.lastCases_last]
    · refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Fin.lastCases_castSucc,Fin.lastCases_last]
      · simp only [Fin.lastCases_castSucc]
  rw [hv]

theorem monotone (hM : FirstOrder.Theory.Models M nativeZF) {k l : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    (names : Fin l → Fin k) (phi : Formula (l+2))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6))) :
    Monotone (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho)
      (relationOf rho G F mul names phi) env (env (rho 6)) (env G) (env F) := by
  intro p q x y hp hq hqp _ _ hh
  exact (relationOf_semantics env rho G F mul names phi q x y).mpr
    (ForcingFormula.mono hM hpre phi _ hp hq hqp
      ((relationOf_semantics env rho G F mul names phi p x y).mp hh))

theorem congruent (hM : FirstOrder.Theory.Models M nativeZF) {k l : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    (names : Fin l → Fin k) (phi : Formula (l+2))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6))) :
    Congruent (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho)
      (relationOf rho G F mul names phi) env (env (rho 6)) (env G) (env F) := by
  intro p x y x' y' _ _ _ _ hx hy
  rw [relationOf_semantics,relationOf_semantics]
  have hp := ForcingAtomicBasic.condition hM hx
  apply ForcingFormula.tuple_congr hM hpre phi _ _ p hp
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simpa only [Fin.lastCases_last] using hy
  · refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [Fin.lastCases_castSucc,Fin.lastCases_last] using hx
    · simpa only [Fin.lastCases_castSucc] using ForcingAtomicBasic.eq_refl hM hpre (env (names i)) p hp

theorem regular (hM : FirstOrder.Theory.Models M nativeZF) {k l : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    (names : Fin l → Fin k) (phi : Formula (l+2))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6))) :
    Regular (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho)
      (relationOf rho G F mul names phi) env (env (rho 6)) (env G) (env F) := by
  intro p x y hp _ _ hh
  apply (relationOf_semantics env rho G F mul names phi p x y).mpr
  apply ForcingFormula.of_dense hM hpre phi _ hp
  intro q hq hqp
  obtain ⟨r,hr,hrq,hi⟩ := hh q hq hqp
  exact ⟨r,hr,hrq,(relationOf_semantics env rho G F mul names phi r x y).mp hi⟩

theorem move (hM : FirstOrder.Theory.Models M nativeZF) {k l : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    (names : Fin l → Fin k) (phi : Formula (l+2))
    {I K two w pi action p q x y x' y' : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K two w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpi : ForcingConditionGraphs.Permutation I pi)
    (ha : MapRel actionFormula (fun j => env (rho j)) pi action)
    (hnames : ∀ j, Action (env (rho 6)) action (env (names j)) (env (names j)))
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hpq : PureKuratowski.PairMember M p q action)
    (hxx : Action (env (rho 6)) action x x') (hyy : Action (env (rho 6)) action y y')
    (hi : Holds (relationOf rho G F mul names phi) env p x y) :
    Holds (relationOf rho G F mul names phi) env q x' y' := by
  apply (relationOf_semantics env rho G F mul names phi q x' y').mpr
  apply (ForcingSeparation.symmetry hM env rho G F mul hp hG hF hpi ha phi
    (Fin.lastCases y (Fin.lastCases x (fun j => env (names j))))
    (Fin.lastCases y' (Fin.lastCases x' (fun j => env (names j))))
    (by
      intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [Fin.lastCases_last] using hyy
      · refine Fin.lastCases ?_ (fun i => ?_) j
        · simpa only [Fin.lastCases_castSucc,Fin.lastCases_last] using hxx
        · simpa only [Fin.lastCases_castSucc] using hnames i) hpW hpq).mp
  exact (relationOf_semantics env rho G F mul names phi p x y).mp hi

/-- Consume the actual tuple fixedness; no relation movement oracle is supplied. -/
theorem construct (hM : FirstOrder.Theory.Models M nativeZF) {k l : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K two w G F S mul top : Fin k)
    (names : Fin l → Fin k) (phi : Formula (l+2)) (d e : Fin l)
    (hp : Presentation (env (rho 0)) (env I) (env K) (env two) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hS : ForcingConjugationGraph.Subgroup (env I) (env G) (env S))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem (env S) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hNames : ∀ j, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env (names j)))
    (hTuple : ForcingTupleStabilizer.TupleFixed (fun j => env (rho j)) (env G) (env (rho 6))
      (fun j => env (names j)) (env S)) :
    ∃ J, ForcingRelationGraph.Graph (orderFormula (rho 0) mul) (relationOf rho G F mul names phi)
      env (rho 6) top (names d) (names e) J ∧
      HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) J ∧
      ForcingSupportedNames.Supported (fun j => env (rho j)) (env S) J := by
  have hFix {pi a : M.Carrier .set}
      (hpi : (Project.FirstOrderSemantics.reduct M).mem pi (env S))
      (ha : MapRel actionFormula (fun j => env (rho j)) pi a) (j : Fin l) :
      Action (env (rho 6)) a (env (names j)) (env (names j)) :=
    ForcingTupleStabilizer.fixed_action hM hTuple hpi ha j
  apply ForcingRelationGraphSupport.construct hM (relationOf rho G F mul names phi) env rho
    I K two w G F S mul top (names d) (names e) hp hG hF hS ht (hNames d) (hNames e)
    (fun pi hpi a ha => hFix hpi ha d) (fun pi hpi a ha => hFix hpi ha e) ?_ hSF
  intro pi hpi a ha p q x y x' y' hpW hpq _ _ hxx hyy hi
  exact move hM env rho G F mul names phi hp hG hF ((hG pi).mp (hS.1 pi hpi)) ha
    (fun j => hFix hpi ha j) hpW hpq hxx hyy hi

private theorem app_congr (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p f g x x' y y' : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hf : Forces true R env P f g p) (hx : Forces true R env P x x' p) (hy : Forces true R env P y y' p)
    (hh : Force R H env (args3 f x y) P p (Source.SetLanguage.edge 0 1 2)) :
    Force R H env (args3 g x' y') P p (Source.SetLanguage.edge 0 1 2) := by
  apply (ForcingFormula.tuple_congr hM hpre (Source.SetLanguage.edge 0 1 2) _ _ p hp ?_).mp hh
  intro j
  exact Fin.cases hf (Fin.cases hx (Fin.cases hy (fun i => Fin.elim0 i))) j

private theorem injection_mapsTo (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p f X Y : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hf : Force R H env (args3 f X Y) P p (Source.SetLanguage.injection 0 1 2)) :
    Force R H env (args3 f X Y) P p (Source.SetLanguage.mapsTo 0 1 2) := by
  rw [Source.SetLanguage.injection,ForcingSound.rename hM hpre _ _ _ _ hp,ForcingFormula.force_conj] at hf
  exact hf.1

private theorem injection_one (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p q f X Y x y z : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hf : Force R H env (args3 f X Y) P p (Source.SetLanguage.injection 0 1 2))
    (hx : ForcingClassEvaluation.Predicate H env x) (hy : ForcingClassEvaluation.Predicate H env y)
    (hz : ForcingClassEvaluation.Predicate H env z)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel R env q p)
    (hxX : Forces false R env P x X q) (hyX : Forces false R env P y X q)
    (hxz : Force R H env (args3 f x z) P q (Source.SetLanguage.edge 0 1 2))
    (hyz : Force R H env (args3 f y z) P q (Source.SetLanguage.edge 0 1 2)) :
    Forces true R env P x y q := by
  rw [Source.SetLanguage.injection,ForcingSound.rename hM hpre _ _ _ _ hp,ForcingFormula.force_conj] at hf
  have hh := (ForcingFormula.force_all hM hpre hp _ _).mp hf.2 x hx
  have hh := (ForcingFormula.force_all hM hpre hp _ _).mp hh y hy
  have hh := (ForcingFormula.force_all hM hpre hp _ _).mp hh z hz
  have hh := (ForcingFormula.force_imp hM hpre hp _ _ _).mp hh q hq hqp hxX
  have hh := (ForcingFormula.force_imp hM hpre hq _ _ _).mp hh q hq (hpre.1 q hq) hyX
  have hh := (ForcingFormula.force_imp hM hpre hq _ _ _).mp hh q hq (hpre.1 q hq)
    ⟨(ForcingRelationClass.edge_formula hM hpre hq _ (0 : Fin 6) 3 5).mpr hxz,
      (ForcingRelationClass.edge_formula hM hpre hq _ (0 : Fin 6) 4 5).mpr hyz⟩
  exact hh

/-- Parameters f,g,X,Y,Z followed by x,z; the bound HS witness is y. -/
def compositionFormula : Formula 7 :=
  .ex ((Formula.mem 5 2).conj ((Formula.mem 7 3).conj ((Formula.mem 6 4).conj
    ((Source.SetLanguage.edge 0 5 7).conj (Source.SetLanguage.edge 1 7 6)))))

def compositionRelation {k : Nat} (rho : Fin 7 → Fin k) (G F mul f g X Y Z : Fin k) : Formula (k+3) :=
  relationOf rho G F mul (five f g X Y Z) compositionFormula

/-- Parameters f,X,Y followed by y,x, exactly the bounded-app inverse. -/
def inverseFormula : Formula 5 :=
  (Formula.mem 4 1).conj ((Formula.mem 3 2).conj (Source.SetLanguage.edge 0 4 3))

def inverseRelation {k : Nat} (rho : Fin 7 → Fin k) (G F mul f X Y : Fin k) : Formula (k+3) :=
  relationOf rho G F mul (args3 f X Y) inverseFormula


private theorem composition_force_dense (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p f g X Y Z x z : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P) :
    Force R H env (Fin.lastCases z (Fin.lastCases x (five f g X Y Z))) P p compositionFormula ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p → ∃ r,
        (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧
        ∃ y, ForcingClassEvaluation.Predicate H env y ∧
          Forces false R env P x X r ∧ Forces false R env P y Y r ∧ Forces false R env P z Z r ∧
          Force R H env (args3 f x y) P r (Source.SetLanguage.edge 0 1 2) ∧
          Force R H env (args3 g y z) P r (Source.SetLanguage.edge 0 1 2) := by
  change (∀ q, _ → _ → ∃ r, _ ∧ _ ∧ ∃ y, _ ∧ _ ∧ _ ∧ _ ∧
    Force R H env (Fin.lastCases y (Fin.lastCases z (Fin.lastCases x (five f g X Y Z)))) P r
      (Source.SetLanguage.edge 0 5 7) ∧
    Force R H env (Fin.lastCases y (Fin.lastCases z (Fin.lastCases x (five f g X Y Z)))) P r
      (Source.SetLanguage.edge 1 7 6)) ↔ _
  constructor
  · intro hd q hq hqp
    obtain ⟨r,hr,hrq,y,hy,hx,hyY,hz,hf,hg⟩ := hd q hq hqp
    exact ⟨r,hr,hrq,y,hy,hx,hyY,hz,
      (ForcingRelationClass.edge_formula hM hpre hr _ (0 : Fin 8) 5 7).mp hf,
      (ForcingRelationClass.edge_formula hM hpre hr _ (1 : Fin 8) 7 6).mp hg⟩
  · intro hd q hq hqp
    obtain ⟨r,hr,hrq,y,hy,hx,hyY,hz,hf,hg⟩ := hd q hq hqp
    exact ⟨r,hr,hrq,y,hy,hx,hyY,hz,
      (ForcingRelationClass.edge_formula hM hpre hr _ (0 : Fin 8) 5 7).mpr hf,
      (ForcingRelationClass.edge_formula hM hpre hr _ (1 : Fin 8) 7 6).mpr hg⟩

/-- Exact regular dense composition of the two bounded applications. -/
theorem composition_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul f g X Y Z : Fin k)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6))) (p x z : M.Carrier .set) :
    Holds (compositionRelation rho G F mul f g X Y Z) env p x z ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
        MapRel (orderFormula (rho 0) mul) env q p → ∃ r,
        (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) ∧ MapRel (orderFormula (rho 0) mul) env r q ∧
        ∃ y, ForcingClassEvaluation.Predicate (domain rho G F) env y ∧
          Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env X) r ∧
          Forces false (orderFormula (rho 0) mul) env (env (rho 6)) y (env Y) r ∧
          Forces false (orderFormula (rho 0) mul) env (env (rho 6)) z (env Z) r ∧
          Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) x y) (env (rho 6)) r (Source.SetLanguage.edge 0 1 2) ∧
          Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env g) y z) (env (rho 6)) r (Source.SetLanguage.edge 0 1 2) := by
  rw [compositionRelation,relationOf_semantics,five_map]
  exact composition_force_dense hM hpre

theorem inverse_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul f X Y : Fin k)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (p y x : M.Carrier .set) (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Holds (inverseRelation rho G F mul f X Y) env p y x ↔
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env X) p ∧
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) y (env Y) p ∧
      Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) x y) (env (rho 6)) p (Source.SetLanguage.edge 0 1 2) := by
  rw [inverseRelation,relationOf_semantics,args3_map,inverseFormula,ForcingFormula.force_conj,ForcingFormula.force_conj]
  exact and_congr Iff.rfl (and_congr Iff.rfl
    (ForcingRelationClass.edge_formula hM hpre hpW _ (0 : Fin 5) 4 3))


section Laws
variable {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul f g X Y Z : Fin k)
variable (hM : FirstOrder.Theory.Models M nativeZF)
variable (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
include hM hpre

/-- Pinned compositionRelation_one:249-267. -/
theorem composition_one {p : M.Carrier .set}
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y)) (env (rho 6)) p (Source.SetLanguage.mapsTo 0 1 2))
    (hg : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env g) (env Y) (env Z)) (env (rho 6)) p (Source.SetLanguage.mapsTo 0 1 2)) :
    ForcingRelationGraphFunctions.One (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho)
      (compositionRelation rho G F mul f g X Y Z) env (env (rho 6)) (env G) (env F) p := by
  intro q hq hqp x y z hx hy hz hxy hxz
  have hx := (domain_semantics env rho G F x).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hx)
  have hy := (domain_semantics env rho G F y).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hy)
  have hz := (domain_semantics env rho G F z).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hz)
  have hd := (composition_semantics hM env rho G F mul f g X Y Z hpre q x y).mp hxy
  have he := (composition_semantics hM env rho G F mul f g X Y Z hpre q x z).mp hxz
  apply ForcingAtomicBasic.eq_of_dense hM hpre hq
  intro r hr hrq
  obtain ⟨s,hs,hsr,a,ha,hxX,haY,hyZ,hxa,hay⟩ := hd r hr hrq
  have hsq := hpre.2 s r q hs hr hq hsr hrq
  obtain ⟨t,ht,hts,b,hb,hxX',hbY,hzZ,hxb,hbz⟩ := he s hs hsq
  have htp := hpre.2 t q p ht hq hpW (hpre.2 t s q ht hs hq hts hsq) hqp
  have hab := ForcingKernelImage.mapsTo_unique_reuse hM hpre hpW ht htp hf hx ha hb
    (ForcingAtomicBasic.mem_mono hM hpre ht hts hxX)
    (ForcingFormula.mono hM hpre _ _ hs ht hts hxa) hxb
  have hby := app_congr hM hpre ht (ForcingAtomicBasic.eq_refl hM hpre (env g) t ht)
    hab (ForcingAtomicBasic.eq_refl hM hpre y t ht) (ForcingFormula.mono hM hpre _ _ hs ht hts hay)
  exact ⟨t,ht,hpre.2 t s r ht hs hr hts hsr,
    ForcingKernelImage.mapsTo_unique_reuse hM hpre hpW ht htp hg hb hy hz hbY hby hbz⟩

/-- Exact dense totality from the two complete mapsTo formulas. -/
theorem composition_total {p : M.Carrier .set}
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y)) (env (rho 6)) p (Source.SetLanguage.mapsTo 0 1 2))
    (hg : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env g) (env Y) (env Z)) (env (rho 6)) p (Source.SetLanguage.mapsTo 0 1 2)) :
    ForcingRelationGraphFunctions.Total (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho)
      (compositionRelation rho G F mul f g X Y Z) env (env (rho 6)) (env G) (env F) (env X) (env Z) p := by
  intro x hx q hq hqp hxX r hr hrq
  have hx := (domain_semantics env rho G F x).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hx)
  obtain ⟨s,hs,hsr,y,hy,hyY,hxy⟩ := ForcingImageQuotient.mapsTo_total_reuse hM hpre hpW hf hx hq hqp hxX hr hrq
  have hsq := hpre.2 s r q hs hr hq hsr hrq
  have hsp := hpre.2 s q p hs hq hpW hsq hqp
  obtain ⟨t,ht,hts,z,hz,hzZ,hyz⟩ := ForcingImageQuotient.mapsTo_total_reuse hM hpre hpW hg hy hs hsp hyY hs (hpre.1 s hs)
  refine ⟨t,ht,hpre.2 t s r ht hs hr hts hsr,z,
    (ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mpr ((domain_semantics env rho G F z).mp hz),hzZ,?_⟩
  apply (composition_semantics hM env rho G F mul f g X Y Z hpre t x z).mpr
  intro a ha hat
  have has := hpre.2 a t s ha ht hs hat hts
  have haq := hpre.2 a s q ha hs hq has hsq
  exact ⟨a,ha,hpre.1 a ha,y,hy,ForcingAtomicBasic.mem_mono hM hpre ha haq hxX,
    ForcingAtomicBasic.mem_mono hM hpre ha has hyY,ForcingAtomicBasic.mem_mono hM hpre ha hat hzZ,
    ForcingFormula.mono hM hpre _ _ hs ha has hxy,ForcingFormula.mono hM hpre _ _ ht ha hat hyz⟩

/-- Pinned compositionGraph_surjection:284-297, the onto obligation. -/
theorem composition_onto {p : M.Carrier .set}
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y)) (env (rho 6)) p (Source.SetLanguage.surjection 0 1 2))
    (hg : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env g) (env Y) (env Z)) (env (rho 6)) p (Source.SetLanguage.surjection 0 1 2)) :
    ForcingRelationGraphFunctions.Onto (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho)
      (compositionRelation rho G F mul f g X Y Z) env (env (rho 6)) (env G) (env F) (env X) (env Z) p := by
  intro z hz q hq hqp hzZ r hr hrq
  have hz := (domain_semantics env rho G F z).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hz)
  obtain ⟨s,hs,hsr,y,hy,hyY,hyz⟩ := ForcingImageQuotient.surjection_onto_reuse hM hpre hpW hg hz hq hqp hzZ hr hrq
  have hsq := hpre.2 s r q hs hr hq hsr hrq
  have hsp := hpre.2 s q p hs hq hpW hsq hqp
  obtain ⟨t,ht,hts,x,hx,hxX,hxy⟩ := ForcingImageQuotient.surjection_onto_reuse hM hpre hpW hf hy hs hsp hyY hs (hpre.1 s hs)
  refine ⟨t,ht,hpre.2 t s r ht hs hr hts hsr,x,
    (ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mpr ((domain_semantics env rho G F x).mp hx),hxX,?_⟩
  apply (composition_semantics hM env rho G F mul f g X Y Z hpre t x z).mpr
  intro a ha hat
  have has := hpre.2 a t s ha ht hs hat hts
  have haq := hpre.2 a s q ha hs hq has hsq
  exact ⟨a,ha,hpre.1 a ha,y,hy,ForcingAtomicBasic.mem_mono hM hpre ha hat hxX,
    ForcingAtomicBasic.mem_mono hM hpre ha has hyY,ForcingAtomicBasic.mem_mono hM hpre ha haq hzZ,
    ForcingFormula.mono hM hpre _ _ ht ha hat hxy,ForcingFormula.mono hM hpre _ _ hs ha has hyz⟩

/-- Pinned compositionGraph_injection:299-313, retaining both injections. -/
theorem composition_injective {p : M.Carrier .set}
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y)) (env (rho 6)) p (Source.SetLanguage.injection 0 1 2))
    (hg : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env g) (env Y) (env Z)) (env (rho 6)) p (Source.SetLanguage.injection 0 1 2)) :
    ForcingRelationGraphFunctions.Injective (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho)
      (compositionRelation rho G F mul f g X Y Z) env (env (rho 6)) (env G) (env F) p := by
  intro q hq hqp x y z hx hy hz hxz hyz
  have hx := (domain_semantics env rho G F x).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hx)
  have hy := (domain_semantics env rho G F y).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hy)
  have hz := (domain_semantics env rho G F z).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hz)
  have hd := (composition_semantics hM env rho G F mul f g X Y Z hpre q x z).mp hxz
  have he := (composition_semantics hM env rho G F mul f g X Y Z hpre q y z).mp hyz
  apply ForcingAtomicBasic.eq_of_dense hM hpre hq
  intro r hr hrq
  obtain ⟨s,hs,hsr,a,ha,hxX,haY,hzZ,hxa,haz⟩ := hd r hr hrq
  have hsq := hpre.2 s r q hs hr hq hsr hrq
  obtain ⟨t,ht,hts,b,hb,hyX,hbY,hzZ',hyb,hbz⟩ := he s hs hsq
  have htp := hpre.2 t q p ht hq hpW (hpre.2 t s q ht hs hq hts hsq) hqp
  have hab := injection_one hM hpre hpW hg ha hb hz ht htp
    (ForcingAtomicBasic.mem_mono hM hpre ht hts haY) hbY
    (ForcingFormula.mono hM hpre _ _ hs ht hts haz) hbz
  have hxb := app_congr hM hpre ht (ForcingAtomicBasic.eq_refl hM hpre (env f) t ht)
    (ForcingAtomicBasic.eq_refl hM hpre x t ht) hab (ForcingFormula.mono hM hpre _ _ hs ht hts hxa)
  exact ⟨t,ht,hpre.2 t s r ht hs hr hts hsr,injection_one hM hpre hpW hf hx hy hb ht htp
    (ForcingAtomicBasic.mem_mono hM hpre ht hts hxX) hyX hxb hyb⟩

/-- Inverse totality is supplied by the original surjection, not an oracle. -/
theorem inverse_total {p : M.Carrier .set}
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y)) (env (rho 6)) p (Source.SetLanguage.surjection 0 1 2)) :
    ForcingRelationGraphFunctions.Total (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho)
      (inverseRelation rho G F mul f X Y) env (env (rho 6)) (env G) (env F) (env Y) (env X) p := by
  intro y hy q hq hqp hyY r hr hrq
  have hy := (domain_semantics env rho G F y).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hy)
  obtain ⟨s,hs,hsr,x,hx,hxX,hxy⟩ := ForcingImageQuotient.surjection_onto_reuse hM hpre hpW hf hy hq hqp hyY hr hrq
  refine ⟨s,hs,hsr,x,(ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mpr
    ((domain_semantics env rho G F x).mp hx),hxX,?_⟩
  exact (inverse_semantics hM env rho G F mul f X Y hpre s y x hs).mpr
    ⟨hxX,ForcingAtomicBasic.mem_mono hM hpre hs (hpre.2 s r q hs hr hq hsr hrq) hyY,hxy⟩

theorem inverse_one {p : M.Carrier .set}
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hi : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y)) (env (rho 6)) p (Source.SetLanguage.injection 0 1 2)) :
    ForcingRelationGraphFunctions.One (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho)
      (inverseRelation rho G F mul f X Y) env (env (rho 6)) (env G) (env F) p := by
  intro q hq hqp y x z hy hx hz hyx hyz
  have hy := (domain_semantics env rho G F y).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hy)
  have hx := (domain_semantics env rho G F x).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hx)
  have hz := (domain_semantics env rho G F z).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hz)
  have hx' := (inverse_semantics hM env rho G F mul f X Y hpre q y x hq).mp hyx
  have hz' := (inverse_semantics hM env rho G F mul f X Y hpre q y z hq).mp hyz
  exact injection_one hM hpre hpW hi hx hz hy hq hqp hx'.1 hz'.1 hx'.2.2 hz'.2.2

theorem inverse_injective {p : M.Carrier .set}
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y)) (env (rho 6)) p (Source.SetLanguage.mapsTo 0 1 2)) :
    ForcingRelationGraphFunctions.Injective (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho)
      (inverseRelation rho G F mul f X Y) env (env (rho 6)) (env G) (env F) p := by
  intro q hq hqp x y z hx hy hz hxz hyz
  have hx := (domain_semantics env rho G F x).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hx)
  have hy := (domain_semantics env rho G F y).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hy)
  have hz := (domain_semantics env rho G F z).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hz)
  have hx' := (inverse_semantics hM env rho G F mul f X Y hpre q x z hq).mp hxz
  have hy' := (inverse_semantics hM env rho G F mul f X Y hpre q y z hq).mp hyz
  exact ForcingKernelImage.mapsTo_unique_reuse hM hpre hpW hq hqp hf hz hx hy hx'.1 hx'.2.2 hy'.2.2

theorem inverse_onto {p : M.Carrier .set}
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y)) (env (rho 6)) p (Source.SetLanguage.mapsTo 0 1 2)) :
    ForcingRelationGraphFunctions.Onto (orderFormula (rho 0) mul) (ForcingRelationGraphApplication.actionAt rho)
      (inverseRelation rho G F mul f X Y) env (env (rho 6)) (env G) (env F) (env Y) (env X) p := by
  intro x hx q hq hqp hxX r hr hrq
  have hx := (domain_semantics env rho G F x).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hx)
  obtain ⟨s,hs,hsr,y,hy,hyY,hxy⟩ := ForcingImageQuotient.mapsTo_total_reuse hM hpre hpW hf hx hq hqp hxX hr hrq
  refine ⟨s,hs,hsr,y,(ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mpr
    ((domain_semantics env rho G F y).mp hy),hyY,?_⟩
  exact (inverse_semantics hM env rho G F mul f X Y hpre s y x hs).mpr
    ⟨ForcingAtomicBasic.mem_mono hM hpre hs (hpre.2 s r q hs hr hq hsr hrq) hxX,hyY,hxy⟩

end Laws


section Graphs
variable {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top f g X Y Z : Fin k)
variable (hM : FirstOrder.Theory.Models M nativeZF)
variable {I K two w : M.Carrier .set}
variable (hp : Presentation (env (rho 0)) I K two w (env (rho 1)) (env (rho 2))
  (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
variable (hG : ForcingLabelPermutations.Carrier I (env G))
variable (hF : ForcingNormalFilter.Normal I (env G) (env F))
variable (ht : ForcingWithTopCarrier.Empty (env top))
variable (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
include hM hp hG hF ht hpre

theorem composition_app {J p x z : M.Carrier .set}
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hZ : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Z))
    (hGraph : ForcingRelationGraph.Graph (orderFormula (rho 0) mul)
      (compositionRelation rho G F mul f g X Y Z) env (rho 6) top X Z J)
    (hx : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) x)
    (hz : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) z)
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 J x z) (env (rho 6)) p (Source.SetLanguage.edge 0 1 2) ↔
      Holds (compositionRelation rho G F mul f g X Y Z) env p x z := by
  rw [ForcingRelationGraphApplication.app_graph hM env rho G F mul top X Z
    (compositionRelation rho G F mul f g X Y Z) (args3 J x z) 0 1 2 hp hG hF ht hpre hX hZ
    (monotone hM env rho G F mul (five f g X Y Z) compositionFormula hpre)
    (congruent hM env rho G F mul (five f g X Y Z) compositionFormula hpre)
    (regular hM env rho G F mul (five f g X Y Z) compositionFormula hpre) hGraph hx hz hpW]
  constructor
  · exact fun hh => hh.2.2
  · intro hh
    have hd := (composition_semantics hM env rho G F mul f g X Y Z hpre p x z).mp hh
    refine ⟨?_,?_,hh⟩
    · apply ForcingAtomicBasic.mem_of_dense hM hpre hpW
      intro q hq hqp
      obtain ⟨r,hr,hrq,y,_,hxX,_⟩ := hd q hq hqp
      exact ⟨r,hr,hrq,hxX⟩
    · apply ForcingAtomicBasic.mem_of_dense hM hpre hpW
      intro q hq hqp
      obtain ⟨r,hr,hrq,y,_,_,_,hzZ,_⟩ := hd q hq hqp
      exact ⟨r,hr,hrq,hzZ⟩

theorem inverse_app {J p y x : M.Carrier .set}
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hY : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Y))
    (hGraph : ForcingRelationGraph.Graph (orderFormula (rho 0) mul)
      (inverseRelation rho G F mul f X Y) env (rho 6) top Y X J)
    (hy : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) y)
    (hx : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) x)
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 J y x) (env (rho 6)) p (Source.SetLanguage.edge 0 1 2) ↔
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env X) p ∧
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) y (env Y) p ∧
      Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) x y) (env (rho 6)) p (Source.SetLanguage.edge 0 1 2) := by
  rw [ForcingRelationGraphApplication.app_graph hM env rho G F mul top Y X
    (inverseRelation rho G F mul f X Y) (args3 J y x) 0 1 2 hp hG hF ht hpre hY hX
    (monotone hM env rho G F mul (args3 f X Y) inverseFormula hpre)
    (congruent hM env rho G F mul (args3 f X Y) inverseFormula hpre)
    (regular hM env rho G F mul (args3 f X Y) inverseFormula hpre) hGraph hy hx hpW]
  constructor
  · intro hh
    exact (inverse_semantics hM env rho G F mul f X Y hpre p y x hpW).mp hh.2.2
  · intro hh
    exact ⟨hh.2.1,hh.1,(inverse_semantics hM env rho G F mul f X Y hpre p y x hpW).mpr hh⟩

/-- Discharge all function obligations of the SAME composition graph. -/
theorem composition_graph_functions {J p : M.Carrier .set}
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hZ : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Z))
    (hGraph : ForcingRelationGraph.Graph (orderFormula (rho 0) mul)
      (compositionRelation rho G F mul f g X Y Z) env (rho 6) top X Z J)
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    (Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y)) (env (rho 6)) p (Source.SetLanguage.mapsTo 0 1 2) →
      Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env g) (env Y) (env Z)) (env (rho 6)) p (Source.SetLanguage.mapsTo 0 1 2) →
      Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 J (env X) (env Z)) (env (rho 6)) p (Source.SetLanguage.mapsTo 0 1 2)) ∧
    (Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y)) (env (rho 6)) p (Source.SetLanguage.surjection 0 1 2) →
      Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env g) (env Y) (env Z)) (env (rho 6)) p (Source.SetLanguage.surjection 0 1 2) →
      Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 J (env X) (env Z)) (env (rho 6)) p (Source.SetLanguage.surjection 0 1 2)) ∧
    (Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y)) (env (rho 6)) p (Source.SetLanguage.injection 0 1 2) →
      Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env g) (env Y) (env Z)) (env (rho 6)) p (Source.SetLanguage.injection 0 1 2) →
      Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 J (env X) (env Z)) (env (rho 6)) p (Source.SetLanguage.injection 0 1 2)) := by
  have hMono := monotone hM env rho G F mul (five f g X Y Z) compositionFormula hpre
  have hCong := congruent hM env rho G F mul (five f g X Y Z) compositionFormula hpre
  have hReg := regular hM env rho G F mul (five f g X Y Z) compositionFormula hpre
  let v := args3 J (env X) (env Z)
  refine ⟨?_,?_,?_⟩
  · intro hf hg
    exact ForcingRelationGraphFunctions.graph_mapsTo hM env rho G F mul top X Z
      (compositionRelation rho G F mul f g X Y Z) v (0 : Fin 3) 1 2 hp hG hF ht hpre hX hZ hMono hCong hReg hGraph rfl rfl
      (composition_total env rho G F mul f g X Y Z hM hpre hpW hf hg)
      (composition_one env rho G F mul f g X Y Z hM hpre hpW hf hg) hpW
  · intro hf hg
    have hf' := ForcingImageQuotient.surjection_mapsTo_reuse hM hpre hpW hf
    have hg' := ForcingImageQuotient.surjection_mapsTo_reuse hM hpre hpW hg
    exact ForcingRelationGraphFunctions.graph_surjection hM env rho G F mul top X Z
      (compositionRelation rho G F mul f g X Y Z) v (0 : Fin 3) 1 2 hp hG hF ht hpre hX hZ hMono hCong hReg hGraph rfl rfl
      (composition_total env rho G F mul f g X Y Z hM hpre hpW hf' hg')
      (composition_one env rho G F mul f g X Y Z hM hpre hpW hf' hg')
      (composition_onto env rho G F mul f g X Y Z hM hpre hpW hf hg) hpW
  · intro hf hg
    have hf' := injection_mapsTo hM hpre hpW hf
    have hg' := injection_mapsTo hM hpre hpW hg
    exact ForcingRelationGraphFunctions.graph_injection hM env rho G F mul top X Z
      (compositionRelation rho G F mul f g X Y Z) v (0 : Fin 3) 1 2 hp hG hF ht hpre hX hZ hMono hCong hReg hGraph rfl rfl
      (composition_total env rho G F mul f g X Y Z hM hpre hpW hf' hg')
      (composition_one env rho G F mul f g X Y Z hM hpre hpW hf' hg')
      (composition_injective env rho G F mul f g X Y Z hM hpre hpW hf hg) hpW

/-- Source inverseGraph_surjection/injection, retaining the full bijection input. -/
theorem inverse_graph_functions {J p : M.Carrier .set}
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hY : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Y))
    (hGraph : ForcingRelationGraph.Graph (orderFormula (rho 0) mul)
      (inverseRelation rho G F mul f X Y) env (rho 6) top Y X J)
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y)) (env (rho 6)) p (Source.SetLanguage.surjection 0 1 2))
    (hi : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y)) (env (rho 6)) p (Source.SetLanguage.injection 0 1 2)) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 J (env Y) (env X)) (env (rho 6)) p (Source.SetLanguage.surjection 0 1 2) ∧
    Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 J (env Y) (env X)) (env (rho 6)) p (Source.SetLanguage.injection 0 1 2) := by
  have hMono := monotone hM env rho G F mul (args3 f X Y) inverseFormula hpre
  have hCong := congruent hM env rho G F mul (args3 f X Y) inverseFormula hpre
  have hReg := regular hM env rho G F mul (args3 f X Y) inverseFormula hpre
  have hf' := ForcingImageQuotient.surjection_mapsTo_reuse hM hpre hpW hf
  have hTot := inverse_total env rho G F mul f X Y hM hpre hpW hf
  have hOne := inverse_one env rho G F mul f X Y hM hpre hpW hi
  have hOnto := inverse_onto env rho G F mul f X Y hM hpre hpW hf'
  have hInj := inverse_injective env rho G F mul f X Y hM hpre hpW hf'
  let v := args3 J (env Y) (env X)
  exact ⟨ForcingRelationGraphFunctions.graph_surjection hM env rho G F mul top Y X
      (inverseRelation rho G F mul f X Y) v (0 : Fin 3) 1 2 hp hG hF ht hpre hY hX hMono hCong hReg hGraph rfl rfl hTot hOne hOnto hpW,
    ForcingRelationGraphFunctions.graph_injection hM env rho G F mul top Y X
      (inverseRelation rho G F mul f X Y) v (0 : Fin 3) 1 2 hp hG hF ht hpre hY hX hMono hCong hReg hGraph rfl rfl hTot hOne hInj hpW⟩

end Graphs


/-- Produce the actual stabilizer and graph; merely supplying a support is
not the delivery endpoint. Reuse the existing tuple and graph constructors. -/
private theorem actual (hM : FirstOrder.Theory.Models M nativeZF) {k l : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K two w G F mul top : Fin k)
    (names : Fin l → Fin k) (phi : Formula (l+2)) (d e : Fin l)
    (hp : Presentation (env (rho 0)) (env I) (env K) (env two) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hNames : ∀ j, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env (names j))) :
    ∃ S J,
      ForcingConjugationGraph.Subgroup (env I) (env G) S ∧
      (Project.FirstOrderSemantics.reduct M).mem S (env F) ∧
      ForcingTupleStabilizer.TupleFixed (fun j => env (rho j)) (env G) (env (rho 6)) (fun j => env (names j)) S ∧
      ForcingRelationGraph.Graph (orderFormula (rho 0).succ mul.succ)
        (relationOf (fun j => (rho j).succ) G.succ F.succ mul.succ (fun j => (names j).succ) phi)
        (Fin.cases S env) (rho 6).succ top.succ (names d).succ (names e).succ J ∧
      HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) J ∧
      ForcingSupportedNames.Supported (fun j => env (rho j)) S J := by
  obtain ⟨S,hS,hSF,hTuple⟩ := ForcingTupleStabilizer.exists_tuple hM (fun j => env (rho j))
    hp hG hF (fun j => env (names j)) hNames
  let other : Fin (k+1) → M.Carrier .set := Fin.cases S env
  let ra : Fin 7 → Fin (k+1) := fun j => (rho j).succ
  have he (j : Fin k) : other j.succ = env j := rfl
  have hSVal : other 0 = S := rfl
  have hp' : Presentation (other (ra 0)) (other I.succ) (other K.succ) (other two.succ) (other w.succ)
      (other (ra 1)) (other (ra 2)) (other (ra 3)) (other (ra 4)) (other (ra 5)) (other (ra 6)) := by
    simpa only [ra,he] using hp
  have hG' : ForcingLabelPermutations.Carrier (other I.succ) (other G.succ) := by simpa only [he] using hG
  have hF' : ForcingNormalFilter.Normal (other I.succ) (other G.succ) (other F.succ) := by simpa only [he] using hF
  have hS' : ForcingConjugationGraph.Subgroup (other I.succ) (other G.succ) (other 0) := by simpa only [he,hSVal] using hS
  have hSF' : (Project.FirstOrderSemantics.reduct M).mem (other 0) (other F.succ) := by simpa only [he,hSVal] using hSF
  have hNames' (j : Fin l) : HS actionFormula (fun j => other (ra j)) (other G.succ) (other (ra 6)) (other F.succ)
      (other (names j).succ) := by simpa only [ra,he] using hNames j
  have hTuple' : ForcingTupleStabilizer.TupleFixed (fun j => other (ra j)) (other G.succ) (other (ra 6))
      (fun j => other (names j).succ) (other 0) := by simpa only [ra,he,hSVal] using hTuple
  obtain ⟨J,hGraph,hJHS,hFixed⟩ := construct hM other ra I.succ K.succ two.succ w.succ G.succ F.succ
    0 mul.succ top.succ (fun j => (names j).succ) phi d e hp' hG' hF' hS' hSF' ht hNames' hTuple'
  refine ⟨S,J,hS,hSF,hTuple,hGraph,?_,?_⟩
  · simpa only [ra,he] using hJHS
  · simpa only [ra,he,hSVal] using hFixed

private def forceAt {n m : Nat} (rho : Fin 7 → Fin n) (G F mul : Fin n)
    (base : Fin n → Fin m) (v : Fin 3 → Fin m) (p : Fin m) (phi : Formula 3) : Project.Formula 1 m :=
  ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) base v (base (rho 6)) p phi)

/-- All internal conditions and all three complete source map principles. -/
def compositionLaws {n m : Nat} (rho : Fin 7 → Fin n) (G F mul f g X Y Z : Fin n)
    (base : Fin n → Fin m) (J : Fin m) : Project.Formula 1 m :=
  let rr : Fin n → Fin (m+1) := fun j => (base j).succ
  let first := fun phi => forceAt rho G F mul rr (args3 (rr f) (rr X) (rr Y)) 0 phi
  let second := fun phi => forceAt rho G F mul rr (args3 (rr g) (rr Y) (rr Z)) 0 phi
  let output := fun phi => forceAt rho G F mul rr (args3 J.succ (rr X) (rr Z)) 0 phi
  .forallE (.imp (.mem (.bound 0) (.bound (rr (rho 6))))
    (.conj (.imp (first (Source.SetLanguage.mapsTo 0 1 2))
      (.imp (second (Source.SetLanguage.mapsTo 0 1 2)) (output (Source.SetLanguage.mapsTo 0 1 2))))
      (.conj (.imp (first (Source.SetLanguage.surjection 0 1 2))
        (.imp (second (Source.SetLanguage.surjection 0 1 2)) (output (Source.SetLanguage.surjection 0 1 2))))
        (.imp (first (Source.SetLanguage.injection 0 1 2))
          (.imp (second (Source.SetLanguage.injection 0 1 2)) (output (Source.SetLanguage.injection 0 1 2)))))))

def inverseLaws {n m : Nat} (rho : Fin 7 → Fin n) (G F mul f X Y : Fin n)
    (base : Fin n → Fin m) (J : Fin m) : Project.Formula 1 m :=
  let rr : Fin n → Fin (m+1) := fun j => (base j).succ
  let input := fun phi => forceAt rho G F mul rr (args3 (rr f) (rr X) (rr Y)) 0 phi
  let output := fun phi => forceAt rho G F mul rr (args3 J.succ (rr Y) (rr X)) 0 phi
  .forallE (.imp (.mem (.bound 0) (.bound (rr (rho 6))))
    (.imp (input (Source.SetLanguage.surjection 0 1 2))
      (.imp (input (Source.SetLanguage.injection 0 1 2))
        (.conj (output (Source.SetLanguage.surjection 0 1 2)) (output (Source.SetLanguage.injection 0 1 2))))))

/-- Keep the exact support and the raw graph/collector witness. -/
def produced {k l : Nat} (rho : Fin 7 → Fin k) (I G F mul top : Fin k)
    (names : Fin l → Fin k) (phi : Formula (l+2)) (d e : Fin l)
    (tail : Project.Formula 1 (k+2)) : Project.Formula 1 k :=
  let ra : Fin 7 → Fin (k+1) := fun j => (rho j).succ
  let ns : Fin l → Fin (k+1) := fun j => (names j).succ
  let fields : List (Project.Formula 1 (k+2)) :=
    [ProjectSyntax.encode id (ForcingConjugationGraph.subgroup I.succ.succ G.succ.succ 1),
     .mem (.bound 1) (.bound F.succ.succ),
     ProjectSyntax.encode id (ForcingTupleStabilizer.tupleFixed (fun j => (rho j).succ.succ)
       G.succ.succ (rho 6).succ.succ (fun j => (names j).succ.succ) 1),
     ProjectSyntax.encode id (ForcingRelationGraph.graph (orderFormula (ra 0) mul.succ)
       (relationOf ra G.succ F.succ mul.succ ns phi) Fin.succ (ra 6) top.succ (ns d) (ns e) 0),
     ProjectSyntax.encode id (ForcingHS.hs actionFormula (fun j => (rho j).succ.succ)
       G.succ.succ (rho 6).succ.succ F.succ.succ 0),
     ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll (fun j => (rho j).succ.succ) 1 0)]
  .existsE (.existsE (fields.foldr (fun a b => .conj a b) tail))

def compositionResult {k : Nat} (rho : Fin 7 → Fin k) (I G F mul top f g X Y Z : Fin k) : Project.Formula 1 k :=
  produced rho I G F mul top (five f g X Y Z) compositionFormula 2 4
    (compositionLaws (fun j => (rho j).succ) G.succ F.succ mul.succ f.succ g.succ X.succ Y.succ Z.succ Fin.succ 0)

def inverseResult {k : Nat} (rho : Fin 7 → Fin k) (I G F mul top f X Y : Fin k) : Project.Formula 1 k :=
  produced rho I G F mul top (args3 f X Y) inverseFormula 2 1
    (inverseLaws (fun j => (rho j).succ) G.succ F.succ mul.succ f.succ X.succ Y.succ Fin.succ 0)

private def basePremises {k : Nat} (rho : Fin 7 → Fin k) (I K two w G F mul top : Fin k) : List (Project.Formula 1 k) :=
  [ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K two w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
   ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
   ProjectSyntax.encode id (ForcingNormalFilter.normal I G F),
   ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
   ProjectSyntax.encode id (ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6))]

def compositionSentence {k : Nat} (rho : Fin 7 → Fin k) (I K two w G F mul top f g X Y Z : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (((basePremises rho I K two w G F mul top) ++
    [ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F f),
     ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F g),
     ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F X),
     ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F Y),
     ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F Z)]).foldr
      (fun a b => .imp a b) (compositionResult rho I G F mul top f g X Y Z))
  freeClosed := by
    simp -implicitDefEqProofs [basePremises,compositionResult,produced,compositionLaws,forceAt,List.foldr,
      Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

def inverseSentence {k : Nat} (rho : Fin 7 → Fin k) (I K two w G F mul top f X Y : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (((basePremises rho I K two w G F mul top) ++
    [ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F f),
     ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F X),
     ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F Y)]).foldr
      (fun a b => .imp a b) (inverseResult rho I G F mul top f X Y))
  freeClosed := by
    simp -implicitDefEqProofs [basePremises,inverseResult,produced,inverseLaws,forceAt,List.foldr,
      Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]


theorem composition_models {k : Nat} (rho : Fin 7 → Fin k) (I K two w G F mul top f g X Y Z : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (compositionSentence rho I K two w G F mul top f g X Y Z)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [basePremises,List.foldr_append,List.foldr,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductFamily.presentation_semantics,
    ForcingLabelPermutations.carrier_semantics,ForcingNormalFilter.normal_semantics,ForcingWithTopCarrier.empty_semantics,
    ForcingAtomicBasic.preorder_semantics,ForcingHS.hs_semantics,id_eq]
  intro hp hG hF ht hpre hf hg hX hY hZ
  have hNames (j : Fin 5) : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env (five f g X Y Z j)) :=
    Fin.cases hf (Fin.cases hg (Fin.cases hX (Fin.cases hY (Fin.cases hZ (fun i => Fin.elim0 i))))) j
  obtain ⟨S,J,hS,hSF,hTuple,hGraph,hJHS,hFixed⟩ := actual hM env rho I K two w G F mul top
    (five f g X Y Z) compositionFormula 2 4 hp hG hF ht hNames
  let other : Fin (k+1) → M.Carrier .set := Fin.cases S env
  let ra : Fin 7 → Fin (k+1) := fun j => (rho j).succ
  have he (j : Fin k) : other j.succ = env j := rfl
  have hR (x y : M.Carrier .set) : MapRel (orderFormula (rho 0) mul) env x y ↔
      MapRel (orderFormula (ra 0) mul.succ) other x y := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,ra,he]
  have hpre' : ForcingAtomicBasic.PreorderOn (orderFormula (ra 0) mul.succ) other (other (ra 6)) := by
    constructor
    · intro p hpW
      exact (hR p p).mp (hpre.1 p hpW)
    · intro p q r hpW hqW hrW hpq hqr
      exact (hR p r).mp (hpre.2 p q r hpW hqW hrW ((hR p q).mpr hpq) ((hR q r).mpr hqr))
  have hDom : five f g X Y Z (2 : Fin 5) = X := rfl
  have hCod : five f g X Y Z (4 : Fin 5) = Z := rfl
  have hGraph' : ForcingRelationGraph.Graph (orderFormula (ra 0) mul.succ)
      (compositionRelation ra G.succ F.succ mul.succ f.succ g.succ X.succ Y.succ Z.succ)
      other (ra 6) top.succ X.succ Z.succ J := by
    simpa only [compositionRelation,five_map,hDom,hCod] using hGraph
  have hFunctions (p : M.Carrier .set) (hpW : (Project.FirstOrderSemantics.reduct M).mem p (other (ra 6))) :=
    composition_graph_functions other ra G.succ F.succ mul.succ top.succ f.succ g.succ X.succ Y.succ Z.succ
      hM hp hG hF ht hpre' hX hZ hGraph' hpW
  simp only [compositionResult,produced,List.foldr,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,compositionLaws,forceAt,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConjugationGraph.subgroup_semantics,
    ForcingTupleStabilizer.tupleFixed_semantics,ForcingRelationGraph.graph_semantics,ForcingHS.hs_semantics,
    ForcingSupportedNames.supported_semantics,ForcingFormula.formula_semantics,args3_map,id_eq]
  exact ⟨S,J,hS,hSF,hTuple,hGraph,hJHS,hFixed,hFunctions⟩

theorem inverse_models {k : Nat} (rho : Fin 7 → Fin k) (I K two w G F mul top f X Y : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (inverseSentence rho I K two w G F mul top f X Y)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [basePremises,List.foldr_append,List.foldr,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductFamily.presentation_semantics,
    ForcingLabelPermutations.carrier_semantics,ForcingNormalFilter.normal_semantics,ForcingWithTopCarrier.empty_semantics,
    ForcingAtomicBasic.preorder_semantics,ForcingHS.hs_semantics,id_eq]
  intro hp hG hF ht hpre hf hX hY
  have hNames (j : Fin 3) : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env (args3 f X Y j)) :=
    Fin.cases hf (Fin.cases hX (Fin.cases hY (fun i => Fin.elim0 i))) j
  obtain ⟨S,J,hS,hSF,hTuple,hGraph,hJHS,hFixed⟩ := actual hM env rho I K two w G F mul top
    (args3 f X Y) inverseFormula 2 1 hp hG hF ht hNames
  let other : Fin (k+1) → M.Carrier .set := Fin.cases S env
  let ra : Fin 7 → Fin (k+1) := fun j => (rho j).succ
  have he (j : Fin k) : other j.succ = env j := rfl
  have hR (x y : M.Carrier .set) : MapRel (orderFormula (rho 0) mul) env x y ↔
      MapRel (orderFormula (ra 0) mul.succ) other x y := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,ra,he]
  have hpre' : ForcingAtomicBasic.PreorderOn (orderFormula (ra 0) mul.succ) other (other (ra 6)) := by
    constructor
    · intro p hpW
      exact (hR p p).mp (hpre.1 p hpW)
    · intro p q r hpW hqW hrW hpq hqr
      exact (hR p r).mp (hpre.2 p q r hpW hqW hrW ((hR p q).mpr hpq) ((hR q r).mpr hqr))
  have hDom : args3 f X Y (2 : Fin 3) = Y := rfl
  have hCod : args3 f X Y (1 : Fin 3) = X := rfl
  have hGraph' : ForcingRelationGraph.Graph (orderFormula (ra 0) mul.succ)
      (inverseRelation ra G.succ F.succ mul.succ f.succ X.succ Y.succ)
      other (ra 6) top.succ Y.succ X.succ J := by
    simpa only [inverseRelation,args3_map,hDom,hCod] using hGraph
  have hFunctions (p : M.Carrier .set) (hpW : (Project.FirstOrderSemantics.reduct M).mem p (other (ra 6))) :=
    inverse_graph_functions other ra G.succ F.succ mul.succ top.succ f.succ X.succ Y.succ
      hM hp hG hF ht hpre' hX hY hGraph' hpW
  simp only [inverseResult,produced,List.foldr,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,inverseLaws,forceAt,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConjugationGraph.subgroup_semantics,
    ForcingTupleStabilizer.tupleFixed_semantics,ForcingRelationGraph.graph_semantics,ForcingHS.hs_semantics,
    ForcingSupportedNames.supported_semantics,ForcingFormula.formula_semantics,args3_map,id_eq]
  exact ⟨S,J,hS,hSF,hTuple,hGraph,hJHS,hFixed,hFunctions⟩

/-- Original YesMetaZFC kernel: actual composition graph and all source laws. -/
theorem composition_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K two w G F mul top f g X Y Z : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (compositionSentence rho I K two w G F mul top f g X Y Z)) :=
  ModelTransfer.derives (fun _ hM => composition_models rho I K two w G F mul top f g X Y Z hM)

/-- Original YesMetaZFC kernel: actual inverse graph and full bijection laws. -/
theorem inverse_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K two w G F mul top f X Y : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (inverseSentence rho I K two w G F mul top f X Y)) :=
  ModelTransfer.derives (fun _ hM => inverse_models rho I K two w G F mul top f X Y hM)

end PPAC.Migration.ForcingMapCalculus
