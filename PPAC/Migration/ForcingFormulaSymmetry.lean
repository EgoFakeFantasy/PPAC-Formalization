/- Migration of pinned ForcingTruth.AtomicData.force_symmetry, lines 14-44.
Consumer: SymmetricNames.forces_symmetry and its Separation-name construction.
The source name equivalence becomes explicit object closure/surjectivity of H
under the already constructed mapConditions. Actual HS must discharge it. -/
import PPAC.Migration.ForcingSound
import PPAC.Migration.ForcingAtomicSymmetry

namespace PPAC.Migration.ForcingFormulaSymmetry
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (MapRel Mapped mapping)
open ForcingClassEvaluation (Predicate)
open ForcingFormula (Basic BasicForce Force formula)
open ForcingAtomicSymmetry (Transport)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The two witness directions used by the original name permutation. -/
def DomainTransport {k : Nat} (f : Formula (k+2)) (H : Formula (k+1))
    (params : Fin k → M.Carrier .set) : Prop :=
  (∀ x, Predicate H params x → ∃ y, Predicate H params y ∧ Mapped f params x y) ∧
  (∀ y, Predicate H params y → ∃ x, Predicate H params x ∧ Mapped f params x y)

def domainTransport {k m : Nat} (f : Formula (k+2)) (H : Formula (k+1))
    (rho : Fin k → Fin m) : Formula m :=
  let rr := fun i => (rho i).castSucc.castSucc
  let x := (Fin.last m).castSucc
  let y := Fin.last (m+1)
  (Formula.all ((MinimalPredicates.pred H (ReplacementPredicates.paramsUp rho) (Fin.last m)).imp
    (.ex ((MinimalPredicates.pred H rr y).conj (mapping f rr x y))))).conj
  (Formula.all ((MinimalPredicates.pred H (ReplacementPredicates.paramsUp rho) (Fin.last m)).imp
    (.ex ((MinimalPredicates.pred H rr y).conj (mapping f rr y x)))))

theorem domainTransport_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (f : Formula (k+2)) (H : Formula (k+1)) (rho : Fin k → Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (domainTransport f H rho) ↔
      DomainTransport f H (fun i => env (rho i)) := by
  simp only [domainTransport,DomainTransport,Formula.Realize,
    ForcingClassEvaluation.predicate_semantics (M := M),ForcingMapConditions.mapping_semantics (M := M),
    ReplacementPredicates.paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- Literal six-case source induction, with internal witnesses instead of host maps. -/
theorem basic_symmetry (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {f R : Formula (k+2)} {H : Formula (k+1)} {params : Fin k → M.Carrier .set}
    {P : M.Carrier .set} (ht : Transport f R params P) (hd : DomainTransport f H params)
    (phi : Basic n) (v w : Fin n → M.Carrier .set) (p p' : M.Carrier .set)
    (hv : ∀ i, Mapped f params (v i) (w i))
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P) (hpp : MapRel f params p p') :
    BasicForce R H params v P p phi ↔ BasicForce R H params w P p' phi := by
  have hin := ht.2.2.1
  have hon := ht.2.2.2.1
  have hord := ht.2.2.2.2
  induction phi generalizing p p' with
  | bot => rfl
  | mem a b => exact (ForcingAtomicSymmetry.atomic_symmetry hM f R params P ht
      (v a) (v b) (w a) (w b) p p' (hv a) (hv b) hp hpp).1
  | equal a b => exact (ForcingAtomicSymmetry.atomic_symmetry hM f R params P ht
      (v a) (v b) (w a) (w b) p p' (hv a) (hv b) hp hpp).2
  | conj a b ia ib => exact and_congr (ia v w p p' hv hp hpp) (ib v w p p' hv hp hpp)
  | neg a ia =>
    constructor
    · intro h q' hq' hqp' hqforce
      obtain ⟨q,hq,hqq⟩ := hon q' hq'
      exact h q hq ((hord q p q' p' hq hp hqq hpp).mp hqp')
        ((ia v w q q' hv hq hqq).mpr hqforce)
    · intro h q hq hqp hqforce
      obtain ⟨q',hqq,_⟩ := ht.1 q
      exact h q' (hin q q' hq hqq) ((hord q p q' p' hq hp hqq hpp).mpr hqp)
        ((ia v w q q' hv hq hqq).mp hqforce)
  | ex a ia =>
    constructor
    · intro h q' hq' hqp'
      obtain ⟨q,hq,hqq⟩ := hon q' hq'
      obtain ⟨r,hr,hrq,x,hx,hforce⟩ := h q hq ((hord q p q' p' hq hp hqq hpp).mp hqp')
      obtain ⟨r',hrr,_⟩ := ht.1 r
      obtain ⟨y,hy,hxy⟩ := hd.1 x hx
      refine ⟨r',hin r r' hr hrr,(hord r q r' q' hr hq hrr hqq).mpr hrq,y,hy,?_⟩
      apply (ia (Fin.lastCases x v) (Fin.lastCases y w) r r' ?_ hr hrr).mp hforce
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.lastCases_last] using hxy
      · simpa only [Fin.lastCases_castSucc] using hv j
    · intro h q hq hqp
      obtain ⟨q',hqq,_⟩ := ht.1 q
      obtain ⟨r',hr',hrq',y,hy,hforce⟩ := h q' (hin q q' hq hqq)
        ((hord q p q' p' hq hp hqq hpp).mpr hqp)
      obtain ⟨r,hr,hrr⟩ := hon r' hr'
      obtain ⟨x,hx,hxy⟩ := hd.2 y hy
      refine ⟨r,hr,(hord r q r' q' hr hq hrr hqq).mp hrq',x,hx,?_⟩
      apply (ia (Fin.lastCases x v) (Fin.lastCases y w) r r' ?_ hr hrr).mpr hforce
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.lastCases_last] using hxy
      · simpa only [Fin.lastCases_castSucc] using hv j

theorem symmetry (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {f R : Formula (k+2)} {H : Formula (k+1)} {params : Fin k → M.Carrier .set}
    {P : M.Carrier .set} (ht : Transport f R params P) (hd : DomainTransport f H params)
    (phi : Formula n) (v w : Fin n → M.Carrier .set) (p p' : M.Carrier .set)
    (hv : ∀ i, Mapped f params (v i) (w i))
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P) (hpp : MapRel f params p p') :
    Force R H params v P p phi ↔ Force R H params w P p' phi :=
  basic_symmetry hM ht hd (ForcingFormula.toBasic phi) v w p p' hv hp hpp

def conclusion {k n : Nat} (f R : Formula (k+2)) (H : Formula (k+1))
    (v w : Fin n → Fin k) (P p p' : Fin k) (phi : Formula n) : Formula k :=
  (Formula.mem p P).imp ((ReplacementPredicates.rel f id p p').imp
    ((ForcingSound.conjunction ((List.finRange n).map (fun i => mapping f id (v i) (w i)))).imp
      ((formula R H id v P p phi).iff (formula R H id w P p' phi))))

theorem conclusion_models (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (f R : Formula (k+2)) (H : Formula (k+1)) (v w : Fin n → Fin k) (P p p' : Fin k)
    (phi : Formula n) (env : Fin k → M.Carrier .set)
    (ht : Transport f R env (env P)) (hd : DomainTransport f H env) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env
      (conclusion f R H v w P p p' phi) := by
  intro hp hpp hv
  have hmap := (ForcingSound.conjunction_semantics (M := M) env _).mp hv
  have hs := symmetry hM ht hd phi (fun i => env (v i)) (fun i => env (w i)) (env p) (env p')
    (fun i => (ForcingMapConditions.mapping_semantics (M := M) env f id (v i) (w i)).mp
      (hmap _ (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩))) hp
    ((ForcingMapConditions.rel_semantics (M := M) env f id p p').mp hpp)
  have ha := ForcingFormula.formula_semantics (M := M) env R H id v P p phi
  have hb := ForcingFormula.formula_semantics (M := M) env R H id w P p' phi
  exact ⟨fun h => hb.mpr (hs.mp (ha.mp h)),fun h => ha.mpr (hs.mpr (hb.mp h))⟩

def sentence {k n : Nat} (f R : Formula (k+2)) (H : Formula (k+1))
    (v w : Fin n → Fin k) (P p p' : Fin k) (phi : Formula n) : Source.Sentence :=
  ((ForcingAtomicSymmetry.transport f R id P).imp ((domainTransport f H id).imp
    (conclusion f R H v w P p p' phi))).close

theorem models {k n : Nat} (f R : Formula (k+2)) (H : Formula (k+1))
    (v w : Fin n → Fin k) (P p p' : Fin k) (phi : Formula n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (sentence f R H v w P p p' phi)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env ht hd
  exact conclusion_models hM f R H v w P p p' phi env
    ((ForcingAtomicSymmetry.transport_semantics (M := M) env f R id P).mp ht)
    ((domainTransport_semantics (M := M) env f H id).mp hd)

theorem kernel_certificate {k n : Nat} (f R : Formula (k+2)) (H : Formula (k+1))
    (v w : Fin n → Fin k) (P p p' : Fin k) (phi : Formula n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (sentence f R H v w P p p' phi)) :=
  ModelTransfer.derives (fun _ hM => models f R H v w P p p' phi hM)

/-- The condition action is the existing literal actCode, not an assumed new map. -/
def actionSentence {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1))
    (v w : Fin n → Fin k) (P r p p' : Fin k) (phi : Formula n) : Source.Sentence :=
  ((ForcingConditionGraphs.permutation P r).imp ((ForcingAtomicSymmetry.orderOn R P r).imp
    ((domainTransport (ForcingConditionAction.actFormula P r) H id).imp
      (conclusion (ForcingConditionAction.actFormula P r) R H v w P p p' phi)))).close

theorem action_models {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1))
    (v w : Fin n → Fin k) (P r p p' : Fin k) (phi : Formula n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (actionSentence R H v w P r p p' phi)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hr ho hd
  exact conclusion_models hM (ForcingConditionAction.actFormula P r) R H v w P p p' phi env
    (ForcingAtomicSymmetry.action_transport R env P r
      ((ForcingConditionGraphs.permutation_semantics (M := M) env P r).mp hr)
      ((ForcingAtomicSymmetry.orderOn_semantics (M := M) env R P r).mp ho))
    ((domainTransport_semantics (M := M) env (ForcingConditionAction.actFormula P r) H id).mp hd)

theorem action_kernel_certificate {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1))
    (v w : Fin n → Fin k) (P r p p' : Fin k) (phi : Formula n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (actionSentence R H v w P r p p' phi)) :=
  ModelTransfer.derives (fun _ hM => action_models R H v w P r p p' phi hM)

end PPAC.Migration.ForcingFormulaSymmetry
