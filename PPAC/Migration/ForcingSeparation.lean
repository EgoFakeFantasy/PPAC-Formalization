/- Pinned SymmetricNames.entry_permute/separationTest_permute/separate.
The source indexed family is the first-coordinate graph on the original raw
name. Existing atomic/formula symmetry and collect_HS are the proof engines. -/
import PPAC.Migration.ForcingTupleStabilizer
import PPAC.Migration.ForcingCollectedHS
import PPAC.Migration.ForcingPairUnion

namespace PPAC.Migration.ForcingSeparation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (MapRel Mapped)
open ForcingStabilizer (Action)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingConditionGraphs (Endomap Permutation InverseGraph)
open ForcingFormula (Basic BasicForce Force)
open ForcingClassEvaluation (Predicate)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Adding internal graph parameters leaves the same atomic recursion witnesses. -/
theorem atomic_congr {k l : Nat} {R : Formula (k+2)} {S : Formula (l+2)}
    {env : Fin k → M.Carrier .set} {other : Fin l → M.Carrier .set}
    (hR : ∀ x y, MapRel R env x y ↔ MapRel S other x y)
    (eq : Bool) (P x y p : M.Carrier .set) :
    ForcingAtomicRelations.Forces eq R env P x y p ↔ ForcingAtomicRelations.Forces eq S other P x y p := by
  simp only [ForcingAtomicRelations.Forces, ForcingAtomicGraphs.Good, ForcingAtomicStep.Equation,
    ForcingAtomicStep.MemBody, ForcingAtomicStep.EqBody, ForcingAtomicStep.EqHalf, hR]

/-- Only the presentation changes; the quantifier domain and forcing stay exact. -/
theorem basic_congr {k l n : Nat} {R : Formula (k+2)} {S : Formula (l+2)}
    {H : Formula (k+1)} {J : Formula (l+1)}
    {env : Fin k → M.Carrier .set} {other : Fin l → M.Carrier .set}
    (hR : ∀ x y, MapRel R env x y ↔ MapRel S other x y)
    (hH : ∀ x, Predicate H env x ↔ Predicate J other x)
    (phi : Basic n) (v : Fin n → M.Carrier .set) (P p : M.Carrier .set) :
    BasicForce R H env v P p phi ↔ BasicForce S J other v P p phi := by
  induction phi generalizing p with
  | bot => rfl
  | mem x y => exact atomic_congr hR false P (v x) (v y) p
  | equal x y => exact atomic_congr hR true P (v x) (v y) p
  | conj a b ia ib => exact and_congr (ia v p) (ib v p)
  | neg a ia => simp only [BasicForce,hR,ia]
  | ex a ia => simp only [BasicForce,hR,hH,ia]

theorem force_congr {k l n : Nat} {R : Formula (k+2)} {S : Formula (l+2)}
    {H : Formula (k+1)} {J : Formula (l+1)}
    {env : Fin k → M.Carrier .set} {other : Fin l → M.Carrier .set}
    (hR : ∀ x y, MapRel R env x y ↔ MapRel S other x y)
    (hH : ∀ x, Predicate H env x ↔ Predicate J other x)
    (phi : Formula n) (v : Fin n → M.Carrier .set) (P p : M.Carrier .set) :
    Force R H env v P p phi ↔ Force S J other v P p phi :=
  basic_congr hR hH (ForcingFormula.toBasic phi) v P p

/-- Literal forward edge action, using the already proved mapConditions equation. -/
theorem edge_action (hM : FirstOrder.Theory.Models M nativeZF)
    {P a sigma out child image p q : M.Carrier .set} (ha : Endomap P a)
    (hs : Action P a sigma out) (he : PureKuratowski.PairMember M child p sigma)
    (hc : Action P a child image) (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p P)
    (hpq : PureKuratowski.PairMember M p q a) : PureKuratowski.PairMember M image q out := by
  apply (ForcingMapConditions.edge_mapping hM
    (ForcingConditionAction.act_function (Source.SetLanguage.args2 P a) (0 : Fin 2) 1 ha) hs image q).mpr
  exact ⟨child,p,he,hc,(ForcingConditionAction.relation_semantics (Source.SetLanguage.args2 P a)
    (0 : Fin 2) 1 p q).mpr (Or.inl ⟨hp,hpq⟩)⟩

theorem entry_permute (hM : FirstOrder.Theory.Models M nativeZF)
    {P a sigma out child p : M.Carrier .set} (ha : Endomap P a)
    (hn : ForcingNames.IsName P sigma) (hs : Action P a sigma out)
    (he : PureKuratowski.PairMember M child p sigma) :
    ∃ image q, PureKuratowski.PairMember M image q out ∧ Action P a child image ∧
      PureKuratowski.PairMember M p q a := by
  have hp := (ForcingNames.child_condition hn he).1
  obtain ⟨q,hpq,_⟩ := ha.1.2 p hp
  obtain ⟨image,hc⟩ := ForcingNameConjugacy.exists_action hM ha child
  exact ⟨image,q,edge_action hM ha hs he hc hp hpq,hc,hpq⟩

/-- Reuse the source group covariance and generic HS.smul under its Normal premise. -/
theorem normal_context (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G F pi inv c r i : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingNormalFilter.Normal I G F)
    (hpi : Permutation I pi) (hinv : Permutation I inv) (hpii : InverseGraph pi inv)
    (hcc : Permutation G c) (hc : ForcingConjugationGraph.Graph I G pi inv c)
    (hA : MapRel actionFormula v pi r) (hB : MapRel actionFormula v inv i) :
    ForcingStabilizerTransport.Context actionFormula v G (v 6) F c r i := by
  have hA' := (mapRel_action v pi r).mp hA
  have hB' := (mapRel_action v inv i).mp hB
  exact ⟨ForcingProductFamily.family hM v hp hG,hcc,ForcingProductFamily.action_permutation hA',
    (ForcingProductFamily.action_permutation hB').1,
    ForcingProductCovariance.inverse hM hp hpi hpii hA' hB',
    ForcingProductCovariance.covariance hM v hp hG hinv hc hA' hB',
    hF.2.2.2 pi inv c hpi hinv.1 hpii hcc hc⟩

theorem domain_transport (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F r : Fin k)
    {I K B w pi : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F)) (hpi : Permutation I pi)
    (hA : MapRel actionFormula (fun j => env (rho j)) pi (env r)) :
    ForcingFormulaSymmetry.DomainTransport (ForcingConditionAction.actFormula (rho 6) r)
      (ForcingPairUnion.domain rho G F) env := by
  let v := fun j => env (rho j)
  obtain ⟨inv,hinv,hpii⟩ := ForcingConditionGraphs.exists_inverse hM hpi
  obtain ⟨b,hB⟩ := ForcingProductFamily.exists_action hM hp hinv
  have hB' := (mapRel_action v inv b).mpr hB
  obtain ⟨c,hcc,hc⟩ := ForcingConjugationGraph.exists_graph hM hG hpi hinv hpii
  have hf := normal_context hM v hp hG hF hpi hinv hpii hcc hc hA hB'
  have hi : InverseGraph inv pi := fun x y => (hpii y x).symm
  obtain ⟨d,hdd,hd⟩ := ForcingConjugationGraph.exists_graph hM hG hinv hpi hi
  have hb := normal_context hM v hp hG hF hinv hpi hi hdd hd hB' hA
  constructor
  · intro x hx
    have hx' := (ForcingPairUnion.domain_semantics env rho G F x).mp hx
    obtain ⟨y,hy⟩ := ForcingNameConjugacy.exists_action hM hf.2.2.1.1 x
    exact ⟨y,(ForcingPairUnion.domain_semantics env rho G F y).mpr
      (ForcingHSAction.hs_action hM hf x hx' y hy),
      (ForcingNameConjugacy.action_iff env (rho 6) r x y).mpr hy⟩
  · intro y hy
    have hy' := (ForcingPairUnion.domain_semantics env rho G F y).mp hy
    obtain ⟨x,hx⟩ := ForcingNameConjugacy.exists_action hM hb.2.2.1.1 y
    exact ⟨x,(ForcingPairUnion.domain_semantics env rho G F x).mpr
      (ForcingHSAction.hs_action hM hb y hy' x hx),
      (ForcingNameConjugacy.action_iff env (rho 6) r x y).mpr
        (ForcingNameConjugacy.inverse_action hM hb.2.2.1.1 hf.2.2.1.1 hb.2.2.2.2.1
          (ForcingHS.isName hy') hx)⟩

/-- The existing full formula symmetry, for the literal HS domain and any
internally obtained action graph. No extra ambient parameter is assumed. -/
theorem symmetry (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w pi a p q : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F)) (hpi : Permutation I pi)
    (hA : MapRel actionFormula (fun j => env (rho j)) pi a)
    (phi : Formula n) (v v' : Fin n → M.Carrier .set)
    (hv : ∀ j, Action (env (rho 6)) a (v j) (v' j))
    (hcond : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hpq : PureKuratowski.PairMember M p q a) :
    Force (ForcingProductSymmetry.orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F)
      env v (env (rho 6)) p phi ↔
    Force (ForcingProductSymmetry.orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F)
      env v' (env (rho 6)) q phi := by
  let ext : Fin (k+1) → M.Carrier .set := Fin.lastCases a env
  let up : Fin 7 → Fin (k+1) := fun j => (rho j).castSucc
  let R := ForcingProductSymmetry.orderFormula (rho 0) mul
  let H := ForcingPairUnion.domain rho G F
  let S := ForcingProductSymmetry.orderFormula (rho 0).castSucc mul.castSucc
  let J := ForcingPairUnion.domain up G.castSucc F.castSucc
  have hR : ∀ x y, MapRel R env x y ↔ MapRel S ext x y := by
    intro x y
    simp only [R,S,ForcingProductSymmetry.orderFormula_semantics,ext,Fin.lastCases_castSucc]
  have hH : ∀ x, Predicate H env x ↔ Predicate J ext x := by
    intro x
    simp only [H,J,ForcingPairUnion.domain_semantics,ext,up,Fin.lastCases_castSucc]
  have hp' : Presentation (ext (up 0)) I K B w (ext (up 1)) (ext (up 2))
      (ext (up 3)) (ext (up 4)) (ext (up 5)) (ext (up 6)) := by
    simpa only [ext,up,Fin.lastCases_castSucc] using hp
  have hG' : ForcingLabelPermutations.Carrier I (ext G.castSucc) := by
    simpa only [ext,Fin.lastCases_castSucc] using hG
  have hF' : ForcingNormalFilter.Normal I (ext G.castSucc) (ext F.castSucc) := by
    simpa only [ext,Fin.lastCases_castSucc] using hF
  have hA' : MapRel actionFormula (fun j => ext (up j)) pi (ext (Fin.last k)) := by
    simpa only [ext,up,Fin.lastCases_castSucc,Fin.lastCases_last] using hA
  have hr := ForcingProductFamily.action_permutation ((mapRel_action _ _ _).mp hA')
  have ho : ForcingAtomicSymmetry.OrderOn S ext (ext (up 6)) (ext (Fin.last k)) := by
    have horder := ForcingProductFamily.order hM (ext mul.castSucc) hp' hpi ((mapRel_action _ _ _).mp hA')
    intro x y b c hx hy hxb hyc
    rw [ForcingProductSymmetry.orderFormula_semantics,ForcingProductSymmetry.orderFormula_semantics]
    exact (horder x y b c ((ForcingConditionAction.act_inside hx).mp hxb)
      ((ForcingConditionAction.act_inside hy).mp hyc)).symm
  have ht := ForcingAtomicSymmetry.action_transport S ext (up 6) (Fin.last k) hr ho
  have hd := domain_transport hM ext up G.castSucc F.castSucc (Fin.last k) hp' hG' hF' hpi hA'
  have hv' : ∀ j, Mapped (ForcingConditionAction.actFormula (up 6) (Fin.last k)) ext (v j) (v' j) := by
    intro j
    apply (ForcingNameConjugacy.action_iff ext (up 6) (Fin.last k) _ _).mpr
    simpa only [ext,up,Fin.lastCases_castSucc,Fin.lastCases_last] using hv j
  have hc' : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (ext (up 6)) := by
    simpa only [ext,up,Fin.lastCases_castSucc] using hcond
  have hpq' : MapRel (ForcingConditionAction.actFormula (up 6) (Fin.last k)) ext p q := by
    apply (ForcingConditionAction.relation_semantics ext (up 6) (Fin.last k) p q).mpr
    apply (ForcingConditionAction.act_inside hc').mpr
    simpa only [ext,Fin.lastCases_last] using hpq
  have hh := ForcingFormulaSymmetry.symmetry hM ht hd phi v v' p q hv' hc' hpq'
  have hh' : Force S J ext v (env (rho 6)) p phi ↔ Force S J ext v' (env (rho 6)) q phi := by
    simpa only [ext,up,Fin.lastCases_castSucc] using hh
  exact (force_congr hR hH phi v _ p).trans (hh'.trans (force_congr hR hH phi v' _ q).symm)

/-- The exact internal child projection on the source index set `Edges sigma`. -/
def Family (sigma f : M.Carrier .set) : Prop :=
  ∀ i child, PureKuratowski.PairMember M i child f ↔
    (Definitional.Project.FirstOrderSemantics.reduct M).mem i sigma ∧ ∃ c, PureKuratowski.Code M i child c

def family {m : Nat} (sigma f : Fin m) : Formula m :=
  .all (.all ((Source.SetLanguage.edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.mem (Fin.last m).castSucc sigma.castSucc.castSucc).conj
      (.ex (PairSyntax.ordered (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)))))))

theorem family_semantics {m : Nat} (env : Fin m → M.Carrier .set) (sigma f : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (family sigma f) ↔
      Family (env sigma) (env f) := by
  simp only [family,Family,Source.Formula.iff,Formula.Realize,KuratowskiZF.source_edge,
    KuratowskiZF.source_code,Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h i child => ⟨(h i child).1,(h i child).2⟩,
    fun h i child => ⟨(h i child).mp,(h i child).mpr⟩⟩

def familyEntry {m : Nat} (sigma z : Fin m) : Formula m :=
  .ex (.ex (((Formula.mem (Fin.last m).castSucc sigma.castSucc.castSucc).conj
    (.ex (PairSyntax.ordered (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))))).conj
      (PairSyntax.ordered z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))))

theorem familyEntry_semantics {m : Nat} (env : Fin m → M.Carrier .set) (sigma z : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (familyEntry sigma z) ↔
      ∃ i child, ((Definitional.Project.FirstOrderSemantics.reduct M).mem i (env sigma) ∧
        ∃ c, PureKuratowski.Code M i child c) ∧ PureKuratowski.Code M (env z) i child := by
  simp only [familyEntry,Formula.Realize,KuratowskiZF.source_code,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem exists_family (hM : FirstOrder.Theory.Models M nativeZF) (sigma : M.Carrier .set) :
    ∃ f, Family sigma f := by
  obtain ⟨bound,hbound⟩ := ForcingMapConditions.coordinate_bound hM sigma
  obtain ⟨product,hproduct⟩ := ForcingCohenCoordinates.exists_cartesian hM sigma bound
  let env : Fin 1 → M.Carrier .set := fun _ => sigma
  let query := familyEntry (0 : Fin 1).castSucc (Fin.last 1)
  have hq : ∀ z, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases z env) query ↔ ∃ i child,
        ((Definitional.Project.FirstOrderSemantics.reduct M).mem i sigma ∧
          ∃ c, PureKuratowski.Code M i child c) ∧ PureKuratowski.Code M z i child := by
    intro z
    simpa only [query,env,Fin.lastCases_last,Fin.lastCases_castSucc] using
      familyEntry_semantics (M := M) (Fin.lastCases z env) (0 : Fin 1).castSucc (Fin.last 1)
  have hsep := (GodelDefOutput.separation_semantics (Definitional.Project.FirstOrderSemantics.reduct M).mem query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨f,hf⟩ := hsep env product
  refine ⟨f,fun i child => ?_⟩
  constructor
  · rintro ⟨z,hz,hzf⟩
    obtain ⟨j,other,hj,hz'⟩ := (hq z).mp ((hf z).mp hzf).2
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz'
    exact hj
  · rintro ⟨hi,c,hc⟩
    obtain ⟨z,hz⟩ := KuratowskiZF.exists_code hM i child
    exact ⟨z,hz,(hf z).mpr ⟨(hproduct z).mpr ⟨i,hi,child,(hbound child c ⟨i,hc,hi⟩).1,hz⟩,
      (hq z).mpr ⟨i,child,⟨hi,c,hc⟩,hz⟩⟩⟩

def Test {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1))
    (env : Fin k → M.Carrier .set) (v : Fin n → M.Carrier .set) (P sigma i p : M.Carrier .set)
    (phi : Formula (n+1)) : Prop :=
  ∃ child c, PureKuratowski.Code M i child c ∧
    ForcingAtomicRelations.Forces false R env P child sigma p ∧
    Force R H env (Fin.lastCases child v) P p phi

def test {k n m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (rho : Fin k → Fin m)
    (v : Fin n → Fin m) (P sigma i p : Fin m) (phi : Formula (n+1)) : Formula m :=
  .ex (.ex ((PairSyntax.ordered i.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    ((ForcingAtomicRelations.forces false R (paramsUp (paramsUp rho)) P.castSucc.castSucc
      (Fin.last m).castSucc sigma.castSucc.castSucc p.castSucc.castSucc).conj
      (ForcingFormula.formula R H (paramsUp (paramsUp rho))
        (Fin.lastCases (Fin.last m).castSucc (fun j => (v j).castSucc.castSucc))
        P.castSucc.castSucc p.castSucc.castSucc phi))))

theorem test_semantics {k n m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (rho : Fin k → Fin m)
    (v : Fin n → Fin m) (P sigma i p : Fin m) (phi : Formula (n+1)) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env
      (test R H rho v P sigma i p phi) ↔
    Test R H (fun j => env (rho j)) (fun j => env (v j)) (env P) (env sigma) (env i) (env p) phi := by
  simp only [test,Test,Formula.Realize,KuratowskiZF.source_code,
    ForcingAtomicRelations.forces_semantics (M := M),ForcingFormula.formula_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  have he : ∀ child c, (fun j => Fin.lastCases c (Fin.lastCases child env)
      (Fin.lastCases (Fin.last m).castSucc (fun l => (v l).castSucc.castSucc) j)) =
      Fin.lastCases child (fun j => env (v j)) := by
    intro child c
    funext j
    refine Fin.lastCases ?_ (fun l => ?_) j <;> simp only [Fin.lastCases_last,Fin.lastCases_castSucc]
  simp only [he]
  rfl

def testFormula {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1))
    (v : Fin n → Fin k) (P sigma : Fin k) (phi : Formula (n+1)) : Formula (k+2) :=
  test R H (fun j => j.castSucc.castSucc) (fun j => (v j).castSucc.castSucc)
    P.castSucc.castSucc sigma.castSucc.castSucc (Fin.last k).castSucc (Fin.last (k+1)) phi

theorem testFormula_semantics {k n : Nat} (env : Fin k → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (v : Fin n → Fin k) (P sigma : Fin k)
    (phi : Formula (n+1)) (i p : M.Carrier .set) :
    MapRel (testFormula R H v P sigma phi) env i p ↔
      Test R H env (fun j => env (v j)) (env P) (env sigma) i p phi := by
  unfold MapRel testFormula
  rw [test_semantics]
  simp only [Fin.lastCases_last,Fin.lastCases_castSucc]

/-- Literal separationTest_permute: a selected edge index is transported to
an actual edge of the same fixed name, and its forcing test is preserved. -/
theorem test_permute (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w pi a sigma f i child image p q : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F)) (hpi : Permutation I pi)
    (hA : MapRel actionFormula (fun j => env (rho j)) pi a)
    (hs : ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) sigma)
    (hf : Family sigma f) (hfix : Action (env (rho 6)) a sigma sigma)
    (v : Fin n → M.Carrier .set) (hfixed : ∀ j, Action (env (rho 6)) a (v j) (v j))
    (phi : Formula (n+1)) (hfic : PureKuratowski.PairMember M i child f)
    (ht : Test (ForcingProductSymmetry.orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F)
      env v (env (rho 6)) sigma i p phi)
    (him : Action (env (rho 6)) a child image)
    (hcond : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hpq : PureKuratowski.PairMember M p q a) :
    ∃ j, (Definitional.Project.FirstOrderSemantics.reduct M).mem j sigma ∧
      PureKuratowski.PairMember M j image f ∧
      Test (ForcingProductSymmetry.orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F)
        env v (env (rho 6)) sigma j q phi := by
  obtain ⟨hi,c,hic⟩ := (hf i child).mp hfic
  obtain ⟨old,d,hid,hmem,hforce⟩ := ht
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hic hid
  have har := (ForcingProductFamily.action_permutation ((mapRel_action _ _ _).mp hA)).1
  obtain ⟨image',c',hedge,himage,_⟩ := entry_permute hM har (ForcingHS.isName hs) hfix ⟨i,hic,hi⟩
  have heq := ForcingNameConjugacy.unique hM har himage him
  subst image'
  obtain ⟨j,hjcode,hj⟩ := hedge
  refine ⟨j,hj,(hf j image).mpr ⟨hj,c',hjcode⟩,image,c',hjcode,?_,?_⟩
  · have hv : ∀ l, Action (env (rho 6)) a (Source.SetLanguage.args2 child sigma l)
        (Source.SetLanguage.args2 image sigma l) := by
      intro l
      refine Fin.cases him (fun j => ?_) l
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact hfix
    exact (symmetry hM env rho G F mul hp hG hF hpi hA (.mem (0 : Fin 2) 1)
      (Source.SetLanguage.args2 child sigma) (Source.SetLanguage.args2 image sigma) hv hcond hpq).mp hmem
  · have hv : ∀ l, Action (env (rho 6)) a (Fin.lastCases child v l) (Fin.lastCases image v l) := by
      intro l
      refine Fin.lastCases ?_ (fun t => ?_) l
      · simpa only [Fin.lastCases_last] using him
      · simpa only [Fin.lastCases_castSucc] using hfixed t
    exact (symmetry hM env rho G F mul hp hG hF hpi hA phi
      (Fin.lastCases child v) (Fin.lastCases image v) hv hcond hpq).mp hforce

/-- Instantiate the source collection with its literal child-index family,
actual separation test and the constructed common subgroup. -/
theorem exists_separate (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul sigma : Fin k)
    {I K B w : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hs : ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env sigma))
    (v : Fin n → Fin k)
    (hv : ∀ j, ForcingHS.HS actionFormula (fun l => env (rho l)) (env G) (env (rho 6)) (env F) (env (v j)))
    (phi : Formula (n+1)) :
    ∃ f name, Family (env sigma) f ∧
      ForcingCollectedName.Collected
        (testFormula (ForcingProductSymmetry.orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F)
          v (rho 6) sigma phi) env (env sigma) f (env (rho 6)) name ∧
      ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name := by
  let R := ForcingProductSymmetry.orderFormula (rho 0) mul
  let H := ForcingPairUnion.domain rho G F
  let T := testFormula R H v (rho 6) sigma phi
  obtain ⟨f,hf⟩ := exists_family hM (env sigma)
  obtain ⟨S,hS,hSF,hfixed⟩ := ForcingTupleStabilizer.separation_support hM (fun j => env (rho j))
    hp hG hF hs (fun j => env (v j)) hv
  have hfamily : ForcingCollectedHS.FamilyHS (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env sigma) f := by
    intro i child _ hic
    obtain ⟨hi,c,hcode⟩ := (hf i child).mp hic
    exact ForcingHS.child hs ⟨i,hcode,hi⟩
  have hperm : ForcingCollectedHS.Permutes T env (fun j => env (rho j)) S (env sigma) f (env (rho 6)) := by
    intro g hg a hga child p image q had him hpq
    obtain ⟨hcond,i,_,hic,ht⟩ := had
    obtain ⟨hfix,hparams⟩ := hfixed g hg a hga
    obtain ⟨j,hj,hji,hT⟩ := test_permute hM env rho G F mul hp hG hF ((hG g).mp (hS.1 g hg))
      hga hs hf hfix (fun j => env (v j)) hparams phi hic
      ((testFormula_semantics env R H v (rho 6) sigma phi i p).mp ht) him hcond hpq
    exact ⟨(ForcingProductFamily.action_permutation ((mapRel_action _ _ _).mp hga)).1.2 p q hpq,
      j,hj,hji,(testFormula_semantics env R H v (rho 6) sigma phi j q).mpr hT⟩
  obtain ⟨name,hn⟩ := ForcingCollectedName.exists_collected hM T env (env sigma) f (env (rho 6))
  exact ⟨f,name,hf,hn,ForcingCollectedHS.collect_HS hM T env (fun j => env (rho j))
    hp hG hF hS hSF hfamily hperm hn⟩

/-- Exact source edge_separate, with no rank restriction on the queried child. -/
theorem edge_separate (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {v : Fin n → Fin k} {P sigma : Fin k} {f name : M.Carrier .set} {phi : Formula (n+1)}
    (hf : Family (env sigma) f)
    (hn : ForcingCollectedName.Collected (testFormula R H v P sigma phi) env (env sigma) f (env P) name)
    (child p : M.Carrier .set) : PureKuratowski.PairMember M child p name ↔
      (∃ c, PureKuratowski.PairMember M child c (env sigma)) ∧
      (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env P) ∧
      ForcingAtomicRelations.Forces false R env (env P) child (env sigma) p ∧
      Force R H env (Fin.lastCases child (fun j => env (v j))) (env P) p phi := by
  rw [ForcingCollectedName.edge_collected hM hn]
  constructor
  · rintro ⟨hp,i,hi,hic,ht⟩
    obtain ⟨_,c,hcode⟩ := (hf i child).mp hic
    obtain ⟨other,d,hcode',hm,hforce⟩ := (testFormula_semantics env R H v P sigma phi i p).mp ht
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
    exact ⟨⟨c,i,hcode,hi⟩,hp,hm,hforce⟩
  · rintro ⟨⟨c,i,hcode,hi⟩,hp,hm,hforce⟩
    exact ⟨hp,i,hi,(hf i child).mpr ⟨hi,c,hcode⟩,
      (testFormula_semantics env R H v P sigma phi i p).mpr ⟨child,c,hcode,hm,hforce⟩⟩

def Separated {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1))
    (env : Fin k → M.Carrier .set) (v : Fin n → M.Carrier .set)
    (P sigma name : M.Carrier .set) (phi : Formula (n+1)) : Prop :=
  ∀ child p, PureKuratowski.PairMember M child p name ↔
    (∃ c, PureKuratowski.PairMember M child c sigma) ∧
    (Definitional.Project.FirstOrderSemantics.reduct M).mem p P ∧
    ForcingAtomicRelations.Forces false R env P child sigma p ∧
    Force R H env (Fin.lastCases child v) P p phi

def separated {k n m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (rho : Fin k → Fin m)
    (v : Fin n → Fin m) (P sigma name : Fin m) (phi : Formula (n+1)) : Formula m :=
  let up : Fin m → Fin (m+2) := fun j => j.castSucc.castSucc
  let child := (Fin.last m).castSucc
  let p := Fin.last (m+1)
  .all (.all ((Source.SetLanguage.edge (up name) child p).iff
    ((Formula.ex (Source.SetLanguage.edge (up sigma).castSucc child.castSucc (Fin.last (m+2)))).conj
      ((Formula.mem p (up P)).conj ((ForcingAtomicRelations.forces false R (fun j => up (rho j))
        (up P) child (up sigma) p).conj
          (ForcingFormula.formula R H (fun j => up (rho j))
            (Fin.lastCases child (fun j => up (v j))) (up P) p phi))))))

theorem separated_semantics {k n m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (rho : Fin k → Fin m)
    (v : Fin n → Fin m) (P sigma name : Fin m) (phi : Formula (n+1)) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env
      (separated R H rho v P sigma name phi) ↔
    Separated R H (fun j => env (rho j)) (fun j => env (v j)) (env P) (env sigma) (env name) phi := by
  simp only [separated,Separated,Source.Formula.iff,Formula.Realize,KuratowskiZF.source_edge,
    ForcingAtomicRelations.forces_semantics (M := M),ForcingFormula.formula_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  have he : ∀ child p, (fun j => Fin.lastCases p (Fin.lastCases child env)
      (Fin.lastCases (Fin.last m).castSucc (fun l => (v l).castSucc.castSucc) j)) =
      Fin.lastCases child (fun j => env (v j)) := by
    intro child p
    funext j
    refine Fin.lastCases ?_ (fun l => ?_) j <;> simp only [Fin.lastCases_last,Fin.lastCases_castSucc]
  simp only [he]
  exact ⟨fun h child p => ⟨(h child p).1,(h child p).2⟩,
    fun h child p => ⟨(h child p).mp,(h child p).mpr⟩⟩

def sentence {k n : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul sigma : Fin k)
    (v : Fin n → Fin k) (phi : Formula (n+1)) : Source.Sentence :=
  let R := ForcingProductSymmetry.orderFormula (rho 0) mul
  let H := ForcingPairUnion.domain rho G F
  ((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp
    ((ForcingLabelPermutations.carrier I G).imp ((ForcingNormalFilter.normal I G F).imp
      ((ForcingHS.hs actionFormula rho G (rho 6) F sigma).imp
        ((ForcingTupleStabilizer.tupleHS rho G (rho 6) F v).imp
          (.ex ((ForcingHS.hs actionFormula (paramsUp rho) G.castSucc (rho 6).castSucc F.castSucc (Fin.last k)).conj
            (separated R H Fin.castSucc (fun j => (v j).castSucc)
              (rho 6).castSucc sigma.castSucc (Fin.last k) phi)))))))).close

theorem models {k n : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul sigma : Fin k)
    (v : Fin n → Fin k) (phi : Formula (n+1)) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (sentence rho I K B w G F mul sigma v phi)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp hG hF hs hv
  obtain ⟨f,name,hf,hn,hname⟩ := exists_separate hM env rho G F mul sigma
    ((ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hp)
    ((ForcingLabelPermutations.carrier_semantics (M := M) env I G).mp hG)
    ((ForcingNormalFilter.normal_semantics (M := M) env I G F).mp hF)
    ((ForcingHS.hs_semantics (M := M) env actionFormula rho G (rho 6) F sigma).mp hs) v
    ((ForcingTupleStabilizer.tupleHS_semantics (M := M) env rho G (rho 6) F v).mp hv) phi
  refine ⟨name,?_,?_⟩
  · apply (ForcingHS.hs_semantics (M := M) (Fin.lastCases name env) actionFormula (paramsUp rho)
      G.castSucc (rho 6).castSucc F.castSucc (Fin.last k)).mpr
    simpa only [paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc] using hname
  · apply (separated_semantics (M := M) (Fin.lastCases name env)
      (ForcingProductSymmetry.orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) Fin.castSucc
      (fun j => (v j).castSucc) (rho 6).castSucc sigma.castSucc (Fin.last k) phi).mpr
    simpa only [Fin.lastCases_last,Fin.lastCases_castSucc,Separated] using edge_separate hM hf hn

theorem kernel_certificate {k n : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul sigma : Fin k)
    (v : Fin n → Fin k) (phi : Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (sentence rho I K B w G F mul sigma v phi)) :=
  ModelTransfer.derives (fun _ hM => models rho I K B w G F mul sigma v phi hM)

end PPAC.Migration.ForcingSeparation
