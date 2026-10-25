/- Pinned SymmetricNames.tupleStabilizer/tupleStabilizer_mem/mem_tupleStabilizer.
Use the source finite intersection of actual name stabilizers. Arbitrary
external tuple length indexes a pure object formula and original-kernel proof. -/
import PPAC.Migration.ForcingProductStabilizer
import PPAC.Migration.ForcingNormalFilter
import PPAC.Migration.ForcingSound

namespace PPAC.Migration.ForcingTupleStabilizer
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (MapRel)
open ForcingStabilizer (Fixed Action)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem finite_conjunction {n m : Nat} (env : Fin m → M.Carrier .set) (fs : Fin n → Formula m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env
      (ForcingSound.conjunction ((List.finRange n).map fs)) ↔
      ∀ j, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (fs j) := by
  rw [ForcingSound.conjunction_semantics]
  constructor
  · intro h j
    exact h _ (List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩)
  · intro h p hp
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hp
    exact h j

def tupleHS {n m : Nat} (rho : Fin 7 → Fin m) (G P F : Fin m) (v : Fin n → Fin m) : Formula m :=
  ForcingSound.conjunction ((List.finRange n).map (fun j => ForcingHS.hs actionFormula rho G P F (v j)))

theorem tupleHS_semantics {n m : Nat} (env : Fin m → M.Carrier .set) (rho : Fin 7 → Fin m)
    (G P F : Fin m) (v : Fin n → Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (tupleHS rho G P F v) ↔
      ∀ j, ForcingHS.HS actionFormula (fun i => env (rho i)) (env G) (env P) (env F) (env (v j)) := by
  simp only [tupleHS,finite_conjunction,ForcingHS.hs_semantics (M := M)]

def tupleFixed {n m : Nat} (rho : Fin 7 → Fin m) (G P : Fin m) (v : Fin n → Fin m) (S : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) S.castSucc).iff ((Formula.mem (Fin.last m) G.castSucc).conj
    (ForcingSound.conjunction ((List.finRange n).map (fun j =>
      ForcingStabilizer.fixed actionFormula (paramsUp rho) P.castSucc (v j).castSucc (Fin.last m))))))

def TupleFixed {n : Nat} (aenv : Fin 7 → M.Carrier .set) (G P : M.Carrier .set)
    (v : Fin n → M.Carrier .set) (S : M.Carrier .set) : Prop :=
  ∀ g, (Definitional.Project.FirstOrderSemantics.reduct M).mem g S ↔
    (Definitional.Project.FirstOrderSemantics.reduct M).mem g G ∧ ∀ j, Fixed actionFormula aenv P (v j) g

theorem tupleFixed_semantics {n m : Nat} (env : Fin m → M.Carrier .set) (rho : Fin 7 → Fin m)
    (G P : Fin m) (v : Fin n → Fin m) (S : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (tupleFixed rho G P v S) ↔
      TupleFixed (fun i => env (rho i)) (env G) (env P) (fun j => env (v j)) (env S) := by
  simp only [tupleFixed,TupleFixed,Source.Formula.iff,Formula.Realize,finite_conjunction,
    ForcingStabilizer.fixed_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h g => ⟨(h g).1,(h g).2⟩,fun h g => ⟨(h g).mp,(h g).mpr⟩⟩

theorem exists_tuple (hM : FirstOrder.Theory.Models M nativeZF) (aenv : Fin 7 → M.Carrier .set)
    {I K B w G F : M.Carrier .set}
    (hp : Presentation (aenv 0) I K B w (aenv 1) (aenv 2) (aenv 3) (aenv 4) (aenv 5) (aenv 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingNormalFilter.Normal I G F)
    {n : Nat} (v : Fin n → M.Carrier .set)
    (hv : ∀ j, ForcingHS.HS actionFormula aenv G (aenv 6) F (v j)) :
    ∃ S, ForcingConjugationGraph.Subgroup I G S ∧
      (Definitional.Project.FirstOrderSemantics.reduct M).mem S F ∧ TupleFixed aenv G (aenv 6) v S := by
  induction n with
  | zero =>
    refine ⟨G,ForcingSupportFilter.top_subgroup hM hG,hF.1,?_⟩
    intro g
    exact ⟨fun hg => ⟨hg,fun j => Fin.elim0 j⟩,And.left⟩
  | succ n ih =>
    obtain ⟨S,hS,hSF,hST⟩ := ih (fun j => v j.castSucc) (fun j => hv j.castSucc)
    obtain ⟨T,hT,hTF⟩ := ForcingHS.symmetric_of_hs (hv (Fin.last n))
    have hTG := ForcingProductStabilizer.subgroup hM aenv hp hG (ForcingHS.isName (hv (Fin.last n))) hT
    obtain ⟨U,hU⟩ := SetTheory.KP.intersection_exists_d
      (SetTheory.ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) S T
    refine ⟨U,ForcingSupportIntersection.subgroup_intersection hM hG hS hTG hU,
      hF.2.2.1 S T U hSF hTF hU,?_⟩
    intro g
    constructor
    · intro hg
      obtain ⟨hgS,hgT⟩ := (hU g).mp hg
      obtain ⟨hgG,hrest⟩ := (hST g).mp hgS
      have hlast := ((hT g).mp hgT).2
      refine ⟨hgG,?_⟩
      intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · exact hlast
      · exact hrest i
    · rintro ⟨hgG,hfixed⟩
      exact (hU g).mpr ⟨(hST g).mpr ⟨hgG,fun j => hfixed j.castSucc⟩,
        (hT g).mpr ⟨hgG,hfixed (Fin.last n)⟩⟩

theorem fixed_action (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {aenv : Fin 7 → M.Carrier .set} {G S g a : M.Carrier .set} {v : Fin n → M.Carrier .set}
    (hS : TupleFixed aenv G (aenv 6) v S)
    (hg : (Definitional.Project.FirstOrderSemantics.reduct M).mem g S)
    (ha : MapRel actionFormula aenv g a) : ∀ j, Action (aenv 6) a (v j) (v j) := by
  intro j
  obtain ⟨b,hb,hfixed⟩ := ((hS g).mp hg).2 j
  have hba := ForcingProductFamily.unique hM ((mapRel_action aenv g b).mp hb) ((mapRel_action aenv g a).mp ha)
  exact hba ▸ hfixed

/-- The subgroup used by source `separate`: it fixes the original name and
all parameters simultaneously, without assuming a common support exists. -/
theorem separation_support (hM : FirstOrder.Theory.Models M nativeZF) (aenv : Fin 7 → M.Carrier .set)
    {I K B w G F sigma : M.Carrier .set}
    (hp : Presentation (aenv 0) I K B w (aenv 1) (aenv 2) (aenv 3) (aenv 4) (aenv 5) (aenv 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingNormalFilter.Normal I G F)
    (hs : ForcingHS.HS actionFormula aenv G (aenv 6) F sigma)
    {n : Nat} (v : Fin n → M.Carrier .set)
    (hv : ∀ j, ForcingHS.HS actionFormula aenv G (aenv 6) F (v j)) :
    ∃ S, ForcingConjugationGraph.Subgroup I G S ∧
      (Definitional.Project.FirstOrderSemantics.reduct M).mem S F ∧
      ∀ g, (Definitional.Project.FirstOrderSemantics.reduct M).mem g S →
        ∀ a, MapRel actionFormula aenv g a →
          Action (aenv 6) a sigma sigma ∧ ∀ j, Action (aenv 6) a (v j) (v j) := by
  have htuple : ∀ j, ForcingHS.HS actionFormula aenv G (aenv 6) F (Fin.lastCases sigma v j) := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [Fin.lastCases_last] using hs
    · simpa only [Fin.lastCases_castSucc] using hv i
  obtain ⟨S,hS,hSF,hfixed⟩ := exists_tuple hM aenv hp hG hF (Fin.lastCases sigma v) htuple
  refine ⟨S,hS,hSF,?_⟩
  intro g hg a ha
  have h := fixed_action hM hfixed hg ha
  constructor
  · simpa only [Fin.lastCases_last] using h (Fin.last n)
  · intro j
    simpa only [Fin.lastCases_castSucc] using h j.castSucc

def sentence {n m : Nat} (rho : Fin 7 → Fin m) (I K B w G F : Fin m) (v : Fin n → Fin m) : Source.Sentence :=
  ((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp
    ((ForcingLabelPermutations.carrier I G).imp ((ForcingNormalFilter.normal I G F).imp
      ((tupleHS rho G (rho 6) F v).imp (.ex
        ((ForcingConjugationGraph.subgroup I.castSucc G.castSucc (Fin.last m)).conj
          ((Formula.mem (Fin.last m) F.castSucc).conj
            (tupleFixed (paramsUp rho) G.castSucc (rho 6).castSucc (fun j => (v j).castSucc) (Fin.last m))))))))).close

theorem models {n m : Nat} (rho : Fin 7 → Fin m) (I K B w G F : Fin m) (v : Fin n → Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence (sentence rho I K B w G F v)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp hG hF hv
  obtain ⟨S,hS,hSF,hST⟩ := exists_tuple hM (fun j => env (rho j))
    ((ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hp)
    ((ForcingLabelPermutations.carrier_semantics (M := M) env I G).mp hG)
    ((ForcingNormalFilter.normal_semantics (M := M) env I G F).mp hF)
    (fun j => env (v j)) ((tupleHS_semantics (M := M) env rho G (rho 6) F v).mp hv)
  refine ⟨S,?_,?_,?_⟩
  · apply (ForcingConjugationGraph.subgroup_semantics (M := M) (Fin.lastCases S env)
      I.castSucc G.castSucc (Fin.last m)).mpr
    simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hS
  · simpa only [Formula.Realize,Fin.lastCases_last,Fin.lastCases_castSucc,
      Definitional.Project.FirstOrderSemantics.reduct] using hSF
  · apply (tupleFixed_semantics (M := M) (Fin.lastCases S env) (paramsUp rho) G.castSucc (rho 6).castSucc
      (fun j => (v j).castSucc) (Fin.last m)).mpr
    simpa only [paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc] using hST

theorem kernel_certificate {n m : Nat} (rho : Fin 7 → Fin m) (I K B w G F : Fin m) (v : Fin n → Fin m) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (sentence rho I K B w G F v)) :=
  ModelTransfer.derives (fun _ hM => models rho I K B w G F v hM)

end PPAC.Migration.ForcingTupleStabilizer
