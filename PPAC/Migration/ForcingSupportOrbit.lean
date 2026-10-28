/- Pinned LocalQuotients.support_descent:158-169: the actual root-subgroup
indexed name/activation families, their equivariance, and identity entry.
Reuse native functional images/graphs, actual Product action and HS closure. -/
import PPAC.Migration.ForcingActiveEquality
import PPAC.Migration.ForcingReplacementOrbit

namespace PPAC.Migration.ForcingSupportOrbit
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingMapConditions (MapRel)
open ForcingStabilizer (Action)
open ForcingConditionGraphs (Permutation)
open ForcingReplacementOrbit (Moved moved moved_semantics moved_unique)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def ConditionMoved (v : Fin 7 → M.Carrier .set) (g z out : M.Carrier .set) : Prop :=
  ∃ A, MapRel actionFormula v g A ∧ PureKuratowski.PairMember M z out A

def conditionMoved {k : Nat} (rho : Fin 7 → Fin k) (g z out : Fin k) : Formula k :=
  .ex ((ReplacementPredicates.rel actionFormula (paramsUp rho) g.castSucc (Fin.last k)).conj
    (Source.SetLanguage.edge (Fin.last k) z.castSucc out.castSucc))

theorem conditionMoved_semantics {k : Nat} (env : Fin k → M.Carrier .set)
    (rho : Fin 7 → Fin k) (g z out : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (conditionMoved rho g z out) ↔
      ConditionMoved (fun i => env (rho i)) (env g) (env z) (env out) := by
  simp only [conditionMoved,ConditionMoved,Formula.Realize,
    ForcingMapConditions.rel_semantics (M := M),KuratowskiZF.source_edge,
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def NameFamily (v : Fin 7 → M.Carrier .set) (H sigma f : M.Carrier .set) : Prop :=
  ∀ g out, PureKuratowski.PairMember M g out f ↔
    (Project.FirstOrderSemantics.reduct M).mem g H ∧ Moved v g sigma out

def ActivationFamily (v : Fin 7 → M.Carrier .set) (H z a : M.Carrier .set) : Prop :=
  ∀ g out, PureKuratowski.PairMember M g out a ↔
    (Project.FirstOrderSemantics.reduct M).mem g H ∧ ConditionMoved v g z out

theorem condition_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {v : Fin 7 → M.Carrier .set} {g z x y : M.Carrier .set}
    (hx : ConditionMoved v g z x) (hy : ConditionMoved v g z y) : x = y := by
  obtain ⟨A,hA,hx⟩ := hx
  obtain ⟨B,hB,hy⟩ := hy
  have e := ForcingProductFamily.unique hM ((mapRel_action _ _ _).mp hA) ((mapRel_action _ _ _).mp hB)
  subst B
  exact ForcingConditionGraphs.function_unique
    (ForcingProductFamily.action_permutation ((mapRel_action _ _ _).mp hA)).1.1 hx hy

theorem condition_mem {v : Fin 7 → M.Carrier .set} {g z x : M.Carrier .set}
    (hx : ConditionMoved v g z x) : (Project.FirstOrderSemantics.reduct M).mem x (v 6) := by
  obtain ⟨A,hA,hx⟩ := hx
  exact (ForcingProductFamily.action_permutation ((mapRel_action _ _ _).mp hA)).1.2 z x hx

/-- Both original families are constructed as exact internal graphs. -/
theorem exists_families (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G H sigma z : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G)
    (hH : (Project.FirstOrderSemantics.reduct M).MemberSubset H G)
    (hz : (Project.FirstOrderSemantics.reduct M).mem z (v 6)) :
    ∃ f a, NameFamily v H sigma f ∧ ActivationFamily v H z a := by
  obtain ⟨seed,hSeed⟩ := ForcingWithTopCarrier.exists_single hM sigma
  obtain ⟨O,hO⟩ := ForcingReplacementOrbit.exists_orbit hM v hp hG seed
  let inputs : Fin 8 → M.Carrier .set := Fin.lastCases sigma v
  let ra : Fin 7 → Fin 10 := fun i => i.castSucc.castSucc.castSucc
  let gg : Fin 10 := (Fin.last 8).castSucc
  let ss : Fin 10 := (Fin.last 7).castSucc.castSucc
  let oo : Fin 10 := Fin.last 9
  let matrix := moved ra gg ss oo
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 8 :=
    { bound := fun j => inputs j.rev, free := fun _ => H }
  have hr g out : (ProjectSyntax.binary matrix).denote env g out ↔ Moved v g sigma out := by
    rw [ForcingMapConditions.binary_semantics hM matrix inputs H g out]
    simpa only [MapRel,inputs,matrix,ra,gg,ss,oo,Fin.lastCases_last,Fin.lastCases_castSucc] using
      moved_semantics (M := M) (Fin.lastCases out (Fin.lastCases g inputs)) ra gg ss oo
  obtain ⟨f,_,hf⟩ := ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) (ProjectSyntax.binary matrix) env
    (source := H) (target := O)
    (fun g hg => by
      obtain ⟨A,hA⟩ := ForcingProductFamily.exists_action hM hp ((hG g).mp (hH g hg))
      obtain ⟨out,hout⟩ := ForcingNameConjugacy.exists_action hM (ForcingProductFamily.action_permutation hA).1 sigma
      exact ⟨out,(hr g out).mpr ⟨A,(mapRel_action v g A).mpr hA,hout⟩⟩)
    (fun _ _ _ _ hx hy => moved_unique hM ((hr _ _).mp hx) ((hr _ _).mp hy))
    (fun g out hg hm => (hO out).mpr ⟨g,hH g hg,sigma,(hSeed sigma).mpr rfl,(hr g out).mp hm⟩)
  have hNF : NameFamily v H sigma f := fun g out => (hf g out).trans (and_congr Iff.rfl (hr g out))
  let inputsA : Fin 8 → M.Carrier .set := Fin.lastCases z v
  let matrixA := conditionMoved ra gg ss oo
  let envA : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 8 :=
    { bound := fun j => inputsA j.rev, free := fun _ => H }
  have hrA g out : (ProjectSyntax.binary matrixA).denote envA g out ↔ ConditionMoved v g z out := by
    rw [ForcingMapConditions.binary_semantics hM matrixA inputsA H g out]
    simpa only [MapRel,inputsA,matrixA,ra,gg,ss,oo,Fin.lastCases_last,Fin.lastCases_castSucc] using
      conditionMoved_semantics (M := M) (Fin.lastCases out (Fin.lastCases g inputsA)) ra gg ss oo
  obtain ⟨a,_,ha⟩ := ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) (ProjectSyntax.binary matrixA) envA
    (source := H) (target := v 6)
    (fun g hg => by
      obtain ⟨A,hA⟩ := ForcingProductFamily.exists_action hM hp ((hG g).mp (hH g hg))
      obtain ⟨out,hout,_⟩ := (ForcingProductFamily.action_permutation hA).1.1.2 z hz
      exact ⟨out,(hrA g out).mpr ⟨A,(mapRel_action v g A).mpr hA,hout⟩⟩)
    (fun _ _ _ _ hx hy => condition_unique hM ((hrA _ _).mp hx) ((hrA _ _).mp hy))
    (fun _ _ _ hm => condition_mem ((hrA _ _).mp hm))
  exact ⟨f,a,hNF,fun g out => (ha g out).trans (and_congr Iff.rfl (hrA g out))⟩

theorem family_HS (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G F H sigma f : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingNormalFilter.Normal I G F)
    (hH : (Project.FirstOrderSemantics.reduct M).MemberSubset H G)
    (hs : ForcingHS.HS actionFormula v G (v 6) F sigma) (hf : NameFamily v H sigma f) :
    ForcingCollectedHS.FamilyHS v G (v 6) F H f := by
  intro g out hg he
  obtain ⟨_,A,hA,hout⟩ := (hf g out).mp he
  exact ForcingPowerName.hs_move hM v hp hG hF ((hG g).mp (hH g hg)) hA hs hout

theorem activations {v : Fin 7 → M.Carrier .set} {H z a : M.Carrier .set}
    (ha : ActivationFamily v H z a) : ForcingMixLaws.Activations (v 6) H a :=
  fun g out _ he => condition_mem ((ha g out).mp he).2

theorem permutes (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G H sigma z f a : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hH : ForcingConjugationGraph.Subgroup I G H)
    (hz : (Project.FirstOrderSemantics.reduct M).mem z (v 6))
    (hf : NameFamily v H sigma f) (ha : ActivationFamily v H z a) :
    ForcingEquivariantMix.Permutes v H H f a := by
  intro g hg A hA i si t hi hfi hai
  obtain ⟨_,B,hB,hsi⟩ := (hf i si).mp hfi
  obtain ⟨_,B',hB',hzt⟩ := (ha i t).mp hai
  have eB := ForcingProductFamily.unique hM ((mapRel_action _ _ _).mp hB') ((mapRel_action _ _ _).mp hB)
  subst B'
  obtain ⟨j,hj,hcomp⟩ := hH.2.2.2 g i hg hi
  obtain ⟨C,hC⟩ := ForcingProductFamily.exists_action hM hp ((hG j).mp (hH.1 j hj))
  have hAactual := (mapRel_action _ _ _).mp hA
  have hBactual := (mapRel_action _ _ _).mp hB
  have hProd := ForcingProductFamily.multiplication hM hp ((hG i).mp (hH.1 i hi)) hcomp hAactual hBactual hC
  obtain ⟨sj,hsj⟩ := ForcingNameConjugacy.exists_action hM (ForcingProductFamily.action_permutation hAactual).1 si
  have ht := (ForcingProductFamily.action_permutation hBactual).1.2 z t hzt
  obtain ⟨b,htb,_⟩ := (ForcingProductFamily.action_permutation hAactual).1.1.2 t ht
  have hCrel := (mapRel_action v j C).mpr hC
  exact ⟨j,sj,b,hj,(hf j sj).mpr ⟨hj,C,hCrel,
    ForcingNameConjugacy.composition hM (ForcingProductFamily.action_permutation hAactual).1
      (ForcingProductFamily.action_permutation hBactual).1 hProd hsi hsj⟩,
    (ha j b).mpr ⟨hj,C,hCrel,(hProd z b).mpr ⟨hz,t,hzt,htb⟩⟩,hsj,htb⟩

theorem identity_members (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G H sigma z f a : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hH : ForcingConjugationGraph.Subgroup I G H)
    (hn : ForcingNames.IsName (v 6) sigma) (hz : (Project.FirstOrderSemantics.reduct M).mem z (v 6))
    (hf : NameFamily v H sigma f) (ha : ActivationFamily v H z a) :
    ∃ e, (Project.FirstOrderSemantics.reduct M).mem e H ∧
      PureKuratowski.PairMember M e sigma f ∧ PureKuratowski.PairMember M e z a := by
  obtain ⟨e,he,hId⟩ := hH.2.1
  obtain ⟨A,hA⟩ := ForcingProductFamily.exists_action hM hp ((hG e).mp (hH.1 e he))
  have hAI := ForcingProductFamily.identity hM hp hId hA
  have hAR := (mapRel_action v e A).mpr hA
  exact ⟨e,he,(hf e sigma).mpr ⟨he,A,hAR,
    ForcingConditionAction.name_identity hM (Source.SetLanguage.args2 (v 6) A) (0 : Fin 2) 1 hAI sigma hn⟩,
    (ha e z).mpr ⟨he,A,hAR,(hAI z z).mpr ⟨hz,rfl⟩⟩⟩

/-- Read the exact moved coordinates through the existing action, using its
uniqueness and the already constructed Cohen/diagram coordinate operations. -/
theorem moved_coordinates (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w g A d s z out : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hg : Permutation I g) (hA : MapRel actionFormula v g A)
    (hd : ForcingCohenConditions.Condition (v 2) w d) (hs : ForcingSupportSize.Injection (v 0) I s)
    (hz : ForcingSupportingRoot.Code z d s) (hzo : PureKuratowski.PairMember M z out A) :
    ∃ d' s', ForcingSupportSize.Injection (v 0) I s' ∧
      ConstructionDescentPlacement.ActualMoved (v 1) (v 2) w g d d' ∧
      ForcingConditionGraphs.CompositionGraph (v 0) g s s' ∧ ForcingSupportingRoot.Code out d' s' := by
  obtain ⟨s',hs',hsg⟩ := ForcingDiagramAction.exists_permute hM hg hs
  obtain ⟨f,q,d',hf,hfg,hq,hqg,hd',him,hmove⟩ :=
    ConstructionCohenCompatibility.exists_moved hM hp.1 hp.2.1 hg hd
  have hMoved : ConstructionDescentPlacement.ActualMoved (v 1) (v 2) w g d d' :=
    ⟨f,q,hf,hfg,hq,hqg,hd',him,hmove⟩
  obtain ⟨z',hz'⟩ := ForcingSupportingRoot.exists_code hM d' s'
  have hmoved := ForcingSupportingRoot.moved_code hM hp ((mapRel_action _ _ _).mp hA) hd hs hs' hMoved hsg hz hz'
  have e := ForcingConditionGraphs.function_unique
    (ForcingProductFamily.action_permutation ((mapRel_action _ _ _).mp hA)).1.1 hmoved hzo
  exact ⟨d',s',hs',hMoved,hsg,e ▸ hz'⟩

end PPAC.Migration.ForcingSupportOrbit
