/- Pinned MergerCones.wordHeight:371 / wordCost:376, actual letter parameters.
Construct theta=1/4+letterHeight/4, sigma=1-theta and factor=min(1/8,letterCost/4).
All graphs use native definable-function construction and existing cut arithmetic.
No new scalar oracle, real field, recursion, finite fold or object Choice. -/
import PPAC.Migration.ConstructionMergerHeightCost
import PPAC.Migration.ConstructionProbeHeightIntervalGraphs

namespace PPAC.Migration.ConstructionMergerWordParameters
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts (Subset Cut CutCarrier)
open ConstructionCutAddition (SumCut)
open ConstructionProbeIntervals (Strict)
open ConstructionProbeHeightIntervalGraphs (project)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Source 1/4+h/4 is positive and strictly below the SAME unit cut. -/
theorem theta_bounds (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q one two three four unit quarter h qh theta : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : ConstructionFractionOrder.Carrier w Q)
    (hd : ConstructionBaseWeights.Digits w one two three)
    (hf : (Project.FirstOrderSemantics.reduct M).SuccessorOf four three)
    (hfw : (Project.FirstOrderSemantics.reduct M).mem four w)
    (hUnit : Cut hM w Q unit) (hUnitN : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p unit)
    (hH : Cut hM w Q h) (hHUnit : Strict h unit)
    (hQuarter : ConstructionCutDivision.Value hM w Q four unit quarter)
    (hQH : ConstructionCutDivision.Value hM w Q four h qh)
    (hTheta : SumCut hM w Q quarter qh theta) :
    Cut hM w Q theta ∧ ConstructionCutWeights.BoundedPositive theta unit := by
  have hfp : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p four := ⟨three,hf.predecessor_mem⟩
  have hQuarterCut := ConstructionCutDivision.value_cut hw hQ hfw hfp hUnit hQuarter
  have hQuarterN := (ConstructionCutDivision.nonempty_iff hw hQ hfw hfp hUnit hQuarter).mpr hUnitN
  have hQHCut := ConstructionCutDivision.value_cut hw hQ hfw hfp hH hQH
  have hSmall := (ConstructionCutDivision.strict_iff hw hQ hfw hfp hH hUnit hQH hQuarter).mpr hHUnit
  obtain ⟨half,hHalf,hDouble⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hQuarterCut hQuarterCut
  obtain ⟨full,hFull,hFour⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hHalf hHalf
  have he := ConstructionCutQuarterSum.quarter_fourfold hM hw hQ hd hf hfw hUnit hQuarterCut hHalf hFull hQuarter hDouble hFour
  have hHalfN : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p half := by
    obtain ⟨p,hp⟩ := hQuarterN
    exact ⟨p,(ConstructionCutArithmetic.sum_contains hQuarterCut hQuarterCut hDouble).1 p hp⟩
  have hHalfUnit : Strict half unit := he ▸ ConstructionProbeIntervals.sum_positive hM hw hQ hHalf hHalf hHalfN hFour
  have hThetaHalf := (ConstructionCutDifference.sum_strict_iff hM hw hQ hQHCut hQuarterCut hQuarterCut
    (ConstructionCutArithmetic.sum_comm hM hw hTheta) hDouble).mpr hSmall
  have hThetaN : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p theta := by
    obtain ⟨p,hp⟩ := hQuarterN
    exact ⟨p,(ConstructionCutArithmetic.sum_contains hQuarterCut hQHCut hTheta).1 p hp⟩
  exact ⟨ConstructionCutAssociativity.sum_is_cut hM hw hQ hQuarterCut hQHCut hTheta,
    hThetaN,ConstructionProbeIntervals.le_strict_trans hThetaHalf.1 hHalfUnit⟩

/-- Exact source letter parameters, with both true complement equations. -/
def Recipe (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q four unit quarter eighth H C s theta sigma factor : M.Carrier .set) : Prop :=
  ∃ h c qh qc, PureKuratowski.PairMember M s h H ∧ PureKuratowski.PairMember M s c C ∧
    ConstructionCutDivision.Value hM w Q four h qh ∧ ConstructionCutDivision.Value hM w Q four c qc ∧
    SumCut hM w Q quarter qh theta ∧ ConstructionCutDifference.Value hM w Q theta unit sigma ∧
    SumCut hM w Q theta sigma unit ∧ ConstructionCutMinimum.Value eighth qc factor

def recipe {m : Nat} (w Q four unit quarter eighth H C s theta sigma factor : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  H.succ.succ.succ.succ s.succ.succ.succ.succ 3)) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge C.succ.succ.succ.succ s.succ.succ.succ.succ 2)) (.conj
  (ConstructionCutDivision.value w.succ.succ.succ.succ Q.succ.succ.succ.succ
  four.succ.succ.succ.succ 3 1) (.conj (ConstructionCutDivision.value w.succ.succ.succ.succ
  Q.succ.succ.succ.succ four.succ.succ.succ.succ 2 0) (.conj (ConstructionCutAddition.sumCut
  w.succ.succ.succ.succ Q.succ.succ.succ.succ quarter.succ.succ.succ.succ 1
  theta.succ.succ.succ.succ) (.conj (ConstructionCutDifference.value w.succ.succ.succ.succ
  Q.succ.succ.succ.succ theta.succ.succ.succ.succ unit.succ.succ.succ.succ
  sigma.succ.succ.succ.succ) (.conj (ConstructionCutAddition.sumCut w.succ.succ.succ.succ
  Q.succ.succ.succ.succ theta.succ.succ.succ.succ sigma.succ.succ.succ.succ
  unit.succ.succ.succ.succ) (ConstructionCutMinimum.value eighth.succ.succ.succ.succ 0
  factor.succ.succ.succ.succ))))))))))))

theorem recipe_freeClosed {m : Nat} (w Q four unit quarter eighth H C s theta sigma factor : Fin m) :
    (recipe w Q four unit quarter eighth H C s theta sigma factor).FreeClosed := by
  simp -implicitDefEqProofs [recipe,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionCutDivision.value_freeClosed,ConstructionCutDifference.value_freeClosed,
    ConstructionCutAddition.sumCut_freeClosed,ConstructionCutMinimum.value_freeClosed]

theorem recipe_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (w Q four unit quarter eighth H C s theta sigma factor : Fin m) :
    Project.Formula.satisfies env (recipe w Q four unit quarter eighth H C s theta sigma factor) ↔
      Recipe hM (env.bound w) (env.bound Q) (env.bound four) (env.bound unit) (env.bound quarter) (env.bound eighth)
        (env.bound H) (env.bound C) (env.bound s) (env.bound theta) (env.bound sigma) (env.bound factor) := by
  simp only [recipe,Recipe,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionCutDivision.value_semantics hM,ConstructionCutDifference.value_semantics hM,
    ConstructionCutAddition.sumCut_semantics hM,ConstructionCutMinimum.value_semantics]
  rfl

theorem recipe_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q four unit quarter eighth S R H C s theta sigma factor theta' sigma' factor' : M.Carrier .set}
    (hH : MapsTo S R H) (hC : MapsTo S R C)
    (h : Recipe hM w Q four unit quarter eighth H C s theta sigma factor)
    (h' : Recipe hM w Q four unit quarter eighth H C s theta' sigma' factor') :
    theta = theta' ∧ sigma = sigma' ∧ factor = factor' := by
  obtain ⟨a,c,qh,qc,hha,hcc,hqh,hqc,ht,hs,_,hb⟩ := h
  obtain ⟨a',c',qh',qc',hha',hcc',hqh',hqc',ht',hs',_,hb'⟩ := h'
  have he := ForcingConditionGraphs.function_unique hH.1 hha hha';subst a'
  have he := ForcingConditionGraphs.function_unique hC.1 hcc hcc';subst c'
  have he := ConstructionCutDivision.value_unique hM hqh hqh';subst qh'
  have he := ConstructionCutDivision.value_unique hM hqc hqc';subst qc'
  have he := ConstructionCutAddition.sum_unique hM ht ht';subst theta'
  exact ⟨rfl,ConstructionCutDifference.value_unique hM hs hs',ConstructionCutMinimum.value_unique hM hb hb'⟩

theorem recipe_bounds (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R S one two three four unit quarter eighth H C s theta sigma factor : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hd : ConstructionBaseWeights.Digits w one two three)
    (hf : (Project.FirstOrderSemantics.reduct M).SuccessorOf four three)
    (hfw : (Project.FirstOrderSemantics.reduct M).mem four w)
    (hUnit : Cut hM w Q unit) (hUnitN : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p unit)
    (hQuarter : ConstructionCutDivision.Value hM w Q four unit quarter)
    (hEighth : Cut hM w Q eighth) (hEighthN : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p eighth)
    (hH : MapsTo S R H) (hC : MapsTo S R C)
    (hHB : ConstructionCutWeights.RangeBound unit H) (hCB : ConstructionProbeGateCap.Bounds unit C)
    (h : Recipe hM w Q four unit quarter eighth H C s theta sigma factor) :
    Cut hM w Q theta ∧ Cut hM w Q sigma ∧ Cut hM w Q factor ∧
      ConstructionCutWeights.BoundedPositive theta unit ∧
      (∃ p, (Project.FirstOrderSemantics.reduct M).mem p sigma) ∧
      (∃ p, (Project.FirstOrderSemantics.reduct M).mem p factor) ∧ Subset factor eighth := by
  obtain ⟨a,c,qh,qc,hha,hcc,hqh,hqc,ht,hs,hSum,hb⟩ := h
  have ha := (hR a).mp (hH.2 s a hha)
  have hc := (hR c).mp (hC.2 s c hcc)
  have htBounds := theta_bounds hM hw hQ hd hf hfw hUnit hUnitN ha (hHB s a hha).2 hQuarter hqh ht
  have hSigma := ConstructionCutDifference.value_cut hM hw hQ hUnit hs
  have hQCCut := ConstructionCutDivision.value_cut hw hQ hfw ⟨three,hf.predecessor_mem⟩ hc hqc
  have hQCNonempty := (ConstructionCutDivision.nonempty_iff hw hQ hfw ⟨three,hf.predecessor_mem⟩ hc hqc).mpr (hCB s c hcc).1
  have hFactor : Cut hM w Q factor := by
    rcases ConstructionCutMinimum.value_cases hM hw hQ hEighth hQCCut hb with he | he
    · exact he.symm ▸ hEighth
    · exact he.symm ▸ hQCCut
  have hSigmaN : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p sigma := by
    obtain ⟨gap,_,hg,_,_,hN⟩ := ConstructionCutDifference.exists_difference hM hw hQ htBounds.1 hUnit htBounds.2.2.1
    have he := ConstructionCutDifference.value_unique hM hg hs
    exact he ▸ hN htBounds.2.2.2
  exact ⟨htBounds.1,hSigma,hFactor,htBounds.2,hSigmaN,
    ConstructionCutMinimum.value_nonempty hM hw hQ hEighth hQCCut hb hEighthN hQCNonempty,
    (ConstructionCutMinimum.value_bounds hb).1⟩

theorem exists_recipe (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R S one two three four unit quarter eighth H C s : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hd : ConstructionBaseWeights.Digits w one two three)
    (hf : (Project.FirstOrderSemantics.reduct M).SuccessorOf four three)
    (hfw : (Project.FirstOrderSemantics.reduct M).mem four w)
    (hUnit : Cut hM w Q unit) (hUnitN : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p unit)
    (hQuarter : ConstructionCutDivision.Value hM w Q four unit quarter)
    (hEighth : Cut hM w Q eighth) (hH : MapsTo S R H) (hC : MapsTo S R C)
    (hHB : ConstructionCutWeights.RangeBound unit H) (hs : (Project.FirstOrderSemantics.reduct M).mem s S) :
    ∃ theta sigma factor, Recipe hM w Q four unit quarter eighth H C s theta sigma factor := by
  obtain ⟨a,hha,_⟩ := hH.1.2 s hs
  obtain ⟨c,hcc,_⟩ := hC.1.2 s hs
  have ha := (hR a).mp (hH.2 s a hha)
  have hc := (hR c).mp (hC.2 s c hcc)
  have hQuarterCut := ConstructionCutDivision.value_cut hw hQ hfw ⟨three,hf.predecessor_mem⟩ hUnit hQuarter
  obtain ⟨qh,hqh⟩ := ConstructionCutDivision.exists_value hM w Q four a
  obtain ⟨qc,hqc⟩ := ConstructionCutDivision.exists_value hM w Q four c
  have hQHCut := ConstructionCutDivision.value_cut hw hQ hfw ⟨three,hf.predecessor_mem⟩ ha hqh
  have hQCCut := ConstructionCutDivision.value_cut hw hQ hfw ⟨three,hf.predecessor_mem⟩ hc hqc
  obtain ⟨theta,_,ht⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hQuarterCut hQHCut
  have htBounds := theta_bounds hM hw hQ hd hf hfw hUnit hUnitN ha (hHB s a hha).2 hQuarter hqh ht
  obtain ⟨sigma,_,hsigma,hSum,_,_⟩ := ConstructionCutDifference.exists_difference hM hw hQ htBounds.1 hUnit htBounds.2.2.1
  obtain ⟨factor,_,hb⟩ := ConstructionCutMinimum.exists_minimum hM hw hQ hEighth hQCCut
  exact ⟨theta,sigma,factor,a,c,qh,qc,hha,hcc,hqh,hqc,ht,hsigma,hSum,hb⟩

def Selected (i : Fin 3) (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q four unit quarter eighth H C s value : M.Carrier .set) : Prop :=
  ∃ theta sigma factor, Recipe hM w Q four unit quarter eighth H C s theta sigma factor ∧ value = project i theta sigma factor

def Graph (i : Fin 3) (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q four unit quarter eighth S H C G : M.Carrier .set) : Prop := ∀ s value,
  PureKuratowski.PairMember M s value G ↔ (Project.FirstOrderSemantics.reduct M).mem s S ∧
    Selected i hM w Q four unit quarter eighth H C s value

def selected {m : Nat} (i : Fin 3) (w Q four unit quarter eighth H C s value : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.conj
    (recipe w.succ.succ.succ Q.succ.succ.succ four.succ.succ.succ unit.succ.succ.succ quarter.succ.succ.succ
      eighth.succ.succ.succ H.succ.succ.succ C.succ.succ.succ s.succ.succ.succ 2 1 0)
    (Project.Formula.extensionalEq (.bound value.succ.succ.succ) (.bound (project i (2 : Fin (m+3)) 1 0))))))

theorem selected_freeClosed {m : Nat} (i : Fin 3) (w Q four unit quarter eighth H C s value : Fin m) :
    (selected i w Q four unit quarter eighth H C s value).FreeClosed := by
  simp -implicitDefEqProofs [selected,Definitional.Formula.FreeClosed,recipe_freeClosed]

theorem selected_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (i : Fin 3)
    (w Q four unit quarter eighth H C s value : Fin m) :
    Project.Formula.satisfies env (selected i w Q four unit quarter eighth H C s value) ↔
      Selected i hM (env.bound w) (env.bound Q) (env.bound four) (env.bound unit) (env.bound quarter)
        (env.bound eighth) (env.bound H) (env.bound C) (env.bound s) (env.bound value) := by
  simp only [selected,Selected,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    recipe_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> simp only [project,h0,h1,ite_true,ite_false] <;> rfl

def graph {m : Nat} (i : Fin 3) (w Q four unit quarter eighth S H C G : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge G.succ.succ 1 0))
    (.conj (.mem (.bound 1) (.bound S.succ.succ))
      (selected i w.succ.succ Q.succ.succ four.succ.succ unit.succ.succ quarter.succ.succ
        eighth.succ.succ H.succ.succ C.succ.succ 1 0))))

theorem graph_freeClosed {m : Nat} (i : Fin 3) (w Q four unit quarter eighth S H C G : Fin m) :
    (graph i w Q four unit quarter eighth S H C G).FreeClosed := by
  simp -implicitDefEqProofs [graph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,selected_freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (i : Fin 3)
    (w Q four unit quarter eighth S H C G : Fin m) :
    Project.Formula.satisfies env (graph i w Q four unit quarter eighth S H C G) ↔
      Graph i hM (env.bound w) (env.bound Q) (env.bound four) (env.bound unit) (env.bound quarter)
        (env.bound eighth) (env.bound S) (env.bound H) (env.bound C) (env.bound G) := by
  simp only [graph,Graph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,selected_semantics hM]
  rfl

theorem selected_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q four unit quarter eighth S R H C s value value' : M.Carrier .set} (i : Fin 3)
    (hH : MapsTo S R H) (hC : MapsTo S R C)
    (h : Selected i hM w Q four unit quarter eighth H C s value)
    (h' : Selected i hM w Q four unit quarter eighth H C s value') : value = value' := by
  obtain ⟨theta,sigma,factor,hRecipe,hValue⟩ := h
  obtain ⟨theta',sigma',factor',hRecipe',hValue'⟩ := h'
  obtain ⟨he1,he2,he3⟩ := recipe_unique hM hH hC hRecipe' hRecipe
  subst theta';subst sigma';subst factor'
  exact hValue.trans hValue'.symm

theorem selected_value (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q four unit quarter eighth S R H C s value theta sigma factor : M.Carrier .set} (i : Fin 3)
    (hH : MapsTo S R H) (hC : MapsTo S R C)
    (h : Selected i hM w Q four unit quarter eighth H C s value)
    (hr : Recipe hM w Q four unit quarter eighth H C s theta sigma factor) : value = project i theta sigma factor :=
  selected_unique hM i hH hC h ⟨theta,sigma,factor,hr,rfl⟩

theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q four unit quarter eighth S R H C : M.Carrier .set} (i : Fin 3)
    (hR : CutCarrier hM w Q R) (hH : MapsTo S R H) (hC : MapsTo S R C)
    (hTotal : ∀ s, (Project.FirstOrderSemantics.reduct M).mem s S → ∃ theta sigma factor,
      Recipe hM w Q four unit quarter eighth H C s theta sigma factor ∧
        Cut hM w Q theta ∧ Cut hM w Q sigma ∧ Cut hM w Q factor) :
    ∃ G, MapsTo S R G ∧ Graph i hM w Q four unit quarter eighth S H C G := by
  let schema : Project.BinarySchema 8 := {
    body := selected i 2 3 4 5 6 7 8 9 1 0
    freeClosed := selected_freeClosed _ _ _ _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 8 := {
    bound := Fin.cases w (Fin.cases Q (Fin.cases four (Fin.cases unit (Fin.cases quarter
      (Fin.cases eighth (Fin.cases H (fun _ => C))))))), free := fun _ => w }
  have he (s value : M.Carrier .set) : schema.denote env s value ↔ Selected i hM w Q four unit quarter eighth H C s value :=
    selected_semantics hM ((env.push s).push value) i 2 3 4 5 6 7 8 9 1 0
  obtain ⟨G,hG,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := S) (target := R) (by
      intro s hs
      obtain ⟨theta,sigma,factor,hRecipe,_,_,_⟩ := hTotal s hs
      exact ⟨project i theta sigma factor,(he _ _).mpr ⟨theta,sigma,factor,hRecipe,rfl⟩⟩) (by
      intro s _ v v' hv hv'
      exact selected_unique hM i hH hC ((he _ _).mp hv) ((he _ _).mp hv')) (by
      intro s v hs hv
      obtain ⟨theta,sigma,factor,hRecipe,hTheta,hSigma,hFactor⟩ := hTotal s hs
      have ev := selected_value hM i hH hC ((he _ _).mp hv) hRecipe
      apply (hR v).mpr
      rw [ev]
      by_cases h0 : i = 0
      · simpa [project,h0] using hTheta
      · by_cases h1 : i = 1
        · simpa [project,h0,h1] using hSigma
        · simpa [project,h0,h1] using hFactor)
  exact ⟨G,(ForcingSupportSize.native_mapsTo hM S R G).mpr hG,
    fun s v => (hGraph s v).trans (and_congr_right (fun _ => he s v))⟩

/-- All constants and all three actual parameter graphs, from source bounds. -/
theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R S H C one unit : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (ho : (Project.FirstOrderSemantics.reduct M).mem one w)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hUnit : Cut hM w Q unit) (hUnitN : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p unit)
    (hH : MapsTo S R H) (hC : MapsTo S R C)
    (hHB : ConstructionCutWeights.RangeBound unit H) (hCB : ConstructionProbeGateCap.Bounds unit C) :
    ∃ two three four five six seven eight quarter eighth O V B,
      ConstructionBaseWeights.Digits w one two three ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf four three ∧ (Project.FirstOrderSemantics.reduct M).mem four w ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf five four ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf six five ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf seven six ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf eight seven ∧ (Project.FirstOrderSemantics.reduct M).mem eight w ∧
      ConstructionCutDivision.Value hM w Q four unit quarter ∧ ConstructionCutDivision.Value hM w Q eight unit eighth ∧
      (Project.FirstOrderSemantics.reduct M).mem quarter R ∧ (Project.FirstOrderSemantics.reduct M).mem eighth R ∧
      MapsTo S R O ∧ MapsTo S R V ∧ MapsTo S R B ∧
      Graph 0 hM w Q four unit quarter eighth S H C O ∧
      Graph 1 hM w Q four unit quarter eighth S H C V ∧
      Graph 2 hM w Q four unit quarter eighth S H C B ∧
      (∀ s theta sigma factor, PureKuratowski.PairMember M s theta O →
        PureKuratowski.PairMember M s sigma V → PureKuratowski.PairMember M s factor B →
        Recipe hM w Q four unit quarter eighth H C s theta sigma factor) ∧
      ConstructionCutWeights.RangeBound unit O ∧
      (∀ s sigma, PureKuratowski.PairMember M s sigma V → ∃ p, (Project.FirstOrderSemantics.reduct M).mem p sigma) ∧
      ConstructionProbeGateCap.Bounds eighth B := by
  obtain ⟨two,htwo,htwow⟩ := hw.1.2 one ho
  obtain ⟨three,hthree,hthreew⟩ := hw.1.2 two htwow
  obtain ⟨four,hfour,hfourw⟩ := hw.1.2 three hthreew
  obtain ⟨five,hfive,hfivew⟩ := hw.1.2 four hfourw
  obtain ⟨six,hsix,hsixw⟩ := hw.1.2 five hfivew
  obtain ⟨seven,hseven,hsevenw⟩ := hw.1.2 six hsixw
  obtain ⟨eight,height,heighw⟩ := hw.1.2 seven hsevenw
  have hd : ConstructionBaseWeights.Digits w one two three := ⟨ho,htwow,hthreew,hone,htwo,hthree⟩
  obtain ⟨quarter,hQuarter⟩ := ConstructionCutDivision.exists_value hM w Q four unit
  obtain ⟨eighth,hEighth⟩ := ConstructionCutDivision.exists_value hM w Q eight unit
  have hQuarterCut := ConstructionCutDivision.value_cut hw hQ hfourw ⟨three,hfour.predecessor_mem⟩ hUnit hQuarter
  have hEighthCut := ConstructionCutDivision.value_cut hw hQ heighw ⟨seven,height.predecessor_mem⟩ hUnit hEighth
  have hEighthN := (ConstructionCutDivision.nonempty_iff hw hQ heighw ⟨seven,height.predecessor_mem⟩ hUnit hEighth).mpr hUnitN
  have hTotal (s) (hs : (Project.FirstOrderSemantics.reduct M).mem s S) : ∃ theta sigma factor,
      Recipe hM w Q four unit quarter eighth H C s theta sigma factor ∧
        Cut hM w Q theta ∧ Cut hM w Q sigma ∧ Cut hM w Q factor := by
    obtain ⟨theta,sigma,factor,hr⟩ := exists_recipe hM hw hQ hR hd hfour hfourw hUnit hUnitN hQuarter hEighthCut hH hC hHB hs
    have hb := recipe_bounds hM hw hQ hR hd hfour hfourw hUnit hUnitN hQuarter hEighthCut hEighthN hH hC hHB hCB hr
    exact ⟨theta,sigma,factor,hr,hb.1,hb.2.1,hb.2.2.1⟩
  obtain ⟨O,hO,hOG⟩ := exists_graph hM 0 hR hH hC hTotal
  obtain ⟨V,hV,hVG⟩ := exists_graph hM 1 hR hH hC hTotal
  obtain ⟨B,hB,hBG⟩ := exists_graph hM 2 hR hH hC hTotal
  have hLaws (s theta sigma factor) (ho : PureKuratowski.PairMember M s theta O)
      (hv : PureKuratowski.PairMember M s sigma V) (hb : PureKuratowski.PairMember M s factor B) :
      Recipe hM w Q four unit quarter eighth H C s theta sigma factor := by
    obtain ⟨hs,hsel⟩ := (hOG s theta).mp ho
    obtain ⟨theta',sigma',factor',hr,_,_,_⟩ := hTotal s hs
    have he1 := selected_value hM 0 hH hC hsel hr
    have he2 := selected_value hM 1 hH hC ((hVG s sigma).mp hv).2 hr
    have he3 := selected_value hM 2 hH hC ((hBG s factor).mp hb).2 hr
    simp [project] at he1 he2 he3
    subst theta';subst sigma';subst factor'
    exact hr
  refine ⟨two,three,four,five,six,seven,eight,quarter,eighth,O,V,B,hd,hfour,hfourw,hfive,hsix,hseven,height,heighw,hQuarter,hEighth,
    (hR quarter).mpr hQuarterCut,(hR eighth).mpr hEighthCut,hO,hV,hB,hOG,hVG,hBG,hLaws,?_,?_,?_⟩
  · intro s theta ho
    have hs := ForcingConditionGraphs.function_input hO.1 ho
    obtain ⟨sigma,hv,_⟩ := hV.1.2 s hs
    obtain ⟨factor,hb,_⟩ := hB.1.2 s hs
    exact (recipe_bounds hM hw hQ hR hd hfour hfourw hUnit hUnitN hQuarter hEighthCut hEighthN hH hC hHB hCB (hLaws s theta sigma factor ho hv hb)).2.2.2.1
  · intro s sigma hv
    have hs := ForcingConditionGraphs.function_input hV.1 hv
    obtain ⟨theta,ho,_⟩ := hO.1.2 s hs
    obtain ⟨factor,hb,_⟩ := hB.1.2 s hs
    exact (recipe_bounds hM hw hQ hR hd hfour hfourw hUnit hUnitN hQuarter hEighthCut hEighthN hH hC hHB hCB (hLaws s theta sigma factor ho hv hb)).2.2.2.2.1
  · intro s factor hb
    have hs := ForcingConditionGraphs.function_input hB.1 hb
    obtain ⟨theta,ho,_⟩ := hO.1.2 s hs
    obtain ⟨sigma,hv,_⟩ := hV.1.2 s hs
    exact (recipe_bounds hM hw hQ hR hd hfour hfourw hUnit hUnitN hQuarter hEighthCut hEighthN hH hC hHB hCB (hLaws s theta sigma factor ho hv hb)).2.2.2.2.2

end PPAC.Migration.ConstructionMergerWordParameters
