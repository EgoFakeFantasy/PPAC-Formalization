/- Pinned MergerCones.copies_uniform_margin:337.
Combine the already constructed per-coordinate WHOLE-class bounds by native
formula-indexed omega induction and the existing binary Cut maximum.
No internal choice function, new finite fold/recursor or standardness premise. -/
import PPAC.Migration.ConstructionMergerCoordinateMargin

namespace PPAC.Migration.ConstructionMergerUniformMargin
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts (Subset Cut CutCarrier)
open ConstructionCutAddition (SumCut)
open ConstructionProbeIntervals (Strict)
open ConstructionProbeLetters (Representatives)
open ConstructionMergerCopyCones (Reaches)
open ConstructionMergerCoordinates (HasRep)
open ConstructionMergerFiniteWeights (HeightValue CostValue)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- One bound for all missed costs in a coordinate, on the actual cost graph. -/
def ClassBound (D L A projection NC i z t bound : M.Carrier .set) : Prop :=
  ∀ d cd, (Project.FirstOrderSemantics.reduct M).mem d L → PureKuratowski.PairMember M d cd NC →
    Reaches D A d t → ¬ Reaches D A d z → HasRep projection i d → Subset cd bound

/-- The partial finite maximum, expressed with existential witnesses only. -/
def Stage (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q n D L A projection NC z t a b k : M.Carrier .set) : Prop :=
  Subset k n → ∃ bound total, Cut hM w Q bound ∧ SumCut hM w Q a bound total ∧ Strict total b ∧
    ∀ i, (Project.FirstOrderSemantics.reduct M).mem i k → ClassBound D L A projection NC i z t bound

def classBound {m : Nat} (D L A projection NC i z t bound : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (.mem (.bound 1) (.bound L.succ.succ)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge NC.succ.succ 1 0)) (.imp (ConstructionMergerCopyCones.reaches D.succ.succ
  A.succ.succ 1 t.succ.succ) (.imp (.neg (ConstructionMergerCopyCones.reaches D.succ.succ
  A.succ.succ 1 z.succ.succ)) (.imp (ConstructionMergerCoordinates.hasRep projection.succ.succ
  i.succ.succ 1) (Project.Formula.subset (.bound 0) (.bound bound.succ.succ)))))))))

theorem classBound_freeClosed {m : Nat} (D L A projection NC i z t bound : Fin m) :
    (classBound D L A projection NC i z t bound).FreeClosed := by
  simp -implicitDefEqProofs [classBound,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionMergerCopyCones.reaches_freeClosed,ConstructionMergerCoordinates.hasRep_freeClosed]

theorem classBound_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D L A projection NC i z t bound : Fin m) :
    Project.Formula.satisfies env (classBound D L A projection NC i z t bound) ↔
      ClassBound (env.bound D) (env.bound L) (env.bound A) (env.bound projection) (env.bound NC)
        (env.bound i) (env.bound z) (env.bound t) (env.bound bound) := by
  simp only [classBound,ClassBound,ConstructionRealCuts.Subset,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionMergerCopyCones.reaches_semantics hM,ConstructionMergerCoordinates.hasRep_semantics hM]
  rfl

def stage {m : Nat} (w Q n D L A projection NC z t a b k : Fin m) : Project.Formula 1 m :=
  (.imp (Project.Formula.subset (.bound k) (.bound n)) (.existsE (.existsE (.conj
  (ConstructionRealCuts.cut w.succ.succ Q.succ.succ 1) (.conj (ConstructionCutAddition.sumCut
  w.succ.succ Q.succ.succ a.succ.succ 1 0) (.conj (.conj (Project.Formula.subset (.bound 0) (.bound
  b.succ.succ)) (.neg (Project.Formula.subset (.bound b.succ.succ) (.bound 0)))) (.forallE (.imp
  (.mem (.bound 0) (.bound k.succ.succ.succ)) (classBound D.succ.succ.succ L.succ.succ.succ
  A.succ.succ.succ projection.succ.succ.succ NC.succ.succ.succ 0 z.succ.succ.succ t.succ.succ.succ
  2)))))))))

theorem stage_freeClosed {m : Nat} (w Q n D L A projection NC z t a b k : Fin m) :
    (stage w Q n D L A projection NC z t a b k).FreeClosed := by
  simp -implicitDefEqProofs [stage,Definitional.Formula.FreeClosed,
    ConstructionRealCuts.cut_freeClosed,ConstructionCutAddition.sumCut_freeClosed,classBound_freeClosed]

theorem stage_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q n D L A projection NC z t a b k : Fin m) :
    Project.Formula.satisfies env (stage w Q n D L A projection NC z t a b k) ↔
      Stage hM (env.bound w) (env.bound Q) (env.bound n) (env.bound D) (env.bound L) (env.bound A)
        (env.bound projection) (env.bound NC) (env.bound z) (env.bound t) (env.bound a) (env.bound b) (env.bound k) := by
  simp only [stage,Stage,ConstructionProbeIntervals.Strict,ConstructionRealCuts.Subset,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionRealCuts.cut_semantics hM,ConstructionCutAddition.sumCut_semantics hM,classBound_semantics hM]
  rfl

/-- Source finite maximum argument without choosing an internal family. -/
theorem finite_uniform (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q n D L A projection NC z t a b zero : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : ConstructionFractionOrder.Carrier w Q)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (ha : Cut hM w Q a) (hab : Strict a b)
    (hEach : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i n →
      ∃ bound total, Cut hM w Q bound ∧ SumCut hM w Q a bound total ∧ Strict total b ∧
        ClassBound D L A projection NC i z t bound) :
    ∃ bound total, Cut hM w Q bound ∧ SumCut hM w Q a bound total ∧ Strict total b ∧
      ∀ i, (Project.FirstOrderSemantics.reduct M).mem i n → ClassBound D L A projection NC i z t bound := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 12 := {
    bound := Fin.cases w (Fin.cases Q (Fin.cases n (Fin.cases D (Fin.cases L (Fin.cases A
      (Fin.cases projection (Fin.cases NC (Fin.cases z (Fin.cases t (Fin.cases a (fun _ => b))))))))))),
    free := fun _ => w }
  let schema : Project.UnarySchema 12 := {
    body := stage 1 2 3 4 5 6 7 8 9 10 11 12 0
    freeClosed := stage_freeClosed _ _ _ _ _ _ _ _ _ _ _ _ _ }
  have he (k : M.Carrier .set) : schema.denote env k ↔ Stage hM w Q n D L A projection NC z t a b k :=
    stage_semantics hM (env.push k) 1 2 3 4 5 6 7 8 9 10 11 12 0
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hAll : ∀ k, (Project.FirstOrderSemantics.reduct M).mem k w → Stage hM w Q n D L A projection NC z t a b k := by
    apply hw.induction (Stage hM w Q n D L A projection NC z t a b)
    · obtain ⟨B,hB⟩ := ZF.separation_exists_d hZF schema env w
      exact ⟨B,fun k => (hB k).trans (and_congr_right (fun _ => he k))⟩
    · intro k hk _
      obtain ⟨q,hq,_⟩ := ha.2.2.2
      have hZeroCut : Cut hM w Q zero := ⟨fun p hp => (hz p hp).elim,
        fun _ p hp _ => (hz p hp).elim,fun p hp => (hz p hp).elim,q,hq,hz q⟩
      exact ⟨zero,a,hZeroCut,(ConstructionCutArithmetic.sum_zero hz ha).2,hab,
        fun i hi => (hk i hi).elim⟩
    · intro k hk ih next hs hSub
      have hkSub : Subset k n := fun i hi => hSub i ((hs i).mpr (Or.inl hi))
      have hkn := hSub k hs.predecessor_mem
      obtain ⟨c0,s0,hC0,hS0,hStrict0,hClasses0⟩ := ih hkSub
      obtain ⟨c1,s1,hC1,hS1,hStrict1,hClass1⟩ := hEach k hkn
      obtain ⟨bound,hBound,hMax⟩ := ConstructionCutArithmetic.exists_max hM hw hQ hC0 hC1
      obtain ⟨total,_,hTotal⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ ha hBound
      have hStrict : Strict total b := by
        rcases ConstructionCutArithmetic.max_cases hM hw hQ hC0 hC1 hMax with h0 | h1
        · subst bound
          have hEq := ConstructionCutAddition.sum_unique hM hTotal hS0
          exact hEq.symm ▸ hStrict0
        · subst bound
          have hEq := ConstructionCutAddition.sum_unique hM hTotal hS1
          exact hEq.symm ▸ hStrict1
      refine ⟨bound,total,hBound,hTotal,hStrict,?_⟩
      intro i hi v cv hv hcv hvt hvz hRep
      rcases (hs i).mp hi with hik | hik
      · exact fun p hp => (hMax p).mpr (Or.inl (hClasses0 i hik v cv hv hcv hvt hvz hRep p hp))
      · have hei : i = k := hZF.1.eq_of_same_members i k hik
        subst i
        exact fun p hp => (hMax p).mpr (Or.inr (hClass1 v cv hv hcv hvt hvz hRep p hp))
  exact hAll n hn (fun _ h => h)

/-- One bound for the entire missed-cost family, after eliminating the coordinate. -/
def MissedBound (D L A NC z t bound : M.Carrier .set) : Prop := ∀ d cd,
  (Project.FirstOrderSemantics.reduct M).mem d L → PureKuratowski.PairMember M d cd NC →
    Reaches D A d t → ¬ Reaches D A d z → Subset cd bound

def UniformAt (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q D L A NC z t a b : M.Carrier .set) : Prop :=
  ∃ bound total, Cut hM w Q bound ∧ SumCut hM w Q a bound total ∧ Strict total b ∧ MissedBound D L A NC z t bound

theorem copies_uniform_margin (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R zero add mulCut Id n CH CC D mul e P C L projection A Height Cost top J one u two unitHeight cap z t a b NC : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hId : ForcingConditionGraphs.IdentityGraph R Id)
    (hAdd : ConstructionCutArithmetic.Graph hM w Q R add)
    (hMul : ConstructionCutProduct.Graph hM w Q R mulCut)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hnp : ∃ j, (Project.FirstOrderSemantics.reduct M).mem j n)
    (ho : (Project.FirstOrderSemantics.reduct M).mem one w)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hunit : ConstructionRealCuts.Principal hM w Q u top)
    (htwo : (Project.FirstOrderSemantics.reduct M).SuccessorOf two one)
    (htwow : (Project.FirstOrderSemantics.reduct M).mem two w)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hc : ForcingDiagramPoset.Conical D mul e)
    (hC : Representatives n D C) (hL : ConstructionMergerCopies.Copies n D mul P C L)
    (hp : MapsTo C L projection) (hProj : ConstructionMergerCopies.Projection n D mul P C projection)
    (hEq : ConstructionMergerCopies.EqualityLaw n D mul P projection)
    (hCopy : ConstructionMergerAction.CopyLaw D mul projection A)
    (hJ : Representatives n L J) (hCH : MapsTo J R CH) (hCC : MapsTo J R CC)
    (hHeight : MapsTo D R Height) (hHB : ConstructionCutWeights.RangeBound top Height)
    (hCost : MapsTo D R Cost) (hCB : ConstructionProbeGateCap.Bounds top Cost)
    (hUniform : ConstructionProbeLetterIntervals.UniformMargins hM w Q D mul Height Cost)
    (hGraph : ConstructionMergerCoordinates.Graph n L projection Height zero CH)
    (hCoordC : ConstructionMergerCoordinates.Graph n L projection Cost top CC)
    (hEdge : PureKuratowski.PairMember M e unitHeight Height)
    (hCap : ConstructionCutDivision.Value hM w Q two unitHeight cap)
    (hNCGraph : ∀ d cd, PureKuratowski.PairMember M d cd NC ↔
      (Project.FirstOrderSemantics.reduct M).mem d L ∧ CostValue hM w Q n R mulCut Id top cap CC d cd)
    (hzL : (Project.FirstOrderSemantics.reduct M).mem z L) (htL : (Project.FirstOrderSemantics.reduct M).mem t L)
    (ha : HeightValue hM w Q n R add Id zero CH z a) (hb : HeightValue hM w Q n R add Id zero CH t b)
    (hReach : Reaches D A z t) (hne : z ≠ t) :
    UniformAt hM w Q D L A NC z t a b := by
  have hACut : Cut hM w Q a := by
    obtain ⟨sum,hSum,hDiv⟩ := ha
    exact ConstructionCutDivision.value_cut hw hQ hn hnp
      ((hR sum).mp (ConstructionMergerFiniteWeights.coordinateEval_range hM hSum)) hDiv
  have hStrict := (ConstructionMergerHeightComparison.copiesHeight_order hM hw hz hzw hQ hR hId hAdd hn hnp hm hc hC hL hp hProj hEq hCopy hJ hCH hHeight hHB hUniform hGraph hzL htL ha hb hReach).2 hne
  have hEach (i) (hi : (Project.FirstOrderSemantics.reduct M).mem i n) :
      ∃ bound total, Cut hM w Q bound ∧ SumCut hM w Q a bound total ∧ Strict total b ∧
        ClassBound D L A projection NC i z t bound := by
    obtain ⟨bound,total,hBound,hTotal,hRoom,hMissed⟩ :=
      ConstructionMergerCoordinateMargin.copies_coordinate_margin hM hw hz hzw hQ hR hId hAdd hMul hn hnp ho hone hu hunit htwo htwow hm hc hC hL hp hProj hEq hCopy hJ hCH hCC hHeight hHB hCost hCB hUniform hGraph hCoordC hEdge hCap hzL htL ha hb hi hReach hne
    exact ⟨bound,total,hBound,hTotal,hRoom,fun d cd hd hdc hdt hdz hRep =>
      hMissed d cd hd ((hNCGraph d cd).mp hdc).2 hdt hdz hRep⟩
  obtain ⟨bound,total,hBound,hTotal,hRoom,hClasses⟩ := finite_uniform hM hw hQ hz hn hACut hStrict hEach
  refine ⟨bound,total,hBound,hTotal,hRoom,?_⟩
  intro d cd hd hdc hdt hdz
  obtain ⟨i,x,hi,_,hRep⟩ := ConstructionMergerCopies.representative hC hL hProj hd
  exact hClasses i hi d cd hd hdc hdt hdz ⟨x,hRep⟩

/-- Exact costs of missed actual copies. -/
def CostMember (D L A NC z t cd : M.Carrier .set) : Prop := ∃ d,
  (Project.FirstOrderSemantics.reduct M).mem d L ∧ PureKuratowski.PairMember M d cd NC ∧
    Reaches D A d t ∧ ¬ Reaches D A d z

def Family (D L A NC z t f : M.Carrier .set) : Prop := ∀ cd,
  (Project.FirstOrderSemantics.reduct M).mem cd f ↔ CostMember D L A NC z t cd

def Cap (D L A NC z t cap : M.Carrier .set) : Prop := ∃ f,
  Family D L A NC z t f ∧ ConstructionRealCuts.UpperBound f cap ∧
    ∀ c, ConstructionRealCuts.UpperBound f c → Subset cap c

def costMember {m : Nat} (D L A NC z t cd : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (.mem (.bound 0) (.bound L.succ))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge NC.succ 0 cd.succ))
      (.conj (ConstructionMergerCopyCones.reaches D.succ A.succ 0 t.succ)
        (.neg (ConstructionMergerCopyCones.reaches D.succ A.succ 0 z.succ)))))

theorem costMember_freeClosed {m : Nat} (D L A NC z t cd : Fin m) :
    (costMember D L A NC z t cd).FreeClosed := by
  simp -implicitDefEqProofs [costMember,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionMergerCopyCones.reaches_freeClosed]

theorem costMember_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D L A NC z t cd : Fin m) :
    Project.Formula.satisfies env (costMember D L A NC z t cd) ↔
      CostMember (env.bound D) (env.bound L) (env.bound A) (env.bound NC) (env.bound z) (env.bound t) (env.bound cd) := by
  simp only [costMember,CostMember,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionMergerCopyCones.reaches_semantics hM]
  rfl

theorem exists_family (hM : FirstOrder.Theory.Models M nativeZF) {D L A NC R z t : M.Carrier .set}
    (hNC : MapsTo L R NC) : ∃ f, Family D L A NC z t f ∧ Subset f R := by
  let schema : Project.UnarySchema 6 := {
    body := costMember 1 2 3 4 5 6 0
    freeClosed := costMember_freeClosed _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 6 := {
    bound := Fin.cases D (Fin.cases L (Fin.cases A (Fin.cases NC (Fin.cases z (fun _ => t))))), free := fun _ => D }
  obtain ⟨f,hf⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env R
  have he (cd : M.Carrier .set) : schema.denote env cd ↔ CostMember D L A NC z t cd :=
    costMember_semantics hM (env.push cd) 1 2 3 4 5 6 0
  refine ⟨f,?_,fun cd hcd => ((hf cd).mp hcd).1⟩
  intro cd
  constructor
  · exact fun hcd => (he cd).mp ((hf cd).mp hcd).2
  · intro hcd
    have hCopy := hcd
    obtain ⟨d,_,hdc,_,_⟩ := hCopy
    exact (hf cd).mpr ⟨hNC.2 d cd hdc,(he cd).mpr hcd⟩

/-- Construct the actual missed-cost supremum, not just a pointwise upper bound. -/
theorem canonical_uniform (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D L A NC z t a b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hNC : MapsTo L R NC) (ha : Cut hM w Q a)
    (hUniform : UniformAt hM w Q D L A NC z t a b) :
    ∃ bound total, Cut hM w Q bound ∧ Cap D L A NC z t bound ∧
      SumCut hM w Q a bound total ∧ Strict total b ∧ MissedBound D L A NC z t bound := by
  obtain ⟨old,oldTotal,hOld,hOldSum,hRoom,hMissed⟩ := hUniform
  obtain ⟨f,hf,hfR⟩ := exists_family hM hNC
  have hBound : ConstructionRealCuts.UpperBound f old := by
    intro cd hcd
    obtain ⟨d,hd,hdc,hdt,hdz⟩ := (hf cd).mp hcd
    exact hMissed d cd hd hdc hdt hdz
  obtain ⟨bound,hCut,hUpper,hLeast⟩ := ConstructionRealCuts.bounded_union hM hR hfR hOld hBound
  have hBoundLe := hLeast old hBound
  obtain ⟨total,_,hTotal⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ ha hCut
  have hTotalLe := ConstructionCutArithmetic.sum_mono hTotal hOldSum (fun _ h => h) hBoundLe
  refine ⟨bound,total,hCut,⟨f,hf,hUpper,hLeast⟩,hTotal,ConstructionProbeIntervals.le_strict_trans hTotalLe hRoom,?_⟩
  intro d cd hd hdc hdt hdz
  exact hUpper cd ((hf cd).mpr ⟨d,hd,hdc,hdt,hdz⟩)

end PPAC.Migration.ConstructionMergerUniformMargin
