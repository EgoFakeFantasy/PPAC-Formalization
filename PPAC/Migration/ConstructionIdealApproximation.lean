/- Pinned DiagramOrder.HeightCost.directed_cofinal_sequence:
exact internal supremum, monotone heights and 1/(n+1) approximation.
These are representation adapters consumed by ConstructionIdealCofinal. -/
import PPAC.Migration.ConstructionSaturationCardinals
import PPAC.Migration.ConstructionCutLocatedness

namespace PPAC.Migration.ConstructionIdealApproximation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts
open ConstructionFractionOrder (Coordinates Carrier)
open ConstructionCutAddition (SumCut)
open ConstructionBaseMonoid (Divides)
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (function_input function_unique)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Supremum (U H r : M.Carrier .set) : Prop :=
  ∀ q, (Project.FirstOrderSemantics.reduct M).mem q r ↔ ∃ x h,
    (Project.FirstOrderSemantics.reduct M).mem x U ∧ PureKuratowski.PairMember M x h H ∧
      (Project.FirstOrderSemantics.reduct M).mem q h

theorem supremum_exists (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D H U : M.Carrier .set}
    (hR : CutCarrier hM w Q R) (hTop : Cut hM w Q top)
    (hH : MapsTo D R H) (hBound : ConstructionCutWeights.RangeBound top H)
    :
    ∃ r, Cut hM w Q r ∧ Supremum U H r := by
  let schema : Project.UnarySchema 2 := {
    body := .existsE (.existsE (.conj (.mem (.bound 1) (.bound 4))
      (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (3 : Fin 5) (1 : Fin 5) (0 : Fin 5)))
        (.mem (.bound 2) (.bound 0)))))
    freeClosed := by simp [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed] }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 :=
    { bound := Fin.cases H (fun _ => U), free := fun _ => D }
  obtain ⟨r,hr⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env Q
  have hc {x h} (hxh : PureKuratowski.PairMember M x h H) : Cut hM w Q h :=
    (hR h).mp (hH.2 x h hxh)
  have hs : Supremum U H r := by
    intro q
    have he : Project.Formula.satisfies (env.push q) schema.body ↔ ∃ x h,
        (Project.FirstOrderSemantics.reduct M).mem x U ∧ PureKuratowski.PairMember M x h H ∧
          (Project.FirstOrderSemantics.reduct M).mem q h := by
      simp only [schema,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
        Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
        GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
      rfl
    exact ⟨fun h => he.mp ((hr q).mp h).2,
      fun h => (hr q).mpr ⟨by obtain ⟨x,c,_,hxc,hqc⟩ := h; exact (hc hxc).1 q hqc,he.mpr h⟩⟩
  refine ⟨r,⟨?_,?_,?_,?_⟩,hs⟩
  · exact fun q hq => ((hr q).mp hq).1
  · intro p q hq hpq
    obtain ⟨x,h,hx,hxh,hqh⟩ := (hs q).mp hq
    exact (hs p).mpr ⟨x,h,hx,hxh,(hc hxh).2.1 p q hqh hpq⟩
  · intro q hq
    obtain ⟨x,h,hx,hxh,hqh⟩ := (hs q).mp hq
    obtain ⟨p,hph,hqp⟩ := (hc hxh).2.2.1 q hqh
    exact ⟨p,(hs p).mpr ⟨x,h,hx,hxh,hph⟩,hqp⟩
  · obtain ⟨q,hq,hnq⟩ := hTop.2.2.2
    refine ⟨q,hq,fun hqr => ?_⟩
    obtain ⟨x,h,_,hxh,hqh⟩ := (hs q).mp hqr
    exact hnq ((hBound x h hxh).2.1 q hqh)

theorem height_mono (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D mul e H C x y hx hy : M.Carrier .set}
    (hR : CutCarrier hM w Q R) (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e)
    (hH : MapsTo D R H) (hMargin : ConstructionProbeLetterIntervals.UniformMargins hM w Q D mul H C)
    (hxh : PureKuratowski.PairMember M x hx H) (hyh : PureKuratowski.PairMember M y hy H)
    (hxy : Divides D mul x y) : Subset hx hy := by
  classical
  by_cases hyx : Divides D mul y x
  · have he := ConstructionProbeGateCap.divides_antisymm hm hc (function_input hH.1 hxh) hxy hyx
    subst y
    have hh := function_unique hH.1 hxh hyh
    exact hh ▸ (fun p hp => hp : Subset hx hx)
  · obtain ⟨c,s,hc,hSum,hStrict,_⟩ := hMargin x y hx hy hxh hyh hxy hyx
    exact fun p hp => hStrict.1 p ((ConstructionCutArithmetic.sum_contains
      ((hR hx).mp (hH.2 x hx hxh)) hc hSum).1 p hp)

def Approximates (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q H r i y : M.Carrier .set) : Prop :=
  ∃ n one step eps hy total,
    (Project.FirstOrderSemantics.reduct M).SuccessorOf n i ∧
    (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one ∧
    Coordinates w step one n ∧ Principal hM w Q step eps ∧
    PureKuratowski.PairMember M y hy H ∧ SumCut hM w Q hy eps total ∧ Subset r total

theorem approximate (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D H U r i : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hR : CutCarrier hM w Q R) (hH : MapsTo D R H)
    (hr : Cut hM w Q r) (hSup : Supremum U H r)
    (hn : ∃ q, (Project.FirstOrderSemantics.reduct M).mem q r)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i w) :
    ∃ y, (Project.FirstOrderSemantics.reduct M).mem y U ∧ Approximates hM w Q H r i y := by
  obtain ⟨one,hone,how⟩ := hw.exists_ordinalOne_mem
  obtain ⟨n,hni,hnw⟩ := hw.1.2 i hi
  obtain ⟨step,hStepCode⟩ := KuratowskiZF.exists_code hM one n
  have hstep : Coordinates w step one n := ⟨how,hnw,⟨i,hni.predecessor_mem⟩,hStepCode⟩
  have hStepQ := (hQ step).mpr ⟨one,n,hstep⟩
  obtain ⟨eps,hEps⟩ := exists_principal hM w Q step
  have hEpsCut := principal_cut hM hw hQ hStepQ hEps
  obtain ⟨q,s,hqr,hns,hSum⟩ := ConstructionCutLocatedness.grid_boundary hM hw hQ hr hn hone hstep
  obtain ⟨y,hy,hyU,hyH,hqy⟩ := (hSup q).mp hqr
  have hHyCut := (hR hy).mp (hH.2 y hy hyH)
  have hqQ := hr.1 q hqr
  obtain ⟨qa,hQA⟩ := exists_principal hM w Q q
  obtain ⟨sa,hSA⟩ := exists_principal hM w Q s
  have hSumCopy := hSum
  obtain ⟨a,b,c,d,num,den,_,_,hsCoord,_⟩ := hSumCopy
  have hsQ := (hQ s).mpr ⟨num,den,hsCoord⟩
  have hAdd := ConstructionPrincipalSumBridge.principal_sum hM hw hQ
    (⟨q,step,s,hqQ,hStepQ,hQA,hEps,hSum,hSA⟩ :
      ConstructionPrincipalAddition.PrincipalAdd hM w Q qa eps sa)
  obtain ⟨total,_,hTotal⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hHyCut hEpsCut
  have hQAIn : Subset qa hy := fun p hp =>
    hHyCut.2.1 p q hqy ((hQA p).mp hp).2.1
  have hSIn : Subset r sa := fun p hp => (hSA p).mpr
    ⟨hr.1 p hp,ConstructionCutArithmetic.below_omitted hM hw hQ hr hsQ hns hp⟩
  have hAddMono := ConstructionCutArithmetic.sum_mono hAdd hTotal hQAIn (fun _ h => h)
  exact ⟨y,hyU,n,one,step,eps,hy,total,hni,hone,hstep,hEps,hyH,hTotal,fun p hp => hAddMono p (hSIn p hp)⟩

theorem approximate_mono (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D mul e H C r i x y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hR : CutCarrier hM w Q R) (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e)
    (hH : MapsTo D R H) (hMargin : ConstructionProbeLetterIntervals.UniformMargins hM w Q D mul H C)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y D)
    (hxy : Divides D mul x y) (hApprox : Approximates hM w Q H r i x) :
    Approximates hM w Q H r i y := by
  obtain ⟨n,one,step,eps,hx,total,hs,hone,hstep,hEps,hxh,hTotal,hBound⟩ := hApprox
  obtain ⟨hy,hyh,_⟩ := hH.1.2 y hy
  have hMono := height_mono hM hR hm hc hH hMargin hxh hyh hxy
  have hStepQ := (hQ step).mpr ⟨one,n,hstep⟩
  obtain ⟨out,_,hOut⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ
    ((hR hy).mp (hH.2 y hy hyh)) (principal_cut hM hw hQ hStepQ hEps)
  exact ⟨n,one,step,eps,hy,out,hs,hone,hstep,hEps,hyh,hOut,
    fun p hp => ConstructionCutArithmetic.sum_mono hTotal hOut hMono (fun _ h => h) p (hBound p hp)⟩

theorem small_cost_step (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q cost : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hc : Cut hM w Q cost) (hn : ∃ q, (Project.FirstOrderSemantics.reduct M).mem q cost) :
    ∃ i n one step eps,
      (Project.FirstOrderSemantics.reduct M).mem i w ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf n i ∧
      (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one ∧
      Coordinates w step one n ∧ Principal hM w Q step eps ∧ Subset eps cost := by
  classical
  obtain ⟨q,hq⟩ := hn
  obtain ⟨delta,hd,hqd⟩ := hc.2.2.1 q hq
  obtain ⟨a,b,hDelta⟩ := (hQ delta).mp (hc.1 delta hd)
  have ha : ∃ x, (Project.FirstOrderSemantics.reduct M).mem x a := by
    apply Classical.byContradiction
    intro h
    exact hqd.2 (ConstructionCutLocatedness.empty_le hM hw hDelta (fun x hx => h ⟨x,hx⟩)
      ((hQ q).mp (hc.1 q hq)))
  obtain ⟨one,n,step,hone,hstep,hlt⟩ := ConstructionCutLocatedness.smaller_unit hM hw hDelta ha
  obtain ⟨i,hi,hni⟩ := hw.exists_predecessor_of_mem_of_nonempty
    (ModelTransfer.project_models_iff.mp hM) hstep.2.1 hstep.2.2.1
  obtain ⟨eps,hEps⟩ := exists_principal hM w Q step
  have hStepCost := hc.2.1 step delta hd hlt.1
  exact ⟨i,n,one,step,eps,hi,hni,hone,hstep,hEps,fun p hp =>
    hc.2.1 p step hStepCost ((hEps p).mp hp).2.1⟩


def approximates {m : Nat} (w Q H r i y : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (Project.Formula.isSuccessor (.bound (5 :
  Fin (m+6))) (.bound i.succ.succ.succ.succ.succ.succ)) (.conj (Project.Formula.isOrdinalOne (.bound (4 :
  Fin (m+6)))) (.conj (ConstructionFractionOrder.coordinates w.succ.succ.succ.succ.succ.succ (3 : Fin (m+6))
  (4 : Fin (m+6)) (5 : Fin (m+6))) (.conj (ConstructionRealCuts.principal w.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ (3 : Fin (m+6)) (2 : Fin (m+6))) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge H.succ.succ.succ.succ.succ.succ y.succ.succ.succ.succ.succ.succ (1 : Fin (m+6))))
  (.conj (ConstructionCutAddition.sumCut w.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ (1
  : Fin (m+6)) (2 : Fin (m+6)) (0 : Fin (m+6))) (Project.Formula.subset (.bound
  r.succ.succ.succ.succ.succ.succ) (.bound (0 : Fin (m+6))))))))))))))))

theorem approximates_freeClosed {m : Nat} (w Q H r i y : Fin m) :
    (approximates w Q H r i y).FreeClosed := by
  simp -implicitDefEqProofs [approximates,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isSuccessor,Project.Formula.isOrdinalOne,ConstructionFractionOrder.coordinates_freeClosed,ConstructionRealCuts.principal_freeClosed,ConstructionCutAddition.sumCut_freeClosed]

theorem approximates_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q H r i y : Fin m) :
    Project.Formula.satisfies env (approximates w Q H r i y) ↔ Approximates hM (env.bound w) (env.bound Q) (env.bound H) (env.bound r) (env.bound i) (env.bound y) := by
  simp only [approximates,Approximates,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Formula.satisfies_isSuccessor_iff,Project.Formula.satisfies_isOrdinalOne_iff,ConstructionFractionOrder.coordinates_semantics hM,ConstructionRealCuts.principal_semantics hM,ConstructionCutAddition.sumCut_semantics hM,Project.Formula.satisfies_subset_iff]
  rfl

end PPAC.Migration.ConstructionIdealApproximation
