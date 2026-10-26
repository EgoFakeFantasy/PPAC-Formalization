/- Pinned ProbeMargins.height_bounds/cost_le_scale. Consume the actual
height/cost graphs, original interval fields and exact product unit law.
The resulting bounded weight package is not yet the full HeightCost margin. -/
import PPAC.Migration.ConstructionCutProductUnit
import PPAC.Migration.ConstructionProbeCostFoldSyntax
import PPAC.Migration.ConstructionProbeHeightIntervalsSyntax
import PPAC.Migration.ConstructionProbeHeightFoldSyntax

namespace PPAC.Migration.ConstructionProbeWeightBounds
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionRealCuts
open ConstructionProbeRaw (Cons)
open ConstructionProbeWord (WordCarrier)
open ConstructionCutWeights (BoundedPositive RangeBound)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The actual source interval inequalities bound one affine height step. -/
theorem height_step_bound (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R one u unit four D mul S A K E H C F s o d bound v p y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q) (hR : CutCarrier hM w Q R)
    (hu : Coordinates w u one one) (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : Principal hM w Q u unit) (hF : MapsTo S R F) (hHB : RangeBound unit H)
    (hv : Cut hM w Q v) (hvU : Subset v unit)
    (hi : ConstructionProbeIntervalChoices.Valid hM w Q four D mul S A K E H C F s o d bound)
    (hp : ConstructionCutProduct.Value hM w Q d v p) (hy : ConstructionCutAddition.SumCut hM w Q o p y) :
    BoundedPositive y unit := by
  obtain ⟨floor,t,exit,ht,he,c,hCtx,_,hInterval,_⟩ := hi
  obtain ⟨hO,hD,hB,hDN,gap,lower,upperStep,upper,_,_,_,_,hLower,hLowerO,hStep,hUpper,hUpperExit⟩ := hInterval
  have hFloor := (hR floor).mp (hF.2 s floor hCtx.1)
  have hP := ConstructionCutProduct.value_cut hM hw hQ hD hv hp
  have hOffsetY := (ConstructionCutArithmetic.sum_contains hO hP hy).1
  obtain ⟨r,hr⟩ := hDN
  have hOffsetN : ∃ r, (Project.FirstOrderSemantics.reduct M).mem r o :=
    ⟨r,hLowerO.1 r ((ConstructionCutArithmetic.sum_contains hFloor hD hLower).2 r hr)⟩
  have hProductBound := ConstructionCutProductUnit.bounded_right hM hw hQ hu hone hunit hD hp hvU
  have hYStep := ConstructionCutArithmetic.sum_mono hy hStep (fun _ h => h) hProductBound
  have hStepCut := ConstructionCutAssociativity.sum_is_cut hM hw hQ hO hD hStep
  have hStepUpper := (ConstructionCutArithmetic.sum_contains hStepCut hB hUpper).1
  have hYExit := ConstructionProbeIntervals.le_strict_trans (fun r hr => hStepUpper r (hYStep r hr)) hUpperExit
  have hExitUnit := hHB exit he hCtx.2.2.2.2.1
  obtain ⟨r,hr⟩ := hOffsetN
  exact ⟨⟨r,hOffsetY r hr⟩,
    fun r hr => hExitUnit.2.1 r (hYExit.1 r hr),
    fun h => hExitUnit.2.2 (fun r hr => hYExit.1 r (h r hr))⟩

def boundAt {m : Nat} (unit HL q : Fin m) : Project.Formula 1 m :=
  .forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge HL.succ q.succ 0))
    (ConstructionCutWeights.boundedPositive 0 unit.succ))

theorem boundAt_freeClosed {m : Nat} (unit HL q : Fin m) : (boundAt unit HL q).FreeClosed := by
  simp -implicitDefEqProofs [boundAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionCutWeights.boundedPositive_freeClosed]

theorem boundAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (unit HL q : Fin m) :
    Project.Formula.satisfies env (boundAt unit HL q) ↔
      ∀ y, PureKuratowski.PairMember M (env.bound q) y (env.bound HL) → BoundedPositive y (env.bound unit) := by
  simp only [boundAt,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionCutWeights.boundedPositive_semantics]
  rfl

theorem height_bounds (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W Q R H C F K E Off V B HL one u unit four : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : Carrier w Q) (hR : CutCarrier hM w Q R) (hu : Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one) (hunit : Principal hM w Q u unit)
    (hW : WordCarrier w D S mul A b W) (hHL : MapsTo W R HL)
    (hF : MapsTo S R F) (hB : MapsTo S R B) (hHB : RangeBound unit H)
    (hI : ConstructionProbeHeightIntervalGraphs.Laws hM w Q four D mul S A K E H C F Off V B)
    (hLaws : ConstructionProbeHeightFold.Laws hM w D S zero W Q H Off V HL) : RangeBound unit HL := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases unit (fun _ => HL), free := fun _ => w }
  let p : Project.UnarySchema 2 := { body := boundAt 1 2 0, freeClosed := boundAt_freeClosed _ _ _ }
  have he (q : M.Carrier .set) : p.denote env q ↔
      ∀ y, PureKuratowski.PairMember M q y HL → BoundedPositive y unit := boundAt_semantics hM (env.push q) 1 2 0
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro x q hOld
    exact (he q).mpr (fun y hy => hHB x y ((hLaws.1 x q y hOld).mp hy))) (by
    intro s t q hCons ih
    apply (he q).mpr
    intro y hy
    have hq := ForcingConditionGraphs.function_input hHL.1 hy
    obtain ⟨v,htv,o,d,prod,hso,hsd,hProd,hSum⟩ := (hLaws.2 s t q y hCons hq).mp hy
    obtain ⟨bound,hsb,_⟩ := hB.1.2 s (ConstructionProbeRawAction.cons_letter hCons)
    exact height_step_bound hM hw hQ hR hu hone hunit hF hHB ((hR v).mp (hHL.2 t v htv))
      ((he t).mp ih v htv).2.1 (hI s o d bound hso hsd hsb) hProd hSum)
  intro q y hy
  have hq := ForcingConditionGraphs.function_input hHL.1 hy
  exact (he q).mp (hAll q (ConstructionProbeWord.word_raw hW hq)) y hy

/-- Source cost_le_scale on the exact source cons/head representation. -/
theorem cost_le_scale (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero W Q R C V Cap LC one u unit s t q c d : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q) (hR : CutCarrier hM w Q R)
    (hu : Coordinates w u one one) (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : Principal hM w Q u unit) (hV : MapsTo S R V)
    (hCB : ConstructionProbeGateCap.Bounds unit LC)
    (hLaws : ConstructionProbeCostFold.Laws hM w D S zero W Q C V Cap LC)
    (hCons : Cons w D S s t q) (hq : (Project.FirstOrderSemantics.reduct M).mem q W)
    (hc : PureKuratowski.PairMember M q c LC) (hd : PureKuratowski.PairMember M s d V) : Subset c d := by
  obtain ⟨v,htv,d',prod,cap,hd',hProd,hcap,hMin⟩ := (hLaws.2 s t q c hCons hq).mp hc
  have he := ForcingConditionGraphs.function_unique hV.1 hd hd'
  subst d'
  have hp := ConstructionCutProductUnit.bounded_right hM hw hQ hu hone hunit
    ((hR d).mp (hV.2 s d hd)) hProd (hCB t v htv).2
  exact fun x hx => hp x ((ConstructionCutMinimum.value_bounds hMin).1 x hx)

/-- Construct the bounded height and cost graphs on the same actual Word.
All maps/recurrences are built by the previously accepted constructors. -/
theorem exists_bounded_weights (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W Q R Emb H C Off V B F K E e G one u unit four : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : Carrier w Q) (hR : CutCarrier hM w Q R) (hu : Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one) (hunit : Principal hM w Q u unit)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hCon : ForcingDiagramPoset.Conical D mul e)
    (hW : WordCarrier w D S mul A b W) (hEmb : MapsTo D W Emb) (hOld : ConstructionProbeOldEmbedding.OldGraph zero D Emb)
    (hH : MapsTo D R H) (hHB : RangeBound unit H) (hC : MapsTo D R C) (hCB : ConstructionProbeGateCap.Bounds unit C)
    (hOff : MapsTo S R Off) (hV : MapsTo S R V) (hB : MapsTo S R B) (hF : MapsTo S R F)
    (hI : ConstructionProbeHeightIntervalGraphs.Laws hM w Q four D mul S A K E H C F Off V B) :
    ∃ HL Cap LC, MapsTo W R HL ∧ ConstructionProbeHeightFold.Laws hM w D S zero W Q H Off V HL ∧ RangeBound unit HL ∧
      MapsTo W R Cap ∧ ConstructionProbeGateCap.Graph D W mul G Emb C unit Cap ∧ ConstructionProbeGateCap.Bounds unit Cap ∧
      MapsTo W R LC ∧ ConstructionProbeCostFold.Laws hM w D S zero W Q C V Cap LC ∧ ConstructionProbeGateCap.Bounds unit LC ∧
      (∀ s t q c d, Cons w D S s t q → (Project.FirstOrderSemantics.reduct M).mem q W →
        PureKuratowski.PairMember M q c LC → PureKuratowski.PairMember M s d V → Subset c d) ∧
      (∀ L, MapsTo W R L → ConstructionProbeHeightFold.Laws hM w D S zero W Q H Off V L → L = HL) ∧
      (∀ L, MapsTo W R L → ConstructionProbeCostFold.Laws hM w D S zero W Q C V Cap L → L = LC) := by
  have hUnitR := (hR unit).mpr (principal_cut hM hw hQ ((hQ u).mpr ⟨one,one,hu⟩) hunit)
  obtain ⟨he,hhe,_⟩ := hH.1.2 e hm.1.1
  obtain ⟨r,hr⟩ := (hHB e he hhe).1
  have hUnitN : ∃ r, (Project.FirstOrderSemantics.reduct M).mem r unit := ⟨r,(hHB e he hhe).2.1 r hr⟩
  have hVP : ∀ s d, PureKuratowski.PairMember M s d V → ∃ p, (Project.FirstOrderSemantics.reduct M).mem p d := by
    intro s d hsd
    have hs := ForcingConditionGraphs.function_input hV.1 hsd
    obtain ⟨o,hso,_⟩ := hOff.1.2 s hs
    obtain ⟨bound,hsb,_⟩ := hB.1.2 s hs
    obtain ⟨_,_,_,_,_,_,_,_,hInterval,_⟩ := hI s o d bound hso hsd hsb
    exact hInterval.2.2.2.1
  obtain ⟨HL,hHL,hHeight,hHU⟩ := ConstructionProbeHeightFold.existsUnique_height hM hw hz hzw hQ hR hH hOff hV hW
  have hHBNew := height_bounds hM hw hz hzw hQ hR hu hone hunit hW hHL hF hB hHB hI hHeight
  obtain ⟨Cap,LC,hCap,hCapG,hCapB,hLC,hCost,hCBNew,hCU⟩ :=
    ConstructionProbeCostFold.exists_bounded_cost hM hw hz hzw hQ hR hm hCon hW hEmb hOld hC hV hUnitR hUnitN hCB hVP
  exact ⟨HL,Cap,LC,hHL,hHeight,hHBNew,hCap,hCapG,hCapB,hLC,hCost,hCBNew,
    fun _ _ _ _ _ hc hq hqc hsd => cost_le_scale hM hw hQ hR hu hone hunit hV hCBNew hCost hc hq hqc hsd,hHU,hCU⟩

end PPAC.Migration.ConstructionProbeWeightBounds
