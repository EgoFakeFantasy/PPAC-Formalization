/- Pinned MergerCones.wordCost:376 and exact old/snoc equations.
The source snoc cost depends ONLY on prefix height, not prefix cost. Apply
native function construction to existing Raw one-step decomposition directly;
NO cost recursion/state fold is introduced. Heights and literal letter factor
are the actual previously constructed functions on the SAME internal Word. -/
import PPAC.Migration.ConstructionMergerWordHeights

namespace PPAC.Migration.ConstructionMergerWordCosts
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts (Subset Cut CutCarrier)
open ConstructionCutAddition (SumCut)
open ConstructionProbeRaw (Raw Old Cons)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Value (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q D S zero unit HL C B q y : M.Carrier .set) : Prop :=
  (∃ x, Old zero D x q ∧ PureKuratowski.PairMember M x y C) ∨
    ∃ letter pref h room factor, Cons w D S letter pref q ∧ PureKuratowski.PairMember M pref h HL ∧
      ConstructionCutDifference.Value hM w Q h unit room ∧ SumCut hM w Q h room unit ∧
      PureKuratowski.PairMember M letter factor B ∧ ConstructionCutProduct.Value hM w Q room factor y

def value {m : Nat} (w Q D S zero unit HL C B q y : Fin m) : Project.Formula 1 m :=
  (.disj (.existsE (.conj (ConstructionProbeRaw.old zero.succ D.succ 0 q.succ) (ProjectSyntax.encode
  id (Source.SetLanguage.edge C.succ 0 y.succ)))) (.existsE (.existsE (.existsE (.existsE (.existsE
  (.conj (ConstructionProbeRaw.cons w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ
  S.succ.succ.succ.succ.succ 4 3 q.succ.succ.succ.succ.succ) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge HL.succ.succ.succ.succ.succ 3 2)) (.conj (ConstructionCutDifference.value
  w.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ 2 unit.succ.succ.succ.succ.succ 1) (.conj
  (ConstructionCutAddition.sumCut w.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ 2 1
  unit.succ.succ.succ.succ.succ) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  B.succ.succ.succ.succ.succ 4 0)) (ConstructionCutProduct.value w.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ 1 0 y.succ.succ.succ.succ.succ))))))))))))

theorem value_freeClosed {m : Nat} (w Q D S zero unit HL C B q y : Fin m) :
    (value w Q D S zero unit HL C B q y).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionProbeRaw.old_freeClosed,ConstructionProbeRaw.cons_freeClosed,
    ConstructionCutDifference.value_freeClosed,ConstructionCutAddition.sumCut_freeClosed,ConstructionCutProduct.value_freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q D S zero unit HL C B q y : Fin m) :
    Project.Formula.satisfies env (value w Q D S zero unit HL C B q y) ↔
      Value hM (env.bound w) (env.bound Q) (env.bound D) (env.bound S) (env.bound zero) (env.bound unit)
        (env.bound HL) (env.bound C) (env.bound B) (env.bound q) (env.bound y) := by
  simp only [value,Value,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionProbeRaw.old_semantics hM,ConstructionProbeRaw.cons_semantics hM,
    ConstructionCutDifference.value_semantics hM,ConstructionCutAddition.sumCut_semantics hM,ConstructionCutProduct.value_semantics hM]
  rfl

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q D S zero W R unit HL C B q y y' : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hHL : MapsTo W R HL) (hC : MapsTo D R C) (hB : MapsTo S R B)
    (hy : Value hM w Q D S zero unit HL C B q y) (hy' : Value hM w Q D S zero unit HL C B q y') : y = y' := by
  rcases hy with ⟨x,hOld,hx⟩ | ⟨letter,pref,h,room,factor,hCons,hh,hDiff,hSum,hf,hProd⟩
  · rcases hy' with ⟨x',hOld',hx'⟩ | ⟨letter,pref,h,room,factor,hCons,_,_,_,_,_⟩
    · have he := (PureKuratowski.code_injective hOld.2 hOld'.2).2
      subst x'
      exact ForcingConditionGraphs.function_unique hC.1 hx hx'
    · exact (ConstructionProbeRaw.old_ne_cons hz hOld hCons).elim
  · rcases hy' with ⟨x,hOld,hx⟩ | ⟨letter',pref',h',room',factor',hCons',hh',hDiff',_,hf',hProd'⟩
    · exact (ConstructionProbeRaw.old_ne_cons hz hOld hCons).elim
    · obtain ⟨he1,he2⟩ := ConstructionProbeRaw.cons_injective hM hw hCons hCons'
      subst letter';subst pref'
      have he := ForcingConditionGraphs.function_unique hHL.1 hh hh';subst h'
      have he := ConstructionCutDifference.value_unique hM hDiff hDiff';subst room'
      have he := ForcingConditionGraphs.function_unique hB.1 hf hf';subst factor'
      exact ConstructionCutProduct.value_unique hM hProd hProd'

theorem value_range (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q D S zero R unit HL C B q y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hUnit : Cut hM w Q unit) (hC : MapsTo D R C) (hB : MapsTo S R B)
    (hy : Value hM w Q D S zero unit HL C B q y) : (Project.FirstOrderSemantics.reduct M).mem y R := by
  rcases hy with ⟨x,_,hx⟩ | ⟨letter,pref,h,room,factor,_,_,hDiff,_,hf,hProd⟩
  · exact hC.2 x y hx
  · exact (hR y).mpr (ConstructionCutProduct.value_cut hM hw hQ
      (ConstructionCutDifference.value_cut hM hw hQ hUnit hDiff) ((hR factor).mp (hB.2 letter factor hf)) hProd)

theorem value_total (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q D S zero W R unit HL C B q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R) (hUnit : Cut hM w Q unit)
    (hW : ConstructionProbeRaw.Carrier w D S W) (hHL : MapsTo W R HL) (hC : MapsTo D R C) (hB : MapsTo S R B)
    (hHB : ConstructionCutWeights.RangeBound unit HL) (hq : (Project.FirstOrderSemantics.reduct M).mem q W) :
    ∃ y, Value hM w Q D S zero unit HL C B q y := by
  rcases ConstructionProbeRaw.cases_raw hM hw hz hzw ((hW q).mp hq) with ⟨x,hOld⟩ | ⟨letter,pref,hCons⟩
  · obtain ⟨y,hy,_⟩ := hC.1.2 x hOld.1
    exact ⟨y,Or.inl ⟨x,hOld,hy⟩⟩
  · have hpref := (hW pref).mpr (ConstructionProbeRaw.cons_raw hCons).1
    obtain ⟨h,hh,_⟩ := hHL.1.2 pref hpref
    obtain ⟨factor,hf,_⟩ := hB.1.2 letter (ConstructionProbeRawAction.cons_letter hCons)
    obtain ⟨room,hRoom,hDiff,hSum,_,_⟩ := ConstructionCutDifference.exists_difference hM hw hQ
      ((hR h).mp (hHL.2 pref h hh)) hUnit (hHB pref h hh).2.1
    obtain ⟨y,_,hProd⟩ := ConstructionCutProduct.exists_product hM hw hQ hRoom ((hR factor).mp (hB.2 letter factor hf))
    exact ⟨y,Or.inr ⟨letter,pref,h,room,factor,hCons,hh,hDiff,hSum,hf,hProd⟩⟩

theorem value_bounds (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q D S zero W R unit one u HL C B eighth q y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : ConstructionRealCuts.Principal hM w Q u unit)
    (hHL : MapsTo W R HL) (hB : MapsTo S R B)
    (hHB : ConstructionCutWeights.RangeBound unit HL) (hCB : ConstructionProbeGateCap.Bounds unit C)
    (hBB : ConstructionProbeGateCap.Bounds eighth B) (hEU : Subset eighth unit)
    (hy : Value hM w Q D S zero unit HL C B q y) :
    (∃ p, (Project.FirstOrderSemantics.reduct M).mem p y) ∧ Subset y unit := by
  have hUnit := ConstructionRealCuts.principal_cut hM hw hQ ((hQ u).mpr ⟨one,one,hu⟩) hunit
  rcases hy with ⟨x,_,hx⟩ | ⟨letter,pref,h,room,factor,_,hh,hDiff,hSum,hf,hProd⟩
  · exact hCB x y hx
  · have hH := (hR h).mp (hHL.2 pref h hh)
    have hRoom := ConstructionCutDifference.value_cut hM hw hQ hUnit hDiff
    have hFactor := (hR factor).mp (hB.2 letter factor hf)
    have hRoomN : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p room := by
      obtain ⟨room',_,hd,_,_,hN⟩ := ConstructionCutDifference.exists_difference hM hw hQ hH hUnit (hHB pref h hh).2.1
      have he := ConstructionCutDifference.value_unique hM hd hDiff
      exact he ▸ hN (hHB pref h hh).2.2
    have hRoomLe := (ConstructionCutArithmetic.sum_contains hH hRoom hSum).2
    have hLeFactor := ConstructionCutProductUnit.bounded_right hM hw hQ hu hone hunit hFactor
      (ConstructionCutProduct.value_comm hM hw hProd) hRoomLe
    exact ⟨ConstructionCutProduct.value_nonempty hM hw hQ hRoom hFactor hProd hRoomN (hBB letter factor hf).1,
      fun p hp => hEU p ((hBB letter factor hf).2 p (hLeFactor p hp))⟩

theorem exists_cost (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q D S zero W R unit HL C B one u eighth : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : ConstructionRealCuts.Principal hM w Q u unit)
    (hW : ConstructionProbeRaw.Carrier w D S W) (hHL : MapsTo W R HL) (hC : MapsTo D R C) (hB : MapsTo S R B)
    (hHB : ConstructionCutWeights.RangeBound unit HL) (hCB : ConstructionProbeGateCap.Bounds unit C)
    (hBB : ConstructionProbeGateCap.Bounds eighth B) (hEU : Subset eighth unit) :
    ∃ CL, MapsTo W R CL ∧
      (∀ q y, PureKuratowski.PairMember M q y CL ↔ (Project.FirstOrderSemantics.reduct M).mem q W ∧ Value hM w Q D S zero unit HL C B q y) ∧
      ConstructionProbeGateCap.Bounds unit CL := by
  have hUnit := ConstructionRealCuts.principal_cut hM hw hQ ((hQ u).mpr ⟨one,one,hu⟩) hunit
  let schema : Project.BinarySchema 9 := {
    body := value 2 3 4 5 6 7 8 9 10 1 0
    freeClosed := value_freeClosed _ _ _ _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 9 := {
    bound := Fin.cases w (Fin.cases Q (Fin.cases D (Fin.cases S (Fin.cases zero
      (Fin.cases unit (Fin.cases HL (Fin.cases C (fun _ => B)))))))), free := fun _ => w }
  have he (q y : M.Carrier .set) : schema.denote env q y ↔ Value hM w Q D S zero unit HL C B q y :=
    value_semantics hM ((env.push q).push y) 2 3 4 5 6 7 8 9 10 1 0
  obtain ⟨CL,hCL,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := W) (target := R) (by
      intro q hq
      obtain ⟨y,hy⟩ := value_total hM hw hz hzw hQ hR hUnit hW hHL hC hB hHB hq
      exact ⟨y,(he q y).mpr hy⟩) (by
      intro q _ y z hy hzv
      exact value_unique hM hw hz hHL hC hB ((he _ _).mp hy) ((he _ _).mp hzv)) (by
      intro q y _ hy
      exact value_range hM hw hQ hR hUnit hC hB ((he _ _).mp hy))
  have hMaps : MapsTo W R CL := (ForcingSupportSize.native_mapsTo hM W R CL).mpr hCL
  have hEquations (q y) : PureKuratowski.PairMember M q y CL ↔
      (Project.FirstOrderSemantics.reduct M).mem q W ∧ Value hM w Q D S zero unit HL C B q y :=
    (hGraph q y).trans (and_congr_right (fun _ => he q y))
  exact ⟨CL,hMaps,hEquations,fun q y hy => value_bounds hM hw hQ hR hu hone hunit hHL hB hHB hCB hBB hEU ((hEquations q y).mp hy).2⟩

theorem cost_old_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q D S zero W unit HL C B CL x q y : M.Carrier .set}
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : ConstructionProbeRaw.Carrier w D S W)
    (hGraph : ∀ q y, PureKuratowski.PairMember M q y CL ↔
      (Project.FirstOrderSemantics.reduct M).mem q W ∧ Value hM w Q D S zero unit HL C B q y)
    (hOld : Old zero D x q) : PureKuratowski.PairMember M q y CL ↔ PureKuratowski.PairMember M x y C := by
  constructor
  · intro hy
    rcases ((hGraph q y).mp hy).2 with ⟨x',hx',hy'⟩ | ⟨letter,pref,h,room,factor,hCons,_,_,_,_,_⟩
    · have he := (PureKuratowski.code_injective hOld.2 hx'.2).2
      exact he.symm ▸ hy'
    · exact (ConstructionProbeRaw.old_ne_cons hz hOld hCons).elim
  · intro hy
    exact (hGraph q y).mpr ⟨(hW q).mpr (ConstructionProbeRaw.old_raw hM hz hzw hOld),Or.inl ⟨x,hOld,hy⟩⟩

theorem cost_snoc_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q D S zero W unit HL C B CL letter pref q y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hW : ConstructionProbeRaw.Carrier w D S W)
    (hGraph : ∀ q y, PureKuratowski.PairMember M q y CL ↔
      (Project.FirstOrderSemantics.reduct M).mem q W ∧ Value hM w Q D S zero unit HL C B q y)
    (hCons : Cons w D S letter pref q) :
    PureKuratowski.PairMember M q y CL ↔ ∃ h room factor, PureKuratowski.PairMember M pref h HL ∧
      ConstructionCutDifference.Value hM w Q h unit room ∧ SumCut hM w Q h room unit ∧
      PureKuratowski.PairMember M letter factor B ∧ ConstructionCutProduct.Value hM w Q room factor y := by
  constructor
  · intro hy
    rcases ((hGraph q y).mp hy).2 with ⟨x,hOld,_⟩ | ⟨letter',pref',h,room,factor,hCons',hh,hDiff,hSum,hf,hProd⟩
    · exact (ConstructionProbeRaw.old_ne_cons hz hOld hCons).elim
    · obtain ⟨he1,he2⟩ := ConstructionProbeRaw.cons_injective hM hw hCons hCons'
      subst letter';subst pref'
      exact ⟨h,room,factor,hh,hDiff,hSum,hf,hProd⟩
  · rintro ⟨h,room,factor,hh,hDiff,hSum,hf,hProd⟩
    exact (hGraph q y).mpr ⟨(hW q).mpr (ConstructionProbeRaw.cons_raw hCons).2,
      Or.inr ⟨letter,pref,h,room,factor,hCons,hh,hDiff,hSum,hf,hProd⟩⟩

/-- Both actual source Word weight graphs and all pointwise bounds, on SAME Raw carrier. -/
theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D S zero W one u unit H C HD CD e : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : ConstructionRealCuts.Principal hM w Q u unit)
    (hW : ConstructionProbeRaw.Carrier w D S W)
    (hH : MapsTo D R H) (hC : MapsTo D R C)
    (hHD : MapsTo S R HD) (hCD : MapsTo S R CD)
    (hHB : ConstructionCutWeights.RangeBound unit H) (hCB : ConstructionProbeGateCap.Bounds unit C)
    (hHDB : ConstructionCutWeights.RangeBound unit HD) (hCDB : ConstructionProbeGateCap.Bounds unit CD)
    (he : (Project.FirstOrderSemantics.reduct M).mem e D) :
    ∃ two three four five six seven eight quarter eighth O V B HL CL, (
      ConstructionBaseWeights.Digits w one two three ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf four three ∧ (Project.FirstOrderSemantics.reduct M).mem four w ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf five four ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf six five ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf seven six ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf eight seven ∧ (Project.FirstOrderSemantics.reduct M).mem eight w ∧
      ConstructionCutDivision.Value hM w Q four unit quarter ∧ ConstructionCutDivision.Value hM w Q eight unit eighth ∧
      (Project.FirstOrderSemantics.reduct M).mem quarter R ∧ (Project.FirstOrderSemantics.reduct M).mem eighth R ∧
      MapsTo S R O ∧ MapsTo S R V ∧ MapsTo S R B ∧
      ConstructionMergerWordParameters.Graph 0 hM w Q four unit quarter eighth S HD CD O ∧
      ConstructionMergerWordParameters.Graph 1 hM w Q four unit quarter eighth S HD CD V ∧
      ConstructionMergerWordParameters.Graph 2 hM w Q four unit quarter eighth S HD CD B ∧
      (∀ s theta sigma factor, PureKuratowski.PairMember M s theta O →
        PureKuratowski.PairMember M s sigma V → PureKuratowski.PairMember M s factor B →
        ConstructionMergerWordParameters.Recipe hM w Q four unit quarter eighth HD CD s theta sigma factor) ∧
      ConstructionCutWeights.RangeBound unit O ∧
      (∀ s sigma, PureKuratowski.PairMember M s sigma V → ∃ p, (Project.FirstOrderSemantics.reduct M).mem p sigma) ∧
      ConstructionProbeGateCap.Bounds eighth B) ∧
      MapsTo W R HL ∧ ConstructionProbeHeightFold.Laws hM w D S zero W Q H O V HL ∧
      ConstructionMergerWordHeights.LiteralLaws hM w Q D S zero unit H O HL ∧
      ConstructionCutWeights.RangeBound unit HL ∧ MapsTo W R CL ∧
      (∀ q y, PureKuratowski.PairMember M q y CL ↔ (Project.FirstOrderSemantics.reduct M).mem q W ∧ Value hM w Q D S zero unit HL C B q y) ∧
      ConstructionProbeGateCap.Bounds unit CL ∧
      (∀ x q y, Old zero D x q → (PureKuratowski.PairMember M q y CL ↔ PureKuratowski.PairMember M x y C)) ∧
      (∀ letter pref q y, Cons w D S letter pref q →
        (PureKuratowski.PairMember M q y CL ↔ ∃ h room factor, PureKuratowski.PairMember M pref h HL ∧
          ConstructionCutDifference.Value hM w Q h unit room ∧ SumCut hM w Q h room unit ∧
          PureKuratowski.PairMember M letter factor B ∧ ConstructionCutProduct.Value hM w Q room factor y)) := by
  have hUnit := ConstructionRealCuts.principal_cut hM hw hQ ((hQ u).mpr ⟨one,one,hu⟩) hunit
  have hZeroR := ConstructionMergerCoordinateLaws.empty_cut_mem hM hR hz ((hR unit).mpr hUnit)
  obtain ⟨oldUnitHeight,hOldEdge,_⟩ := hH.1.2 e he
  have hUnitN : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p unit := by
    obtain ⟨p,hp⟩ := (hHB e oldUnitHeight hOldEdge).1
    exact ⟨p,(hHB e oldUnitHeight hOldEdge).2.1 p hp⟩
  obtain ⟨two,three,four,five,six,seven,eight,quarter,eighth,O,V,B,hParamFields⟩ :=
    ConstructionMergerWordParameters.exists_system hM hw hQ hR hu.1 hone hUnit hUnitN hHD hCD hHDB hCDB
  have hRetained := hParamFields
  obtain ⟨hd,hFour,hFourW,hFive,hSix,hSeven,hEight,hEightW,hQuarter,hEighth,hQuarterR,hEighthR,hO,hV,hB,gO,gV,gB,hParams,hOB,hVP,hBB⟩ := hParamFields
  have hComp (letter theta sigma) (ho : PureKuratowski.PairMember M letter theta O)
      (hv : PureKuratowski.PairMember M letter sigma V) : SumCut hM w Q theta sigma unit := by
    obtain ⟨factor,hf,_⟩ := hB.1.2 letter (ForcingConditionGraphs.function_input hO.1 ho)
    obtain ⟨ah,ac,qh,qc,_,_,_,_,_,_,hc,_⟩ := hParams letter theta sigma factor ho hv hf
    exact hc
  obtain ⟨HL,hHL,hAffine⟩ := ConstructionMergerWordHeights.exists_height hM hw hz hzw hQ hR hZeroR hH hO hV hW
  have hHeightBound := ConstructionMergerWordHeights.height_bounds hM hw hz hzw hQ hR hu hone hunit hW hHL hO hV hB hOB hVP hParams hHB hAffine
  have hLiteral := ConstructionMergerWordHeights.literal_laws hM hw hQ hR hu hone hunit hW hO hV hHL hHeightBound hComp hAffine
  have hEU := ConstructionMergerHeightComparison.division_subset hM hw hu.1 hone hEightW ⟨seven,hEight.predecessor_mem⟩ hUnit hEighth
  obtain ⟨CL,hCL,hCostGraph,hCostBound⟩ := exists_cost hM hw hz hzw hQ hR hu hone hunit hW hHL hC hB hHeightBound hCB hBB hEU
  exact ⟨two,three,four,five,six,seven,eight,quarter,eighth,O,V,B,HL,CL,hRetained,hHL,hAffine,hLiteral,hHeightBound,hCL,hCostGraph,hCostBound,
    fun _ _ _ hOld => cost_old_iff hM hz hzw hW hCostGraph hOld,
    fun _ _ _ _ hCons => cost_snoc_iff hM hw hz hW hCostGraph hCons⟩

end PPAC.Migration.ConstructionMergerWordCosts
