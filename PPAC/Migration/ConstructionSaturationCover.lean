/- Pinned ContinuousTower.exists_rep / CompleteRounds.Saturation.countable_stage.
Read the SAME actual internal recursive history at its actual limit row.
No supplied coverage, external stages or replacement colimit. -/
import PPAC.Migration.ConstructionSaturationBoundedness

namespace PPAC.Migration.ConstructionSaturationCover
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row)
open ConstructionTowerValidity (Valid row_field)
open ForcingConditionGraphs (FunctionOn)
open ForcingSupportSize (Small)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}
variable {w Q R top D mul e mark H C zero one u K mu B history : M.Carrier .set}

def Representative (history F kappa x : M.Carrier .set) : Prop :=
  ∃ i N m v a W V incoming base leg y,
    (Project.FirstOrderSemantics.reduct M).mem i kappa ∧
    Row history i N m v a W V incoming base i ∧
    ForcingDiagramOrder.Product F i kappa leg ∧
    (Project.FirstOrderSemantics.reduct M).mem y N ∧ PureKuratowski.PairMember M y x leg

theorem exists_rep (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {P F kappa N m v a W V incoming base x : M.Carrier .set}
    (hCtx : ConstructionSaturationIterationCases.Context hM w Q R top D mul e mark H C zero one u K mu B)
    (hRec : ConstructionSaturationIteration.Recursive hM w Q R top D mul e mark H C zero one K mu B B history)
    (hF : ConstructionTowerTransitions.Matrix B history zero P F)
    (hLimit : (Project.FirstOrderSemantics.reduct M).IsLimitOrdinal kappa)
    (hk : (Project.FirstOrderSemantics.reduct M).mem kappa B)
    (hRow : Row history kappa N m v a W V incoming base kappa)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x N) :
    Representative history F kappa x := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let rawM := Project.FirstOrderSemantics.reduct M
  have hCtxCopy := hCtx
  obtain ⟨_,_,_,_,_,_,_,hz,_,_,_,_,_,_,hB,_⟩ := hCtxCopy
  have hValid := (ConstructionSaturationIterationValidity.recursive_valid_small hM hOrder hChoice
    hCtx hRec (fun _ h => h)).1
  obtain ⟨code,hCode,hTargetPack⟩ := hRow
  obtain ⟨prior,hRestrict,hOp⟩ := hRec.2 kappa hk code hCode
  have hPriorRec := Structure.IsRecursiveSequence.restriction hRec hk hRestrict
  have hPrior := ConstructionSaturationIterationValidity.recursive_valid_small hM hOrder hChoice
    hCtx hPriorRec (hB.transitive kappa hk)
  have hCase := (ConstructionSaturationIteration.valid_step hM hOrder hChoice hCtx
    ⟨hLimit.1,hk,hPrior.1,hPrior.2⟩ hOp).1
  rcases hCase with ⟨he,_⟩ | ⟨_,prev,hSucc,_⟩ | ⟨_,_,hValue⟩
  · obtain ⟨q,hq⟩ := hLimit.2.1
    exact False.elim (hz q (he ▸ hq))
  · obtain ⟨larger,hl,hpl⟩ := hLimit.2.2 prev hSucc.predecessor_mem
    rcases (hSucc larger).mp hl with hlp | he
    · exact False.elim (KP.mem_irrefl_d (ZF.modelsKP hZF) prev
        ((hLimit.1.mem hSucc.predecessor_mem).transitive larger hlp prev hpl))
    · have eq := hZF.1.eq_of_same_members larger prev he
      subst larger
      exact False.elim (KP.mem_irrefl_d (ZF.modelsKP hZF) prev hpl)
  · obtain ⟨Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P0,F0,hCharts,_,_,
      L,G,unitL,markL,HL,LC,Legs,baseL,next,identity,NewDomains,NewOut,hResult,_,hSelf,hPack⟩ := hValue
    have eqN := (ConstructionRoundSelection.pack_injective hPack hTargetPack).1
    subst N
    obtain ⟨rep,projection,Bproduct,hRep,hProjectionMap,hCarrier,hProjection,hBproduct,hG,hGraph,
      hUnit,hMark,hWeights,hObj,hCocone,hFull,hProfiles,hBase,hNatural,hBaseProfiles,hColimit,hCard,hUnique⟩ := hResult
    obtain ⟨p,hp,hpx⟩ := ConstructionDirectedLimitCarrier.projection_onto hCarrier hProjection hx
    obtain ⟨i,y,⟨hi,A,hAi,hy⟩,hCodeP⟩ := (hRep p).mp hp
    obtain ⟨leg,hLeg,_⟩ := hCocone.1.1.2 i hi
    have hyx : PureKuratowski.PairMember M y x leg :=
      (hCocone.2.2 i A leg hi hAi hLeg y x).mpr ⟨hy,p,hCodeP,hpx⟩
    obtain ⟨N0,m0,v0,a0,W0,V0,in0,b0,hSourceRow⟩ := hPrior.1.1.2 i hi
    have hN0 := ConstructionTowerHistory.chart_of_row 0 hCharts.1 hi hSourceRow
    have eqA := ForcingConditionGraphs.function_unique hCharts.1.1 hAi hN0
    subst A
    have hGlobalRow : Row history i N0 m0 v0 a0 W0 V0 in0 b0 i := by
      obtain ⟨c,hc,hp⟩ := hSourceRow
      exact ⟨c,((hRestrict.2 i c).mp hc).2,hp⟩
    obtain ⟨_,_,_,_,_,hNewGraph,_⟩ := hSelf
    have hNewLeg := (hNewGraph i leg).mpr (Or.inl hLeg)
    have hFinalRow : Row history kappa L G unitL markL HL LC NewOut baseL kappa :=
      ⟨code,hCode,hPack⟩
    have hGlobalLeg : ForcingDiagramOrder.Product F i kappa leg :=
      (ConstructionTowerTransitions.matrix_at hValid.1 hF (hB.transitive kappa hk i hi) hk
        (Or.inl hi) (row_field 6 hFinalRow)).mpr hNewLeg
    exact ⟨i,N0,m0,v0,a0,W0,V0,in0,b0,leg,y,hi,hGlobalRow,hGlobalLeg,hy,hyx⟩


def Birth (F kappa input a i : M.Carrier .set) : Prop :=
  ∃ x leg y, PureKuratowski.PairMember M a x input ∧
    ForcingDiagramOrder.Product F i kappa leg ∧ PureKuratowski.PairMember M y x leg

def birth {m : Nat} (F kappa input a i : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge input.succ.succ.succ a.succ.succ.succ 2))
      (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product F.succ.succ.succ i.succ.succ.succ kappa.succ.succ.succ 1))
        (ProjectSyntax.encode id (Source.SetLanguage.edge 1 0 2))))))

theorem birth_freeClosed {m : Nat} (F kappa input a i : Fin m) :
    (birth F kappa input a i).FreeClosed := by
  simp -implicitDefEqProofs [birth,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem birth_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (F kappa input a i : Fin m) :
    Project.Formula.satisfies env (birth F kappa input a i) ↔
      Birth (env.bound F) (env.bound kappa) (env.bound input) (env.bound a) (env.bound i) := by
  simp only [birth,Birth,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,ForcingDiagramOrder.product_semantics (M := M)]
  rfl

def preimage {m : Nat} (input leg a y : Fin m) : Project.Formula 1 m :=
  .existsE (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.edge input.succ a.succ 0))
    (ProjectSyntax.encode id (Source.SetLanguage.edge leg.succ y.succ 0)))

theorem preimage_freeClosed {m : Nat} (input leg a y : Fin m) :
    (preimage input leg a y).FreeClosed := by
  simp -implicitDefEqProofs [preimage,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem preimage_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (input leg a y : Fin m) :
    Project.Formula.satisfies env (preimage input leg a y) ↔
      ∃ x, PureKuratowski.PairMember M (env.bound a) x (env.bound input) ∧
        PureKuratowski.PairMember M (env.bound y) x (env.bound leg) := by
  simp only [preimage,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def Factor (history F kappa A input : M.Carrier .set) : Prop :=
  ∃ j N m v a W V incoming base leg lift,
    (Project.FirstOrderSemantics.reduct M).mem j kappa ∧
    Row history j N m v a W V incoming base j ∧
    ForcingDiagramOrder.Product F j kappa leg ∧ ForcingSupportSize.MapsTo A N lift ∧
    ConstructionProbeMappedPath.NodeMap lift leg input

theorem exists_factor (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {P F kappa N m v a W V incoming base A input : M.Carrier .set}
    (hCtx : ConstructionSaturationIterationCases.Context hM w Q R top D mul e mark H C zero one u K mu B)
    (hRec : ConstructionSaturationIteration.Recursive hM w Q R top D mul e mark H C zero one K mu B B history)
    (hF : ConstructionTowerTransitions.Matrix B history zero P F)
    (hHartogs : ConstructionSaturationIndex.Hartogs hM w kappa)
    (hRegular : (Project.FirstOrderSemantics.reduct M).IsRegularCardinal (KuratowskiZF.interpretation hM) kappa)
    (hk : (Project.FirstOrderSemantics.reduct M).mem kappa B)
    (hRow : Row history kappa N m v a W V incoming base kappa)
    (hSmall : ForcingSupportSize.Small A w) (hInput : ForcingSupportSize.MapsTo A N input) :
    Factor history F kappa A input := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let rawM := Project.FirstOrderSemantics.reduct M
  let I := KuratowskiZF.interpretation hM
  have hCtxCopy := hCtx
  obtain ⟨hw,_,_,_,_,_,_,_,_,_,_,_,_,_,hB,_⟩ := hCtxCopy
  have hValid := (ConstructionSaturationIterationValidity.recursive_valid_small hM hOrder hChoice
    hCtx hRec (fun _ h => h)).1
  let birthSchema : Project.BinarySchema 3 :=
    { body := birth 2 3 4 1 0, freeClosed := birth_freeClosed .. }
  let birthEnv : SetTheory.Env rawM 3 :=
    { bound := fun n => match n.val with | 0 => F | 1 => kappa | _ => input
      free := fun _ => zero }
  have hBirth a i : birthSchema.denote birthEnv a i ↔ Birth F kappa input a i :=
    birth_semantics hM (birthEnv.push a |>.push i) 2 3 4 1 0
  obtain ⟨birthMap,hBirthMap,hBirthValues⟩ := ExistingSmallUnion.uniformize_formula_l I
    (ConstructionDirectedCardinality.models_zfc hM hChoice) birthSchema birthEnv
    (X := A) (Y := kappa) (by
      intro a ha
      obtain ⟨x,hax,_⟩ := hInput.1.2 a ha
      obtain ⟨i,N0,m0,v0,a0,W0,V0,in0,b0,leg,y,hi,_,hLeg,_,hyx⟩ :=
        exists_rep hM hOrder hChoice hCtx hRec hF hRegular.isLimitOrdinal hk hRow (hInput.2 a x hax)
      exact ⟨i,hi,(hBirth a i).mpr ⟨x,leg,y,hax,hLeg,hyx⟩⟩)
  obtain ⟨j,hj,hBound⟩ := ConstructionSaturationBoundedness.countable_bounded hM hw hHartogs
    hRegular hSmall hBirthMap
  have hjB := hB.transitive kappa hk j hj
  obtain ⟨Nj,mj,vj,aj,Wj,Vj,Ij,bj,hRowJ⟩ := hValid.1.2 j hjB
  have hRows := ConstructionTowerValidity.incoming_rows hM hValid
  have leg_exists (i j) (hi : rawM.mem i B) (hj : rawM.mem j B) :
      ∃ leg, ForcingDiagramOrder.Product F i j leg := by
    obtain ⟨leg,hleg⟩ := ConstructionTowerTransitions.leg_total (zero := zero) (i := i) hValid.1 hRows hj
    exact ⟨leg,(hF.2.2 i j leg).mpr ⟨hi,hj,hleg⟩⟩
  obtain ⟨leg,hLeg⟩ := leg_exists j kappa hjB hk
  have hLegIn := (ConstructionTowerTransitions.matrix_at hValid.1 hF hjB hk (Or.inl hj)
    (row_field 6 hRow)).mp hLeg
  have hMap := (hValid.2.2.1 j kappa Nj mj vj aj Wj Vj Ij bj N m v a W V incoming base leg
    hjB hk (Or.inl hj) hRowJ hRow hLegIn).1.1.1.1
  have hInjection := (hValid.2.2.1 j kappa Nj mj vj aj Wj Vj Ij bj N m v a W V incoming base leg
    hjB hk (Or.inl hj) hRowJ hRow hLegIn).1.1.1
  have hPreimages : ∀ a, rawM.mem a A → ∃ y, rawM.mem y Nj ∧
      ∃ x, PureKuratowski.PairMember M a x input ∧ PureKuratowski.PairMember M y x leg := by
    intro a ha
    obtain ⟨i,hi,hai⟩ := hBirthMap.2.2 a ha
    obtain ⟨x,oldLeg,y,hax,hOldLeg,hyx⟩ := (hBirth a i).mp (hBirthValues a i hai)
    have hiB := hB.transitive kappa hk i hi
    have hij : ConstructionTowerTransitions.Before i j := (hBound a i hai).elim Or.inr Or.inl
    obtain ⟨middle,hMiddle⟩ := leg_exists i j hiB hjB
    have hMiddleIn := (ConstructionTowerTransitions.matrix_at hValid.1 hF hiB hjB hij
      (row_field 6 hRowJ)).mp hMiddle
    have hOldIn := (ConstructionTowerTransitions.matrix_at hValid.1 hF hiB hk (Or.inl hi)
      (row_field 6 hRow)).mp hOldLeg
    have hComposition := hValid.2.2.2.1 i j kappa Ij incoming middle leg oldLeg
      hiB hjB hk hij (Or.inl hj) (row_field 6 hRowJ) (row_field 6 hRow)
      hMiddleIn hLegIn hOldIn
    obtain ⟨z,_,hzx⟩ := (hComposition y x).mp hyx
    exact ⟨z,ForcingConditionGraphs.function_input hMap.1 hzx,x,hax,hzx⟩
  let liftSchema : Project.BinarySchema 2 :=
    { body := preimage 2 3 1 0, freeClosed := preimage_freeClosed .. }
  let liftEnv : SetTheory.Env rawM 2 :=
    { bound := fun n => if n.val = 0 then input else leg, free := fun _ => zero }
  have hLift a y : liftSchema.denote liftEnv a y ↔
      ∃ x, PureKuratowski.PairMember M a x input ∧ PureKuratowski.PairMember M y x leg :=
    preimage_semantics hM (liftEnv.push a |>.push y) 2 3 1 0
  obtain ⟨lift,hLiftMap,hLiftGraph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I liftSchema liftEnv
    (source := A) (target := Nj)
    (by intro a ha; obtain ⟨y,_,hy⟩ := hPreimages a ha; exact ⟨y,(hLift a y).mpr hy⟩)
    (by
      intro a ha y z hy hz
      obtain ⟨x,hax,hyx⟩ := (hLift a y).mp hy
      obtain ⟨x',hax',hzx⟩ := (hLift a z).mp hz
      have ex := ForcingConditionGraphs.function_unique hInput.1 hax' hax
      exact hInjection.2 y z x hyx (ex ▸ hzx))
    (by
      intro a y ha hy
      obtain ⟨x,_,hyx⟩ := (hLift a y).mp hy
      exact ForcingConditionGraphs.function_input hMap.1 hyx)
  refine ⟨j,Nj,mj,vj,aj,Wj,Vj,Ij,bj,leg,lift,hj,hRowJ,hLeg,
    (ForcingSupportSize.native_mapsTo hM A Nj lift).mpr hLiftMap,?_⟩
  intro a x
  constructor
  · intro hax
    obtain ⟨y,_,hay⟩ := hLiftMap.2.2 a (ForcingConditionGraphs.function_input hInput.1 hax)
    obtain ⟨x',hax',hyx'⟩ := (hLift a y).mp ((hLiftGraph a y).mp hay).2
    have ex := ForcingConditionGraphs.function_unique hInput.1 hax' hax
    exact ⟨y,hay,ex ▸ hyx'⟩
  · rintro ⟨y,hay,hyx⟩
    obtain ⟨x',hax',hyx'⟩ := (hLift a y).mp ((hLiftGraph a y).mp hay).2
    have ex := ForcingConditionGraphs.function_unique hMap.1 hyx' hyx
    exact ex ▸ hax'


/-- Coverage of every internal countable family at the actual final row. -/
def Covered (w history F kappa : M.Carrier .set) : Prop :=
  ∀ N m v a W V incoming base A input,
    Row history kappa N m v a W V incoming base kappa →
    ForcingSupportSize.Small A w → ForcingSupportSize.MapsTo A N input →
      Factor history F kappa A input

/-- Quantify the SAME actual recursive history and its SAME matrix.
This universal property applies in particular to the constructed tower. -/
def AllHistoriesCovered (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one K mu kappa B : M.Carrier .set) : Prop :=
  ∀ history P F,
    ConstructionSaturationIteration.Recursive hM w Q R top D mul e mark H C zero one K mu B B history →
    ConstructionTowerTransitions.Matrix B history zero P F → Covered w history F kappa

def CoveredTower (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one u K mu kappa B : M.Carrier .set) : Prop :=
  ConstructionSaturationIndex.Tower hM w Q R top D mul e mark H C zero one u K mu kappa B ∧
  AllHistoriesCovered hM w Q R top D mul e mark H C zero one K mu kappa B

theorem tower_covered (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {kappa : M.Carrier .set}
    (hTower : ConstructionSaturationIndex.Tower hM w Q R top D mul e mark H C zero one u K mu kappa B) :
    CoveredTower hM w Q R top D mul e mark H C zero one u K mu kappa B := by
  refine ⟨hTower,?_⟩
  intro history P F hRec hF N m v a W V incoming base A input hRow hSmall hInput
  exact exists_factor hM hOrder hChoice hTower.2.1 hRec hF hTower.1.1 hTower.1.2.1
    hTower.1.2.2.2.1.predecessor_mem hRow hSmall hInput

theorem exists_covered_tower (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top D mul e mark H C zero one u K mu : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : ConstructionRealCuts.CutCarrier hM w Q R)
    (hCoordinates : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hTop : ConstructionRealCuts.Principal hM w Q u top)
    (hObj : ConstructionRoundFields.ObjectFields hM w Q R top D mul e mark H C)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hK : ∃ k, (Project.FirstOrderSemantics.reduct M).mem k K)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hpow : (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation (KuratowskiZF.interpretation hM) mu mu w)
    (hD : Small D mu) (hKSmall : Small K mu) (hOmegaOne : ConstructionSaturationIndex.OmegaOneLe hM w mu) :
    ∃ kappa B, CoveredTower hM w Q R top D mul e mark H C zero one u K mu kappa B := by
  obtain ⟨kappa,B,hTower⟩ := ConstructionSaturationIndex.exists_tower hM hOrder hChoice
    hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall hOmegaOne
  exact ⟨kappa,B,tower_covered hM hOrder hChoice hTower⟩


def factor {m : Nat} (history F kappa A input : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.conj (.mem (.bound (10 : Fin (m+11))) (.bound
  kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.conj (ConstructionTowerHistory.row
  history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (10 : Fin (m+11)) (9 : Fin (m+11)) (8 : Fin
  (m+11)) (7 : Fin (m+11)) (6 : Fin (m+11)) (5 : Fin (m+11)) (4 : Fin (m+11)) (3 : Fin (m+11)) (2 : Fin
  (m+11)) (10 : Fin (m+11))) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product
  F.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (10 : Fin (m+11))
  kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin (m+11)))) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin (m+11))
  A.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin (m+11))))
  (ConstructionProbeMappedPathSyntax.nodeMap (0 : Fin (m+11)) (1 : Fin (m+11))
  input.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))))))))))))))))

theorem factor_freeClosed {m : Nat} (history F kappa A input : Fin m) :
    (factor history F kappa A input).FreeClosed := by
  simp -implicitDefEqProofs [factor,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed]

theorem factor_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (history F kappa A input : Fin m) :
    Project.Formula.satisfies env (factor history F kappa A input) ↔ Factor (env.bound history) (env.bound F) (env.bound kappa) (env.bound A) (env.bound input) := by
  simp only [factor,Factor,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionTowerHistory.row_semantics hM,ForcingDiagramOrder.product_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),ConstructionProbeMappedPathSyntax.nodeMap_semantics hM]
  rfl


def covered {m : Nat} (w history F kappa : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp
  (ConstructionTowerHistory.row history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin (m+10)) (8 : Fin (m+10)) (7 : Fin (m+10))
  (6 : Fin (m+10)) (5 : Fin (m+10)) (4 : Fin (m+10)) (3 : Fin (m+10)) (2 : Fin (m+10))
  kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.imp (ProjectSyntax.encode id
  (ForcingSupportSize.small (1 : Fin (m+10)) w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin (m+10)) (1 : Fin (m+10)) (9 : Fin (m+10))))
  (factor history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  F.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin (m+10)) (0 : Fin (m+10))))))))))))))))

theorem covered_freeClosed {m : Nat} (w history F kappa : Fin m) :
    (covered w history F kappa).FreeClosed := by
  simp -implicitDefEqProofs [covered,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionTowerHistory.row_freeClosed,factor_freeClosed]

theorem covered_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w history F kappa : Fin m) :
    Project.Formula.satisfies env (covered w history F kappa) ↔ Covered (env.bound w) (env.bound history) (env.bound F) (env.bound kappa) := by
  simp only [covered,Covered,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionTowerHistory.row_semantics hM,ForcingSupportSize.small_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),factor_semantics hM]
  rfl


def allHistoriesCovered {m : Nat} (w Q R top D mul e mark H C zero one K mu kappa B : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.imp (ConstructionSaturationIteration.recursive w.succ.succ.succ
  Q.succ.succ.succ R.succ.succ.succ top.succ.succ.succ D.succ.succ.succ mul.succ.succ.succ e.succ.succ.succ
  mark.succ.succ.succ H.succ.succ.succ C.succ.succ.succ zero.succ.succ.succ one.succ.succ.succ
  K.succ.succ.succ mu.succ.succ.succ B.succ.succ.succ B.succ.succ.succ (2 : Fin (m+3))) (.imp
  (ConstructionTowerTransitions.matrix B.succ.succ.succ (2 : Fin (m+3)) zero.succ.succ.succ (1 : Fin (m+3))
  (0 : Fin (m+3))) (covered w.succ.succ.succ (2 : Fin (m+3)) (0 : Fin (m+3)) kappa.succ.succ.succ))))))

theorem allHistoriesCovered_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one K mu kappa B : Fin m) :
    (allHistoriesCovered w Q R top D mul e mark H C zero one K mu kappa B).FreeClosed := by
  simp -implicitDefEqProofs [allHistoriesCovered,Definitional.Formula.FreeClosed,ConstructionSaturationIteration.recursive_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,covered_freeClosed]

theorem allHistoriesCovered_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one K mu kappa B : Fin m) :
    Project.Formula.satisfies env (allHistoriesCovered w Q R top D mul e mark H C zero one K mu kappa B) ↔ AllHistoriesCovered hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound K) (env.bound mu) (env.bound kappa) (env.bound B) := by
  simp only [allHistoriesCovered,AllHistoriesCovered,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    
    ConstructionSaturationIteration.recursive_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,covered_semantics hM]
  rfl


def coveredTower {m : Nat} (w Q R top D mul e mark H C zero one u K mu kappa B : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionSaturationIndex.tower w Q R top D mul e mark H C zero one u K mu kappa B)
  (allHistoriesCovered w Q R top D mul e mark H C zero one K mu kappa B))

theorem coveredTower_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one u K mu kappa B : Fin m) :
    (coveredTower w Q R top D mul e mark H C zero one u K mu kappa B).FreeClosed := by
  simp -implicitDefEqProofs [coveredTower,Definitional.Formula.FreeClosed,ConstructionSaturationIndex.tower_freeClosed,allHistoriesCovered_freeClosed]

theorem coveredTower_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one u K mu kappa B : Fin m) :
    Project.Formula.satisfies env (coveredTower w Q R top D mul e mark H C zero one u K mu kappa B) ↔ CoveredTower hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound u) (env.bound K) (env.bound mu) (env.bound kappa) (env.bound B) := by
  simp only [coveredTower,CoveredTower,
    Project.Formula.satisfies_conj_iff,
    
    ConstructionSaturationIndex.tower_semantics hM,allHistoriesCovered_semantics hM]


def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 15 (.imp (Project.Formula.isOmega (.bound (0 : Fin 15))) (.imp
    (ConstructionFractionOrder.carrier (0 : Fin 15) (1 : Fin 15)) (.imp (ConstructionRealCuts.cutCarrier (0
    : Fin 15) (1 : Fin 15) (2 : Fin 15)) (.imp (ConstructionFractionOrder.coordinates (0 : Fin 15) (12 : Fin
    15) (11 : Fin 15) (11 : Fin 15)) (.imp (Project.Formula.isOrdinalOne (.bound (11 : Fin 15))) (.imp
    (ConstructionRealCuts.principal (0 : Fin 15) (1 : Fin 15) (12 : Fin 15) (3 : Fin 15)) (.imp
    (ConstructionRoundStepSyntax.objectFields (0 : Fin 15) (1 : Fin 15) (2 : Fin 15) (3 : Fin 15) (4 : Fin
    15) (5 : Fin 15) (6 : Fin 15) (7 : Fin 15) (8 : Fin 15) (9 : Fin 15)) (.imp (Project.Formula.isEmpty
    (.bound (10 : Fin 15))) (.imp (.mem (.bound (10 : Fin 15)) (.bound (0 : Fin 15))) (.imp (.existsE (.mem
    (.bound (0 : Fin 16)) (.bound (13 : Fin 15).succ))) (.imp (Project.Formula.isInfiniteCardinal
    PureKuratowskiProject.convention (.bound (0 : Fin 15)) (.bound (14 : Fin 15))) (.imp
    (Project.Formula.isCardinalExponentiation PureKuratowskiProject.convention (.bound (14 : Fin 15))
    (.bound (14 : Fin 15)) (.bound (0 : Fin 15))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small
    (4 : Fin 15) (14 : Fin 15))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (13 : Fin 15) (14
    : Fin 15))) (.imp (ConstructionSaturationIndex.omegaOneLe (0 : Fin 15) (14 : Fin 15)) (.existsE (.existsE (coveredTower (0 : Fin
    15).succ.succ (1 : Fin 15).succ.succ (2 : Fin 15).succ.succ (3 : Fin 15).succ.succ (4 : Fin
    15).succ.succ (5 : Fin 15).succ.succ (6 : Fin 15).succ.succ (7 : Fin 15).succ.succ (8 : Fin
    15).succ.succ (9 : Fin 15).succ.succ (10 : Fin 15).succ.succ (11 : Fin 15).succ.succ (12 : Fin
    15).succ.succ (13 : Fin 15).succ.succ (14 : Fin 15).succ.succ (1 : Fin 17) (0 : Fin
    17))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,ConstructionFractionOrder.carrier_freeClosed,
      ConstructionRealCuts.cutCarrier_freeClosed,ConstructionFractionOrder.coordinates_freeClosed,
      Project.Formula.isOrdinalOne,ConstructionRealCuts.principal_freeClosed,
      ConstructionRoundStepSyntax.objectFields_freeClosed,Project.Formula.isEmpty,
      Project.Formula.isInfiniteCardinal,Project.Formula.isCardinalExponentiation,Project.Formula.isFunctionSpace,
      ConstructionSaturationIndex.omegaOneLe_freeClosed,coveredTower_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isOrdinalOne_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isCardinalExponentiation_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    ConstructionFractionOrder.coordinates_semantics hM,ConstructionRealCuts.principal_semantics hM,
    ConstructionRoundStepSyntax.objectFields_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationIndex.omegaOneLe_semantics hM,coveredTower_semantics hM]
  exact fun hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall hOmegaOne =>
    exists_covered_tower hM hOrder hChoice hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall hOmegaOne

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative constructionSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let z := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => z }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM constructionSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) constructionSentence).mp
    (construction_models hL (ConstructionRoundSelection.l_order hM) hChoice)




end PPAC.Migration.ConstructionSaturationCover
