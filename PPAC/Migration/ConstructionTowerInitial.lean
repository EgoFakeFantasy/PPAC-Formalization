/- Pinned ConstructionIteration.X0 and MonoidRounds.Under.mk(identity).
Construct the actual initial weighted identity and the SINGLE-stage incoming
family, using existing native identity/constant functions and cut supremum.
The fixed tuple carries exact internal time zero. No tower/recursor backend. -/
import PPAC.Migration.ConstructionTowerCanonicalLimit
import PPAC.Migration.ConstructionRequestCarrier

namespace PPAC.Migration.ConstructionTowerInitial
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (FunctionOn)
open ConstructionRoundFields
open ConstructionProbeMappedPath (NodeMap)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem identity_fields (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C identity : M.Carrier .set}
    (hR : ConstructionRealCuts.CutCarrier hM w Q R)
    (hTop : ConstructionRealCuts.Cut hM w Q top)
    (hObj : ObjectFields hM w Q R top D mul e mark H C)
    (hMaps : MapsTo D D identity) (hId : ForcingConditionGraphs.IdentityGraph D identity) :
    MapFields hM w Q D D mul mul e e mark mark H C H C identity := by
  obtain ⟨hMon,_,_,hMark,_,_,_,hCost,hCostBound,_,_,_⟩ := hObj
  have hCons : ConstructionProbeConservative.Conservative D D mul mul identity := by
    refine ⟨⟨hMaps,?_⟩,?_,?_,?_⟩
    · intro x y z hx hy
      exact ((hId x z).mp hx).2.trans ((hId y z).mp hy).2.symm
    · intro x y z fx fy hx hy hz _
      exact ⟨z,(hId z z).mpr ⟨hz,rfl⟩⟩
    · intro x y j fx fy fj hx hy hj hJoin
      simpa only [((hId x fx).mp hx).2,((hId y fy).mp hy).2,((hId j fj).mp hj).2] using hJoin
    · intro x y fx fy hx hy hCommon
      simpa only [← ((hId x fx).mp hx).2,← ((hId y fy).mp hy).2] using hCommon
  refine ⟨hCons,?_,(hId e e).mpr ⟨hMon.1.1,rfl⟩,(hId mark mark).mpr ⟨hMark,rfl⟩,?_,?_,?_⟩
  · intro x y z fx fy fz hprod hx hy hz
    simpa only [((hId x fx).mp hx).2,((hId y fy).mp hy).2,((hId z fz).mp hz).2] using hprod
  · intro x fx r hx
    rcases (hId x fx).mp hx with ⟨_,rfl⟩
    rfl
  · intro x fx r hx
    rcases (hId x fx).mp hx with ⟨_,rfl⟩
    rfl
  · intro x y fx fy hx hy
    rcases (hId x fx).mp hx with ⟨_,rfl⟩
    rcases (hId y fy).mp hy with ⟨_,rfl⟩
    obtain ⟨family,hF,hFR⟩ := ConstructionProbeCostSupremum.exists_family (x := x) (y := y) (mul := mul) hM hCost
    have hBound : ∀ c, (Project.FirstOrderSemantics.reduct M).mem c family → ConstructionRealCuts.Subset c top := by
      intro c hc
      obtain ⟨d,_,hd,_,_⟩ := (hF c).mp hc
      exact (hCostBound d c hd).2
    obtain ⟨cap,hCut,hUpper,hLeast⟩ := ConstructionRealCuts.bounded_union hM hR hFR hTop hBound
    have hCap : ConstructionProbeCostSupremum.Cap D mul C x y cap := ⟨family,hF,hUpper,hLeast⟩
    exact ⟨family,family,cap,hF,hF,hCut,hCap,hCap,
      fun _ _ hc hd => ConstructionProbeCostSupremum.cap_unique hM hc hd⟩

theorem identity_profiles {w D mul identity : M.Carrier .set}
    (hId : ForcingConditionGraphs.IdentityGraph D identity) : Profiles w D D mul mul identity := by
  intro a b d p node hp
  refine ⟨node,a,b,d,p,?_,(hId a a).mpr ⟨hp.1,rfl⟩,(hId b b).mpr ⟨hp.2.1,rfl⟩,
    (hId d d).mpr ⟨hp.2.2.1,rfl⟩,(hId p p).mpr ⟨hp.2.2.2.1,rfl⟩,hp⟩
  intro i y
  constructor
  · intro hy
    exact ⟨y,hy,(hId y y).mpr ⟨hp.2.2.2.2.1.2 i y hy,rfl⟩⟩
  · rintro ⟨x,hx,hxy⟩
    exact ((hId x y).mp hxy).2 ▸ hx

def Value (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one output : M.Carrier .set) : Prop :=
  ObjectFields hM w Q R top D mul e mark H C ∧ ∃ identity K, MapsTo D D identity ∧ ForcingConditionGraphs.IdentityGraph D identity ∧
    MapFields hM w Q D D mul mul e e mark mark H C H C identity ∧ Profiles w D D mul mul identity ∧
    FunctionOn one K ∧ ConstructionRequestCarrier.ConstantNode one identity K ∧
    PureKuratowski.PairMember M zero identity K ∧ ConstructionTowerSuccessor.BaseNatural one K K identity ∧
    ConstructionRoundSelection.Pack D mul e mark H C K identity zero output

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one x y : M.Carrier .set}
    (hx : Value hM w Q R top D mul e mark H C zero one x)
    (hy : Value hM w Q R top D mul e mark H C zero one y) : x = y := by
  obtain ⟨_,identity,K,hMaps,hId,_,_,hKF,hKG,_,_,hPack⟩ := hx
  obtain ⟨_,identity',K',hMaps',hId',_,_,hKF',hKG',_,_,hPack'⟩ := hy
  have heId := SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM D D identity).mp hMaps).1.1
    ((ForcingSupportSize.native_mapsTo hM D D identity').mp hMaps').1.1
    (fun x y => (hId x y).trans (hId' x y).symm)
  subst identity'
  have rel {A} (hA : FunctionOn one A) :
      (Project.FirstOrderSemantics.reduct M).IsSetRelation (KuratowskiZF.interpretation hM) A := by
    intro p hp
    obtain ⟨a,b,_,hc⟩ := hA.1 p hp
    exact ⟨a,b,hc⟩
  have heK := SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    (rel hKF) (rel hKF') (fun i f => (hKG i f).trans (hKG' i f).symm)
  subst K'
  exact ConstructionTowerCanonicalLimit.packet_unique hM hPack hPack'

theorem exists_value (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one : M.Carrier .set}
    (hR : ConstructionRealCuts.CutCarrier hM w Q R)
    (hTop : ConstructionRealCuts.Cut hM w Q top)
    (hObj : ObjectFields hM w Q R top D mul e mark H C)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hOne : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one) :
    ∃ output, Value hM w Q R top D mul e mark H C zero one output ∧
      ∀ other, Value hM w Q R top D mul e mark H C zero one other → other = output := by
  obtain ⟨identity,hPerm,hId⟩ := ForcingConditionGraphs.exists_identity hM D
  have hMaps : MapsTo D D identity := hPerm.1
  have hFields := identity_fields hM hR hTop hObj hMaps hId
  have hProfiles : Profiles w D D mul mul identity := identity_profiles hId
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨singleton,hS⟩ := KP.exists_singleton (ZF.modelsKP hZF) identity
  obtain ⟨K,hK,hKG⟩ := ZF.exists_constantFunction hZF (KuratowskiZF.interpretation hM)
    (source := one) ((hS identity).mpr rfl)
  have hFn := ((ForcingSupportSize.native_mapsTo hM one singleton K).mpr hK).1
  have hConst : ConstructionRequestCarrier.ConstantNode one identity K := hKG
  have hzOne : (Project.FirstOrderSemantics.reduct M).mem zero one := by
    obtain ⟨z,hz',hSucc⟩ := hOne
    apply (hSucc zero).mpr
    right
    intro x
    exact ⟨fun h => False.elim (hz x h),fun h => False.elim (hz' x h)⟩
  have hNatural : ConstructionTowerSuccessor.BaseNatural one K K identity := by
    intro i fi ki _ hfi hki
    have hefi := ((hKG i fi).mp hfi).2
    have heki := ((hKG i ki).mp hki).2
    subst fi; subst ki
    intro x y
    constructor
    · intro hxy
      exact ⟨x,(hId x x).mpr ⟨((hId x y).mp hxy).1,rfl⟩,hxy⟩
    · rintro ⟨z,hxz,hzy⟩
      exact ((hId x z).mp hxz).2.symm ▸ hzy
  obtain ⟨output,hPack⟩ := ConstructionRoundSelection.pack_exists hM D mul e mark H C K identity zero
  have hValue : Value hM w Q R top D mul e mark H C zero one output :=
    ⟨hObj,identity,K,hMaps,hId,hFields,hProfiles,hFn,hConst,(hKG zero identity).mpr ⟨hzOne,rfl⟩,hNatural,hPack⟩
  exact ⟨output,hValue,fun other hOther => value_unique hM hOther hValue⟩


def value {m : Nat} (w Q R top D mul e mark H C zero one output : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionRoundStepSyntax.objectFields w Q R top D mul e mark H C) (.existsE (.existsE (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (1 : Fin (m+2)) D.succ.succ D.succ.succ)) (.conj
  (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph D.succ.succ (1 : Fin (m+2)))) (.conj
  (ConstructionRoundStepSyntax.mapFields w.succ.succ Q.succ.succ D.succ.succ D.succ.succ mul.succ.succ
  mul.succ.succ e.succ.succ e.succ.succ mark.succ.succ mark.succ.succ H.succ.succ C.succ.succ H.succ.succ
  C.succ.succ (1 : Fin (m+2))) (.conj (ConstructionRoundStepSyntax.profiles w.succ.succ D.succ.succ
  D.succ.succ mul.succ.succ mul.succ.succ (1 : Fin (m+2))) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.functionOn (0 : Fin (m+2)) one.succ.succ)) (.conj
  (ConstructionRequestCarrier.constantNode one.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2))) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin (m+2)) zero.succ.succ (1 : Fin (m+2)))) (.conj
  (ConstructionTowerSuccessor.baseNatural one.succ.succ (0 : Fin (m+2)) (0 : Fin (m+2)) (1 : Fin (m+2)))
  (ConstructionRoundSelection.pack D.succ.succ mul.succ.succ e.succ.succ mark.succ.succ H.succ.succ
  C.succ.succ (0 : Fin (m+2)) (1 : Fin (m+2)) zero.succ.succ output.succ.succ))))))))))))

theorem value_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one output : Fin m) :
    (value w Q R top D mul e mark H C zero one output).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionRoundStepSyntax.objectFields_freeClosed,ConstructionRoundStepSyntax.mapFields_freeClosed,ConstructionRoundStepSyntax.profiles_freeClosed,ConstructionRequestCarrier.constantNode_freeClosed,ConstructionTowerSuccessor.baseNatural_freeClosed,ConstructionRoundSelection.pack_freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one output : Fin m) :
    Project.Formula.satisfies env (value w Q R top D mul e mark H C zero one output) ↔ Value hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound output) := by
  simp only [value,Value,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionRoundStepSyntax.objectFields_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),ForcingConditionGraphs.identityGraph_semantics (M := M),ConstructionRoundStepSyntax.mapFields_semantics hM,ConstructionRoundStepSyntax.profiles_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M),ConstructionRequestCarrier.constantNode_semantics hM,ConstructionTowerSuccessor.baseNatural_semantics hM,ConstructionRoundSelection.pack_semantics hM]
  rfl


def initialSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 12 (.imp (ConstructionRealCuts.cutCarrier (0 : Fin 12) (1 : Fin 12) (2 : Fin
    12)) (.imp (ConstructionRealCuts.cut (0 : Fin 12) (1 : Fin 12) (3 : Fin 12)) (.imp
    (ConstructionRoundStepSyntax.objectFields (0 : Fin 12) (1 : Fin 12) (2 : Fin 12) (3 : Fin 12) (4 : Fin
    12) (5 : Fin 12) (6 : Fin 12) (7 : Fin 12) (8 : Fin 12) (9 : Fin 12)) (.imp (Project.Formula.isEmpty
    (.bound (10 : Fin 12))) (.imp (Project.Formula.isOrdinalOne (.bound (11 : Fin 12))) (.existsE (.conj
    (value (0 : Fin 12).succ (1 : Fin 12).succ (2 : Fin 12).succ (3 : Fin 12).succ (4 : Fin 12).succ (5 :
    Fin 12).succ (6 : Fin 12).succ (7 : Fin 12).succ (8 : Fin 12).succ (9 : Fin 12).succ (10 : Fin 12).succ
    (11 : Fin 12).succ (0 : Fin 13)) (.forallE (.imp (value (0 : Fin 12).succ.succ (1 : Fin 12).succ.succ (2
    : Fin 12).succ.succ (3 : Fin 12).succ.succ (4 : Fin 12).succ.succ (5 : Fin 12).succ.succ (6 : Fin
    12).succ.succ (7 : Fin 12).succ.succ (8 : Fin 12).succ.succ (9 : Fin 12).succ.succ (10 : Fin
    12).succ.succ (11 : Fin 12).succ.succ (0 : Fin 14)) (Project.Formula.extensionalEq (.bound (0 : Fin 14))
    (.bound (0 : Fin 13).succ))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isEmpty,
      Project.Formula.isOrdinalOne,Project.Formula.extensionalEq,
      ConstructionRealCuts.cutCarrier_freeClosed,ConstructionRealCuts.cut_freeClosed,
      ConstructionRoundStepSyntax.objectFields_freeClosed,value_freeClosed]

theorem initial_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence initialSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) initialSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_isOrdinalOne_iff,
    ConstructionRealCuts.cutCarrier_semantics hM,ConstructionRealCuts.cut_semantics hM,
    ConstructionRoundStepSyntax.objectFields_semantics hM,value_semantics hM]
  exact fun hR hTop hObj hz hOne => exists_value hM hR hTop hObj hz hOne

theorem initial_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence initialSentence) := ModelTransfer.derives (fun _ hM => initial_models hM)

end PPAC.Migration.ConstructionTowerInitial
