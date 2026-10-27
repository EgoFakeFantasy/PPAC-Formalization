/- Pinned CompleteRounds.RoundOrdinal / OuterIndex / countable_bounded.
Construct internal omega1 = Hartogs(omega), use the EXISTING donor successor
regularity and native successor, and consume the original omega1<=mu bound.
No external countability, inaccessible, GCH or rebuilt cardinal backend. -/
import PPAC.Migration.ExistingSuccessorRegularity
import PPAC.Migration.ConstructionSaturationIterationValidity
import YesMetaZFC.SetTheory.Card.Cofinality.Boundedness

namespace PPAC.Migration.ConstructionSaturationIndex
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (Small)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

abbrev Hartogs (hM : FirstOrder.Theory.Models M nativeZF) (w kappa : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) kappa w

def OmegaOneLe (hM : FirstOrder.Theory.Models M nativeZF) (w mu : M.Carrier .set) : Prop :=
  ∃ kappa, (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) kappa w ∧ Small kappa mu

def Data (hM : FirstOrder.Theory.Models M nativeZF) (w mu kappa B : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) kappa w ∧
  (Project.FirstOrderSemantics.reduct M).IsRegularCardinal (KuratowskiZF.interpretation hM) kappa ∧
  (Project.FirstOrderSemantics.reduct M).mem w kappa ∧
  (Project.FirstOrderSemantics.reduct M).SuccessorOf B kappa ∧
  (Project.FirstOrderSemantics.reduct M).IsOrdinal B ∧ Small kappa mu ∧ Small B mu

theorem hartogs_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w a b : M.Carrier .set}
    (ha : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) a w)
    (hb : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) b w) : a = b := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hKP := ZF.modelsKP hZF
  rcases Structure.IsOrdinal.trichotomy hZF.1 ha.1 hb.1 (KP.difference_exists_d hKP)
      (KP.intersection_exists_d hKP a b) with he | hlt | hgt
  · exact hZF.1.eq_of_same_members a b he
  · exact False.elim (ha.not_cardinalLessOrEqual hKP ((hb.2 a ha.1).mp hlt))
  · exact False.elim (hb.not_cardinalLessOrEqual hKP ((ha.2 b hb.1).mp hgt))

theorem exists_omega_one (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) :
    ∃ kappa, (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) kappa w ∧
      (Project.FirstOrderSemantics.reduct M).IsRegularCardinal (KuratowskiZF.interpretation hM) kappa ∧
      (Project.FirstOrderSemantics.reduct M).mem w kappa := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨kappa,hKappa⟩ := ExistingOrdinalEnumeration.exists_hartogsNumber_kernel hZF I w
  have hWC := ExistingCardinalBounds.omega_cardinal_l I hZF hw
  obtain ⟨id,hId⟩ := ZF.exists_identityBijection hZF I w
  have hWI : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal I w w := ⟨hWC,id,hId.1⟩
  exact ⟨kappa,hKappa,ExistingSuccessorRegularity.hartogs_regular_l I
    (ConstructionDirectedCardinality.models_zfc hM hChoice) hw hWI hKappa,
    (hKappa.2 w hWC.1).mpr ⟨id,hId.1⟩⟩

/-- The existing infinite two-set union bound handles the one added top.
The actual singleton/constant function and successor equations are retained. -/
theorem successor_small (hM : FirstOrder.Theory.Models M nativeZF)
    {w mu kappa B : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hKappa : Small kappa mu)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B kappa) : Small B mu := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  have hWC := ExistingCardinalBounds.omega_cardinal_l I hZF hw
  have hMuLimit := ZF.infiniteCardinal_isLimitOrdinal hZF I hw hWC hmu
  obtain ⟨z,_,hzw⟩ := hw.1.1
  have hzmu := hw.subset_limitOrdinal hZF hMuLimit z hzw
  obtain ⟨single,hSingle⟩ := KP.exists_singleton (ZF.modelsKP hZF) kappa
  obtain ⟨f,hf,_⟩ := ZF.exists_constantFunction hZF I (source := single) hzmu
  have hSingleSmall : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual I single mu := by
    refine ⟨f,hf,?_⟩
    intro a b v ha hb
    exact ((hSingle a).mp (hf.input_mem_of_pairMember ha)).trans
      ((hSingle b).mp (hf.input_mem_of_pairMember hb)).symm
  have hUnion : (Project.FirstOrderSemantics.reduct M).IsUnionOfTwo B kappa single := by
    intro x
    constructor
    · intro hx
      rcases (hB x).mp hx with hx | he
      · exact Or.inl hx
      · exact Or.inr ((hSingle x).mpr (hZF.1.eq_of_same_members x kappa he))
    · rintro (hx | hx)
      · exact (hB x).mpr (Or.inl hx)
      · have eq := (hSingle x).mp hx
        subst x
        exact hB.predecessor_mem
  exact (ForcingSupportSize.native_small hM B mu).mpr
    (ExistingCardinalBounds.infinite_union_two_l I hZF hw hmu
      ((ForcingSupportSize.native_small hM kappa mu).mp hKappa) hSingleSmall hUnion)

theorem exists_index (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w mu : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hBound : OmegaOneLe hM w mu) : ∃ kappa B, Data hM w mu kappa B := by
  obtain ⟨kappa,hKappa,hReg,hwk⟩ := exists_omega_one hM hChoice hw
  obtain ⟨given,hGiven,hGivenSmall⟩ := hBound
  have eq := hartogs_unique hM hGiven hKappa
  subst given
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨B,hB⟩ := KP.exists_successor (ZF.modelsKP hZF) kappa
  exact ⟨kappa,B,hKappa,hReg,hwk,hB,KP.successor_isOrdinal (ZF.modelsKP hZF) hKappa.1 hB,
    hGivenSmall,successor_small hM hw hmu hGivenSmall hB⟩

/-- The actual concrete omega1+1 tower; retain its SAME recursive history,
all 12 tables, full weighted/base diagram, bounds and adjacent round trace. -/
def Tower (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one u K mu kappa B : M.Carrier .set) : Prop :=
  Data hM w mu kappa B ∧
  ConstructionSaturationIterationCases.Context hM w Q R top D mul e mark H C zero one u K mu B ∧
  ∃ history Domains Muls Units Marks Heights Costs Incoming Origins Times E P F,
    ConstructionSaturationIteration.Recursive hM w Q R top D mul e mark H C zero one K mu B B history ∧
    ConstructionTowerValidity.Valid hM w Q R top D mul e mark H C B history ∧
    ConstructionTowerCardinality.AllSmall B history mu ∧
    ConstructionTowerHistory.Charts B history Domains Muls Units Marks Heights Costs Incoming Origins Times ∧
    ForcingConditionGraphs.IdentityGraph B Times ∧ ConstructionTowerTransitions.Order B E ∧
    ConstructionTowerTransitions.Matrix B history zero P F ∧
    ConstructionTowerDiagram.Data hM w Q R top D mul e mark H C B E Domains F Muls Units Marks Heights Costs Origins ∧
    (∀ i j, (Project.FirstOrderSemantics.reduct M).mem i B →
      (Project.FirstOrderSemantics.reduct M).mem j B →
      (Project.FirstOrderSemantics.reduct M).SuccessorOf j i →
      ∃ raw, ConstructionSaturationIterationValidity.SelectedAt hM w Q R top zero one K mu history F i j raw)

theorem exists_tower (hM : FirstOrder.Theory.Models M nativeZF)
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
    (hD : Small D mu) (hKSmall : Small K mu) (hOmegaOne : OmegaOneLe hM w mu) :
    ∃ kappa B, Tower hM w Q R top D mul e mark H C zero one u K mu kappa B := by
  obtain ⟨kappa,B,hData⟩ := exists_index hM hChoice hw hmu hOmegaOne
  have hCtx : ConstructionSaturationIterationCases.Context hM w Q R top D mul e mark H C zero one u K mu B :=
    ⟨hw,hQ,hR,hCoordinates,hone,hTop,hObj,hz,hzw,hK,hmu,hpow,hD,hKSmall,hData.2.2.2.2.1,hData.2.2.2.2.2.2⟩
  exact ⟨kappa,B,hData,hCtx,ConstructionSaturationIterationValidity.exists_tower hM hOrder hChoice hCtx⟩

def hartogs {m : Nat} (w kappa : Fin m) : Project.Formula 1 m :=
  (.conj (Project.Formula.isOrdinal (.bound kappa)) (.forallE (.imp (Project.Formula.isOrdinal (.bound (0 :
  Fin (m+1)))) (.iff (.mem (.bound (0 : Fin (m+1))) (.bound kappa.succ)) (ProjectSyntax.encode id
  (ForcingSupportSize.small (0 : Fin (m+1)) w.succ))))))

theorem hartogs_freeClosed {m : Nat} (w kappa : Fin m) :
    (hartogs w kappa).FreeClosed := by
  simp -implicitDefEqProofs [hartogs,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOrdinal]

theorem hartogs_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w kappa : Fin m) :
    Project.Formula.satisfies env (hartogs w kappa) ↔ Hartogs hM (env.bound w) (env.bound kappa) := by
  simp only [hartogs,Hartogs,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),Structure.IsHartogsNumber,Project.Formula.satisfies_isOrdinal_iff,ForcingSupportSize.small_semantics (M := M),ForcingSupportSize.native_small hM]
  rfl


def regular {m : Nat} (kappa : Fin m) : Project.Formula 1 m :=
  Project.Formula.isRegularCardinal PureKuratowskiProject.convention (.bound kappa)

theorem regular_freeClosed {m : Nat} (kappa : Fin m) :
    (regular kappa).FreeClosed := by
  simp -implicitDefEqProofs [regular, Project.Formula.isRegularCardinal,
    Project.Formula.isCofinality, Project.Formula.hasCofinalOrdinalSequence,
    Project.Formula.isCofinalOrdinalSequence, Definitional.Formula.FreeClosed,
    Project.Formula.isCardinal_freeClosed, Project.Formula.isLimitOrdinal_freeClosed,
    Project.Formula.isIncreasingOrdinalSequence_freeClosed,
    Project.Formula.isOrdinalSequenceLimit_freeClosed,
    Project.Formula.forallMem, Project.Formula.orderedPairMem_freeClosed,
    Project.Formula.extensionalEq]

theorem regular_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (kappa : Fin m) :
    Project.Formula.satisfies env (regular kappa) ↔
      (Project.FirstOrderSemantics.reduct M).IsRegularCardinal (KuratowskiZF.interpretation hM) (env.bound kappa) := by
  exact Project.Formula.satisfies_isRegularCardinal_iff (KuratowskiZF.interpretation hM)
    (ModelTransfer.extensionality hM) env (.bound kappa)

def omegaOneLe {m : Nat} (w mu : Fin m) : Project.Formula 1 m :=
  (.existsE (.conj (hartogs w.succ (0 : Fin (m+1))) (ProjectSyntax.encode id (ForcingSupportSize.small (0 :
  Fin (m+1)) mu.succ))))

theorem omegaOneLe_freeClosed {m : Nat} (w mu : Fin m) :
    (omegaOneLe w mu).FreeClosed := by
  simp -implicitDefEqProofs [omegaOneLe,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,hartogs_freeClosed]

theorem omegaOneLe_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w mu : Fin m) :
    Project.Formula.satisfies env (omegaOneLe w mu) ↔ OmegaOneLe hM (env.bound w) (env.bound mu) := by
  simp only [omegaOneLe,OmegaOneLe,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,

    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),hartogs_semantics hM,ForcingSupportSize.small_semantics (M := M)]
  rfl


def data {m : Nat} (w mu kappa B : Fin m) : Project.Formula 1 m :=
  (.conj (hartogs w kappa) (.conj (regular kappa) (.conj (.mem (.bound w) (.bound kappa)) (.conj
  (Project.Formula.isSuccessor (.bound B) (.bound kappa)) (.conj (Project.Formula.isOrdinal (.bound B))
  (.conj (ProjectSyntax.encode id (ForcingSupportSize.small kappa mu)) (ProjectSyntax.encode id
  (ForcingSupportSize.small B mu))))))))

theorem data_freeClosed {m : Nat} (w mu kappa B : Fin m) :
    (data w mu kappa B).FreeClosed := by
  simp -implicitDefEqProofs [data,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,hartogs_freeClosed,regular_freeClosed,Project.Formula.isSuccessor,Project.Formula.isOrdinal]

theorem data_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w mu kappa B : Fin m) :
    Project.Formula.satisfies env (data w mu kappa B) ↔ Data hM (env.bound w) (env.bound mu) (env.bound kappa) (env.bound B) := by
  simp only [data,Data,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),hartogs_semantics hM,regular_semantics hM,Project.Formula.satisfies_isSuccessor_iff,Project.Formula.satisfies_isOrdinal_iff,ForcingSupportSize.small_semantics (M := M)]
  rfl


def tower {m : Nat} (w Q R top D mul e mark H C zero one u K mu kappa B : Fin m) : Project.Formula 1 m :=
  (.conj (data w mu kappa B) (.conj (ConstructionSaturationIterationCases.context w Q R top D mul e mark H C
  zero one u K mu B) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionSaturationIteration.recursive
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mu.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  B.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  B.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin (m+13))) (.conj
  (ConstructionTowerValidity.valid w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  B.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin (m+13))) (.conj
  (ConstructionTowerCardinality.allSmall B.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (12 : Fin (m+13)) mu.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj
  (ConstructionTowerHistory.charts B.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 :
  Fin (m+13)) (11 : Fin (m+13)) (10 : Fin (m+13)) (9 : Fin (m+13)) (8 : Fin (m+13)) (7 : Fin (m+13)) (6 :
  Fin (m+13)) (5 : Fin (m+13)) (4 : Fin (m+13)) (3 : Fin (m+13))) (.conj (ProjectSyntax.encode id
  (ForcingConditionGraphs.identityGraph B.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (3 : Fin (m+13)))) (.conj (ConstructionTowerTransitions.order
  B.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin (m+13))) (.conj
  (ConstructionTowerTransitions.matrix B.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (12 : Fin (m+13)) zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin (m+13))
  (0 : Fin (m+13))) (.conj (ConstructionTowerDiagram.data
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  B.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin (m+13)) (11 : Fin (m+13)) (0 :
  Fin (m+13)) (10 : Fin (m+13)) (9 : Fin (m+13)) (8 : Fin (m+13)) (7 : Fin (m+13)) (6 : Fin (m+13)) (4 : Fin
  (m+13))) (.forallE (.forallE (.imp (.mem (.bound (1 : Fin (m+15))) (.bound
  B.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound (0 :
  Fin (m+15))) (.bound B.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp
  (Project.Formula.isSuccessor (.bound (0 : Fin (m+15))) (.bound (1 : Fin (m+15)))) (.existsE
  (ConstructionSaturationIterationValidity.selectedAt
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mu.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin
  (m+13)).succ.succ.succ (0 : Fin (m+13)).succ.succ.succ (2 : Fin (m+16)) (1 : Fin (m+16)) (0 : Fin
  (m+16))))))))))))))))))))))))))))))))

theorem tower_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one u K mu kappa B : Fin m) :
    (tower w Q R top D mul e mark H C zero one u K mu kappa B).FreeClosed := by
  simp -implicitDefEqProofs [tower,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,data_freeClosed,ConstructionSaturationIterationCases.context_freeClosed,ConstructionSaturationIteration.recursive_freeClosed,ConstructionTowerValidity.valid_freeClosed,ConstructionTowerCardinality.allSmall_freeClosed,ConstructionTowerHistory.charts_freeClosed,ConstructionTowerTransitions.order_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerDiagram.data_freeClosed,Project.Formula.isSuccessor,ConstructionSaturationIterationValidity.selectedAt_freeClosed]

theorem tower_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one u K mu kappa B : Fin m) :
    Project.Formula.satisfies env (tower w Q R top D mul e mark H C zero one u K mu kappa B) ↔ Tower hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound u) (env.bound K) (env.bound mu) (env.bound kappa) (env.bound B) := by
  simp only [tower,Tower,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),data_semantics hM,ConstructionSaturationIterationCases.context_semantics hM,ConstructionSaturationIteration.recursive_semantics hM,ConstructionTowerValidity.valid_semantics hM,ConstructionTowerCardinality.allSmall_semantics hM,ConstructionTowerHistory.charts_semantics hM,ForcingConditionGraphs.identityGraph_semantics (M := M),ConstructionTowerTransitions.order_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerDiagram.data_semantics hM,Project.Formula.satisfies_isSuccessor_iff,ConstructionSaturationIterationValidity.selectedAt_semantics hM]
  rfl


def indexSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 2 (.imp (Project.Formula.isOmega (.bound (0 : Fin 2))) (.imp
    (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound (0 : Fin 2)) (.bound (1 :
    Fin 2))) (.imp (omegaOneLe (0 : Fin 2) (1 : Fin 2)) (.existsE (.existsE (data (0 : Fin 2).succ.succ (1 :
    Fin 2).succ.succ (1 : Fin 4) (0 : Fin 4))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      Project.Formula.isOmega,Project.Formula.isInfiniteCardinal,omegaOneLe_freeClosed,data_freeClosed]

theorem index_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence indexSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) indexSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Term.eval_bound,omegaOneLe_semantics hM,data_semantics hM]
  exact fun hw hmu hBound => exists_index hM hChoice hw hmu hBound

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
    : Fin 15))) (.imp (omegaOneLe (0 : Fin 15) (14 : Fin 15)) (.existsE (.existsE (tower (0 : Fin
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
      omegaOneLe_freeClosed,tower_freeClosed]

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
    ForcingSupportSize.small_semantics (M := M),omegaOneLe_semantics hM,tower_semantics hM]
  exact fun hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall hOmegaOne =>
    exists_tower hM hOrder hChoice hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall hOmegaOne

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



theorem index_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative indexSentence)) := by
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
  apply ConstructibleGround.relative_models hM indexSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) indexSentence).mp
    (index_models hL hChoice)



end PPAC.Migration.ConstructionSaturationIndex
