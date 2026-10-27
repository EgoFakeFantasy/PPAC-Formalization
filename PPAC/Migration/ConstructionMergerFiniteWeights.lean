/- Pinned MergerCones.copiesHeight:191 / copiesCost:196. Extract the actual
coordinate row on the SAME copies; use existing Raw evaluation on all
internal lengths, then literal /n and min(cap,product)/n. Consumer:
copiesHeightCost and Merger Word weights. Complete margin laws are separate.
No host List, choice of representatives or new recursion backend. -/
import PPAC.Migration.ConstructionMergerCoordinateLaws
import PPAC.Migration.ConstructionProbeHomEvaluationSyntax
import PPAC.Migration.ConstructionCutDivision
import PPAC.Migration.ConstructionCutProductUnit
import PPAC.Migration.ConstructionCutMinimum

namespace PPAC.Migration.ConstructionMergerFiniteWeights
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeLetters (Representatives)
open ConstructionProbeHomEvaluation (Eval eval_total eval_unique eval_range)
open ConstructionProbeAction (projected projected_range)
open ConstructionRealCuts (CutCarrier)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Row (n Coord z f : M.Carrier .set) : Prop := ∀ i c,
  PureKuratowski.PairMember M i c f ↔ (Project.FirstOrderSemantics.reduct M).mem i n ∧ Product Coord i z c

def row {m : Nat} (n Coord z f : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ 1 0))
    (.conj (.mem (.bound 1) (.bound n.succ.succ))
      (ProjectSyntax.encode id (ForcingDiagramOrder.product Coord.succ.succ 1 z.succ.succ 0)))))

theorem row_freeClosed {m : Nat} (n Coord z f : Fin m) : (row n Coord z f).FreeClosed := by
  simp -implicitDefEqProofs [row,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem row_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n Coord z f : Fin m) :
    Project.Formula.satisfies env (row n Coord z f) ↔ Row (env.bound n) (env.bound Coord) (env.bound z) (env.bound f) := by
  simp only [row,Row,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramOrder.product_semantics (M := M)]
  rfl

theorem exists_row (hM : FirstOrder.Theory.Models M nativeZF)
    {n L J R Coord z : M.Carrier .set} (hJ : Representatives n L J) (hCoord : MapsTo J R Coord)
    (hz : (Project.FirstOrderSemantics.reduct M).mem z L) : ∃ f, MapsTo n R f ∧ Row n Coord z f := by
  let schema : Project.BinarySchema 2 := {
    body := ProjectSyntax.encode id (ForcingDiagramOrder.product 2 1 3 0), freeClosed := ProjectSyntax.freeClosed id _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases Coord (fun _ => z), free := fun _ => n }
  have he (i c) : schema.denote env i c ↔ Product Coord i z c := by
    change Project.Formula.satisfies ((env.push i).push c) schema.body ↔ _
    simp only [schema,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
      ForcingDiagramOrder.product_semantics (M := M)]
    rfl
  obtain ⟨f,hf,hg⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := n) (target := R) (by
      intro i hi
      obtain ⟨c,_,hc⟩ := projected hM hJ hCoord hi hz
      exact ⟨c,(he i c).mpr hc⟩) (by
      intro i _ c d hc hd
      exact ConstructionProbeHomEvaluation.product_unique hM hCoord ((he i c).mp hc) ((he i d).mp hd)) (by
      intro i c _ hc
      exact projected_range hCoord ((he i c).mp hc))
  exact ⟨f,(ForcingSupportSize.native_mapsTo hM n R f).mpr hf,
    fun i c => (hg i c).trans (and_congr_right (fun _ => he i c))⟩

theorem row_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {n R Coord z f g : M.Carrier .set} (hf : MapsTo n R f) (hg : MapsTo n R g)
    (hfr : Row n Coord z f) (hgr : Row n Coord z g) : f = g :=
  SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.project_models_iff.mp hM).1
    ((ForcingSupportSize.native_mapsTo hM n R f).mp hf).1.1
    ((ForcingSupportSize.native_mapsTo hM n R g).mp hg).1.1
    (fun i c => (hfr i c).trans (hgr i c).symm)

/-- Existing Raw evaluator specialized to the actual coordinate row.
Seed is empty cut for addition and canonical unit cut for product. -/
def CoordinateEval (hM : FirstOrder.Theory.Models M nativeZF)
    (w n R op Id seed Coord z y : M.Carrier .set) : Prop := ∃ f q,
  MapsTo n R f ∧ Row n Coord z f ∧ PureKuratowski.Code M q f seed ∧ Eval hM w R R R op Id Id q y

def coordinateEval {m : Nat} (w n R op Id seed Coord z y : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 1 n.succ.succ R.succ.succ))
    (.conj (row n.succ.succ Coord.succ.succ z.succ.succ 1)
      (.conj (PureKuratowskiProject.code (.bound 0) (.bound 1) (.bound seed.succ.succ))
        (ConstructionProbeHomEvaluationSyntax.eval w.succ.succ R.succ.succ R.succ.succ R.succ.succ
          op.succ.succ Id.succ.succ Id.succ.succ 0 y.succ.succ)))))

theorem coordinateEval_freeClosed {m : Nat} (w n R op Id seed Coord z y : Fin m) :
    (coordinateEval w n R op Id seed Coord z y).FreeClosed := by
  simp -implicitDefEqProofs [coordinateEval,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    row_freeClosed,PureKuratowskiProject.code,ConstructionProbeHomEvaluationSyntax.eval_freeClosed]

theorem coordinateEval_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w n R op Id seed Coord z y : Fin m) :
    Project.Formula.satisfies env (coordinateEval w n R op Id seed Coord z y) ↔
      CoordinateEval hM (env.bound w) (env.bound n) (env.bound R) (env.bound op) (env.bound Id)
        (env.bound seed) (env.bound Coord) (env.bound z) (env.bound y) := by
  simp only [coordinateEval,CoordinateEval,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),
    Project.Term.eval_bound,row_semantics hM,KuratowskiZF.code_correct hM,ConstructionProbeHomEvaluationSyntax.eval_semantics hM]
  rfl

theorem coordinateEval_total (hM : FirstOrder.Theory.Models M nativeZF)
    {w n L R J K op Id seed Coord z : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hJ : Representatives n L J) (hCoord : MapsTo J R Coord) (hK : Representatives R R K)
    (hop : MapsTo K R op) (hId : MapsTo R R Id) (hseed : (Project.FirstOrderSemantics.reduct M).mem seed R)
    (hz : (Project.FirstOrderSemantics.reduct M).mem z L) : ∃ y, CoordinateEval hM w n R op Id seed Coord z y := by
  obtain ⟨f,hf,hrow⟩ := exists_row hM hJ hCoord hz
  obtain ⟨q,hq⟩ := KuratowskiZF.exists_code hM f seed
  obtain ⟨y,hy⟩ := eval_total hM hw hK hop hId hId ⟨f,seed,⟨n,hn,hf⟩,hseed,hq⟩
  exact ⟨y,f,q,hf,hrow,hq,hy⟩

theorem coordinateEval_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w n R K op Id seed Coord z a b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hK : Representatives R R K)
    (hop : MapsTo K R op) (hId : MapsTo R R Id)
    (ha : CoordinateEval hM w n R op Id seed Coord z a) (hb : CoordinateEval hM w n R op Id seed Coord z b) : a = b := by
  obtain ⟨f,q,hf,hfr,hq,ha⟩ := ha
  obtain ⟨g,p,hg,hgr,hp,hb⟩ := hb
  have he := row_unique hM hf hg hfr hgr
  subst g
  have he := KuratowskiZF.code_unique hM hq hp
  subst p
  exact eval_unique hM hw hK hop hId hId ha hb

theorem coordinateEval_range (hM : FirstOrder.Theory.Models M nativeZF)
    {w n R op Id seed Coord z y : M.Carrier .set}
    (hy : CoordinateEval hM w n R op Id seed Coord z y) : (Project.FirstOrderSemantics.reduct M).mem y R := by
  obtain ⟨_,_,_,_,_,hy⟩ := hy
  exact eval_range hM hy

def HeightValue (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q n R add Id zero CH z a : M.Carrier .set) : Prop := ∃ s,
  CoordinateEval hM w n R add Id zero CH z s ∧ ConstructionCutDivision.Value hM w Q n s a

def CostValue (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q n R mul Id top cap CC z a : M.Carrier .set) : Prop := ∃ p b,
  CoordinateEval hM w n R mul Id top CC z p ∧ ConstructionCutMinimum.Value cap p b ∧
    ConstructionCutDivision.Value hM w Q n b a

def heightValue {m : Nat} (w Q n R add Id zero CH z a : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (coordinateEval w.succ n.succ R.succ add.succ Id.succ zero.succ CH.succ z.succ 0)
    (ConstructionCutDivision.value w.succ Q.succ n.succ 0 a.succ))

def costValue {m : Nat} (w Q n R mul Id top cap CC z a : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj (coordinateEval w.succ.succ n.succ.succ R.succ.succ mul.succ.succ Id.succ.succ
    top.succ.succ CC.succ.succ z.succ.succ 1) (.conj (ConstructionCutMinimum.value cap.succ.succ 1 0)
      (ConstructionCutDivision.value w.succ.succ Q.succ.succ n.succ.succ 0 a.succ.succ))))

theorem heightValue_freeClosed {m : Nat} (w Q n R add Id zero CH z a : Fin m) :
    (heightValue w Q n R add Id zero CH z a).FreeClosed := by
  simp -implicitDefEqProofs [heightValue,Definitional.Formula.FreeClosed,coordinateEval_freeClosed,ConstructionCutDivision.value_freeClosed]

theorem costValue_freeClosed {m : Nat} (w Q n R mul Id top cap CC z a : Fin m) :
    (costValue w Q n R mul Id top cap CC z a).FreeClosed := by
  simp -implicitDefEqProofs [costValue,Definitional.Formula.FreeClosed,coordinateEval_freeClosed,
    ConstructionCutMinimum.value_freeClosed,ConstructionCutDivision.value_freeClosed]

theorem heightValue_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q n R add Id zero CH z a : Fin m) :
    Project.Formula.satisfies env (heightValue w Q n R add Id zero CH z a) ↔
      HeightValue hM (env.bound w) (env.bound Q) (env.bound n) (env.bound R) (env.bound add) (env.bound Id)
        (env.bound zero) (env.bound CH) (env.bound z) (env.bound a) := by
  simp only [heightValue,HeightValue,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    coordinateEval_semantics hM,ConstructionCutDivision.value_semantics hM]
  rfl

theorem costValue_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q n R mul Id top cap CC z a : Fin m) :
    Project.Formula.satisfies env (costValue w Q n R mul Id top cap CC z a) ↔
      CostValue hM (env.bound w) (env.bound Q) (env.bound n) (env.bound R) (env.bound mul) (env.bound Id)
        (env.bound top) (env.bound cap) (env.bound CC) (env.bound z) (env.bound a) := by
  simp only [costValue,CostValue,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    coordinateEval_semantics hM,ConstructionCutMinimum.value_semantics,ConstructionCutDivision.value_semantics hM]
  rfl

theorem heightValue_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q n R K add Id zero CH z a b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hK : Representatives R R K)
    (hadd : MapsTo K R add) (hId : MapsTo R R Id)
    (ha : HeightValue hM w Q n R add Id zero CH z a) (hb : HeightValue hM w Q n R add Id zero CH z b) : a = b := by
  obtain ⟨s,hs,ha⟩ := ha
  obtain ⟨t,ht,hb⟩ := hb
  have he := coordinateEval_unique hM hw hK hadd hId hs ht
  subst t
  exact ConstructionCutDivision.value_unique hM ha hb

theorem costValue_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q n R K mul Id top cap CC z a b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hK : Representatives R R K)
    (hmul : MapsTo K R mul) (hId : MapsTo R R Id)
    (ha : CostValue hM w Q n R mul Id top cap CC z a) (hb : CostValue hM w Q n R mul Id top cap CC z b) : a = b := by
  obtain ⟨p,s,hp,hs,ha⟩ := ha
  obtain ⟨q,t,hq,ht,hb⟩ := hb
  have he := coordinateEval_unique hM hw hK hmul hId hp hq
  subst q
  have he := ConstructionCutMinimum.value_unique hM hs ht
  subst t
  exact ConstructionCutDivision.value_unique hM ha hb

theorem exists_height_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q n L R J K add Id zero CH : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hnp : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i n)
    (hR : CutCarrier hM w Q R) (hJ : Representatives n L J) (hCH : MapsTo J R CH)
    (hK : Representatives R R K) (hadd : MapsTo K R add) (hId : MapsTo R R Id)
    (hzero : (Project.FirstOrderSemantics.reduct M).mem zero R) : ∃ F, MapsTo L R F ∧ ∀ z a,
      PureKuratowski.PairMember M z a F ↔ (Project.FirstOrderSemantics.reduct M).mem z L ∧ HeightValue hM w Q n R add Id zero CH z a := by
  let schema : Project.BinarySchema 8 := {
    body := heightValue 2 3 4 5 6 7 8 9 1 0,
    freeClosed := heightValue_freeClosed _ _ _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 8 := {
    bound := Fin.cases w (Fin.cases Q (Fin.cases n (Fin.cases R (Fin.cases add (Fin.cases Id (Fin.cases zero (fun _ => CH))))))),
    free := fun _ => w }
  have he (z a) : schema.denote env z a ↔ HeightValue hM w Q n R add Id zero CH z a :=
    heightValue_semantics hM ((env.push z).push a) 2 3 4 5 6 7 8 9 1 0
  obtain ⟨F,hF,hg⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := L) (target := R) (by
      intro z hz
      obtain ⟨s,hs⟩ := coordinateEval_total hM hw hn hJ hCH hK hadd hId hzero hz
      obtain ⟨a,ha⟩ := ConstructionCutDivision.exists_value hM w Q n s
      exact ⟨a,(he z a).mpr ⟨s,hs,ha⟩⟩) (by
      intro z _ a b ha hb
      exact heightValue_unique hM hw hK hadd hId ((he z a).mp ha) ((he z b).mp hb)) (by
      intro z a _ ha
      obtain ⟨s,hs,ha⟩ := (he z a).mp ha
      exact (hR a).mpr (ConstructionCutDivision.value_cut hw hQ hn hnp
        ((hR s).mp (coordinateEval_range hM hs)) ha))
  exact ⟨F,(ForcingSupportSize.native_mapsTo hM L R F).mpr hF,
    fun z a => (hg z a).trans (and_congr_right (fun _ => he z a))⟩

theorem exists_cost_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q n L R J K mul Id top cap CC : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hnp : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i n)
    (hR : CutCarrier hM w Q R) (hJ : Representatives n L J) (hCC : MapsTo J R CC)
    (hK : Representatives R R K) (hmul : MapsTo K R mul) (hId : MapsTo R R Id)
    (htop : (Project.FirstOrderSemantics.reduct M).mem top R) (hcap : (Project.FirstOrderSemantics.reduct M).mem cap R) :
    ∃ F, MapsTo L R F ∧ ∀ z a, PureKuratowski.PairMember M z a F ↔
      (Project.FirstOrderSemantics.reduct M).mem z L ∧ CostValue hM w Q n R mul Id top cap CC z a := by
  let schema : Project.BinarySchema 9 := {
    body := costValue 2 3 4 5 6 7 8 9 10 1 0,
    freeClosed := costValue_freeClosed _ _ _ _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 9 := {
    bound := Fin.cases w (Fin.cases Q (Fin.cases n (Fin.cases R (Fin.cases mul (Fin.cases Id (Fin.cases top (Fin.cases cap (fun _ => CC)))))))),
    free := fun _ => w }
  have he (z a) : schema.denote env z a ↔ CostValue hM w Q n R mul Id top cap CC z a :=
    costValue_semantics hM ((env.push z).push a) 2 3 4 5 6 7 8 9 10 1 0
  obtain ⟨F,hF,hg⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := L) (target := R) (by
      intro z hz
      obtain ⟨p,hp⟩ := coordinateEval_total hM hw hn hJ hCC hK hmul hId htop hz
      obtain ⟨b,_,hb⟩ := ConstructionCutMinimum.exists_minimum hM hw hQ ((hR cap).mp hcap)
        ((hR p).mp (coordinateEval_range hM hp))
      obtain ⟨a,ha⟩ := ConstructionCutDivision.exists_value hM w Q n b
      exact ⟨a,(he z a).mpr ⟨p,b,hp,hb,ha⟩⟩) (by
      intro z _ a b ha hb
      exact costValue_unique hM hw hK hmul hId ((he z a).mp ha) ((he z b).mp hb)) (by
      intro z a _ ha
      obtain ⟨p,b,hp,hb,ha⟩ := (he z a).mp ha
      obtain ⟨c,hc,hcMin⟩ := ConstructionCutMinimum.exists_minimum hM hw hQ ((hR cap).mp hcap)
        ((hR p).mp (coordinateEval_range hM hp))
      have he := ConstructionCutMinimum.value_unique hM hb hcMin
      subst c
      exact (hR a).mpr (ConstructionCutDivision.value_cut hw hQ hn hnp hc ha))
  exact ⟨F,(ForcingSupportSize.native_mapsTo hM L R F).mpr hF,
    fun z a => (hg z a).trans (and_congr_right (fun _ => he z a))⟩

/-- Construct both weight functions, including the actual old-unit-height/2
cap. The unit height is obtained from the supplied OLD height graph. -/
theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q n L R J CH CC zero one u top D e Height : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hnp : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i n)
    (hR : CutCarrier hM w Q R) (hJ : Representatives n L J) (hCH : MapsTo J R CH) (hCC : MapsTo J R CC)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : ConstructionRealCuts.Principal hM w Q u top)
    (hHeight : MapsTo D R Height) (he : (Project.FirstOrderSemantics.reduct M).mem e D) :
    ∃ unitHeight Ka add Km mul Id two cap FH FC,
      PureKuratowski.PairMember M e unitHeight Height ∧
      Representatives R R Ka ∧ MapsTo Ka R add ∧ ConstructionCutArithmetic.Graph hM w Q R add ∧
      Representatives R R Km ∧ MapsTo Km R mul ∧ ConstructionCutProduct.Graph hM w Q R mul ∧
      MapsTo R R Id ∧ ForcingConditionGraphs.IdentityGraph R Id ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf two one ∧ (Project.FirstOrderSemantics.reduct M).mem two w ∧
      (Project.FirstOrderSemantics.reduct M).mem cap R ∧ ConstructionCutDivision.Value hM w Q two unitHeight cap ∧
      MapsTo L R FH ∧ (∀ z a, PureKuratowski.PairMember M z a FH ↔
        (Project.FirstOrderSemantics.reduct M).mem z L ∧ HeightValue hM w Q n R add Id zero CH z a) ∧
      MapsTo L R FC ∧ (∀ z a, PureKuratowski.PairMember M z a FC ↔
        (Project.FirstOrderSemantics.reduct M).mem z L ∧ CostValue hM w Q n R mul Id top cap CC z a) ∧
      (∀ a, (Project.FirstOrderSemantics.reduct M).mem a R → Product mul a top a) ∧
      (∀ a, (Project.FirstOrderSemantics.reduct M).mem a R → Product add zero a a) := by
  obtain ⟨unitHeight,hunitEdge,_⟩ := hHeight.1.2 e he
  have hunitHeight := hHeight.2 e unitHeight hunitEdge
  have htop := (hR top).mpr (ConstructionRealCuts.principal_cut hM hw hQ ((hQ u).mpr ⟨one,one,hu⟩) hunit)
  have hzero := ConstructionMergerCoordinateLaws.empty_cut_mem hM hR hz htop
  obtain ⟨Ka,add,hKa,hadd,hAdd,hAddLaws⟩ := ConstructionCutArithmetic.exists_graph hM hw hQ hR
  obtain ⟨Km,mul,hKm,hmul,hMul⟩ := ConstructionCutProduct.exists_graph hM hw hQ hR
  obtain ⟨Id,hId,hIdGraph⟩ := ForcingConditionGraphs.exists_identity hM R
  obtain ⟨two,htwo,htwow⟩ := hw.1.2 one hu.1
  obtain ⟨cap,hcap⟩ := ConstructionCutDivision.exists_value hM w Q two unitHeight
  have hcapR := (hR cap).mpr (ConstructionCutDivision.value_cut hw hQ htwow
    ⟨one,htwo.predecessor_mem⟩ ((hR unitHeight).mp hunitHeight) hcap)
  obtain ⟨FH,hFH,hHeightGraph⟩ := exists_height_graph hM hw hQ hn hnp hR hJ hCH hKa hadd hId.1 hzero
  obtain ⟨FC,hFC,hCostGraph⟩ := exists_cost_graph hM hw hQ hn hnp hR hJ hCC hKm hmul hId.1 htop hcapR
  refine ⟨unitHeight,Ka,add,Km,mul,Id,two,cap,FH,FC,hunitEdge,hKa,hadd,hAdd,hKm,hmul,hMul,hId.1,hIdGraph,htwo,htwow,
    hcapR,hcap,hFH,hHeightGraph,hFC,hCostGraph,?_,?_⟩
  · intro a ha
    exact (hMul a top a).mpr ⟨ha,htop,ConstructionCutProductUnit.right_unit hM hw hQ hu hone hunit ((hR a).mp ha)⟩
  · intro a ha
    exact (hAddLaws.2.2.2 zero a hzero ha hz).1

end PPAC.Migration.ConstructionMergerFiniteWeights
