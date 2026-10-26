/- Pinned rawHeight: an actual affine operation for the already accepted
Raw evalHom. Native function construction supplies a total extension; on
letters and cut values its equation is exactly offset + scale * value. -/
import PPAC.Migration.ConstructionCutProduct
import PPAC.Migration.ConstructionProbeHomEvaluationSyntax

namespace PPAC.Migration.ConstructionProbeHeightOperation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionRealCuts
open ConstructionProbeLetters (Representatives)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Affine (hM : FirstOrder.Theory.Models M nativeZF) (w Q O V s v y : M.Carrier .set) : Prop :=
  ∃ o d p, PureKuratowski.PairMember M s o O ∧ PureKuratowski.PairMember M s d V ∧
    ConstructionCutProduct.Value hM w Q d v p ∧ ConstructionCutAddition.SumCut hM w Q o p y

def affine {m : Nat} (w Q O V s v y : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge O.succ.succ.succ s.succ.succ.succ 2))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge V.succ.succ.succ s.succ.succ.succ 1))
      (.conj (ConstructionCutProduct.value w.succ.succ.succ Q.succ.succ.succ 1 v.succ.succ.succ 0)
        (ConstructionCutAddition.sumCut w.succ.succ.succ Q.succ.succ.succ 2 0 y.succ.succ.succ))))))

theorem affine_freeClosed {m : Nat} (w Q O V s v y : Fin m) : (affine w Q O V s v y).FreeClosed := by
  simp -implicitDefEqProofs [affine,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionCutProduct.value_freeClosed,ConstructionCutAddition.sumCut_freeClosed]

theorem affine_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q O V s v y : Fin m) :
    Project.Formula.satisfies env (affine w Q O V s v y) ↔
      Affine hM (env.bound w) (env.bound Q) (env.bound O) (env.bound V) (env.bound s) (env.bound v) (env.bound y) := by
  simp only [affine,Affine,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionCutProduct.value_semantics hM,ConstructionCutAddition.sumCut_semantics hM]
  rfl

theorem affine_total (hM : FirstOrder.Theory.Models M nativeZF) {w Q R S O V s v : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hO : MapsTo S R O) (hV : MapsTo S R V)
    (hs : (Project.FirstOrderSemantics.reduct M).mem s S) (hv : (Project.FirstOrderSemantics.reduct M).mem v R) :
    ∃ y, (Project.FirstOrderSemantics.reduct M).mem y R ∧ Affine hM w Q O V s v y := by
  obtain ⟨o,ho,_⟩ := hO.1.2 s hs
  obtain ⟨d,hd,_⟩ := hV.1.2 s hs
  obtain ⟨p,hp,hprod⟩ := ConstructionCutProduct.exists_product hM hw hQ
    ((hR d).mp (hV.2 s d hd)) ((hR v).mp hv)
  obtain ⟨y,hy,hsum⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ ((hR o).mp (hO.2 s o ho)) hp
  exact ⟨y,(hR y).mpr hy,o,d,p,ho,hd,hprod,hsum⟩

theorem affine_unique (hM : FirstOrder.Theory.Models M nativeZF) {w Q R S O V s v y z : M.Carrier .set}
    (hO : MapsTo S R O) (hV : MapsTo S R V)
    (hy : Affine hM w Q O V s v y) (hz : Affine hM w Q O V s v z) : y = z := by
  obtain ⟨o,d,p,ho,hd,hp,hy⟩ := hy
  obtain ⟨o',d',p',ho',hd',hp',hz⟩ := hz
  have he := ForcingConditionGraphs.function_unique hO.1 ho ho'
  subst o'
  have he := ForcingConditionGraphs.function_unique hV.1 hd hd'
  subst d'
  have he := ConstructionCutProduct.value_unique hM hp hp'
  subst p'
  exact ConstructionCutAddition.sum_unique hM hy hz

def Case (hM : FirstOrder.Theory.Models M nativeZF) (w Q R S zero O V s v y : M.Carrier .set) : Prop :=
  (((Project.FirstOrderSemantics.reduct M).mem s S ∧ (Project.FirstOrderSemantics.reduct M).mem v R) ∧
    Affine hM w Q O V s v y) ∨
  (¬ ((Project.FirstOrderSemantics.reduct M).mem s S ∧ (Project.FirstOrderSemantics.reduct M).mem v R) ∧ y = zero)

def operationCase {m : Nat} (w Q R S zero O V s v y : Fin m) : Project.Formula 1 m :=
  .disj (.conj (.conj (.mem (.bound s) (.bound S)) (.mem (.bound v) (.bound R))) (affine w Q O V s v y))
    (.conj (.neg (.conj (.mem (.bound s) (.bound S)) (.mem (.bound v) (.bound R))))
      (Project.Formula.extensionalEq (.bound y) (.bound zero)))

theorem operationCase_freeClosed {m : Nat} (w Q R S zero O V s v y : Fin m) :
    (operationCase w Q R S zero O V s v y).FreeClosed := by
  simp -implicitDefEqProofs [operationCase,Definitional.Formula.FreeClosed,affine_freeClosed]

theorem operationCase_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R S zero O V s v y : Fin m) :
    Project.Formula.satisfies env (operationCase w Q R S zero O V s v y) ↔
      Case hM (env.bound w) (env.bound Q) (env.bound R) (env.bound S) (env.bound zero)
        (env.bound O) (env.bound V) (env.bound s) (env.bound v) (env.bound y) := by
  simp only [operationCase,Case,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,affine_semantics hM]

theorem case_unique (hM : FirstOrder.Theory.Models M nativeZF) {w Q R S zero O V s v y z : M.Carrier .set}
    (hO : MapsTo S R O) (hV : MapsTo S R V)
    (hy : Case hM w Q R S zero O V s v y) (hz : Case hM w Q R S zero O V s v z) : y = z := by
  rcases hy with ⟨h,hy⟩ | ⟨hn,he⟩
  · rcases hz with ⟨_,hz⟩ | ⟨hn,_⟩
    · exact affine_unique hM hO hV hy hz
    · exact (hn h).elim
  · rcases hz with ⟨h,_⟩ | ⟨_,he'⟩
    · exact (hn h).elim
    · exact he.trans he'.symm

theorem case_total (hM : FirstOrder.Theory.Models M nativeZF) {w Q R S zero O V : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hO : MapsTo S R O) (hV : MapsTo S R V)
    (hz : (Project.FirstOrderSemantics.reduct M).mem zero R) (s v : M.Carrier .set) :
    ∃ y, (Project.FirstOrderSemantics.reduct M).mem y R ∧ Case hM w Q R S zero O V s v y := by
  classical
  by_cases h : (Project.FirstOrderSemantics.reduct M).mem s S ∧ (Project.FirstOrderSemantics.reduct M).mem v R
  · obtain ⟨y,hy,ha⟩ := affine_total hM hw hQ hR hO hV h.1 h.2
    exact ⟨y,hy,Or.inl ⟨h,ha⟩⟩
  · exact ⟨zero,hz,Or.inr ⟨h,rfl⟩⟩

theorem case_range (hM : FirstOrder.Theory.Models M nativeZF) {w Q R S zero O V s v y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hO : MapsTo S R O) (hV : MapsTo S R V)
    (hz : (Project.FirstOrderSemantics.reduct M).mem zero R) (hy : Case hM w Q R S zero O V s v y) :
    (Project.FirstOrderSemantics.reduct M).mem y R := by
  obtain ⟨z,hz',hzv⟩ := case_total hM hw hQ hR hO hV hz s v
  exact (case_unique hM hO hV hzv hy) ▸ hz'

def pairCase {m : Nat} (w Q R S zero O V p y : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj (PureKuratowskiProject.code (.bound p.succ.succ) (.bound 1) (.bound 0))
    (operationCase w.succ.succ Q.succ.succ R.succ.succ S.succ.succ zero.succ.succ O.succ.succ V.succ.succ 1 0 y.succ.succ)))

theorem pairCase_freeClosed {m : Nat} (w Q R S zero O V p y : Fin m) : (pairCase w Q R S zero O V p y).FreeClosed := by
  simp -implicitDefEqProofs [pairCase,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,operationCase_freeClosed]

theorem pairCase_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R S zero O V p y : Fin m) :
    Project.Formula.satisfies env (pairCase w Q R S zero O V p y) ↔ ∃ s v, PureKuratowski.Code M (env.bound p) s v ∧
      Case hM (env.bound w) (env.bound Q) (env.bound R) (env.bound S) (env.bound zero)
        (env.bound O) (env.bound V) s v (env.bound y) := by
  simp only [pairCase,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    KuratowskiZF.code_correct hM,Project.Term.eval_bound,operationCase_semantics hM]
  rfl

def Graph (hM : FirstOrder.Theory.Models M nativeZF) (w Q R S zero O V N G : M.Carrier .set) : Prop := ∀ s v y,
  Product G s v y ↔ (Project.FirstOrderSemantics.reduct M).mem s N ∧
    (Project.FirstOrderSemantics.reduct M).mem v N ∧ Case hM w Q R S zero O V s v y

theorem exists_operation (hM : FirstOrder.Theory.Models M nativeZF) {w Q R S zero O V : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hO : MapsTo S R O) (hV : MapsTo S R V)
    (hz : (Project.FirstOrderSemantics.reduct M).mem zero R) (N : M.Carrier .set) :
    ∃ J G, Representatives N N J ∧ MapsTo J R G ∧ Graph hM w Q R S zero O V N G := by
  obtain ⟨J,hJ⟩ := ConstructionProbeLetters.exists_representatives hM N N
  let schema : Project.BinarySchema 7 := {
    body := pairCase 2 3 4 5 6 7 8 1 0
    freeClosed := pairCase_freeClosed _ _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 7 := {
    bound := Fin.cases w (Fin.cases Q (Fin.cases R (Fin.cases S (Fin.cases zero (Fin.cases O (fun _ => V)))))),
    free := fun _ => w }
  have he (p y : M.Carrier .set) : schema.denote env p y ↔ ∃ s v,
      PureKuratowski.Code M p s v ∧ Case hM w Q R S zero O V s v y :=
    pairCase_semantics hM ((env.push p).push y) 2 3 4 5 6 7 8 1 0
  obtain ⟨G,hG,hg⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := J) (target := R) (by
      intro p hp
      obtain ⟨s,v,_,_,hp⟩ := (hJ p).mp hp
      obtain ⟨y,_,hy⟩ := case_total hM hw hQ hR hO hV hz s v
      exact ⟨y,(he p y).mpr ⟨s,v,hp,hy⟩⟩) (by
      intro p _ y z hy hzv
      obtain ⟨s,v,hp,hy⟩ := (he p y).mp hy
      obtain ⟨s',v',hp',hzv⟩ := (he p z).mp hzv
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
      exact case_unique hM hO hV hy hzv) (by
      intro p y _ hy
      obtain ⟨s,v,_,hy⟩ := (he p y).mp hy
      exact case_range hM hw hQ hR hO hV hz hy)
  refine ⟨J,G,hJ,(ForcingSupportSize.native_mapsTo hM J R G).mpr hG,?_⟩
  intro s v y
  constructor
  · rintro ⟨p,hp,hpy⟩
    obtain ⟨s',v',hs,hv,hp'⟩ := (hJ p).mp ((hg p y).mp hpy).1
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
    obtain ⟨s',v',hp',hy⟩ := (he p y).mp ((hg p y).mp hpy).2
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
    exact ⟨hs,hv,hy⟩
  · rintro ⟨hs,hv,hy⟩
    obtain ⟨p,hp⟩ := KuratowskiZF.exists_code hM s v
    exact ⟨p,hp,(hg p y).mpr ⟨(hJ p).mpr ⟨s,v,hs,hv,hp⟩,(he p y).mpr ⟨s,v,hp,hy⟩⟩⟩

end PPAC.Migration.ConstructionProbeHeightOperation
