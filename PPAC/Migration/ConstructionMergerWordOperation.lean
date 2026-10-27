/- Pinned MergerWords.Word.product:118: actual snoc fold operation.
Reuse Raw.Cons and the native function constructor, as in the accepted height
operation; default branches only close the EXISTING evalHom's auxiliary algebra.
Consumer: actual Merger Word.product, not an assumed multiplication graph. -/
import PPAC.Migration.ConstructionMergerWordAction
import PPAC.Migration.ConstructionProbeHomEvaluationSyntax
import PPAC.Migration.ConstructionProbeHeightFold

namespace PPAC.Migration.ConstructionMergerWordOperation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw (Raw Carrier Old Cons)
open ConstructionProbeLetters (Representatives exists_representatives)
open ConstructionProbeHomEvaluation (Prepend Eval)
open ConstructionRealCuts (Subset)
open ForcingDiagramOrder (Product product product_semantics)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Case (w D L W default s v y : M.Carrier .set) : Prop :=
  (((Project.FirstOrderSemantics.reduct M).mem s L ∧ (Project.FirstOrderSemantics.reduct M).mem v W) ∧ Cons w D L s v y) ∨
    (¬ ((Project.FirstOrderSemantics.reduct M).mem s L ∧ (Project.FirstOrderSemantics.reduct M).mem v W)) ∧ y = default

theorem case_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L W default s v y z : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hy : Case w D L W default s v y) (hz : Case w D L W default s v z) : y = z := by
  rcases hy with ⟨h,hy⟩ | ⟨hn,he⟩ <;> rcases hz with ⟨h',hz⟩ | ⟨hn',he'⟩
  · exact ConstructionProbeRaw.cons_unique hM hw hy hz
  · exact (hn' h).elim
  · exact (hn h').elim
  · exact he.trans he'.symm

theorem case_total (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L W default : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hW : Carrier w D L W)
    (hd : (Project.FirstOrderSemantics.reduct M).mem default W) (s v : M.Carrier .set) :
    ∃ y, (Project.FirstOrderSemantics.reduct M).mem y W ∧ Case w D L W default s v y := by
  classical
  by_cases h : (Project.FirstOrderSemantics.reduct M).mem s L ∧ (Project.FirstOrderSemantics.reduct M).mem v W
  · obtain ⟨y,hy⟩ := ConstructionProbeRaw.exists_cons hM hw h.1 ((hW v).mp h.2)
    exact ⟨y,(hW y).mpr (ConstructionProbeRaw.cons_raw hy).2,Or.inl ⟨h,hy⟩⟩
  · exact ⟨default,hd,Or.inr ⟨h,rfl⟩⟩

theorem case_range {w D L W default s v y : M.Carrier .set}
    (hW : Carrier w D L W) (hd : (Project.FirstOrderSemantics.reduct M).mem default W)
    (hy : Case w D L W default s v y) : (Project.FirstOrderSemantics.reduct M).mem y W := by
  rcases hy with ⟨_,hCons⟩ | ⟨_,rfl⟩
  · exact (hW y).mpr (ConstructionProbeRaw.cons_raw hCons).2
  · exact hd

def operationCase {m0 : Nat} (w D L W default s v y : Fin m0) : Project.Formula 1 m0 :=
  (.disj (.conj (.conj (.mem (.bound s) (.bound L)) (.mem (.bound v) (.bound W))) (ConstructionProbeRaw.cons
  w D L s v y)) (.conj (.neg (.conj (.mem (.bound s) (.bound L)) (.mem (.bound v) (.bound W))))
  (Project.Formula.extensionalEq (.bound y) (.bound default))))

theorem operationCase_freeClosed {m0 : Nat} (w D L W default s v y : Fin m0) : (operationCase w D L W default s v y).FreeClosed := by
  simp -implicitDefEqProofs [operationCase,Definitional.Formula.FreeClosed,ConstructionProbeRaw.cons_freeClosed,Project.Formula.extensionalEq]

theorem operationCase_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (w D L W default s v y : Fin m0) :
    Project.Formula.satisfies env (operationCase w D L W default s v y) ↔ Case (env.bound w) (env.bound D) (env.bound L) (env.bound W) (env.bound default) (env.bound s) (env.bound v) (env.bound y) := by
  simp only [operationCase,Case,
    Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,ConstructionProbeRaw.cons_semantics hM,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]

def pairCase {m0 : Nat} (w D L W default p y : Fin m0) : Project.Formula 1 m0 :=
  (.existsE (.existsE (.conj (PureKuratowskiProject.code (.bound p.succ.succ) (.bound 1) (.bound 0))
  (operationCase w.succ.succ D.succ.succ L.succ.succ W.succ.succ default.succ.succ 1 0 y.succ.succ))))

theorem pairCase_freeClosed {m0 : Nat} (w D L W default p y : Fin m0) : (pairCase w D L W default p y).FreeClosed := by
  simp -implicitDefEqProofs [pairCase,Definitional.Formula.FreeClosed,operationCase_freeClosed,PureKuratowskiProject.code]

theorem pairCase_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (w D L W default p y : Fin m0) :
    Project.Formula.satisfies env (pairCase w D L W default p y) ↔ (∃ s v, PureKuratowski.Code M (env.bound p) s v ∧ Case (env.bound w) (env.bound D) (env.bound L) (env.bound W) (env.bound default) s v (env.bound y)) := by
  simp only [pairCase,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,operationCase_semantics hM,KuratowskiZF.code_correct hM]
  rfl

def Graph (w D L W default N G : M.Carrier .set) : Prop := ∀ s v y,
  Product G s v y ↔ (Project.FirstOrderSemantics.reduct M).mem s N ∧
    (Project.FirstOrderSemantics.reduct M).mem v N ∧ Case w D L W default s v y

theorem exists_operation (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L W default : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hW : Carrier w D L W)
    (hd : (Project.FirstOrderSemantics.reduct M).mem default W) (N : M.Carrier .set) :
    ∃ J G, Representatives N N J ∧ MapsTo J W G ∧ Graph w D L W default N G := by
  obtain ⟨J,hJ⟩ := exists_representatives hM N N
  let schema : Project.BinarySchema 5 := { body := pairCase 2 3 4 5 6 1 0, freeClosed := pairCase_freeClosed _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases L (Fin.cases W (fun _ => default)))), free := fun _ => w }
  have he (p y : M.Carrier .set) : schema.denote env p y ↔ ∃ s v, PureKuratowski.Code M p s v ∧ Case w D L W default s v y :=
    pairCase_semantics hM ((env.push p).push y) 2 3 4 5 6 1 0
  obtain ⟨G,hG,hg⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := J) (target := W) (by
      intro p hp
      obtain ⟨s,v,_,_,hcode⟩ := (hJ p).mp hp
      obtain ⟨y,_,hy⟩ := case_total hM hw hW hd s v
      exact ⟨y,(he p y).mpr ⟨s,v,hcode,hy⟩⟩) (by
      intro p _ y z hy hz
      obtain ⟨s,v,hcode,hy⟩ := (he p y).mp hy
      obtain ⟨s',v',hcode',hz⟩ := (he p z).mp hz
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
      exact case_unique hM hw hy hz) (by
      intro p y _ hy
      obtain ⟨s,v,_,hy⟩ := (he p y).mp hy
      exact case_range hW hd hy)
  refine ⟨J,G,hJ,(ForcingSupportSize.native_mapsTo hM J W G).mpr hG,?_⟩
  intro s v y
  constructor
  · rintro ⟨p,hcode,hpy⟩
    obtain ⟨s',v',hs,hv,hcode'⟩ := (hJ p).mp ((hg p y).mp hpy).1
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
    obtain ⟨s',v',hcode',hy⟩ := (he p y).mp ((hg p y).mp hpy).2
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
    exact ⟨hs,hv,hy⟩
  · rintro ⟨hs,hv,hy⟩
    obtain ⟨p,hcode⟩ := KuratowskiZF.exists_code hM s v
    exact ⟨p,hcode,(hg p y).mpr ⟨(hJ p).mpr ⟨s,v,hs,hv,hcode⟩,(he p y).mpr ⟨s,v,hcode,hy⟩⟩⟩

theorem prepend_iff {w D L W default N G Id s v y : M.Carrier .set}
    (hLN : Subset L N) (hWN : Subset W N)
    (hId : ForcingConditionGraphs.IdentityGraph L Id) (hg : Graph w D L W default N G)
    (hs : (Project.FirstOrderSemantics.reduct M).mem s L) (hv : (Project.FirstOrderSemantics.reduct M).mem v W) :
    Prepend Id G s v y ↔ Cons w D L s v y := by
  constructor
  · rintro ⟨a,ha,hprod⟩
    have he := ((hId s a).mp ha).2
    subst a
    rcases ((hg s v y).mp hprod).2.2 with ⟨_,hCons⟩ | ⟨hn,_⟩
    · exact hCons
    · exact (hn ⟨hs,hv⟩).elim
  · intro hCons
    exact ⟨s,(hId s s).mpr ⟨hs,rfl⟩,(hg s v y).mpr ⟨hLN s hs,hWN v hv,Or.inl ⟨⟨hs,hv⟩,hCons⟩⟩⟩

def Initial (D T left F : M.Carrier .set) : Prop := ∀ m y,
  PureKuratowski.PairMember M m y F ↔ (Project.FirstOrderSemantics.reduct M).mem m D ∧ Product T left m y

def initial {m0 : Nat} (D T left F : Fin m0) : Project.Formula 1 m0 :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ 1 0)) (.conj (.mem
  (.bound 1) (.bound D.succ.succ)) (ProjectSyntax.encode id (ForcingDiagramOrder.product T.succ.succ
  left.succ.succ 1 0))))))

theorem initial_freeClosed {m0 : Nat} (D T left F : Fin m0) : (initial D T left F).FreeClosed := by
  simp -implicitDefEqProofs [initial,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem initial_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (D T left F : Fin m0) :
    Project.Formula.satisfies env (initial D T left F) ↔ Initial (env.bound D) (env.bound T) (env.bound left) (env.bound F) := by
  simp only [initial,Initial,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,product_semantics (M := M)]
  rfl

theorem exists_initial (hM : FirstOrder.Theory.Models M nativeZF)
    {W D I T left : M.Carrier .set} (hI : Representatives W D I) (hT : MapsTo I W T)
    (hl : (Project.FirstOrderSemantics.reduct M).mem left W) :
    ∃ F, MapsTo D W F ∧ Initial D T left F := by
  let schema : Project.BinarySchema 2 := {
    body := ProjectSyntax.encode id (ForcingDiagramOrder.product 2 3 1 0)
    freeClosed := by simp -implicitDefEqProofs [ProjectSyntax.freeClosed] }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases T (fun _ => left),free := fun _ => W }
  have he (m y : M.Carrier .set) : schema.denote env m y ↔ Product T left m y := by
    simp only [Project.BinarySchema.denote,schema,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M)]
    rfl
  obtain ⟨F,hF,hg⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := D) (target := W) (by
      intro m hmD
      obtain ⟨y,_,hy⟩ := ConstructionProbeAction.projected hM hI hT hl hmD
      exact ⟨y,(he m y).mpr hy⟩) (by
      intro m _ y z hy hz
      exact ConstructionProbeHomEvaluation.product_unique hM hT ((he m y).mp hy) ((he m z).mp hz)) (by
      intro m y _ hy
      exact ConstructionProbeAction.projected_range hT ((he m y).mp hy))
  exact ⟨F,(ForcingSupportSize.native_mapsTo hM D W F).mpr hF,fun m y => (hg m y).trans (and_congr_right (fun _ => he m y))⟩

theorem initial_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {D W T left F H : M.Carrier .set} (hF : MapsTo D W F) (hH : MapsTo D W H)
    (hf : Initial D T left F) (hh : Initial D T left H) : F = H :=
  SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM D W F).mp hF).1.1
    ((ForcingSupportSize.native_mapsTo hM D W H).mp hH).1.1
    (fun m y => (hf m y).trans (hh m y).symm)

end PPAC.Migration.ConstructionMergerWordOperation
