/- Pinned ConstructionIteration.functor / Round.fromBase_naturality:
construct ALL internal-index transitions from the actual incoming row of
the target record. Function graphs are set-coded on J x J; unrelated pairs
have one explicit default. No ambient ordinal recursion or choice. -/
import PPAC.Migration.ConstructionTowerHistory

namespace PPAC.Migration.ConstructionTowerTransitions
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Records Field)
open ForcingConditionGraphs (FunctionOn function_unique)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Before (i j : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem i j ∨ i = j

/-- The incoming family at j includes its own identity: domain is j+1.
These functions already occur in the three actual case producers. -/
def IncomingRows (J S : M.Carrier .set) : Prop :=
  ∀ j K, (Project.FirstOrderSemantics.reduct M).mem j J → Field 6 S j K →
    ∃ next, (Project.FirstOrderSemantics.reduct M).SuccessorOf next j ∧ FunctionOn next K

def Leg (S zero i j f : M.Carrier .set) : Prop :=
  (Before i j ∧ ∃ K, Field 6 S j K ∧ PureKuratowski.PairMember M i f K) ∨
  (¬ Before i j ∧ f = zero)

def Value (J S zero pair f : M.Carrier .set) : Prop :=
  ∃ i j, PureKuratowski.Code M pair i j ∧
    (Project.FirstOrderSemantics.reduct M).mem i J ∧
    (Project.FirstOrderSemantics.reduct M).mem j J ∧ Leg S zero i j f

def Matrix (J S zero P F : M.Carrier .set) : Prop :=
  ConstructionProbeLetters.Representatives J J P ∧ FunctionOn P F ∧
    ∀ i j f, Product F i j f ↔
      (Project.FirstOrderSemantics.reduct M).mem i J ∧
      (Project.FirstOrderSemantics.reduct M).mem j J ∧ Leg S zero i j f

def Order (J E : M.Carrier .set) : Prop :=
  (∀ p, (Project.FirstOrderSemantics.reduct M).mem p E →
    ∃ i j, PureKuratowski.Code M p i j) ∧
  ∀ i j, PureKuratowski.PairMember M i j E ↔
    (Project.FirstOrderSemantics.reduct M).mem i J ∧
    (Project.FirstOrderSemantics.reduct M).mem j J ∧ Before i j

theorem leg_total {J S zero i j : M.Carrier .set}
    (hS : Records J S) (hK : IncomingRows J S)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j J) :
    ∃ f, Leg S zero i j f := by
  classical
  by_cases hij : Before i j
  · obtain ⟨K,hField⟩ := ConstructionTowerHistory.field_total 6 hS hj
    obtain ⟨next,hSucc,hFn⟩ := hK j K hj hField
    have hi : (Project.FirstOrderSemantics.reduct M).mem i next := by
      apply (hSucc i).mpr
      rcases hij with hi | he
      · exact Or.inl hi
      · subst i
        exact Or.inr fun _ => Iff.rfl
    obtain ⟨f,hf,_⟩ := hFn.2 i hi
    exact ⟨f,Or.inl ⟨hij,K,hField,hf⟩⟩
  · exact ⟨zero,Or.inr ⟨hij,rfl⟩⟩

theorem leg_unique {J S zero i j f g : M.Carrier .set}
    (hS : Records J S) (hK : IncomingRows J S)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j J)
    (hf : Leg S zero i j f) (hg : Leg S zero i j g) : f = g := by
  rcases hf with ⟨hij,K,hField,hf⟩ | ⟨hij,rfl⟩
  · rcases hg with ⟨_,K',hField',hg⟩ | ⟨hij',_⟩
    · have he := ConstructionTowerHistory.field_unique 6 hS.1 hField hField'
      subst K'
      obtain ⟨next,_,hFn⟩ := hK j K hj hField
      exact function_unique hFn hf hg
    · exact False.elim (hij' hij)
  · rcases hg with ⟨hij',_⟩ | ⟨_,rfl⟩
    · exact False.elim (hij hij')
    · rfl

theorem value_unique {J S zero p f g : M.Carrier .set}
    (hS : Records J S) (hK : IncomingRows J S)
    (hf : Value J S zero p f) (hg : Value J S zero p g) : f = g := by
  obtain ⟨i,j,hc,_,hj,hf⟩ := hf
  obtain ⟨i',j',hc',_,_,hg⟩ := hg
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hc hc'
  exact leg_unique hS hK hj hf hg


def before {m : Nat} (i j : Fin m) : Project.Formula 1 m :=
  (.disj (.mem (.bound i) (.bound j)) (Project.Formula.extensionalEq (.bound i) (.bound j)))

theorem before_freeClosed {m : Nat} (i j : Fin m) :
    (before i j).FreeClosed := by
  simp -implicitDefEqProofs [before,Definitional.Formula.FreeClosed,Project.Formula.extensionalEq]

theorem before_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (i j : Fin m) :
    Project.Formula.satisfies env (before i j) ↔ Before (env.bound i) (env.bound j) := by
  simp only [before,Before,
    
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]


def incomingRows {m : Nat} (J S : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (.mem (.bound (1 : Fin (m+2))) (.bound J.succ.succ)) (.imp
  (ConstructionTowerHistory.field 6 S.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2))) (.existsE (.conj
  (Project.Formula.isSuccessor (.bound (0 : Fin (m+3))) (.bound (2 : Fin (m+3)))) (ProjectSyntax.encode id
  (Source.SetLanguage.functionOn (1 : Fin (m+3)) (0 : Fin (m+3))))))))))

theorem incomingRows_freeClosed {m : Nat} (J S : Fin m) :
    (incomingRows J S).FreeClosed := by
  simp -implicitDefEqProofs [incomingRows,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionTowerHistory.field_freeClosed,Project.Formula.isSuccessor]

theorem incomingRows_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J S : Fin m) :
    Project.Formula.satisfies env (incomingRows J S) ↔ IncomingRows (env.bound J) (env.bound S) := by
  simp only [incomingRows,IncomingRows,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionTowerHistory.field_semantics hM,Project.Formula.satisfies_isSuccessor_iff,ForcingConditionGraphs.functionOn_semantics (M := M)]
  rfl


def leg {m : Nat} (S zero i j f : Fin m) : Project.Formula 1 m :=
  (.disj (.conj (before i j) (.existsE (.conj (ConstructionTowerHistory.field 6 S.succ j.succ (0 : Fin (m+1)))
  (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin (m+1)) i.succ f.succ))))) (.conj (.neg (before
  i j)) (Project.Formula.extensionalEq (.bound f) (.bound zero))))

theorem leg_freeClosed {m : Nat} (S zero i j f : Fin m) :
    (leg S zero i j f).FreeClosed := by
  simp -implicitDefEqProofs [leg,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,before_freeClosed,ConstructionTowerHistory.field_freeClosed,Project.Formula.extensionalEq]

theorem leg_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (S zero i j f : Fin m) :
    Project.Formula.satisfies env (leg S zero i j f) ↔ Leg (env.bound S) (env.bound zero) (env.bound i) (env.bound j) (env.bound f) := by
  simp only [leg,Leg,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Formula.satisfies_disj_iff,before_semantics hM,ConstructionTowerHistory.field_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl


def value {m : Nat} (J S zero pair f : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.conj (PureKuratowskiProject.code (.bound pair.succ.succ) (.bound (1 : Fin (m+2)))
  (.bound (0 : Fin (m+2)))) (.conj (.mem (.bound (1 : Fin (m+2))) (.bound J.succ.succ)) (.conj (.mem (.bound
  (0 : Fin (m+2))) (.bound J.succ.succ)) (leg S.succ.succ zero.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2))
  f.succ.succ))))))

theorem value_freeClosed {m : Nat} (J S zero pair f : Fin m) :
    (value J S zero pair f).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,leg_freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J S zero pair f : Fin m) :
    Project.Formula.satisfies env (value J S zero pair f) ↔ Value (env.bound J) (env.bound S) (env.bound zero) (env.bound pair) (env.bound f) := by
  simp only [value,Value,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    KuratowskiZF.code_correct hM,leg_semantics hM]
  rfl


def matrix {m : Nat} (J S zero P F : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionProbeLetters.representatives J J P) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.functionOn F P)) (.forallE (.forallE (.forallE (.iff (ProjectSyntax.encode id
  (ForcingDiagramOrder.product F.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3)) (0 : Fin (m+3)))) (.conj
  (.mem (.bound (2 : Fin (m+3))) (.bound J.succ.succ.succ)) (.conj (.mem (.bound (1 : Fin (m+3))) (.bound
  J.succ.succ.succ)) (leg S.succ.succ.succ zero.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3)) (0 : Fin
  (m+3)))))))))))

theorem matrix_freeClosed {m : Nat} (J S zero P F : Fin m) :
    (matrix J S zero P F).FreeClosed := by
  simp -implicitDefEqProofs [matrix,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeLetters.representatives_freeClosed,leg_freeClosed]

theorem matrix_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J S zero P F : Fin m) :
    Project.Formula.satisfies env (matrix J S zero P F) ↔ Matrix (env.bound J) (env.bound S) (env.bound zero) (env.bound P) (env.bound F) := by
  simp only [matrix,Matrix,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionProbeLetters.representatives_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M),ForcingDiagramOrder.product_semantics (M := M),leg_semantics hM]
  rfl


def order {m : Nat} (J E : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.imp (.mem (.bound (0 : Fin (m+1))) (.bound E.succ)) (.existsE (.existsE
  (PureKuratowskiProject.code (.bound (2 : Fin (m+3))) (.bound (1 : Fin (m+3))) (.bound (0 : Fin
  (m+3)))))))) (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge E.succ.succ (1 :
  Fin (m+2)) (0 : Fin (m+2)))) (.conj (.mem (.bound (1 : Fin (m+2))) (.bound J.succ.succ)) (.conj (.mem
  (.bound (0 : Fin (m+2))) (.bound J.succ.succ)) (before (1 : Fin (m+2)) (0 : Fin (m+2)))))))))

theorem order_freeClosed {m : Nat} (J E : Fin m) :
    (order J E).FreeClosed := by
  simp -implicitDefEqProofs [order,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,PureKuratowskiProject.code,before_freeClosed]

theorem order_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E : Fin m) :
    Project.Formula.satisfies env (order J E) ↔ Order (env.bound J) (env.bound E) := by
  simp only [order,Order,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,KuratowskiZF.code_correct hM,before_semantics hM]
  rfl


theorem exists_order (hM : FirstOrder.Theory.Models M nativeZF) (J : M.Carrier .set) :
    ∃ E, Order J E := by
  let schema : Project.BinarySchema 0 := {
    body := before 1 0
    freeClosed := before_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 0 := {
    bound := Fin.elim0
    free := fun _ => J }
  obtain ⟨E,hRel,hE⟩ := ZF.exists_setRelationOn_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) schema env J
  refine ⟨E,hRel.1,fun i j => ?_⟩
  exact (hE i j).trans (and_congr_right fun _ =>
    and_congr_right fun _ => before_semantics hM ((env.push i).push j) 1 0)

theorem exists_matrix (hM : FirstOrder.Theory.Models M nativeZF)
    {J S : M.Carrier .set} (zero : M.Carrier .set)
    (hS : Records J S) (hK : IncomingRows J S) :
    ∃ P F, Matrix J S zero P F := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨P,hP⟩ := ZF.exists_cartesianProduct hZF (KuratowskiZF.interpretation hM) J J
  have hRep : ConstructionProbeLetters.Representatives J J P := by
    intro p
    constructor
    · rintro hp
      obtain ⟨i,hi,j,hj,hc⟩ := (hP p).mp hp
      exact ⟨i,j,hi,hj,hc⟩
    · rintro ⟨i,j,hi,hj,hc⟩
      exact (hP p).mpr ⟨i,hi,j,hj,hc⟩
  let schema : Project.BinarySchema 3 := {
    body := value 2 3 4 1 0
    freeClosed := value_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases J (Fin.cases S (fun _ => zero))
    free := fun _ => J }
  have he (p f) : schema.denote env p f ↔ Value J S zero p f :=
    value_semantics hM ((env.push p).push f) 2 3 4 1 0
  have ht : ∀ p, (Project.FirstOrderSemantics.reduct M).mem p P →
      ∃ f, schema.denote env p f := by
    intro p hp
    obtain ⟨i,j,hi,hj,hc⟩ := (hRep p).mp hp
    obtain ⟨f,hf⟩ := leg_total hS hK hj
    exact ⟨f,(he p f).mpr ⟨i,j,hc,hi,hj,hf⟩⟩
  have hu : ∀ p, (Project.FirstOrderSemantics.reduct M).mem p P → ∀ f g,
      schema.denote env p f → schema.denote env p g → f = g :=
    fun _ _ _ _ hf hg => value_unique hS hK ((he _ _).mp hf) ((he _ _).mp hg)
  obtain ⟨A,hA⟩ := ZF.exists_functionalImageOn hZF schema env P ht hu
  obtain ⟨F,hF,hG⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (KuratowskiZF.interpretation hM)
    schema env ht hu (fun p f hp hv => (hA f).mpr ⟨p,hp,hv⟩)
  refine ⟨P,F,hRep,((ForcingSupportSize.native_mapsTo hM P A F).mpr hF).1,fun i j f => ?_⟩
  constructor
  · rintro ⟨p,hc,hf⟩
    obtain ⟨i',j',hc',hi,hj,hv⟩ := (he p f).mp ((hG p f).mp hf).2
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hc hc'
    exact ⟨hi,hj,hv⟩
  · rintro ⟨hi,hj,hv⟩
    obtain ⟨p,hc⟩ := KuratowskiZF.exists_code hM i j
    exact ⟨p,hc,(hG p f).mpr ⟨(hRep p).mpr ⟨i,j,hi,hj,hc⟩,
      (he p f).mpr ⟨i,j,hc,hi,hj,hv⟩⟩⟩

/-- The entry actually used by the original successor/limit parents is
literally the saved leg of the target stage, including i=j. -/
theorem matrix_at {J S zero P F i j K f : M.Carrier .set}
    (hS : Records J S) (hMatrix : Matrix J S zero P F)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j J)
    (hij : Before i j) (hK : Field 6 S j K) :
    Product F i j f ↔ PureKuratowski.PairMember M i f K := by
  constructor
  · intro hf
    rcases ((hMatrix.2.2 i j f).mp hf).2.2 with ⟨_,K',hK',hf⟩ | ⟨hno,_⟩
    · exact (ConstructionTowerHistory.field_unique 6 hS.1 hK' hK) ▸ hf
    · exact False.elim (hno hij)
  · intro hf
    exact (hMatrix.2.2 i j f).mpr ⟨hi,hj,Or.inl ⟨hij,K,hK,hf⟩⟩

theorem matrix_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {J S zero P F P' F' : M.Carrier .set}
    (hF : Matrix J S zero P F) (hF' : Matrix J S zero P' F') : P = P' ∧ F = F' := by
  have hP := (ModelTransfer.extensionality hM).eq_of_same_members P P'
    (fun p => (hF.1 p).trans (hF'.1 p).symm)
  subst P'
  have rel {f} (hf : FunctionOn P f) :
      (Project.FirstOrderSemantics.reduct M).IsSetRelation (KuratowskiZF.interpretation hM) f := by
    intro p hp
    obtain ⟨x,y,_,hc⟩ := hf.1 p hp
    exact ⟨x,y,hc⟩
  have edges (p f) : PureKuratowski.PairMember M p f F ↔ PureKuratowski.PairMember M p f F' := by
    by_cases hp : (Project.FirstOrderSemantics.reduct M).mem p P
    · obtain ⟨i,j,_,_,hc⟩ := (hF.1 p).mp hp
      have ff (g) : Product g i j f ↔ PureKuratowski.PairMember M p f g := by
        constructor
        · rintro ⟨p',hc',hf⟩
          exact (KuratowskiZF.code_unique hM hc' hc) ▸ hf
        · intro hf
          exact ⟨p,hc,hf⟩
      exact (ff F).symm.trans ((hF.2.2 i j f).trans ((hF'.2.2 i j f).symm.trans (ff F')))
    · exact ⟨fun hf => False.elim (hp (ForcingConditionGraphs.function_input hF.2.1 hf)),
        fun hf => False.elim (hp (ForcingConditionGraphs.function_input hF'.2.1 hf))⟩
  exact ⟨rfl,SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    (rel hF.2.1) (rel hF'.2.1) edges⟩

theorem order_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {J E E' : M.Carrier .set} (hE : Order J E) (hE' : Order J E') : E = E' := by
  have hRel : (Project.FirstOrderSemantics.reduct M).IsSetRelation
      (KuratowskiZF.interpretation hM) E := hE.1
  have hRel' : (Project.FirstOrderSemantics.reduct M).IsSetRelation
      (KuratowskiZF.interpretation hM) E' := hE'.1
  exact SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    hRel hRel' (fun i j => (hE.2 i j).trans (hE'.2 i j).symm)

/-- Exact original directed-index laws for ANY internal ordinal J.
The empty case is vacuous; nonempty limit parents retain their own guard. -/
theorem order_index_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {J E : M.Carrier .set} (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hE : Order J E) : ConstructionDirectedSystem.IndexLaws J E := by
  refine ⟨fun i hi => (hE.2 i i).mpr ⟨hi,hi,Or.inr rfl⟩,?_,?_⟩
  · intro i j k hi hj hk hij hjk
    have h1 := ((hE.2 i j).mp hij).2.2
    have h2 := ((hE.2 j k).mp hjk).2.2
    apply (hE.2 i k).mpr
    refine ⟨hi,hk,?_⟩
    rcases h1 with h1 | rfl
    · rcases h2 with h2 | rfl
      · exact Or.inl (hJ.wellOrder.linear.trans i hi j hj k hk h1 h2)
      · exact Or.inl h1
    · exact h2
  · intro i j hi hj
    rcases hJ.wellOrder.linear.compare i hi j hj with he | hij | hji
    · have heq := (ModelTransfer.extensionality hM).eq_of_same_members i j he
      subst j
      exact ⟨i,hi,(hE.2 i i).mpr ⟨hi,hi,Or.inr rfl⟩,
        (hE.2 i i).mpr ⟨hi,hi,Or.inr rfl⟩⟩
    · exact ⟨j,hj,(hE.2 i j).mpr ⟨hi,hj,Or.inl hij⟩,
        (hE.2 j j).mpr ⟨hj,hj,Or.inr rfl⟩⟩
    · exact ⟨i,hi,(hE.2 i i).mpr ⟨hi,hi,Or.inr rfl⟩,
        (hE.2 j i).mpr ⟨hj,hi,Or.inl hji⟩⟩

/-- Construct ALL eleven field/order/map tables, not merely arbitrary
families satisfying a requested output contract. P is the actual J x J. -/
theorem exists_tables (hM : FirstOrder.Theory.Models M nativeZF)
    {J S : M.Carrier .set} (zero : M.Carrier .set)
    (hS : Records J S) (hK : IncomingRows J S) :
    ∃ Domains Muls Units Marks Heights Costs Incoming Origins Times E P F,
      ConstructionTowerHistory.Charts J S Domains Muls Units Marks Heights Costs Incoming Origins Times ∧
      ForcingConditionGraphs.IdentityGraph J Times ∧ Order J E ∧ Matrix J S zero P F ∧
      ((Project.FirstOrderSemantics.reduct M).IsOrdinal J →
        ConstructionDirectedSystem.IndexLaws J E) := by
  obtain ⟨Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,hCharts,hTime⟩ :=
    ConstructionTowerHistory.exists_charts hM hS
  obtain ⟨E,hE⟩ := exists_order hM J
  obtain ⟨P,F,hF⟩ := exists_matrix hM zero hS hK
  exact ⟨Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,
    hCharts,hTime,hE,hF,fun hJ => order_index_laws hM hJ hE⟩

def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 3 (.imp (ConstructionTowerHistory.records (0 : Fin 3) (1 : Fin 3)) (.imp
    (incomingRows (0 : Fin 3) (1 : Fin 3)) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionTowerHistory.charts
    (12 : Fin 15) (13 : Fin 15) (11 : Fin 15) (10 : Fin 15) (9 : Fin 15) (8 : Fin 15) (7 : Fin 15) (6 :
    Fin 15) (5 : Fin 15) (4 : Fin 15) (3 : Fin 15)) (.conj (ProjectSyntax.encode id
    (ForcingConditionGraphs.identityGraph (12 : Fin 15) (3 : Fin 15))) (.conj (order (12 : Fin 15) (2 :
    Fin 15)) (.conj (matrix (12 : Fin 15) (13 : Fin 15) (14 : Fin 15) (1 : Fin 15) (0 : Fin 15)) (.imp
    (Project.Formula.isOrdinal (.bound (12 : Fin 15))) (ConstructionDirectedSystem.indexLaws (12 : Fin
    15) (2 : Fin 15))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionTowerHistory.records_freeClosed,incomingRows_freeClosed,
      ConstructionTowerHistory.charts_freeClosed,order_freeClosed,matrix_freeClosed,
      Project.Formula.isOrdinal,ConstructionDirectedSystem.indexLaws_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,ConstructionTowerHistory.records_semantics hM,
    incomingRows_semantics hM,order_semantics hM,matrix_semantics hM,
    ConstructionTowerHistory.charts_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.identityGraph_semantics (M := M),
    Project.Formula.satisfies_isOrdinal_iff,Project.Term.eval_bound,
    ConstructionDirectedSystem.indexLaws_semantics hM]
  exact fun hS hK => exists_tables hM (bound 2) hS hK

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionTowerTransitions
