/- Pinned CellTowers.NewAt/exists_newAt/newIndex/newIndex_eq (249-291).
The source well-founded minimum is an INTERNAL set-coded wellorder minimum.
The stage family is a set function on the same index set; continuity is at
noninitial cuts with no immediate predecessor. Source terminal implies the
coverage premise used here. No external well-foundedness or Choice premise.
Consumer: global CellTowers.dependencies at the unique first active stage.
Concrete BlockTowers.flatten and the stage-cell family are separate inputs. -/
import PPAC.Migration.ConstructionCellParameters
import PPAC.Migration.ConstructionScheduleOrderSyntax

namespace PPAC.Migration.ConstructionFirstAppearance
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingConditionGraphs (FunctionOn function_unique)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def At (S i x : M.Carrier .set) : Prop :=
  ∃ D, PureKuratowski.PairMember M i D S ∧ (Project.FirstOrderSemantics.reduct M).mem x D

def Cover (J r i j : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem i J ∧
  (Project.FirstOrderSemantics.reduct M).mem j J ∧ PureKuratowski.PairMember M i j r ∧
  ∀ k, (Project.FirstOrderSemantics.reduct M).mem k J →
    PureKuratowski.PairMember M i k r → ¬ PureKuratowski.PairMember M k j r

def Timeline (hM : FirstOrder.Theory.Models M nativeZF)
    (T J r bottom S : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) r J ∧
  FunctionOn J S ∧ (Project.FirstOrderSemantics.reduct M).mem bottom J ∧
  (∀ i, (Project.FirstOrderSemantics.reduct M).mem i J → bottom = i ∨ PureKuratowski.PairMember M bottom i r) ∧
  (∀ i x, At S i x → (Project.FirstOrderSemantics.reduct M).mem x T) ∧
  (∀ i j x, i = j ∨ PureKuratowski.PairMember M i j r → At S i x → At S j x) ∧
  (∀ x, (Project.FirstOrderSemantics.reduct M).mem x T →
    ∃ i, (Project.FirstOrderSemantics.reduct M).mem i J ∧ At S i x) ∧
  ∀ j, (Project.FirstOrderSemantics.reduct M).mem j J → j ≠ bottom →
    (¬ ∃ i, Cover J r i j) → ∀ x, At S j x →
      ∃ i, (Project.FirstOrderSemantics.reduct M).mem i J ∧ PureKuratowski.PairMember M i j r ∧ At S i x

def NewAt (J r S i x : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem i J ∧
    ∃ j, Cover J r i j ∧ At S j x ∧ ¬ At S i x

/-- Default bottom is used exactly for elements already in the bottom stage. -/
def Value (J r bottom S x i : M.Carrier .set) : Prop :=
  (At S bottom x ∧ i = bottom) ∨ (¬ At S bottom x ∧ NewAt J r S i x)

def Index (T J r bottom S index : M.Carrier .set) : Prop :=
  MapsTo T J index ∧ ∀ x i, PureKuratowski.PairMember M x i index ↔
    (Project.FirstOrderSemantics.reduct M).mem x T ∧ Value J r bottom S x i

def atStage {m : Nat} (S i x : Fin m) : Project.Formula 1 m :=
  (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge S.succ i.succ 0)) (.mem (.bound x.succ) (.bound 0))))

theorem atStage_freeClosed {m : Nat} (S i x : Fin m) :
    (atStage S i x).FreeClosed := by
  simp -implicitDefEqProofs [atStage,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem atStage_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (S i x : Fin m) :
    Project.Formula.satisfies env (atStage S i x) ↔ At (env.bound S) (env.bound i) (env.bound x) := by
  simp only [atStage,At,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def cover {m : Nat} (J r i j : Fin m) : Project.Formula 1 m :=
    (.conj (.mem (.bound i) (.bound J)) (.conj (.mem (.bound j) (.bound J)) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge r i j)) (.forallE (.imp (.mem (.bound 0) (.bound J.succ)) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge r.succ i.succ 0)) (.neg (ProjectSyntax.encode id
  (Source.SetLanguage.edge r.succ 0 j.succ)))))))))

theorem cover_freeClosed {m : Nat} (J r i j : Fin m) :
    (cover J r i j).FreeClosed := by
  simp -implicitDefEqProofs [cover,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem cover_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J r i j : Fin m) :
    Project.Formula.satisfies env (cover J r i j) ↔ Cover (env.bound J) (env.bound r) (env.bound i) (env.bound j) := by
  simp only [cover,Cover,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def timeline {m : Nat} (T J r bottom S : Fin m) : Project.Formula 1 m :=
    (.conj (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound r) (.bound J)) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.functionOn S J)) (.conj (.mem (.bound bottom) (.bound J))
  (.conj (.forallE (.imp (.mem (.bound 0) (.bound J.succ)) (.disj (Project.Formula.extensionalEq (.bound
  bottom.succ) (.bound 0)) (ProjectSyntax.encode id (Source.SetLanguage.edge r.succ bottom.succ 0))))) (.conj
  (.forallE (.forallE (.imp (atStage S.succ.succ 1 0) (.mem (.bound 0) (.bound T.succ.succ))))) (.conj
  (.forallE (.forallE (.forallE (.imp (.disj (Project.Formula.extensionalEq (.bound 2) (.bound 1))
  (ProjectSyntax.encode id (Source.SetLanguage.edge r.succ.succ.succ 2 1))) (.imp (atStage S.succ.succ.succ 2
  0) (atStage S.succ.succ.succ 1 0)))))) (.conj (.forallE (.imp (.mem (.bound 0) (.bound T.succ)) (.existsE
  (.conj (.mem (.bound 0) (.bound J.succ.succ)) (atStage S.succ.succ 0 1))))) (.forallE (.imp (.mem (.bound 0)
  (.bound J.succ)) (.imp (.neg (Project.Formula.extensionalEq (.bound 0) (.bound bottom.succ))) (.imp (.neg
  (.existsE (cover J.succ.succ r.succ.succ 0 1))) (.forallE (.imp (atStage S.succ.succ 1 0) (.existsE (.conj
  (.mem (.bound 0) (.bound J.succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  r.succ.succ.succ 0 2)) (atStage S.succ.succ.succ 0 1)))))))))))))))))

theorem timeline_freeClosed {m : Nat} (T J r bottom S : Fin m) :
    (timeline T J r bottom S).FreeClosed := by
  simp -implicitDefEqProofs [timeline,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq,atStage_freeClosed,cover_freeClosed]

theorem timeline_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (T J r bottom S : Fin m) :
    Project.Formula.satisfies env (timeline T J r bottom S) ↔ Timeline hM (env.bound T) (env.bound J) (env.bound r) (env.bound bottom) (env.bound S) := by
  simp only [timeline,Timeline,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,atStage_semantics hM,cover_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M),Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM)]
  rfl

def newAt {m : Nat} (J r S i x : Fin m) : Project.Formula 1 m :=
  (.conj (.mem (.bound i) (.bound J)) (.existsE (.conj (cover J.succ r.succ i.succ 0) (.conj (atStage S.succ 0 x.succ) (.neg (atStage S.succ i.succ x.succ))))))

theorem newAt_freeClosed {m : Nat} (J r S i x : Fin m) :
    (newAt J r S i x).FreeClosed := by
  simp -implicitDefEqProofs [newAt,Definitional.Formula.FreeClosed,cover_freeClosed,atStage_freeClosed]

theorem newAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J r S i x : Fin m) :
    Project.Formula.satisfies env (newAt J r S i x) ↔ NewAt (env.bound J) (env.bound r) (env.bound S) (env.bound i) (env.bound x) := by
  simp only [newAt,NewAt,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,cover_semantics hM,atStage_semantics hM]
  rfl

def value {m : Nat} (J r bottom S x i : Fin m) : Project.Formula 1 m :=
  (.disj (.conj (atStage S bottom x) (Project.Formula.extensionalEq (.bound i) (.bound bottom))) (.conj (.neg (atStage S bottom x)) (newAt J r S i x)))

theorem value_freeClosed {m : Nat} (J r bottom S x i : Fin m) :
    (value J r bottom S x i).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,Project.Formula.extensionalEq,atStage_freeClosed,newAt_freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J r bottom S x i : Fin m) :
    Project.Formula.satisfies env (value J r bottom S x i) ↔ Value (env.bound J) (env.bound r) (env.bound bottom) (env.bound S) (env.bound x) (env.bound i) := by
  simp only [value,Value,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),atStage_semantics hM,newAt_semantics hM]

def indexGraph {m : Nat} (T J r bottom S index : Fin m) : Project.Formula 1 m :=
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo index T J)) (.forallE (.forallE (.iff
  (ProjectSyntax.encode id (Source.SetLanguage.edge index.succ.succ 1 0)) (.conj (.mem (.bound 1) (.bound
  T.succ.succ)) (value J.succ.succ r.succ.succ bottom.succ.succ S.succ.succ 1 0))))))

theorem indexGraph_freeClosed {m : Nat} (T J r bottom S index : Fin m) :
    (indexGraph T J r bottom S index).FreeClosed := by
  simp -implicitDefEqProofs [indexGraph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,value_freeClosed]

theorem indexGraph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (T J r bottom S index : Fin m) :
    Project.Formula.satisfies env (indexGraph T J r bottom S index) ↔ Index (env.bound T) (env.bound J) (env.bound r) (env.bound bottom) (env.bound S) (env.bound index) := by
  simp only [indexGraph,Index,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_iff_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,value_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M)]
  rfl

theorem cover_le (hM : FirstOrder.Theory.Models M nativeZF)
    {J r i j k : M.Carrier .set}
    (hr : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) r J)
    (hc : Cover J r i j) (hk : (Project.FirstOrderSemantics.reduct M).mem k J)
    (hik : PureKuratowski.PairMember M i k r) : j = k ∨ PureKuratowski.PairMember M j k r := by
  rcases hr.linear.2.2 j hc.2.1 k hk with he | hjk | hkj
  · exact Or.inl ((ModelTransfer.extensionality hM).eq_of_same_members j k he)
  · exact Or.inr hjk
  · exact (hc.2.2.2 k hk hik hkj).elim

theorem newAt_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {T J r bottom S i j x : M.Carrier .set} (hT : Timeline hM T J r bottom S)
    (hi : NewAt J r S i x) (hj : NewAt J r S j x) : i = j := by
  obtain ⟨hiJ,a,hia,hax,hnix⟩ := hi
  obtain ⟨hjJ,b,hjb,hbx,hnjx⟩ := hj
  rcases hT.1.linear.2.2 i hiJ j hjJ with he | hij | hji
  · exact (ModelTransfer.extensionality hM).eq_of_same_members i j he
  · exact (hnjx (hT.2.2.2.2.2.1 a j x (cover_le hM hT.1 hia hjJ hij) hax)).elim
  · exact (hnix (hT.2.2.2.2.2.1 b i x (cover_le hM hT.1 hjb hiJ hji) hbx)).elim

theorem newAt_not_bottom (hM : FirstOrder.Theory.Models M nativeZF)
    {T J r bottom S i x : M.Carrier .set} (hT : Timeline hM T J r bottom S)
    (hi : NewAt J r S i x) : ¬ At S bottom x := by
  intro hx
  obtain ⟨hiJ,j,_,_,hni⟩ := hi
  exact hni (hT.2.2.2.2.2.1 bottom i x (hT.2.2.2.1 i hiJ) hx)

/-- Separation and the native internal least-element axiom replace the
source's metatheoretic wellFounded_lt.min; continuity excludes a limit. -/
theorem exists_newAt (hM : FirstOrder.Theory.Models M nativeZF)
    {T J r bottom S x : M.Carrier .set} (hT : Timeline hM T J r bottom S)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x T) (hxb : ¬ At S bottom x) :
    ∃ i, NewAt J r S i x := by
  classical
  let N := Project.FirstOrderSemantics.reduct M
  let schema : Project.UnarySchema 2 := {
    body := atStage 1 0 2
    freeClosed := atStage_freeClosed .. }
  let env : SetTheory.Env N 2 := { bound := Fin.cases S (fun _ => x), free := fun _ => S }
  have he i : schema.denote env i ↔ At S i x := atStage_semantics hM (env.push i) 1 0 2
  obtain ⟨A,hA⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env J
  have ha i : N.mem i A ↔ N.mem i J ∧ At S i x :=
    (hA i).trans (and_congr_right fun _ => he i)
  obtain ⟨k,hk,hkx⟩ := hT.2.2.2.2.2.2.1 x hx
  obtain ⟨j,hj,hmin⟩ := hT.1.least A (fun i hi => ((ha i).mp hi).1) ⟨k,(ha k).mpr ⟨hk,hkx⟩⟩
  obtain ⟨hjJ,hjx⟩ := (ha j).mp hj
  have hEarlier : ∀ i, N.mem i J → PureKuratowski.PairMember M i j r → ¬ At S i x := by
    intro i hi hij hix
    rcases hmin i ((ha i).mpr ⟨hi,hix⟩) with heq | hji
    · have eq := (ModelTransfer.extensionality hM).eq_of_same_members j i heq
      subst i
      exact hT.1.linear.2.1.1 j hjJ hij
    · exact hT.1.linear.2.1.1 j hjJ (hT.1.linear.2.1.2 j hjJ i hi j hjJ hji hij)
  have hne : j ≠ bottom := by
    intro eq
    exact hxb (eq ▸ hjx)
  by_cases hp : ∃ i, Cover J r i j
  · obtain ⟨i,hi⟩ := hp
    exact ⟨i,hi.1,j,hi,hjx,hEarlier i hi.1 hi.2.2.1⟩
  · obtain ⟨i,hi,hij,hix⟩ := hT.2.2.2.2.2.2.2 j hjJ hne hp x hjx
    exact (hEarlier i hi hij hix).elim

theorem value_total (hM : FirstOrder.Theory.Models M nativeZF)
    {T J r bottom S x : M.Carrier .set} (hT : Timeline hM T J r bottom S)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x T) : ∃ i, Value J r bottom S x i := by
  classical
  by_cases hb : At S bottom x
  · exact ⟨bottom,Or.inl ⟨hb,rfl⟩⟩
  · obtain ⟨i,hi⟩ := exists_newAt hM hT hx hb
    exact ⟨i,Or.inr ⟨hb,hi⟩⟩

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {T J r bottom S x i j : M.Carrier .set} (hT : Timeline hM T J r bottom S)
    (hi : Value J r bottom S x i) (hj : Value J r bottom S x j) : i = j := by
  rcases hi with ⟨hb,hi⟩ | ⟨hnb,hi⟩
  · rcases hj with ⟨_,hj⟩ | ⟨hnb,_⟩
    · exact hi.trans hj.symm
    · exact (hnb hb).elim
  · rcases hj with ⟨hb,_⟩ | ⟨_,hj⟩
    · exact (hnb hb).elim
    · exact newAt_unique hM hT hi hj

/-- An actual internal total function into the SAME source index set. -/
theorem exists_index (hM : FirstOrder.Theory.Models M nativeZF)
    {T J r bottom S : M.Carrier .set} (hT : Timeline hM T J r bottom S) :
    ∃ index, Index T J r bottom S index := by
  let schema : Project.BinarySchema 4 := {
    body := value 2 3 4 5 1 0
    freeClosed := value_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 := {
    bound := Fin.cases J (Fin.cases r (Fin.cases bottom (fun _ => S)))
    free := fun _ => J }
  have he x i : schema.denote env x i ↔ Value J r bottom S x i :=
    value_semantics hM ((env.push x).push i) 2 3 4 5 1 0
  have ht : ∀ x, (Project.FirstOrderSemantics.reduct M).mem x T → ∃ i, schema.denote env x i := by
    intro x hx
    obtain ⟨i,hi⟩ := value_total hM hT hx
    exact ⟨i,(he x i).mpr hi⟩
  have hu : ∀ x, (Project.FirstOrderSemantics.reduct M).mem x T → ∀ i j,
      schema.denote env x i → schema.denote env x j → i = j :=
    fun _ _ _ _ hi hj => value_unique hM hT ((he _ _).mp hi) ((he _ _).mp hj)
  have hb : ∀ x i, (Project.FirstOrderSemantics.reduct M).mem x T → schema.denote env x i →
      (Project.FirstOrderSemantics.reduct M).mem i J := by
    intro x i _ hi
    rcases (he x i).mp hi with ⟨_,heq⟩ | ⟨_,hi⟩
    · exact heq.symm ▸ hT.2.2.1
    · exact hi.1
  obtain ⟨index,hI,hG⟩ := ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) schema env ht hu hb
  exact ⟨index,(ForcingSupportSize.native_mapsTo hM T J index).mpr hI,
    fun x i => (hG x i).trans (and_congr_right fun _ => he x i)⟩

theorem index_at (hM : FirstOrder.Theory.Models M nativeZF)
    {T J r bottom S index i x : M.Carrier .set} (hT : Timeline hM T J r bottom S)
    (hI : Index T J r bottom S index) (hi : NewAt J r S i x) :
    PureKuratowski.PairMember M x i index := by
  have hx : (Project.FirstOrderSemantics.reduct M).mem x T := by
    obtain ⟨_,j,_,hj,_⟩ := hi
    exact hT.2.2.2.2.1 j x hj
  exact (hI.2 x i).mpr ⟨hx,Or.inr ⟨newAt_not_bottom hM hT hi,hi⟩⟩

theorem index_bottom {T J r bottom S index x : M.Carrier .set}
    (hx : (Project.FirstOrderSemantics.reduct M).mem x T)
    (hI : Index T J r bottom S index) (hb : At S bottom x) :
    PureKuratowski.PairMember M x bottom index :=
  (hI.2 x bottom).mpr ⟨hx,Or.inl ⟨hb,rfl⟩⟩

def constructionSentence {m : Nat} (T J r bottom S : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (timeline T J r bottom S)
      (.existsE (indexGraph T.succ J.succ r.succ bottom.succ S.succ 0)))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,timeline_freeClosed,indexGraph_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (T J r bottom S : Fin m) :
    (Project.fo_sentence (constructionSentence T J r bottom S)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence T J r bottom S)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    timeline_semantics hM,indexGraph_semantics hM]
  exact exists_index hM

theorem construction_kernel_certificate {m : Nat} (T J r bottom S : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence T J r bottom S)) := by
  apply ModelTransfer.derives
  intro M hM
  exact construction_models hM T J r bottom S

/-- Exact source set of selected stages, not the entire index image (which
may also contain the bottom default for retained old elements). -/
def Selected (J r S retained selected : M.Carrier .set) : Prop := ∀ i,
  (Project.FirstOrderSemantics.reduct M).mem i selected ↔
    ∃ x, (Project.FirstOrderSemantics.reduct M).mem x retained ∧ NewAt J r S i x

def selectedSet {m : Nat} (J r S retained selected : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound selected.succ))
    (.existsE (.conj (.mem (.bound 0) (.bound retained.succ.succ))
      (newAt J.succ.succ r.succ.succ S.succ.succ 1 0))))

theorem selectedSet_freeClosed {m : Nat} (J r S retained selected : Fin m) :
    (selectedSet J r S retained selected).FreeClosed := by
  simp -implicitDefEqProofs [selectedSet,Definitional.Formula.FreeClosed,newAt_freeClosed]

theorem selectedSet_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J r S retained selected : Fin m) :
    Project.Formula.satisfies env (selectedSet J r S retained selected) ↔
      Selected (env.bound J) (env.bound r) (env.bound S) (env.bound retained) (env.bound selected) := by
  simp only [selectedSet,Selected,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    newAt_semantics hM]
  rfl

theorem exists_selected (hM : FirstOrder.Theory.Models M nativeZF)
    {w T J r bottom S index retained : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hT : Timeline hM T J r bottom S) (hI : Index T J r bottom S index)
    (hRet : ConstructionRealCuts.Subset retained T) (hSmall : ForcingSupportSize.Small retained w) :
    ∃ selected, Selected J r S retained selected ∧ ForcingSupportSize.Small selected w := by
  let N := Project.FirstOrderSemantics.reduct M
  obtain ⟨f,hf⟩ := ZF.exists_restriction (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) index retained
  have hF : MapsTo retained J f := by
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro row hrow
      obtain ⟨x,i,hcode⟩ := hf.1 row hrow
      exact ⟨x,i,((hf.2 x i).mp ⟨row,hcode,hrow⟩).1,hcode⟩
    · intro x hx
      obtain ⟨i,hxi,_⟩ := hI.1.1.2 x (hRet x hx)
      exact ⟨i,(hf.2 x i).mpr ⟨hx,hxi⟩,fun j hxj =>
        function_unique hI.1.1 ((hf.2 x j).mp hxj).2 hxi⟩
    · intro x i hxi
      exact hI.1.2 x i ((hf.2 x i).mp hxi).2
  obtain ⟨image,hImage,_,hImageSmall⟩ := ConstructionCellParameters.range_small hM hw hF hSmall
  let schema : Project.UnarySchema 4 := {
    body := .existsE (.conj (.mem (.bound 0) (.bound 5)) (newAt 2 3 4 1 0))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,newAt_freeClosed] }
  let env : SetTheory.Env N 4 := {
    bound := Fin.cases J (Fin.cases r (Fin.cases S (fun _ => retained)))
    free := fun _ => J }
  have he i : Project.Formula.satisfies (env.push i) schema.body ↔ ∃ x, N.mem x retained ∧ NewAt J r S i x := by
    simp only [schema,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
      Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,newAt_semantics hM]
    rfl
  obtain ⟨selected,hs⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env J
  have hSelected : Selected J r S retained selected := by
    intro i
    rw [hs i,he i]
    exact ⟨And.right,fun ⟨x,hx,hi⟩ => ⟨hi.1,x,hx,hi⟩⟩
  refine ⟨selected,hSelected,ForcingSupportSize.small_subset hM ?_ hImageSmall⟩
  intro i hi
  obtain ⟨x,hx,hNew⟩ := (hSelected i).mp hi
  exact (hImage i).mpr ⟨x,hx,(hf.2 x i).mpr ⟨hx,index_at hM hT hI hNew⟩⟩

def selectedSentence {m : Nat} (w T J r bottom S index retained : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOmega (.bound w))
      (.imp (timeline T J r bottom S)
        (.imp (indexGraph T J r bottom S index)
          (.imp (Project.Formula.subset (.bound retained) (.bound T))
            (.imp (ProjectSyntax.encode id (ForcingSupportSize.small retained w))
              (.existsE (.conj (selectedSet J.succ r.succ S.succ retained.succ 0)
                (ProjectSyntax.encode id (ForcingSupportSize.small 0 w.succ)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      Project.Formula.isInductive,Project.Formula.isEmpty,Project.Formula.isSuccessor,
      Project.Formula.extensionalEq,ProjectSyntax.freeClosed,timeline_freeClosed,
      indexGraph_freeClosed,selectedSet_freeClosed]

theorem selected_models (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (w T J r bottom S index retained : Fin m) :
    (Project.fo_sentence (selectedSentence w T J r bottom S index retained)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (selectedSentence w T J r bottom S index retained)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_conj_iff,timeline_semantics hM,indexGraph_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),selectedSet_semantics hM]
  exact exists_selected hM

theorem selected_kernel_certificate {m : Nat} (w T J r bottom S index retained : Fin m) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (selectedSentence w T J r bottom S index retained)) := by
  apply ModelTransfer.derives
  intro M hM
  exact selected_models hM w T J r bottom S index retained

end PPAC.Migration.ConstructionFirstAppearance
