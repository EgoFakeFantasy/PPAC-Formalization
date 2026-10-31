/- Pinned StableSelectors.Condition.rows/rows_of_mem/rows_eq_of_le:21-34.
The actual total internal graph on C = I x K, with von Neumann false/true.
Unassigned coordinates default to false; only assigned values persist.
Consumer: GermSelectors.rawPattern and StableSelectors.Complete.pattern_eq. -/
import PPAC.Migration.ForcingCohenFlip

namespace PPAC.Migration.ConstructionCohenRows
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo)
open ForcingCohenConditions (Condition Functional)
open ForcingCohenCoordinates (Cartesian)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Value (z o p a b : M.Carrier .set) : Prop :=
  (PureKuratowski.PairMember M a o p ∧ b = o) ∨
    (¬ PureKuratowski.PairMember M a o p ∧ b = z)

def value {m : Nat} (z o p a b : Fin m) : Project.Formula 1 m := .disj
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge p a o))
    (Project.Formula.extensionalEq (.bound b) (.bound o)))
  (.conj (.neg (ProjectSyntax.encode id (Source.SetLanguage.edge p a o)))
    (Project.Formula.extensionalEq (.bound b) (.bound z)))

theorem value_freeClosed {m : Nat} (z o p a b : Fin m) : (value z o p a b).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (z o p a b : Fin m) :
    Project.Formula.satisfies env (value z o p a b) ↔ Value (env.bound z) (env.bound o) (env.bound p) (env.bound a) (env.bound b) := by
  simp only [value,Value,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Term.eval_bound]
  rfl

theorem value_unique {z o p a b c : M.Carrier .set} (hb : Value z o p a b) (hc : Value z o p a c) : b = c := by
  rcases hb with ⟨hb,rfl⟩ | ⟨hb,rfl⟩ <;> rcases hc with ⟨hc,rfl⟩ | ⟨hc,rfl⟩
  · rfl
  · exact (hc hb).elim
  · exact (hb hc).elim
  · rfl

def Rows (C B z o p R : M.Carrier .set) : Prop := MapsTo C B R ∧ ∀ a b,
  PureKuratowski.PairMember M a b R ↔ (Project.FirstOrderSemantics.reduct M).mem a C ∧ Value z o p a b

def rows {m : Nat} (C B z o p R : Fin m) : Project.Formula 1 m := .conj
  (ProjectSyntax.encode id (Source.SetLanguage.mapsTo R C B))
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge R.succ.succ 1 0))
    (.conj (.mem (.bound 1) (.bound C.succ.succ)) (value z.succ.succ o.succ.succ p.succ.succ 1 0)))))

theorem rows_freeClosed {m : Nat} (C B z o p R : Fin m) : (rows C B z o p R).FreeClosed := by
  simp -implicitDefEqProofs [rows,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,value_freeClosed]

theorem rows_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (C B z o p R : Fin m) :
    Project.Formula.satisfies env (rows C B z o p R) ↔ Rows (env.bound C) (env.bound B) (env.bound z) (env.bound o) (env.bound p) (env.bound R) := by
  simp only [rows,Rows,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,value_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingSupportSize.mapsTo_semantics (M := M)]
  rfl

theorem exists_rows (hM : FirstOrder.Theory.Models M nativeZF) {C B z o p : M.Carrier .set}
    (hzB : (Project.FirstOrderSemantics.reduct M).mem z B)
    (hoB : (Project.FirstOrderSemantics.reduct M).mem o B) : ∃ R, Rows C B z o p R := by
  let schema : Project.BinarySchema 3 := { body := value 2 3 4 1 0, freeClosed := value_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases z (Fin.cases o (fun _ => p)), free := fun _ => p }
  have he a b : schema.denote env a b ↔ Value z o p a b := value_semantics hM ((env.push a).push b) 2 3 4 1 0
  obtain ⟨R,hR,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := C) (target := B) (by
      intro a _
      classical
      by_cases h : PureKuratowski.PairMember M a o p
      · exact ⟨o,(he a o).mpr (Or.inl ⟨h,rfl⟩)⟩
      · exact ⟨z,(he a z).mpr (Or.inr ⟨h,rfl⟩)⟩)
    (fun a _ b c hb hc => value_unique ((he a b).mp hb) ((he a c).mp hc)) (by
      intro a b _ hb
      rcases (he a b).mp hb with ⟨_,rfl⟩ | ⟨_,rfl⟩
      · exact hoB
      · exact hzB)
  exact ⟨R,(ForcingSupportSize.native_mapsTo hM C B R).mpr hR,
    fun a b => (hEdge a b).trans (and_congr Iff.rfl (he a b))⟩

theorem value_of_mem (hM : FirstOrder.Theory.Models M nativeZF) {z o B p a b : M.Carrier .set}
    (hz : ForcingWithTopCarrier.Empty z)
    (ho : (Project.FirstOrderSemantics.reduct M).SuccessorOf o z)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B o)
    (hp : Functional p) (hbB : (Project.FirstOrderSemantics.reduct M).mem b B)
    (hab : PureKuratowski.PairMember M a b p) : Value z o p a b := by
  rcases ForcingCohenFlip.two_cases hM hz ho hB hbB with h | h
  · subst b
    refine Or.inr ⟨?_,rfl⟩
    intro hao
    have e := hp a z o hab hao
    cases e
    exact hz z ho.predecessor_mem
  · subst b
    exact Or.inl ⟨hab,rfl⟩

theorem rows_of_mem (hM : FirstOrder.Theory.Models M nativeZF) {C B z o p R a b : M.Carrier .set}
    (hz : ForcingWithTopCarrier.Empty z)
    (ho : (Project.FirstOrderSemantics.reduct M).SuccessorOf o z)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B o)
    (hp : Functional p) (hR : Rows C B z o p R)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a C) (hb : (Project.FirstOrderSemantics.reduct M).mem b B)
    (hab : PureKuratowski.PairMember M a b p) : PureKuratowski.PairMember M a b R :=
  (hR.2 a b).mpr ⟨ha,value_of_mem hM hz ho hB hp hb hab⟩

theorem rows_eq_of_le (hM : FirstOrder.Theory.Models M nativeZF) {C B z o p q R T a b c : M.Carrier .set}
    (hz : ForcingWithTopCarrier.Empty z)
    (ho : (Project.FirstOrderSemantics.reduct M).SuccessorOf o z)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B o)
    (hp : Functional p) (hq : Functional q)
    (hle : (Project.FirstOrderSemantics.reduct M).MemberSubset p q)
    (hR : Rows C B z o p R) (hT : Rows C B z o q T)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a C)
    (hd : ∃ v, (Project.FirstOrderSemantics.reduct M).mem v B ∧ PureKuratowski.PairMember M a v p)
    (hab : PureKuratowski.PairMember M a b R) (hac : PureKuratowski.PairMember M a c T) : b = c := by
  obtain ⟨v,hv,hav⟩ := hd
  have haq : PureKuratowski.PairMember M a v q := by
    obtain ⟨t,ht,htp⟩ := hav
    exact ⟨t,ht,hle t htp⟩
  exact (ForcingConditionGraphs.function_unique hR.1.1 hab (rows_of_mem hM hz ho hB hp hR ha hv hav)).trans
    (ForcingConditionGraphs.function_unique hT.1.1 hac (rows_of_mem hM hz ho hB hq hT ha hv haq)).symm

theorem construction (hM : FirstOrder.Theory.Models M nativeZF) {C B S w z o p : M.Carrier .set}
    (hz : ForcingWithTopCarrier.Empty z)
    (ho : (Project.FirstOrderSemantics.reduct M).SuccessorOf o z)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B o)
    (hS : Cartesian C B S) (hp : Condition S w p) :
    ∃ R, Rows C B z o p R ∧ (Project.FirstOrderSemantics.reduct M).MemberSubset p R := by
  obtain ⟨R,hR⟩ := exists_rows (C := C) (p := p) hM ((hB z).mpr (Or.inl ho.predecessor_mem)) hB.predecessor_mem
  refine ⟨R,hR,?_⟩
  intro t ht
  obtain ⟨a,ha,b,hb,htab⟩ := (hS t).mp (hp.1 t ht)
  obtain ⟨v,hv,hvR⟩ := rows_of_mem hM hz ho hB hp.2.1 hR ha hb ⟨t,htab,ht⟩
  exact KuratowskiZF.code_unique hM hv htab ▸ hvR

def constructionSentence {m : Nat} (C B S w z o p : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isEmpty (.bound z))
    (.imp (Project.Formula.isSuccessor (.bound o) (.bound z))
      (.imp (Project.Formula.isSuccessor (.bound B) (.bound o))
        (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian C B S))
          (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S w p))
            (.existsE (.conj (rows C.succ B.succ z.succ o.succ p.succ 0)
              (Project.Formula.subset (.bound p.succ) (.bound 0)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isEmpty,Project.Formula.isSuccessor,
      Project.Formula.extensionalEq,Project.Formula.subset,ProjectSyntax.freeClosed,rows_freeClosed]

theorem construction_models {m : Nat} (C B S w z o p : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence C B S w z o p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence C B S w z o p)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_isSuccessor_iff,Project.Formula.satisfies_subset_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M),rows_semantics hM]
  exact construction hM

theorem construction_kernel_certificate {m : Nat} (C B S w z o p : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence C B S w z o p)) :=
  ModelTransfer.derives (fun _ hM => construction_models C B S w z o p hM)

end PPAC.Migration.ConstructionCohenRows
