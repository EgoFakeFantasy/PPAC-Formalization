/- Pinned Algebra/PlacementExtensions.countable_obstructions/exists_fresh_member,
consumed by Construction/DiagramPlacements.witness_placement:129.
Rows are INTERNAL set relations; disjointness is between distinct internal
indices. Reuse Separation and the existing ground-choice uniformization.
The budget is arbitrary; internal omega gives the source countable case. -/
import PPAC.Migration.ConstructionConcreteBase

namespace PPAC.Migration.ConstructionPlacementFreshness
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (Small)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def DisjointRows (K R : M.Carrier .set) : Prop :=
  ∀ i j x, (Project.FirstOrderSemantics.reduct M).mem i K →
    (Project.FirstOrderSemantics.reduct M).mem j K →
    PureKuratowski.PairMember M i x R → PureKuratowski.PairMember M j x R → i = j

def Obstructions (K R C A : M.Carrier .set) : Prop :=
  ∀ i, (Project.FirstOrderSemantics.reduct M).mem i A ↔
    (Project.FirstOrderSemantics.reduct M).mem i K ∧
      ∃ x, (Project.FirstOrderSemantics.reduct M).mem x C ∧ PureKuratowski.PairMember M i x R

def Fresh (K R C i : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem i K ∧
    ∀ x, (Project.FirstOrderSemantics.reduct M).mem x C → ¬ PureKuratowski.PairMember M i x R

theorem exists_obstructions (hM : FirstOrder.Theory.Models M nativeZF)
    (K R C : M.Carrier .set) : ∃ A, Obstructions K R C A := by
  let schema : Project.UnarySchema 2 := {
    body := .existsE (.conj (.mem (.bound 0) (.bound 2))
      (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) (.bound 0) (.bound 3))) }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 :=
    { bound := Fin.cases C (fun _ => R), free := fun _ => K }
  obtain ⟨A,hA⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env K
  refine ⟨A,fun i => ?_⟩
  simpa only [schema,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_orderedPairMem_iff
      (KuratowskiZF.interpretation hM)] using! hA i

/-- A disjoint row family has at most as many obstructed rows as coordinates
in C. The chosen witnesses form an actual internal injection into C. -/
theorem obstructions_small (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {K R C A bound : M.Carrier .set} (hRows : DisjointRows K R)
    (hA : Obstructions K R C A) (hC : Small C bound) : Small A bound := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨F,hF,hSelect⟩ := ExistingSmallUnion.uniformize_l I
    (ConstructionDirectedCardinality.models_zfc hM hChoice)
    (X := A) (Y := C) (R := R) (fun i hi => ((hA i).mp hi).2)
  have hInjective : (Project.FirstOrderSemantics.reduct M).IsSetInjectionFromTo I F A C := by
    refine ⟨hF,fun i j x hix hjx => ?_⟩
    exact hRows i j x ((hA i).mp (hF.input_mem_of_pairMember hix)).1
      ((hA j).mp (hF.input_mem_of_pairMember hjx)).1 (hSelect i x hix) (hSelect j x hjx)
  obtain ⟨G,hG⟩ := (ForcingSupportSize.native_small hM C bound).mp hC
  exact (ForcingSupportSize.native_small hM A bound).mpr
    (ZF.exists_compositionInjection hZF I hInjective hG)

theorem exists_fresh (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {K R C bound : M.Carrier .set} (hRows : DisjointRows K R)
    (hC : Small C bound) (hK : ¬ Small K bound) : ∃ i, Fresh K R C i := by
  obtain ⟨A,hA⟩ := exists_obstructions hM K R C
  have hSmall := obstructions_small hM hChoice hRows hA hC
  apply Classical.byContradiction
  intro hn
  have hSub : (Project.FirstOrderSemantics.reduct M).MemberSubset K A := by
    intro i hi
    apply (hA i).mpr
    refine ⟨hi,?_⟩
    apply Classical.byContradiction
    intro hNo
    exact hn ⟨i,hi,fun x hx hix => hNo ⟨x,hx,hix⟩⟩
  exact hK (ForcingSupportSize.small_subset hM hSub hSmall)

/-- The original set-valued family, with every value a subset of I. -/
def Family (K I F : M.Carrier .set) : Prop :=
  ForcingConditionGraphs.FunctionOn K F ∧
    ∀ i S, PureKuratowski.PairMember M i S F →
      (Project.FirstOrderSemantics.reduct M).MemberSubset S I

def FamilyDisjoint (K F : M.Carrier .set) : Prop :=
  ∀ i j S T x, (Project.FirstOrderSemantics.reduct M).mem i K →
    (Project.FirstOrderSemantics.reduct M).mem j K →
    PureKuratowski.PairMember M i S F → PureKuratowski.PairMember M j T F →
    (Project.FirstOrderSemantics.reduct M).mem x S →
    (Project.FirstOrderSemantics.reduct M).mem x T → i = j

def FamilyRows (K I F R : M.Carrier .set) : Prop :=
  ∀ i x, PureKuratowski.PairMember M i x R ↔
    (Project.FirstOrderSemantics.reduct M).mem i K ∧
      (Project.FirstOrderSemantics.reduct M).mem x I ∧
        ∃ S, PureKuratowski.PairMember M i S F ∧ (Project.FirstOrderSemantics.reduct M).mem x S

def FreshMember (K F C i : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem i K ∧
    ∀ S x, PureKuratowski.PairMember M i S F →
      (Project.FirstOrderSemantics.reduct M).mem x S → ¬ (Project.FirstOrderSemantics.reduct M).mem x C

theorem exists_family_rows (hM : FirstOrder.Theory.Models M nativeZF)
    (K I F : M.Carrier .set) : ∃ R, FamilyRows K I F R := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  obtain ⟨P,hP⟩ := KP.exists_pair (ZF.modelsKP hZF) K I
  obtain ⟨W,hW⟩ := KP.exists_union (ZF.modelsKP hZF) P
  have hK i (hi : (Project.FirstOrderSemantics.reduct M).mem i K) :
      (Project.FirstOrderSemantics.reduct M).mem i W :=
    (hW i).mpr ⟨K,(hP K).mpr (Or.inl rfl),hi⟩
  have hI x (hx : (Project.FirstOrderSemantics.reduct M).mem x I) :
      (Project.FirstOrderSemantics.reduct M).mem x W :=
    (hW x).mpr ⟨I,(hP I).mpr (Or.inr rfl),hx⟩
  let schema : Project.BinarySchema 3 := {
    body := .conj (.mem (.bound 1) (.bound 2)) (.conj (.mem (.bound 0) (.bound 3))
      (.existsE (.conj (Project.Formula.orderedPairMem PureKuratowskiProject.convention
        (.bound 2) (.bound 0) (.bound 5)) (.mem (.bound 1) (.bound 0))))) }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 :=
    { bound := Fin.cases K (Fin.cases I (fun _ => F)), free := fun _ => K }
  have hSchema i x : schema.denote env i x ↔
      (Project.FirstOrderSemantics.reduct M).mem i K ∧
        (Project.FirstOrderSemantics.reduct M).mem x I ∧
          ∃ S, PureKuratowski.PairMember M i S F ∧ (Project.FirstOrderSemantics.reduct M).mem x S := by
    simp only [Project.BinarySchema.denote,schema,Project.Formula.satisfies_conj_iff,
      Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_mem_iff,
      Project.Formula.satisfies_orderedPairMem_iff pair]
    rfl
  obtain ⟨R,_,hR⟩ := ZF.exists_setRelationOn_of_denote hZF pair schema env W
  refine ⟨R,fun i x => ?_⟩
  constructor
  · intro hix
    exact (hSchema i x).mp ((hR i x).mp hix).2.2
  · intro hix
    exact (hR i x).mpr ⟨hK i hix.1,hI x hix.2.1,(hSchema i x).mpr hix⟩

theorem family_rows_disjoint {K I F R : M.Carrier .set}
    (hR : FamilyRows K I F R) (hDisjoint : FamilyDisjoint K F) : DisjointRows K R := by
  intro i j x hi hj hix hjx
  obtain ⟨_,_,S,hiS,hxS⟩ := (hR i x).mp hix
  obtain ⟨_,_,T,hjT,hxT⟩ := (hR j x).mp hjx
  exact hDisjoint i j S T x hi hj hiS hjT hxS hxT

theorem fresh_member_of_rows {K I F R C i : M.Carrier .set}
    (hF : Family K I F) (hR : FamilyRows K I F R) (hi : Fresh K R C i) : FreshMember K F C i := by
  refine ⟨hi.1,fun S x hiS hxS hxC => ?_⟩
  exact hi.2 x hxC ((hR i x).mpr ⟨hi.1,hF.2 i S hiS x hxS,S,hiS,hxS⟩)

theorem exists_fresh_member (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {K I F C bound : M.Carrier .set} (hF : Family K I F) (hDisjoint : FamilyDisjoint K F)
    (hC : Small C bound) (hK : ¬ Small K bound) : ∃ i, FreshMember K F C i := by
  obtain ⟨R,hR⟩ := exists_family_rows hM K I F
  obtain ⟨i,hi⟩ := exists_fresh hM hChoice (family_rows_disjoint hR hDisjoint) hC hK
  exact ⟨i,fresh_member_of_rows hF hR hi⟩

def disjointRows {m : Nat} (K R : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.imp (.mem (.bound 2) (.bound K.succ.succ.succ))
    (.imp (.mem (.bound 1) (.bound K.succ.succ.succ))
      (.imp (Project.Formula.orderedPairMem PureKuratowskiProject.convention
        (.bound 2) (.bound 0) (.bound R.succ.succ.succ))
        (.imp (Project.Formula.orderedPairMem PureKuratowskiProject.convention
          (.bound 1) (.bound 0) (.bound R.succ.succ.succ))
          (Project.Formula.extensionalEq (.bound 2) (.bound 1))))))))

theorem disjointRows_freeClosed {m : Nat} (K R : Fin m) : (disjointRows K R).FreeClosed := by
  simp -implicitDefEqProofs [disjointRows,Definitional.Formula.FreeClosed,
    Project.Formula.orderedPairMem_freeClosed,Project.Formula.extensionalEq]

theorem disjointRows_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (K R : Fin m) :
    Project.Formula.satisfies env (disjointRows K R) ↔ DisjointRows (env.bound K) (env.bound R) := by
  simp only [disjointRows,DisjointRows,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  rfl

def obstructions {m : Nat} (K R C A : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound A.succ))
    (.conj (.mem (.bound 0) (.bound K.succ))
      (.existsE (.conj (.mem (.bound 0) (.bound C.succ.succ))
        (Project.Formula.orderedPairMem PureKuratowskiProject.convention
          (.bound 1) (.bound 0) (.bound R.succ.succ))))))

theorem obstructions_freeClosed {m : Nat} (K R C A : Fin m) :
    (obstructions K R C A).FreeClosed := by
  simp -implicitDefEqProofs [obstructions,Definitional.Formula.FreeClosed,
    Project.Formula.orderedPairMem_freeClosed]

theorem obstructions_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (K R C A : Fin m) :
    Project.Formula.satisfies env (obstructions K R C A) ↔
      Obstructions (env.bound K) (env.bound R) (env.bound C) (env.bound A) := by
  simp only [obstructions,Obstructions,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound]
  rfl

def fresh {m : Nat} (K R C i : Fin m) : Project.Formula 1 m :=
  .conj (.mem (.bound i) (.bound K))
    (.forallE (.imp (.mem (.bound 0) (.bound C.succ))
      (.neg (Project.Formula.orderedPairMem PureKuratowskiProject.convention
        (.bound i.succ) (.bound 0) (.bound R.succ)))))

theorem fresh_freeClosed {m : Nat} (K R C i : Fin m) : (fresh K R C i).FreeClosed := by
  simp -implicitDefEqProofs [fresh,Definitional.Formula.FreeClosed,
    Project.Formula.orderedPairMem_freeClosed]

theorem fresh_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (K R C i : Fin m) :
    Project.Formula.satisfies env (fresh K R C i) ↔
      Fresh (env.bound K) (env.bound R) (env.bound C) (env.bound i) := by
  simp only [fresh,Fresh,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 4
    (.imp (disjointRows 0 1)
      (.imp (ProjectSyntax.encode id (ForcingSupportSize.small 2 3))
        (.imp (.neg (ProjectSyntax.encode id (ForcingSupportSize.small 0 3)))
          (.existsE (.conj (obstructions (0 : Fin 4).succ (1 : Fin 4).succ (2 : Fin 4).succ 0)
            (.conj (ProjectSyntax.encode id (ForcingSupportSize.small (0 : Fin 5) (3 : Fin 4).succ))
              (.existsE (fresh (0 : Fin 4).succ.succ (1 : Fin 4).succ.succ (2 : Fin 4).succ.succ 0))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,disjointRows_freeClosed,
      obstructions_freeClosed,fresh_freeClosed,ProjectSyntax.freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    disjointRows_semantics hM,obstructions_semantics hM,fresh_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M)]
  intro hRows hC hK
  obtain ⟨A,hA⟩ := exists_obstructions hM (bound 0) (bound 1) (bound 2)
  exact ⟨A,hA,obstructions_small hM hChoice hRows hA hC,exists_fresh hM hChoice hRows hC hK⟩

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
    (ModelTransfer.extensionality hL) constructionSentence).mp (construction_models hL hChoice)

def family {m : Nat} (K I F : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn F K))
    (.forallE (.forallE (.imp
      (Project.Formula.orderedPairMem PureKuratowskiProject.convention
        (.bound 1) (.bound 0) (.bound F.succ.succ))
      (Project.Formula.subset (.bound 0) (.bound I.succ.succ)))))

theorem family_freeClosed {m : Nat} (K I F : Fin m) : (family K I F).FreeClosed := by
  simp -implicitDefEqProofs [family,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    Project.Formula.orderedPairMem_freeClosed,Project.Formula.subset]

theorem family_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (K I F : Fin m) :
    Project.Formula.satisfies env (family K I F) ↔ Family (env.bound K) (env.bound I) (env.bound F) := by
  simp only [family,Family,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_subset_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.functionOn_semantics (M := M),
    Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound]
  rfl

def familyDisjoint {m : Nat} (K F : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.forallE (.forallE
    (.imp (.mem (.bound 4) (.bound K.succ.succ.succ.succ.succ))
      (.imp (.mem (.bound 3) (.bound K.succ.succ.succ.succ.succ))
        (.imp (Project.Formula.orderedPairMem PureKuratowskiProject.convention
          (.bound 4) (.bound 2) (.bound F.succ.succ.succ.succ.succ))
          (.imp (Project.Formula.orderedPairMem PureKuratowskiProject.convention
            (.bound 3) (.bound 1) (.bound F.succ.succ.succ.succ.succ))
            (.imp (.mem (.bound 0) (.bound 2)) (.imp (.mem (.bound 0) (.bound 1))
              (Project.Formula.extensionalEq (.bound 4) (.bound 3))))))))))))

theorem familyDisjoint_freeClosed {m : Nat} (K F : Fin m) : (familyDisjoint K F).FreeClosed := by
  simp -implicitDefEqProofs [familyDisjoint,Definitional.Formula.FreeClosed,
    Project.Formula.orderedPairMem_freeClosed,Project.Formula.extensionalEq]

theorem familyDisjoint_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (K F : Fin m) :
    Project.Formula.satisfies env (familyDisjoint K F) ↔ FamilyDisjoint (env.bound K) (env.bound F) := by
  simp only [familyDisjoint,FamilyDisjoint,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  rfl

def freshMember {m : Nat} (K F C i : Fin m) : Project.Formula 1 m :=
  .conj (.mem (.bound i) (.bound K)) (.forallE (.forallE
    (.imp (Project.Formula.orderedPairMem PureKuratowskiProject.convention
      (.bound i.succ.succ) (.bound 1) (.bound F.succ.succ))
      (.imp (.mem (.bound 0) (.bound 1)) (.neg (.mem (.bound 0) (.bound C.succ.succ)))))))

theorem freshMember_freeClosed {m : Nat} (K F C i : Fin m) : (freshMember K F C i).FreeClosed := by
  simp -implicitDefEqProofs [freshMember,Definitional.Formula.FreeClosed,
    Project.Formula.orderedPairMem_freeClosed]

theorem freshMember_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (K F C i : Fin m) :
    Project.Formula.satisfies env (freshMember K F C i) ↔
      FreshMember (env.bound K) (env.bound F) (env.bound C) (env.bound i) := by
  simp only [freshMember,FreshMember,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound]
  rfl

def familySentence : Project.Sentence where
  formula := Project.Formula.forallClosure 5
    (.imp (family 0 1 2) (.imp (familyDisjoint 0 2)
      (.imp (ProjectSyntax.encode id (ForcingSupportSize.small 3 4))
        (.imp (.neg (ProjectSyntax.encode id (ForcingSupportSize.small 0 4)))
          (.existsE (freshMember (0 : Fin 5).succ (2 : Fin 5).succ (3 : Fin 5).succ 0))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,family_freeClosed,
      familyDisjoint_freeClosed,freshMember_freeClosed,ProjectSyntax.freeClosed]

theorem family_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence familySentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) familySentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_exists_iff,family_semantics hM,familyDisjoint_semantics hM,
    freshMember_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M)]
  exact fun hF hDisjoint hC hK => exists_fresh_member hM hChoice hF hDisjoint hC hK

theorem family_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative familySentence)) := by
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
  apply ConstructibleGround.relative_models hM familySentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) familySentence).mp (family_models hL hChoice)

end PPAC.Migration.ConstructionPlacementFreshness
