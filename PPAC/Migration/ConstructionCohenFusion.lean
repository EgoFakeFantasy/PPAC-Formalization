/- Pinned CohenForcing.Condition.countably_closed:111 and
GraphFusion.Condition.countable_fusion:235, consumed by StableSelectors.good_dense.
Reuse existing internal indexed choice, increasing chains and countable union.
Requirements form a set relation on the actual internal condition carrier. -/
import PPAC.Migration.ConstructionGermComplete
import PPAC.Migration.ExistingIndexedChoice
import PPAC.Companion.YesMetaZFC.SetTheory.CountableChain

namespace PPAC.Migration.ConstructionCohenFusion
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingCohenConditions (Condition)
open ForcingSupportSize (Small MapsTo)
open ForcingConditionGraphs (function_input function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Dense (S w A R base : M.Carrier .set) : Prop := ∀ a,
  (Project.FirstOrderSemantics.reduct M).mem a A → ∀ p, Condition S w p →
  (Project.FirstOrderSemantics.reduct M).MemberSubset base p → ∃ r, Condition S w r ∧
    (Project.FirstOrderSemantics.reduct M).MemberSubset p r ∧ PureKuratowski.PairMember M a r R

def Persistent (S w A R : M.Carrier .set) : Prop := ∀ a,
  (Project.FirstOrderSemantics.reduct M).mem a A → ∀ p r, Condition S w p → Condition S w r →
    (Project.FirstOrderSemantics.reduct M).MemberSubset p r →
      PureKuratowski.PairMember M a p R → PureKuratowski.PairMember M a r R

/-- Exact union of all internal stages, not just the externally standard ones. -/
theorem countably_closed (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {S w X f : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hf : MapsTo w X f) (hStates : ∀ p, (Project.FirstOrderSemantics.reduct M).mem p X → Condition S w p)
    (hInc : ∀ i j p q, (Project.FirstOrderSemantics.reduct M).mem i j →
      PureKuratowski.PairMember M i p f → PureKuratowski.PairMember M j q f →
        (Project.FirstOrderSemantics.reduct M).MemberSubset p q) :
    ∃ r, Condition S w r ∧ ∀ i p, PureKuratowski.PairMember M i p f →
      (Project.FirstOrderSemantics.reduct M).MemberSubset p r := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hZFC := ConstructionDirectedCardinality.models_zfc hM hChoice
  let P := KuratowskiZF.interpretation hM
  have hNative := (ForcingSupportSize.native_mapsTo hM w X f).mp hf
  obtain ⟨Y,hY⟩ := ZF.exists_range_of_setFunction hZF P hNative.1 hNative.2.1
  obtain ⟨r,hUnion⟩ := KP.exists_union (ZF.modelsKP hZF) Y
  have hFY : (Project.FirstOrderSemantics.reduct M).IsSetFunctionFromTo P f w Y :=
    ⟨hNative.1,hNative.2.1,fun i hi => by
      obtain ⟨p,_,hip⟩ := hNative.2.2 i hi
      exact ⟨p,(hY p).mpr ⟨i,hip⟩,hip⟩⟩
  have hYSmall := ZFC.surjection_bound_l P hZFC hFY (by
    intro p hp
    obtain ⟨i,hip⟩ := (hY p).mp hp
    exact ⟨i,function_input hf.1 hip,hip⟩)
  have hSmall := ZFC.countable_union_l P hZFC hw hYSmall hUnion (by
    intro p hp
    obtain ⟨i,hip⟩ := (hY p).mp hp
    exact (ForcingSupportSize.native_small hM p w).mp (hStates p (hf.2 i p hip)).2.2)
  have hSub i p (hip : PureKuratowski.PairMember M i p f) :
      (Project.FirstOrderSemantics.reduct M).MemberSubset p r :=
    fun z hz => (hUnion z).mpr ⟨p,(hY p).mpr ⟨i,hip⟩,hz⟩
  refine ⟨r,⟨?_,?_,(ForcingSupportSize.native_small hM r w).mpr hSmall⟩,hSub⟩
  · intro z hz
    obtain ⟨p,hp,hzp⟩ := (hUnion z).mp hz
    obtain ⟨i,hip⟩ := (hY p).mp hp
    exact (hStates p (hf.2 i p hip)).1 z hzp
  · intro a b c hab hac
    obtain ⟨z,hz,hzr⟩ := hab
    obtain ⟨t,ht,htr⟩ := hac
    obtain ⟨p,hp,hzp⟩ := (hUnion z).mp hzr
    obtain ⟨q,hq,htq⟩ := (hUnion t).mp htr
    obtain ⟨i,hip⟩ := (hY p).mp hp
    obtain ⟨j,hjq⟩ := (hY q).mp hq
    rcases ConstructionFractionOrder.nat_compare hM hw (function_input hf.1 hip) (function_input hf.1 hjq) with he | hij | hji
    · subst j
      have he := function_unique hf.1 hip hjq
      subst q
      exact (hStates p (hf.2 i p hip)).2.1 a b c ⟨z,hz,hzp⟩ ⟨t,ht,htq⟩
    · exact (hStates q (hf.2 j q hjq)).2.1 a b c ⟨z,hz,hInc i j p q hij hip hjq z hzp⟩ ⟨t,ht,htq⟩
    · exact (hStates p (hf.2 i p hip)).2.1 a b c ⟨z,hz,hzp⟩ ⟨t,ht,hInc j i q p hji hjq hip t htq⟩

theorem countable_fusion (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {S w A R base : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hSmall : Small A w) (hBase : Condition S w base)
    (hPersist : Persistent S w A R) (hDense : Dense S w A R base) :
    ∃ r, Condition S w r ∧ (Project.FirstOrderSemantics.reduct M).MemberSubset base r ∧
      ∀ a, (Project.FirstOrderSemantics.reduct M).mem a A → PureKuratowski.PairMember M a r R := by
  classical
  have hZF := ModelTransfer.project_models_iff.mp hM
  let P := KuratowskiZF.interpretation hM
  obtain ⟨index,hIndex⟩ := hSmall
  obtain ⟨all,hAll⟩ := ForcingCohenConditions.exists_carrier hM S w
  let above : Project.UnarySchema 1 := {
    body := Project.Formula.subset (.bound 1) (.bound 0)
    freeClosed := by simp [Definitional.Formula.FreeClosed,Project.Formula.subset] }
  let envBase : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 := { bound := fun _ => base, free := fun _ => base }
  have hAbove p : above.denote envBase p ↔ (Project.FirstOrderSemantics.reduct M).MemberSubset base p := by
    simp only [Project.UnarySchema.denote,above,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound]
    rfl
  obtain ⟨X,hX⟩ := ZF.separation_exists_d hZF above envBase all
  have hState p : (Project.FirstOrderSemantics.reduct M).mem p X ↔ Condition S w p ∧
      (Project.FirstOrderSemantics.reduct M).MemberSubset base p :=
    (hX p).trans (and_congr (hAll p) (hAbove p))
  let step : Project.UnarySchema 5 := {
    body := .conj (Project.Formula.subset (.bound 1) (.bound 0)) (.forallE
      (.imp (.mem (.bound 0) (.bound 4)) (.imp
        (ProjectSyntax.encode id (Source.SetLanguage.edge 5 0 3))
        (ProjectSyntax.encode id (Source.SetLanguage.edge 6 0 1)))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.subset,ProjectSyntax.freeClosed] }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases A (Fin.cases index (fun _ => R)), free := fun _ => base }
  have hStep i p r : step.denote ((env.push i).push p) r ↔
      (Project.FirstOrderSemantics.reduct M).MemberSubset p r ∧ ∀ a,
      (Project.FirstOrderSemantics.reduct M).mem a A → PureKuratowski.PairMember M a i index → PureKuratowski.PairMember M a r R := by
    simp only [Project.UnarySchema.denote,step,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_subset_iff,
      Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
      Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
    rfl
  obtain ⟨f,hf,hZero,hNext⟩ := ExistingIndexedChoice.indexed_choice_l P
    (ConstructionDirectedCardinality.models_zfc hM hChoice) step env hw
    ((hState base).mpr ⟨hBase,fun _ h => h⟩) (by
      intro i p _ hp
      obtain ⟨hpCond,hbp⟩ := (hState p).mp hp
      by_cases has : ∃ a, (Project.FirstOrderSemantics.reduct M).mem a A ∧ PureKuratowski.PairMember M a i index
      · obtain ⟨a,ha,hai⟩ := has
        obtain ⟨r,hr,hpr,haR⟩ := hDense a ha p hpCond hbp
        refine ⟨r,(hState r).mpr ⟨hr,fun z hz => hpr z (hbp z hz)⟩,(hStep i p r).mpr ⟨hpr,?_⟩⟩
        intro a' _ hai'
        have he := hIndex.2 a' a i hai' hai
        exact he.symm ▸ haR
      · exact ⟨p,hp,(hStep i p p).mpr ⟨fun _ h => h,fun a ha hai => False.elim (has ⟨a,ha,hai⟩)⟩⟩)
  have hInc := ZF.cc_increasing_of_successor_l P hZF hw hf
    (fun i j p q hij hip hjq => ((hStep i p q).mp (hNext i j p q hij hip hjq)).1)
  have hMaps := (ForcingSupportSize.native_mapsTo hM w X f).mpr hf
  obtain ⟨r,hr,hBelow⟩ := countably_closed hM hChoice hw hMaps (fun p hp => ((hState p).mp hp).1) hInc
  obtain ⟨zero,hzero,_⟩ := hw.1.1
  refine ⟨r,hr,hBelow zero base (hZero zero hzero),?_⟩
  intro a ha
  obtain ⟨i,hai,_⟩ := hIndex.1.1.2 a ha
  have hi := hIndex.1.2 a i hai
  obtain ⟨j,hji,hj⟩ := hw.1.2 i hi
  obtain ⟨p,hp,hip⟩ := hf.2.2 i hi
  obtain ⟨q,hq,hjq⟩ := hf.2.2 j hj
  have hReq := ((hStep i p q).mp (hNext i j p q hji hip hjq)).2 a ha hai
  exact hPersist a ha q r ((hState q).mp hq).1 hr (hBelow j q hjq) hReq

def dense {m : Nat} (S w A R base : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (.mem (.bound 0) (.bound A.succ)) (.forallE (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ.succ w.succ.succ 0)) (.imp (Project.Formula.subset (.bound base.succ.succ) (.bound 0)) (.existsE (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ.succ.succ w.succ.succ.succ 0)) (.conj (Project.Formula.subset (.bound 1) (.bound 0)) (ProjectSyntax.encode id (Source.SetLanguage.edge R.succ.succ.succ 2 0))))))))))

theorem dense_freeClosed {m : Nat} (S w A R base : Fin m) : (dense S w A R base).FreeClosed := by
  simp -implicitDefEqProofs [dense,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.subset]

theorem dense_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (S w A R base : Fin m) :
    Project.Formula.satisfies env (dense S w A R base) ↔
      Dense (env.bound S) (env.bound w) (env.bound A) (env.bound R) (env.bound base) := by
  simp only [dense,Dense,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingCohenConditions.condition_semantics (M := M)]
  rfl

def persistent {m : Nat} (S w A R : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (.mem (.bound 0) (.bound A.succ)) (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ.succ.succ w.succ.succ.succ 1)) (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ.succ.succ w.succ.succ.succ 0)) (.imp (Project.Formula.subset (.bound 1) (.bound 0)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge R.succ.succ.succ 2 1)) (ProjectSyntax.encode id (Source.SetLanguage.edge R.succ.succ.succ 2 0))))))))))

theorem persistent_freeClosed {m : Nat} (S w A R : Fin m) : (persistent S w A R).FreeClosed := by
  simp -implicitDefEqProofs [persistent,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.subset]

theorem persistent_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (S w A R : Fin m) :
    Project.Formula.satisfies env (persistent S w A R) ↔
      Persistent (env.bound S) (env.bound w) (env.bound A) (env.bound R) := by
  simp only [persistent,Persistent,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingCohenConditions.condition_semantics (M := M)]
  rfl

def constructionSentence {m : Nat} (S w A R base : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small A w)) (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S w base)) (.imp (persistent S w A R) (.imp (dense S w A R base) (.existsE (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ w.succ 0)) (.conj (Project.Formula.subset (.bound base.succ) (.bound 0)) (.forallE (.imp (.mem (.bound 0) (.bound A.succ.succ)) (ProjectSyntax.encode id (Source.SetLanguage.edge R.succ.succ 0 1))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega,
      Project.Formula.subset,dense_freeClosed,persistent_freeClosed]

theorem construction_models {m : Nat} (S w A R base : Fin m) (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence S w A R base)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence S w A R base)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingCohenConditions.condition_semantics (M := M),ForcingSupportSize.small_semantics (M := M),
    dense_semantics hM,persistent_semantics hM]
  exact countable_fusion hM hChoice

theorem construction_kernel_certificate {m : Nat} (S w A R base : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (constructionSentence S w A R base))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence S w A R base)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence S w A R base)).mp (construction_models S w A R base hL hChoice)


end PPAC.Migration.ConstructionCohenFusion
