/- Pinned CompleteRounds.RoundOrdinal.countable_bounded:496.
All subsets and maps are internal set codes, including internally countable
sets in nonstandard models. Reuse native bounded/cofinal dichotomy and the
membership wellorder type; no new cardinal, choice or recursion backend. -/
import PPAC.Migration.ConstructionSaturationIndex

namespace PPAC.Migration.ConstructionSaturationBoundedness
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (Small)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem countable_subset_bounded (hM : FirstOrder.Theory.Models M nativeZF)
    {w kappa A : M.Carrier .set}
    (hHartogs : ConstructionSaturationIndex.Hartogs hM w kappa)
    (hRegular : (Project.FirstOrderSemantics.reduct M).IsRegularCardinal (KuratowskiZF.interpretation hM) kappa)
    (hSmall : Small A w)
    (hSub : (Project.FirstOrderSemantics.reduct M).MemberSubset A kappa) :
    (Project.FirstOrderSemantics.reduct M).IsBoundedSubsetOfOrdinal A kappa := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  rcases Structure.bounded_or_cofinalSubset hZF hRegular.isLimitOrdinal hSub with hBounded | hCofinal
  · exact hBounded
  · apply False.elim
    obtain ⟨relation,orderType,hRelation,hOrder,hType⟩ :=
      ZF.exists_membershipWellOrderType_of_subsetOrdinal hZF I hHartogs.1 hSub
    have hOrdinal := hType.isOrdinal hZF I hOrder
    obtain ⟨toA,hToA⟩ := (hType.equinumerous hZF I hOrder).symm hZF I
    obtain ⟨toW,hToW⟩ := (ForcingSupportSize.native_small hM A w).mp hSmall
    obtain ⟨typeToW,hTypeToW⟩ := ZF.exists_compositionInjection hZF I hToA.1 hToW
    rcases hCofinal.cofinality_le_orderType hZF I hRelation hOrder hType hRegular with he | hlt
    · subst orderType
      exact hHartogs.not_cardinalLessOrEqual (ZF.modelsKP hZF) ⟨typeToW,hTypeToW⟩
    · obtain ⟨inclusion,hInclusion⟩ := ZF.exists_inclusionInjection hZF I (hOrdinal.transitive kappa hlt)
      exact hHartogs.not_cardinalLessOrEqual (ZF.modelsKP hZF)
        (ZF.exists_compositionInjection hZF I hInclusion hTypeToW)

theorem countable_range_bounded (hM : FirstOrder.Theory.Models M nativeZF)
    {w kappa A f range : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hHartogs : ConstructionSaturationIndex.Hartogs hM w kappa)
    (hRegular : (Project.FirstOrderSemantics.reduct M).IsRegularCardinal (KuratowskiZF.interpretation hM) kappa)
    (hSmall : Small A w)
    (hFunction : (Project.FirstOrderSemantics.reduct M).IsSetFunctionFromTo (KuratowskiZF.interpretation hM) f A kappa)
    (hRange : (Project.FirstOrderSemantics.reduct M).IsRangeOf (KuratowskiZF.interpretation hM) range f) :
    (Project.FirstOrderSemantics.reduct M).IsBoundedSubsetOfOrdinal range kappa := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  have hFunctionRange : (Project.FirstOrderSemantics.reduct M).IsSetFunctionFromTo I f A range := by
    refine ⟨hFunction.1,hFunction.2.1,?_⟩
    intro a ha
    obtain ⟨b,_,hab⟩ := hFunction.2.2 a ha
    exact ⟨b,(hRange b).mpr ⟨a,hab⟩,hab⟩
  have hSurjective : (Project.FirstOrderSemantics.reduct M).IsSetSurjectiveOnto I f A range := by
    intro b hb
    obtain ⟨a,hab⟩ := (hRange b).mp hb
    exact ⟨a,hFunction.input_mem_of_pairMember hab,hab⟩
  have hRangeSmall := ExistingOrdinalImage.ordinal_image_bound_l I hZF
    (ExistingCardinalBounds.omega_cardinal_l I hZF hw).1
    ((ForcingSupportSize.native_small hM A w).mp hSmall) hFunctionRange hSurjective
  apply countable_subset_bounded hM hHartogs hRegular
    ((ForcingSupportSize.native_small hM range w).mpr hRangeSmall)
  intro b hb
  obtain ⟨a,hab⟩ := (hRange b).mp hb
  exact hFunction.output_mem_of_pairMember hab


def bounded {m : Nat} (A kappa : Fin m) : Project.Formula 1 m :=
  Project.Formula.isBoundedSubsetOfOrdinal (.bound A) (.bound kappa)

theorem bounded_freeClosed {m : Nat} (A kappa : Fin m) : (bounded A kappa).FreeClosed := by
  simp -implicitDefEqProofs [bounded, Project.Formula.isBoundedSubsetOfOrdinal,
    Project.Formula.isOrdinalUpperBound_freeClosed, Project.Formula.isOrdinal_freeClosed,
    Project.Formula.subset, Project.Formula.existsMem, Definitional.Formula.FreeClosed]

theorem bounded_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (A kappa : Fin m) :
    Project.Formula.satisfies env (bounded A kappa) ↔
      (Project.FirstOrderSemantics.reduct M).IsBoundedSubsetOfOrdinal (env.bound A) (env.bound kappa) :=
  Project.Formula.satisfies_isBoundedSubsetOfOrdinal_iff (ModelTransfer.extensionality hM) env (.bound A) (.bound kappa)

def subsetSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 3
    (.imp (ConstructionSaturationIndex.hartogs 0 1)
      (.imp (ConstructionSaturationIndex.regular 1)
        (.imp (ProjectSyntax.encode id (ForcingSupportSize.small 2 0))
          (.imp (Project.Formula.subset (.bound 2) (.bound 1)) (bounded 2 1)))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed, ConstructionSaturationIndex.regular_freeClosed,
      ProjectSyntax.freeClosed, Project.Formula.subset, bounded_freeClosed]

theorem subset_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence subsetSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) subsetSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff, ConstructionSaturationIndex.hartogs_semantics hM,
    ConstructionSaturationIndex.regular_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M), Project.Formula.satisfies_subset_iff,
    Project.Term.eval_bound, bounded_semantics hM]
  exact fun hH hR hSmall hSub => countable_subset_bounded hM hH hR hSmall hSub

theorem subset_kernel_certificate : FirstOrder.Derives nativeZF [] (Project.fo_sentence subsetSentence) := by
  apply ModelTransfer.derives
  exact fun _ hM => subset_models hM


/-- The exact source consumer: an actual internal bound for every internal
function with countable domain. The range is constructed, never a premise. -/
theorem countable_bounded (hM : FirstOrder.Theory.Models M nativeZF)
    {w kappa A f : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hHartogs : ConstructionSaturationIndex.Hartogs hM w kappa)
    (hRegular : (Project.FirstOrderSemantics.reduct M).IsRegularCardinal (KuratowskiZF.interpretation hM) kappa)
    (hSmall : Small A w)
    (hFunction : (Project.FirstOrderSemantics.reduct M).IsSetFunctionFromTo (KuratowskiZF.interpretation hM) f A kappa) :
    ∃ j, (Project.FirstOrderSemantics.reduct M).mem j kappa ∧
      ∀ a b, (Project.FirstOrderSemantics.reduct M).PairMember (KuratowskiZF.interpretation hM) a b f →
        b = j ∨ (Project.FirstOrderSemantics.reduct M).mem b j := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨range,hRange⟩ := ZF.exists_range_of_setFunction hZF (KuratowskiZF.interpretation hM)
    hFunction.1 hFunction.2.1
  obtain ⟨j,hj,hBound⟩ := (countable_range_bounded hM hw hHartogs hRegular hSmall hFunction hRange).exists_bound
  exact ⟨j,hj,fun a b hab => hBound b ((hRange b).mpr ⟨a,hab⟩)⟩

def mapBound {m : Nat} (f kappa : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (.mem (.bound 0) (.bound kappa.succ))
    (.forallE (.forallE (.imp
      (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) (.bound 0) (.bound f.succ.succ.succ))
      (.disj (Project.Formula.extensionalEq (.bound 0) (.bound 2)) (.mem (.bound 0) (.bound 2)))))))

theorem mapBound_freeClosed {m : Nat} (f kappa : Fin m) : (mapBound f kappa).FreeClosed := by
  simp -implicitDefEqProofs [mapBound, Definitional.Formula.FreeClosed,
    Project.Formula.orderedPairMem_freeClosed, Project.Formula.extensionalEq]

theorem mapBound_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (f kappa : Fin m) :
    Project.Formula.satisfies env (mapBound f kappa) ↔
      ∃ j, (Project.FirstOrderSemantics.reduct M).mem j (env.bound kappa) ∧
        ∀ a b, (Project.FirstOrderSemantics.reduct M).PairMember (KuratowskiZF.interpretation hM) a b (env.bound f) →
          b = j ∨ (Project.FirstOrderSemantics.reduct M).mem b j := by
  simp only [mapBound, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),
    Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Project.Term.eval_bound]
  rfl

def countableSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 4
    (.imp (Project.Formula.isOmega (.bound 0))
      (.imp (ConstructionSaturationIndex.hartogs 0 1)
        (.imp (ConstructionSaturationIndex.regular 1)
          (.imp (ProjectSyntax.encode id (ForcingSupportSize.small 2 0))
            (.imp (Project.Formula.isFunctionFromTo PureKuratowskiProject.convention (.bound 3) (.bound 2) (.bound 1))
              (mapBound 3 1))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, Project.Formula.isOmega,
      ConstructionSaturationIndex.hartogs_freeClosed, ConstructionSaturationIndex.regular_freeClosed,
      ProjectSyntax.freeClosed, Project.Formula.isFunctionFromTo_freeClosed, mapBound_freeClosed]

theorem countable_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence countableSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) countableSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_isOmega_iff,
    ConstructionSaturationIndex.hartogs_semantics hM, ConstructionSaturationIndex.regular_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),
    Project.Formula.satisfies_isFunctionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Term.eval_bound, mapBound_semantics hM]
  exact fun hw hH hR hSmall hF => countable_bounded hM hw hH hR hSmall hF

theorem countable_kernel_certificate : FirstOrder.Derives nativeZF [] (Project.fo_sentence countableSentence) := by
  apply ModelTransfer.derives
  exact fun _ hM => countable_models hM


end PPAC.Migration.ConstructionSaturationBoundedness
