/- Pinned DirectLimits.cardinal_le:335. Reuse donor internal small-family
union bound, existing infinite-product bound and arbitrary quotient bound.
Source object Choice is explicit ONLY in the conditional cardinal conclusion. -/
import PPAC.Migration.ExistingSmallUnion
import PPAC.Migration.ConstructionDirectedLimitCarrier

namespace PPAC.Migration.ConstructionDirectedCardinality
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingConditionGraphs (FunctionOn)
open ForcingSupportSize (MapsTo Small)
open ConstructionDirectedLimitCarrier (Representatives Carrier Projection)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Choice : Prop := ∀ A,
  ((∀ a, (Project.FirstOrderSemantics.reduct M).mem a A → ∃ x, (Project.FirstOrderSemantics.reduct M).mem x a) ∧
    (∀ a, (Project.FirstOrderSemantics.reduct M).mem a A → ∀ b, (Project.FirstOrderSemantics.reduct M).mem b A →
      a ≠ b → ¬ ∃ x, (Project.FirstOrderSemantics.reduct M).mem x a ∧ (Project.FirstOrderSemantics.reduct M).mem x b)) →
  ∃ C, ∀ a, (Project.FirstOrderSemantics.reduct M).mem a A → ∃ x,
    ((Project.FirstOrderSemantics.reduct M).mem x C ∧ (Project.FirstOrderSemantics.reduct M).mem x a) ∧
    ∀ y, ((Project.FirstOrderSemantics.reduct M).mem y C ∧ (Project.FirstOrderSemantics.reduct M).mem y a) → y = x

def choice {m : Nat} : Project.Formula 1 m := Axioms.choice.formula.rename Fin.elim0

theorem choice_freeClosed {m : Nat} : (choice (m := m)).FreeClosed := by
  exact (Definitional.Formula.freeClosed_rename Fin.elim0 Axioms.choice.formula).mpr Axioms.choice.freeClosed

theorem choice_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) :
    Project.Formula.satisfies env (choice (m := m)) ↔ Choice (M := M) := by
  simp only [choice,Project.Formula.satisfies_rename,Axioms.choice,Project.Sentence.ofFormula,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forallMem_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.extensionalNe,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Definitional.Term.eval_newest,Definitional.Term.eval_weaken]
  rfl

theorem models_zfc (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : Choice (M := M)) :
    (Project.FirstOrderSemantics.reduct M).Models SetTheory.ZFC := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  refine ⟨hZF.1,?_⟩
  intro sentence hs
  cases hs with
  | zf hs => exact hZF.2 sentence hs
  | choice =>
    apply (Structure.satisfiesSentence_iff _ Axioms.choice).mpr
    intro free
    simp only [Axioms.choice,Project.Sentence.ofFormula,Project.Formula.satisfies_forall_iff,
      Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_forallMem_iff,
      Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
      Project.Formula.extensionalNe,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,
      Project.Formula.satisfies_extensionalEq_iff_eq hZF.1,Definitional.Term.eval_newest,Definitional.Term.eval_weaken]
    exact hChoice

def StageSmall (J Domains mu : M.Carrier .set) : Prop := ∀ i D,
  (Project.FirstOrderSemantics.reduct M).mem i J → PureKuratowski.PairMember M i D Domains → Small D mu

def Bound (hM : FirstOrder.Theory.Models M nativeZF) (J Domains L : M.Carrier .set) : Prop :=
  Choice (M := M) → ∀ w mu, (Project.FirstOrderSemantics.reduct M).IsOmega w →
    (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu →
    Small J mu → StageSmall J Domains mu → Small L mu

theorem carrier_bound (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : Choice (M := M)) {w mu J Domains C : M.Carrier .set}
    (hFn : FunctionOn J Domains) (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hJ : Small J mu) (hSmall : StageSmall J Domains mu) (hC : Representatives J Domains C) : Small C mu := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨T,hT⟩ := ForcingMapConditions.coordinate_bound hM Domains
  have hMapsT : MapsTo J T Domains := ⟨hFn,fun x y hxy => (hT x y hxy).2⟩
  have hDomNative := (ForcingSupportSize.native_mapsTo hM J T Domains).mp hMapsT
  obtain ⟨A,hA⟩ := ZF.exists_range_of_setFunction hZF I hDomNative.1 hDomNative.2.1
  have hMapsA : MapsTo J A Domains := ⟨hFn,fun x y hxy => (hA y).mpr ⟨x,hxy⟩⟩
  have hASmall := ConstructionProbeCardinality.indexed_quotient_bound hM hmu.1.1 hJ hMapsA (by
    intro D hDA
    obtain ⟨i,hiD⟩ := (hA D).mp hDA
    exact ⟨i,ForcingConditionGraphs.function_input hFn hiD,hiD⟩)
  obtain ⟨U,hU⟩ := KP.exists_union (ZF.modelsKP hZF) A
  obtain ⟨Square,hSquare⟩ := ZF.exists_cartesianProduct hZF I mu mu
  obtain ⟨fU,hfU⟩ := ExistingSmallUnion.union_bound_l I (models_zfc hM hChoice)
    ((ForcingSupportSize.native_small hM A mu).mp hASmall) hU (by
      intro D hDA
      obtain ⟨i,hiD⟩ := (hA D).mp hDA
      exact (ForcingSupportSize.native_small hM D mu).mp (hSmall i D (ForcingConditionGraphs.function_input hFn hiD) hiD)) hSquare
  obtain ⟨Id,hId⟩ := ZF.exists_identityBijection hZF I mu
  obtain ⟨fS,hfS⟩ := ExistingCardinalBounds.infinite_product_l I hZF hw hmu ⟨Id,hId.1⟩ ⟨Id,hId.1⟩ hSquare
  have hUSmall := ZF.exists_compositionInjection hZF I hfU hfS
  obtain ⟨P,hP⟩ := ZF.exists_cartesianProduct hZF I J U
  have hPSmall := ExistingCardinalBounds.infinite_product_l I hZF hw hmu
    ((ForcingSupportSize.native_small hM J mu).mp hJ) hUSmall hP
  apply ForcingSupportSize.small_subset hM (B := P) ?_ ((ForcingSupportSize.native_small hM P mu).mpr hPSmall)
  intro p hp
  obtain ⟨i,x,⟨hi,D,hiD,hxD⟩,hcode⟩ := (hC p).mp hp
  exact (hP p).mpr ⟨i,hi,x,(hU x).mpr ⟨D,(hA D).mpr ⟨i,hiD⟩,hxD⟩,hcode⟩

/-- Source cardinal_le requires neither transition injections/conservativity,
nor algebra, weights, or nonempty index. Choice is only its source background. -/
theorem bound (hM : FirstOrder.Theory.Models M nativeZF)
    {J E Domains F C L projection : M.Carrier .set} (hFn : FunctionOn J Domains)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hProjection : Projection J E Domains F C projection) :
    Bound hM J Domains L := by
  intro hChoice w mu hw hmu hJ hSmall
  exact ConstructionProbeCardinality.indexed_quotient_bound hM hmu.1.1
    (carrier_bound hM hChoice hFn hw hmu hJ hSmall hC) hp
    (fun _ hc => ConstructionDirectedLimitCarrier.projection_onto hL hProjection hc)


def stageSmall {m : Nat} (J Domains mu : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (.mem (.bound (1 : Fin (m+2))) (.bound J.succ.succ)) (.imp (ProjectSyntax.encode
  id (Source.SetLanguage.edge Domains.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)))) (ProjectSyntax.encode id
  (ForcingSupportSize.small (0 : Fin (m+2)) mu.succ.succ))))))

theorem stageSmall_freeClosed {m : Nat} (J Domains mu : Fin m) :
    (stageSmall J Domains mu).FreeClosed := by
  simp -implicitDefEqProofs [stageSmall,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem stageSmall_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains mu : Fin m) :
    Project.Formula.satisfies env (stageSmall J Domains mu) ↔ StageSmall (env.bound J) (env.bound Domains) (env.bound mu) := by
  simp only [stageSmall,StageSmall,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingSupportSize.small_semantics (M := M)]
  rfl


def boundProperty {m : Nat} (J Domains L : Fin m) : Project.Formula 1 m :=
  (.imp (choice ) (.forallE (.forallE (.imp (Project.Formula.isOmega (.bound (1 : Fin (m+2)))) (.imp
  (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound (1 : Fin (m+2))) (.bound (0 :
  Fin (m+2)))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small J.succ.succ (0 : Fin (m+2)))) (.imp
  (stageSmall J.succ.succ Domains.succ.succ (0 : Fin (m+2))) (ProjectSyntax.encode id
  (ForcingSupportSize.small L.succ.succ (0 : Fin (m+2)))))))))))

theorem boundProperty_freeClosed {m : Nat} (J Domains L : Fin m) :
    (boundProperty J Domains L).FreeClosed := by
  simp -implicitDefEqProofs [boundProperty,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,choice_freeClosed,stageSmall_freeClosed]

theorem boundProperty_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains L : Fin m) :
    Project.Formula.satisfies env (boundProperty J Domains L) ↔ Bound hM (env.bound J) (env.bound Domains) (env.bound L) := by
  simp only [boundProperty,Bound,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),choice_semantics hM,stageSmall_semantics hM,ForcingSupportSize.small_semantics (M := M),Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM)]
  rfl

def boundSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 7
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn (2 : Fin 7) (0 : Fin 7))) (.imp
    (ConstructionDirectedLimitCarrier.representatives (0 : Fin 7) (2 : Fin 7) (4 : Fin 7)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (6 : Fin 7) (4 : Fin 7) (5 : Fin 7))) (.imp
    (ConstructionDirectedLimitCarrier.carrier (0 : Fin 7) (1 : Fin 7) (2 : Fin 7) (3 : Fin 7) (4 : Fin 7) (5
    : Fin 7)) (.imp (ConstructionDirectedLimitCarrier.projectionGraph (0 : Fin 7) (1 : Fin 7) (2 : Fin 7) (3
    : Fin 7) (4 : Fin 7) (6 : Fin 7)) (boundProperty (0 : Fin 7) (2 : Fin 7) (5 : Fin 7)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionDirectedLimitCarrier.representatives_freeClosed,ConstructionDirectedLimitCarrier.carrier_freeClosed,
      ConstructionDirectedLimitCarrier.projectionGraph_freeClosed,boundProperty_freeClosed]

theorem bound_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence boundSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) boundSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro b
  simp only [Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.functionOn_semantics,ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionDirectedLimitCarrier.representatives_semantics hM,ConstructionDirectedLimitCarrier.carrier_semantics hM,
    ConstructionDirectedLimitCarrier.projectionGraph_semantics hM,boundProperty_semantics hM]
  exact fun hFn hC hp hL hP => bound hM hFn hC hp hL hP

theorem bound_kernel_certificate : FirstOrder.Derives nativeZF [] (Project.fo_sentence boundSentence) :=
  ModelTransfer.derives (fun _ hM => bound_models hM)

end PPAC.Migration.ConstructionDirectedCardinality
