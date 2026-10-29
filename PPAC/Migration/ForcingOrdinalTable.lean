/- Pinned OrdinalCodes.OrderAssignment.Table/chooseTable/indices:548-560.
Actual consumer: GermSelectors.ordinalTable:33 and Preliminary:38-45.
The table is selected once as an INTERNAL set graph. No condition parameter.
Reuse existing internal function spaces and the retained donor uniformizer. -/
import PPAC.Migration.ForcingCodeLinkCovariance
import YesMetaZFC.SetTheory.FunctionSpaceConstruction

namespace PPAC.Migration.ForcingOrdinalTable
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Eligible (hM : FirstOrder.Theory.Models M nativeZF) (labels bound theta : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).IsOrdinal theta ∧
    (theta = bound ∨ (Project.FirstOrderSemantics.reduct M).mem theta bound) ∧
      (Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) labels theta

def eligible {k : Nat} (labels bound theta : Fin k) : Project.Formula 1 k :=
  .conj (Project.Formula.isOrdinal (.bound theta))
    (.conj (.disj (Project.Formula.extensionalEq (.bound theta) (.bound bound)) (.mem (.bound theta) (.bound bound)))
      (Project.Formula.equinumerous PureKuratowskiProject.convention (.bound labels) (.bound theta)))

theorem eligible_freeClosed {k : Nat} (labels bound theta : Fin k) : (eligible labels bound theta).FreeClosed := by
  simp -implicitDefEqProofs [eligible,Definitional.Formula.FreeClosed]

theorem eligible_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k) (labels bound theta : Fin k) :
    Project.Formula.satisfies env (eligible labels bound theta) ↔ Eligible hM (env.bound labels) (env.bound bound) (env.bound theta) := by
  simp only [eligible,Eligible,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_isOrdinal_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_equinumerous_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),Project.Term.eval_bound]

def Table (hM : FirstOrder.Theory.Models M nativeZF) (labels bound tab : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).IsSetFunction (KuratowskiZF.interpretation hM) tab ∧
    (∀ theta, (∃ f, PureKuratowski.PairMember M theta f tab) ↔ Eligible hM labels bound theta) ∧
    ∀ theta f, PureKuratowski.PairMember M theta f tab →
      (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) f labels theta

def table {k : Nat} (labels bound tab : Fin k) : Project.Formula 1 k :=
  .conj (Project.Formula.isFunction PureKuratowskiProject.convention (.bound tab))
    (.conj (.forallE (.iff (.existsE (ProjectSyntax.encode id (Source.SetLanguage.edge tab.succ.succ 1 0)))
      (eligible labels.succ bound.succ 0)))
    (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge tab.succ.succ 1 0))
      (Project.Formula.isBijectionFromTo PureKuratowskiProject.convention (.bound 0) (.bound labels.succ.succ) (.bound 1))))))

theorem table_freeClosed {k : Nat} (labels bound tab : Fin k) : (table labels bound tab).FreeClosed := by
  simp -implicitDefEqProofs [table,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,eligible_freeClosed]

theorem table_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k) (labels bound tab : Fin k) :
    Project.Formula.satisfies env (table labels bound tab) ↔ Table hM (env.bound labels) (env.bound bound) (env.bound tab) := by
  simp only [table,Table,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isFunction_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isBijectionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    eligible_semantics hM,Project.Term.eval_bound]
  rfl

theorem chooseTable (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) (labels bound : M.Carrier .set)
    (hBound : (Project.FirstOrderSemantics.reduct M).IsOrdinal bound) :
    ∃ tab, Table hM labels bound tab := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨successor,hSuccessor⟩ := KP.exists_insert (ZF.modelsKP hZF) bound bound
  let domainSchema : Project.UnarySchema 2 := {
    body := eligible 1 2 0
    freeClosed := eligible_freeClosed _ _ _ }
  let domainEnv : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases labels (fun _ => bound),free := fun _ => labels }
  have he theta : domainSchema.denote domainEnv theta ↔ Eligible hM labels bound theta :=
    eligible_semantics hM (domainEnv.push theta) 1 2 0
  obtain ⟨domain,hDomain⟩ := ZF.separation_exists_d hZF domainSchema domainEnv successor
  have hExact theta : (Project.FirstOrderSemantics.reduct M).mem theta domain ↔ Eligible hM labels bound theta := by
    rw [hDomain theta]
    change (_ ∧ domainSchema.denote domainEnv theta) ↔ _
    rw [he theta]
    exact ⟨And.right,fun h => ⟨(hSuccessor theta).mpr h.2.1.symm,h⟩⟩
  obtain ⟨space,hSpace⟩ := ZF.exists_functionSpace hZF (KuratowskiZF.interpretation hM) labels successor
  let choiceSchema : Project.BinarySchema 1 := {
    body := Project.Formula.isBijectionFromTo PureKuratowskiProject.convention (.bound 0) (.bound 2) (.bound 1)
    freeClosed := Project.Formula.isBijectionFromTo_freeClosed _ _ _ _ rfl rfl rfl }
  let choiceEnv : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 := {
    bound := fun _ => labels,free := fun _ => labels }
  have hc theta f : choiceSchema.denote choiceEnv theta f ↔
      (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) f labels theta :=
    Project.Formula.satisfies_isBijectionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM)
      ((choiceEnv.push theta).push f) (.bound 0) (.bound 2) (.bound 1)
  obtain ⟨tab,hTab,hChosen⟩ := ExistingSmallUnion.uniformize_formula_l (KuratowskiZF.interpretation hM)
    (ConstructionDirectedCardinality.models_zfc hM hChoice) choiceSchema choiceEnv (X := domain) (Y := space) (by
      intro theta hTheta
      have hEligible := (hExact theta).mp hTheta
      obtain ⟨f,hf⟩ := hEligible.2.2
      have hInto : (Project.FirstOrderSemantics.reduct M).MemberSubset theta successor := by
        intro beta hb
        apply (hSuccessor beta).mpr
        apply Or.inl
        rcases hEligible.2.1 with heq | hmem
        · exact heq ▸ hb
        · exact hBound.transitive theta hmem beta hb
      have hFunction : (Project.FirstOrderSemantics.reduct M).IsSetFunctionFromTo (KuratowskiZF.interpretation hM) f labels successor := by
        refine ⟨hf.1.1.1,hf.1.1.2.1,?_⟩
        intro j hj
        obtain ⟨beta,hb,hjb⟩ := hf.1.1.2.2 j hj
        exact ⟨beta,hInto beta hb,hjb⟩
      exact ⟨f,(hSpace f).mpr hFunction,(hc theta f).mpr hf⟩)
  exact ⟨tab,hTab.1,fun theta => (hTab.2.1 theta).symm.trans (hExact theta),
    fun theta f htf => (hc theta f).mp (hChosen theta f htf)⟩

/-- Ordinal initial-segment indices are the members of the internal von Neumann ordinal. -/
def Indices (tab theta label beta : M.Carrier .set) : Prop :=
  ∃ f, PureKuratowski.PairMember M theta f tab ∧ PureKuratowski.PairMember M label beta f

def indices {k : Nat} (tab theta label beta : Fin k) : Project.Formula 1 k :=
  .existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge tab.succ theta.succ 0))
    (ProjectSyntax.encode id (Source.SetLanguage.edge 0 label.succ beta.succ)))

theorem indices_freeClosed {k : Nat} (tab theta label beta : Fin k) : (indices tab theta label beta).FreeClosed := by
  simp [indices,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem indices_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k) (tab theta label beta : Fin k) :
    Project.Formula.satisfies env (indices tab theta label beta) ↔ Indices (M := M) (env.bound tab) (env.bound theta) (env.bound label) (env.bound beta) := by
  simp only [indices,Indices,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

theorem indices_bijection (hM : FirstOrder.Theory.Models M nativeZF) {labels bound tab theta : M.Carrier .set}
    (hTable : Table hM labels bound tab) (hTheta : Eligible hM labels bound theta) :
    ∃ f, (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) f labels theta ∧
      ∀ label beta, Indices tab theta label beta ↔ PureKuratowski.PairMember M label beta f := by
  obtain ⟨f,hf⟩ := (hTable.2.1 theta).mpr hTheta
  refine ⟨f,hTable.2.2 theta f hf,?_⟩
  intro label beta
  constructor
  · rintro ⟨g,hg,hgb⟩
    have hfg := hTable.1.2 theta g f hg hf
    exact hfg ▸ hgb
  · exact fun hb => ⟨f,hf,hb⟩

def indexBijection {k : Nat} (labels tab theta : Fin k) : Project.Formula 1 k :=
  .existsE (.conj (Project.Formula.isBijectionFromTo PureKuratowskiProject.convention (.bound 0) (.bound labels.succ) (.bound theta.succ))
    (.forallE (.forallE (.iff (indices tab.succ.succ.succ theta.succ.succ.succ 1 0)
      (ProjectSyntax.encode id (Source.SetLanguage.edge 2 1 0))))))

theorem indexBijection_freeClosed {k : Nat} (labels tab theta : Fin k) : (indexBijection labels tab theta).FreeClosed := by
  simp -implicitDefEqProofs [indexBijection,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,indices_freeClosed]

theorem indexBijection_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k) (labels tab theta : Fin k) :
    Project.Formula.satisfies env (indexBijection labels tab theta) ↔
      ∃ f, (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) f (env.bound labels) (env.bound theta) ∧
        ∀ label beta, Indices (env.bound tab) (env.bound theta) label beta ↔ PureKuratowski.PairMember M label beta f := by
  simp only [indexBijection,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_isBijectionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    indices_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Term.eval_bound]
  rfl

def constructionSentence {k : Nat} (labels bound : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (Project.Formula.isOrdinal (.bound bound))
    (.existsE (.conj (table labels.succ bound.succ 0)
      (.forallE (.imp (eligible labels.succ.succ bound.succ.succ 0) (indexBijection labels.succ.succ 1 0))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,table_freeClosed,eligible_freeClosed,indexBijection_freeClosed]

theorem construction_models {k : Nat} (labels bound : Fin k) (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence labels bound)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOrdinal_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    table_semantics hM,eligible_semantics hM,indexBijection_semantics hM,Project.Term.eval_bound]
  intro hBound
  obtain ⟨tab,hTab⟩ := chooseTable hM hChoice (env labels) (env bound) hBound
  exact ⟨tab,hTab,fun _ hTheta => indices_bijection hM hTab hTheta⟩

theorem construction_kernel_certificate {k : Nat} (labels bound : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence labels bound))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let witness := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    {bound := Fin.elim0,free := fun _ => witness}
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (constructionSentence labels bound)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence labels bound)).mp
      (construction_models labels bound hL hChoice)

end PPAC.Migration.ForcingOrdinalTable
