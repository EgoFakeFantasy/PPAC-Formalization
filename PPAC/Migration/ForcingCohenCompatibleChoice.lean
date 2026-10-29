/- Pinned AssignedGraphs.Condition.compatibleChoice/compatibleChoice_spec:381-388.
Reuse the ACTUAL existing Cohen compatibility predicate and donor internal
uniformization. Default is the empty condition; choice is discharged in L. -/
import PPAC.Migration.ForcingCohenCodes
import PPAC.Migration.ConstructionCompatiblePlacement

namespace PPAC.Migration.ForcingCohenCompatibleChoice
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionCohenCompatibility (Compatible)
open ForcingWithTopCarrier (Empty)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
universe u
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Literal source successful branch or empty-condition default. -/
def Candidate (A p q : M.Carrier .set) : Prop :=
  ((Project.FirstOrderSemantics.reduct M).mem q A ∧ Compatible p q) ∨
  ((¬ ∃ r, (Project.FirstOrderSemantics.reduct M).mem r A ∧ Compatible p r) ∧ Empty q)

def candidate {m} (A p q : Fin m) : Project.Formula 1 m :=
  .disj (.conj (.mem (.bound q) (.bound A)) (ConstructionCompatiblePlacement.compatible p q))
    (.conj (.neg (.existsE (.conj (.mem .newest (.bound A.succ))
      (ConstructionCompatiblePlacement.compatible p.succ 0)))) (Project.Formula.isEmpty (.bound q)))

theorem candidate_freeClosed {m} (A p q : Fin m) : (candidate A p q).FreeClosed := by
  simp -implicitDefEqProofs [candidate,Definitional.Formula.FreeClosed,ConstructionCompatiblePlacement.compatible_freeClosed]

theorem candidate_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m}
    (ρ : Env (Project.FirstOrderSemantics.reduct M) m) (A p q : Fin m) :
    Project.Formula.satisfies ρ (candidate A p q) ↔ Candidate (ρ.bound A) (ρ.bound p) (ρ.bound q) := by
  simp only [candidate,Candidate,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,ConstructionCompatiblePlacement.compatible_semantics hM,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_isEmpty_iff]
  rfl

def Selection (A P F : M.Carrier .set) : Prop := MapsTo P P F ∧
  ∀ p q, PureKuratowski.PairMember M p q F → Candidate A p q

def selection {m} (A P F : Fin m) : Project.Formula 1 m :=
  .conj (Project.Formula.isFunctionFromTo PureKuratowskiProject.convention (.bound F) (.bound P) (.bound P))
    (.forallE (.forallE (.imp
      (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) .newest (.bound F.succ.succ))
      (candidate A.succ.succ 1 0))))

theorem selection_freeClosed {m} (A P F : Fin m) : (selection A P F).FreeClosed := by
  simp -implicitDefEqProofs [selection,Definitional.Formula.FreeClosed,candidate_freeClosed]

theorem selection_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m}
    (ρ : Env (Project.FirstOrderSemantics.reduct M) m) (A P F : Fin m) :
    Project.Formula.satisfies ρ (selection A P F) ↔ Selection (ρ.bound A) (ρ.bound P) (ρ.bound F) := by
  simp only [selection,Selection,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isFunctionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),candidate_semantics hM]
  exact and_congr (ForcingSupportSize.native_mapsTo hM _ _ _).symm Iff.rfl

theorem exists_selection (hM : FirstOrder.Theory.Models M nativeZF)
    (hZFC : (Project.FirstOrderSemantics.reduct M).Models SetTheory.ZFC) {S w P A : M.Carrier .set}
    (hP : ForcingCohenConditions.Carrier S w P)
    (hA : (Project.FirstOrderSemantics.reduct M).MemberSubset A P) : ∃ F, Selection A P F := by
  let ρ : Env (Project.FirstOrderSemantics.reduct M) 1 := ⟨fun _ => A,fun _ => A⟩
  let φ : Project.BinarySchema 1 := {body := candidate (2 : Fin 3) 1 0, freeClosed := candidate_freeClosed _ _ _}
  have hφ p q : φ.denote ρ p q ↔ Candidate A p q := candidate_semantics hM _ _ _ _
  obtain ⟨F,hF,hf⟩ := ExistingSmallUnion.uniformize_formula_l (KuratowskiZF.interpretation hM) hZFC φ ρ
    (X := P) (Y := P) (by
      intro p _
      classical
      by_cases h : ∃ q, (Project.FirstOrderSemantics.reduct M).mem q A ∧ Compatible p q
      · obtain ⟨q,hq,hpq⟩ := h
        exact ⟨q,hA q hq,(hφ p q).mpr (Or.inl ⟨hq,hpq⟩)⟩
      · obtain ⟨z,hz⟩ := ForcingWithTopCarrier.exists_empty hM
        exact ⟨z,(hP z).mpr (ForcingCohenCodes.empty_condition hM hz),(hφ p z).mpr (Or.inr ⟨h,hz⟩)⟩)
  exact ⟨F,(ForcingSupportSize.native_mapsTo hM P P F).mpr hF,fun p q h => (hφ p q).mp (hf p q h)⟩

/-- Exact source compatibleChoice_spec, with the successful witness discharged. -/
theorem selection_spec {A P F p q : M.Carrier .set} (hF : Selection A P F)
    (hf : PureKuratowski.PairMember M p q F)
    (h : ∃ r, (Project.FirstOrderSemantics.reduct M).mem r A ∧ Compatible p r) :
    (Project.FirstOrderSemantics.reduct M).mem q A ∧ Compatible p q :=
  (hF.2 p q hf).elim id (fun hq => (hq.1 h).elim)

def selectionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 4
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.carrier (0 : Fin 4) 1 2))
      (.imp (Project.Formula.subset (.bound 3) (.bound 2)) (.existsE (selection (4 : Fin 5) 3 0))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,selection_freeClosed]

theorem selection_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hZFC : (Project.FirstOrderSemantics.reduct M).Models SetTheory.ZFC) :
    (Project.FirstOrderSemantics.reduct M).SatisfiesSentence selectionSentence := by
  apply (Structure.satisfiesSentence_iff _ _).mpr
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenConditions.carrier_semantics (M := M),Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_exists_iff,selection_semantics hM]
  exact fun hP hA => exists_selection hM hZFC hP hA

theorem selection_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative selectionSentence)) := by
  apply ModelTransfer.derives
  intro N hN
  apply ConstructibleGround.relative_models hN
  exact selection_models (ConstructibleSource.model_zf hN)
    (InnerModel.l_model_zfc_l (ModelTransfer.project_models_iff.mp hN))

end PPAC.Migration.ForcingCohenCompatibleChoice
