/- Pinned ProbeWords.Path.letters_cardinal_le. Reuse the donor infinite-product
bound and native least-preimage injection; no choice of quotient representatives. -/
import PPAC.Migration.ConstructionProbeCones
import PPAC.Migration.ExistingCardinalBounds
import YesMetaZFC.SetTheory.Card.Cofinality.Comparison

namespace PPAC.Migration.ConstructionProbeCardinality
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Small Injection)
open ConstructionProbeLetters
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Extend the indexed quotient map over unused ordinal indices by a fixed letter,
then apply the existing native least-preimage theorem. Empty quotients are separate. -/
theorem indexed_quotient_bound (hM : FirstOrder.Theory.Models M nativeZF)
    {C L projection mu : M.Carrier .set}
    (hmu : (Project.FirstOrderSemantics.reduct M).IsOrdinal mu)
    (hC : Small C mu) (hp : MapsTo C L projection)
    (honto : ∀ c, (Project.FirstOrderSemantics.reduct M).mem c L →
      ∃ p, (Project.FirstOrderSemantics.reduct M).mem p C ∧ PureKuratowski.PairMember M p c projection) :
    Small L mu := by
  classical
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  by_cases hne : ∃ q, (Project.FirstOrderSemantics.reduct M).mem q L
  · obtain ⟨q,hq⟩ := hne
    obtain ⟨f,hf⟩ := hC
    let schema : Project.BinarySchema 3 := {
      body := (.disj (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 3 0 2))
        (ProjectSyntax.encode id (Source.SetLanguage.edge 4 0 1))))
        (.conj (.neg (.existsE (ProjectSyntax.encode id (Source.SetLanguage.edge 3 0 2))))
          (Project.Formula.extensionalEq (.bound 0) (.bound 4))))
      freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
        ProjectSyntax.freeClosed,Project.Formula.extensionalEq] }
    let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 :=
      { bound := Fin.cases f (Fin.cases projection (fun _ => q)), free := fun _ => q }
    have he (i z) : schema.denote env i z ↔
        (∃ p, PureKuratowski.PairMember M p i f ∧ PureKuratowski.PairMember M p z projection) ∨
        (¬ (∃ p, PureKuratowski.PairMember M p i f)) ∧ z = q := by
      simp only [Project.BinarySchema.denote,schema,Project.Formula.satisfies_disj_iff,
        Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
        Project.Formula.satisfies_neg_iff,
        GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
        Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound]
      rfl
    obtain ⟨G,hG,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I schema env
      (source := mu) (target := L) (by
        intro i _
        by_cases hpre : ∃ p, PureKuratowski.PairMember M p i f
        · obtain ⟨p,hpi⟩ := hpre
          obtain ⟨z,hpz,_⟩ := hp.1.2 p (ForcingConditionGraphs.function_input hf.1.1 hpi)
          exact ⟨z,(he i z).mpr (Or.inl ⟨p,hpi,hpz⟩)⟩
        · exact ⟨q,(he i q).mpr (Or.inr ⟨hpre,rfl⟩)⟩) (by
        intro i _ z v hz hv
        rcases (he i z).mp hz with ⟨p,hpi,hpz⟩ | ⟨hn,hzq⟩ <;>
          rcases (he i v).mp hv with ⟨r,hri,hrv⟩ | ⟨hn',hvq⟩
        · have hpr := hf.2 p r i hpi hri
          subst r
          exact ForcingConditionGraphs.function_unique hp.1 hpz hrv
        · exact (hn' ⟨p,hpi⟩).elim
        · exact (hn ⟨r,hri⟩).elim
        · exact hzq.trans hvq.symm) (by
        intro i z _ hz
        rcases (he i z).mp hz with ⟨p,_,hpz⟩ | ⟨_,rfl⟩
        · exact hp.2 p z hpz
        · exact hq)
    have hSurjective : (Project.FirstOrderSemantics.reduct M).IsSetSurjectiveOnto I G mu L := by
      intro c hc
      obtain ⟨p,hpC,hpc⟩ := honto c hc
      obtain ⟨i,hpi,_⟩ := hf.1.1.2 p hpC
      have hi := hf.1.2 p i hpi
      exact ⟨i,hi,(hGraph i c).mpr ⟨hi,(he i c).mpr (Or.inl ⟨p,hpi,hpc⟩)⟩⟩
    exact (ForcingSupportSize.native_small hM L mu).mpr
      (ZF.exists_rightInverseInjection_of_surjection_from_ordinal hZF I hmu hG hSurjective)
  · apply (ForcingSupportSize.native_small hM L mu).mpr
    exact ZF.exists_inclusionInjection hZF I (fun x hx => (hne ⟨x,hx⟩).elim)

theorem letters_cardinal_le (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul F C L projection mu : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hD : Small D mu) (hC : Representatives w D C) (hL : Letters w D mul F C L)
    (hp : MapsTo C L projection) (hProjection : Projection w D mul F C projection) : Small L mu := by
  have hprod : (Project.FirstOrderSemantics.reduct M).IsCartesianProduct (KuratowskiZF.interpretation hM) C w D := by
    intro p
    exact (hC p).trans ⟨fun ⟨i,x,hi,hx,hcode⟩ => ⟨i,hi,x,hx,hcode⟩,
      fun ⟨i,hi,x,hx,hcode⟩ => ⟨i,x,hi,hx,hcode⟩⟩
  have hBound := ExistingCardinalBounds.infinite_product_l (KuratowskiZF.interpretation hM)
    (ModelTransfer.project_models_iff.mp hM) hw hmu hmu.2
    ((ForcingSupportSize.native_small hM D mu).mp hD) hprod
  exact indexed_quotient_bound hM hmu.1.1 ((ForcingSupportSize.native_small hM C mu).mpr hBound) hp
    (fun _ hc => projection_onto hL hProjection hc)

def boundSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 8
    (.imp (Project.Formula.isOmega (.bound 0))
      (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound 0) (.bound 7))
        (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (1 : Fin 8) 7))
          (.imp (representatives (0 : Fin 8) 1 4)
            (.imp (letters (0 : Fin 8) 1 2 3 4 5)
              (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (6 : Fin 8) 4 5))
                (.imp (projectionGraph (0 : Fin 8) 1 2 3 4 6)
                  (ProjectSyntax.encode id (ForcingSupportSize.small (5 : Fin 8) 7)))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
    ProjectSyntax.freeClosed,representatives_freeClosed,letters_freeClosed,projectionGraph_freeClosed]

theorem bound_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence boundSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) boundSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),representatives_semantics hM,letters_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),projectionGraph_semantics hM]
  exact fun hw hmu hD hC hL hp hProjection => letters_cardinal_le hM hw hmu hD hC hL hp hProjection

theorem bound_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence boundSentence) := ModelTransfer.derives (fun _ hM => bound_models hM)

end PPAC.Migration.ConstructionProbeCardinality
