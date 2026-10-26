/- Pinned OpenAI ProbeWords.Raw.cardinal_le and Path.extension_cardinal_le.
The Raw encoding already is (internal finite sequence, terminal old element).
Reuse YesMetaZFC's existing finite-sequence bound; Word is the actual reduced
subset, and the existing path-letter quotient supplies the alphabet bound. -/
import PPAC.Migration.ExistingFiniteSequenceBounds
import PPAC.Migration.ConstructionProbeCardinality
import PPAC.Migration.ConstructionProbeWord

namespace PPAC.Migration.ConstructionProbeWordCardinality
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (Small MapsTo)
open ConstructionProbeRaw ConstructionProbeWord ConstructionProbeLetters
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The source Raw.code bound, using the existing internal code representation. -/
theorem raw_cardinal_le (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S R mu : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hD : Small D mu) (hS : Small S mu) (hR : Carrier w D S R) : Small R mu := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨Q,hQ⟩ := ExistingFiniteSequenceBounds.fseq_space_exists_l I hZF hw S
  have hQiff (f) : (Project.FirstOrderSemantics.reduct M).mem f Q ↔ FiniteSequence w S f := by
    refine (hQ f).trans ?_
    exact exists_congr (fun n => and_congr_right (fun _ => (ForcingSupportSize.native_mapsTo hM n S f).symm))
  have hprod : (Project.FirstOrderSemantics.reduct M).IsCartesianProduct I R Q D := by
    intro q
    refine (hR q).trans ?_
    exact ⟨fun ⟨f,x,hf,hx,hcode⟩ => ⟨f,(hQiff f).mpr hf,x,hx,hcode⟩,
      fun ⟨f,hf,x,hx,hcode⟩ => ⟨f,x,(hQiff f).mp hf,hx,hcode⟩⟩
  have hQsmall := ExistingFiniteSequenceBounds.fseq_bound_l I hZF hw hmu
    ((ForcingSupportSize.native_small hM S mu).mp hS) hQ
  exact (ForcingSupportSize.native_small hM R mu).mpr
    (ExistingCardinalBounds.infinite_product_l I hZF hw hmu hQsmall
      ((ForcingSupportSize.native_small hM D mu).mp hD) hprod)

/-- Source subtype inclusion; no assumed size bound for reduced words. -/
theorem word_cardinal_le (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S mul A b W mu : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hD : Small D mu) (hS : Small S mu) (hW : WordCarrier w D S mul A b W) : Small W mu := by
  obtain ⟨R,hR⟩ := ConstructionProbeRaw.exists_carrier hM hw D S
  exact ForcingSupportSize.small_subset hM (fun q hq => (hR q).mpr (word_raw hW hq))
    (raw_cardinal_le hM hw hmu hD hS hR)

/-- Original extension bound: derive the letter bound from the path quotient,
then use the actual Word carrier. No cardinal premise on the extension. -/
theorem extension_cardinal_le (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul F C S projection A b W mu : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hD : Small D mu) (hC : Representatives w D C) (hS : Letters w D mul F C S)
    (hp : MapsTo C S projection) (hProjection : Projection w D mul F C projection)
    (hW : WordCarrier w D S mul A b W) : Small W mu :=
  word_cardinal_le hM hw hmu hD
    (ConstructionProbeCardinality.letters_cardinal_le hM hw hmu hD hC hS hp hProjection) hW

def rawBoundSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 5
    (.imp (Project.Formula.isOmega (.bound 0))
      (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound 0) (.bound 4))
        (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (1 : Fin 5) 4))
          (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (2 : Fin 5) 4))
            (.imp (carrier (0 : Fin 5) 1 2 3)
              (ProjectSyntax.encode id (ForcingSupportSize.small (3 : Fin 5) 4)))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
    ProjectSyntax.freeClosed, carrier_freeClosed]

theorem raw_bound_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence rawBoundSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) rawBoundSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Term.eval_bound, GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M), carrier_semantics hM]
  exact fun hw hmu hD hS hR => raw_cardinal_le hM hw hmu hD hS hR

theorem raw_bound_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence rawBoundSentence) := ModelTransfer.derives (fun _ hM => raw_bound_models hM)

def extensionBoundSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 11
    (.imp (Project.Formula.isOmega (.bound 0))
      (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound 0) (.bound 10))
        (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (1 : Fin 11) 10))
          (.imp (representatives (0 : Fin 11) 1 4)
            (.imp (letters (0 : Fin 11) 1 2 3 4 5)
              (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (6 : Fin 11) 4 5))
                (.imp (projectionGraph (0 : Fin 11) 1 2 3 4 6)
                  (.imp (wordCarrier (0 : Fin 11) 1 5 2 7 8 9)
                    (ProjectSyntax.encode id (ForcingSupportSize.small (9 : Fin 11) 10))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
    ProjectSyntax.freeClosed, representatives_freeClosed, letters_freeClosed,
    projectionGraph_freeClosed, wordCarrier_freeClosed]

theorem extension_bound_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence extensionBoundSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) extensionBoundSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Term.eval_bound, GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M), representatives_semantics hM, letters_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M), projectionGraph_semantics hM, wordCarrier_semantics hM]
  exact fun hw hmu hD hC hS hp hProjection hW => extension_cardinal_le hM hw hmu hD hC hS hp hProjection hW

theorem extension_bound_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence extensionBoundSentence) := ModelTransfer.derives (fun _ hM => extension_bound_models hM)

end PPAC.Migration.ConstructionProbeWordCardinality
