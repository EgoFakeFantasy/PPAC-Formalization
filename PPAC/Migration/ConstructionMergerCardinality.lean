/- Pinned MergerWords.Word.cardinal_le:648 / merger_cardinal_le:666.
Merger words are the EXISTING Raw carrier: reuse raw_cardinal_le unchanged.
The actual copies quotient is bounded via the EXISTING indexed_quotient_bound
(native ordinal least-preimages), not arbitrary choice of representatives. -/
import PPAC.Migration.ConstructionProbeWordCardinality
import PPAC.Migration.ConstructionMergerCopies

namespace PPAC.Migration.ConstructionMergerCardinality
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (Small MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem copies_cardinal_le (hM : FirstOrder.Theory.Models M nativeZF)
    {w n D mul P C L projection mu : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hD : Small D mu)
    (hC : ConstructionProbeLetters.Representatives n D C)
    (hL : ConstructionMergerCopies.Copies n D mul P C L) (hp : MapsTo C L projection)
    (hProjection : ConstructionMergerCopies.Projection n D mul P C projection) : Small L mu := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hnSmall : Small n mu := ForcingSupportSize.small_subset hM
    (fun i hi => (hw.isOrdinal hZF).transitive n hn i hi) ((ForcingSupportSize.native_small hM w mu).mpr hmu.2)
  have hprod : (Project.FirstOrderSemantics.reduct M).IsCartesianProduct (KuratowskiZF.interpretation hM) C n D := by
    intro p
    exact (hC p).trans ⟨fun ⟨i,x,hi,hx,hcode⟩ => ⟨i,hi,x,hx,hcode⟩,
      fun ⟨i,hi,x,hx,hcode⟩ => ⟨i,x,hi,hx,hcode⟩⟩
  have hBound := ExistingCardinalBounds.infinite_product_l (KuratowskiZF.interpretation hM)
    hZF hw hmu ((ForcingSupportSize.native_small hM n mu).mp hnSmall)
    ((ForcingSupportSize.native_small hM D mu).mp hD) hprod
  exact ConstructionProbeCardinality.indexed_quotient_bound hM hmu.1.1
    ((ForcingSupportSize.native_small hM C mu).mpr hBound) hp
    (fun _ hc => ConstructionMergerCopies.projection_onto hL hProjection hc)

/-- Source bound on the SAME actual Merger Word; no new carrier/encoding. -/
theorem merger_cardinal_le (hM : FirstOrder.Theory.Models M nativeZF)
    {w n D mul P C L projection W mu : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hD : Small D mu)
    (hC : ConstructionProbeLetters.Representatives n D C)
    (hL : ConstructionMergerCopies.Copies n D mul P C L) (hp : MapsTo C L projection)
    (hProjection : ConstructionMergerCopies.Projection n D mul P C projection)
    (hW : ConstructionProbeRaw.Carrier w D L W) : Small W mu :=
  ConstructionProbeWordCardinality.raw_cardinal_le hM hw hmu hD
    (copies_cardinal_le hM hw hmu hn hD hC hL hp hProjection) hW

def boundSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 10
    (.imp (Project.Formula.isOmega (.bound 0))
      (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound 0) (.bound 9))
        (.imp (.mem (.bound 1) (.bound 0))
          (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (2 : Fin 10) 9))
            (.imp (ConstructionProbeLetters.representatives (1 : Fin 10) 2 5)
              (.imp (ConstructionMergerCopies.copies (1 : Fin 10) 2 3 4 5 6)
                (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (7 : Fin 10) 5 6))
                  (.imp (ConstructionMergerCopies.projectionGraph (1 : Fin 10) 2 3 4 5 7)
                    (.imp (ConstructionProbeRaw.carrier (0 : Fin 10) 2 6 8)
                      (ProjectSyntax.encode id (ForcingSupportSize.small (8 : Fin 10) 9)))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionProbeLetters.representatives_freeClosed,ConstructionMergerCopies.copies_freeClosed,
    ConstructionMergerCopies.projectionGraph_freeClosed,ConstructionProbeRaw.carrier_freeClosed]

theorem bound_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence boundSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) boundSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionProbeLetters.representatives_semantics hM,ConstructionMergerCopies.copies_semantics hM,
    ConstructionMergerCopies.projectionGraph_semantics hM,ConstructionProbeRaw.carrier_semantics hM]
  exact fun hw hmu hn hD hC hL hp hProjection hW => merger_cardinal_le hM hw hmu hn hD hC hL hp hProjection hW

theorem bound_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence boundSentence) := ModelTransfer.derives (fun _ hM => bound_models hM)

end PPAC.Migration.ConstructionMergerCardinality
