/- Pinned SupportFilter.conjugate_fix: conjugating permutations transports
exactly the labels fixed pointwise. Internal label images use Separation;
composition/inverse graphs are the existing donor-backed constructors. -/
import PPAC.Migration.ForcingLabelPermutations
import PPAC.Migration.ForcingStabilizerTransport

namespace PPAC.Migration.ForcingLabelConjugacy
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open Source.SetLanguage (args2)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingConditionGraphs
open ForcingLabelPermutations (Fixes fixes)
open ForcingNameConjugacy (Conjugate conjugate)
open ForcingStabilizerTransport (Image image)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Exact image of an internal label subset, not an assumed external class. -/
theorem exists_image (hM : FirstOrder.Theory.Models M nativeZF) {I r J : M.Carrier .set}
    (hr : Endomap I r) :
    ∃ K, Image r J K ∧ ∀ y, (Definitional.Project.FirstOrderSemantics.reduct M).mem y K →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem y I := by
  let query : Formula 3 := .ex ((Formula.mem (Fin.last 3) (0 : Fin 3).castSucc).conj
    (Source.SetLanguage.edge (1 : Fin 3).castSucc (Fin.last 3) (2 : Fin 3).castSucc))
  have sep := (GodelDefOutput.separation_semantics (Definitional.Project.FirstOrderSemantics.reduct M).mem query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨K,hK⟩ := sep (args2 J r) I
  have hq : ∀ y, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases y (args2 J r)) query ↔ ∃ x,
        (Definitional.Project.FirstOrderSemantics.reduct M).mem x J ∧ PureKuratowski.PairMember M x y r := by
    intro y
    simp only [query,Formula.Realize,KuratowskiZF.source_edge,Fin.lastCases_last,Fin.lastCases_castSucc]
    rfl
  refine ⟨K,?_,fun y hy => ((hK y).mp hy).1⟩
  intro y
  constructor
  · intro hy
    exact (hq y).mp ((hK y).mp hy).2
  · rintro ⟨x,hx,he⟩
    exact (hK y).mpr ⟨hr.2 x y he,(hq y).mpr ⟨x,hx,he⟩⟩

/-- The two directions in the original conjugate_fix proof, on actual graphs. -/
theorem fixes_conjugate {I r i s t J K : M.Carrier .set}
    (hr : Permutation I r) (hi : Endomap I i) (hri : InverseGraph r i)
    (hc : Conjugate I r i s t) (hImage : Image r J K)
    (hJI : ∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x J →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem x I) :
    Fixes J s ↔ Fixes K t := by
  obtain ⟨mid,_,hsi,hrm⟩ := hc
  constructor
  · intro hs y hy
    obtain ⟨x,hx,hxy⟩ := (hImage y).mp hy
    have hyI := hr.1.2 x y hxy
    exact (hrm y y).mpr ⟨hyI,x,(hsi y x).mpr ⟨hyI,x,(hri x y).mp hxy,hs x hx⟩,hxy⟩
  · intro ht x hx
    obtain ⟨y,hxy,_⟩ := hr.1.1.2 x (hJI x hx)
    have hyK := (hImage y).mpr ⟨x,hx,hxy⟩
    obtain ⟨_,z,hyz,hzy⟩ := (hrm y y).mp (ht y hyK)
    obtain ⟨_,w,hyw,hwz⟩ := (hsi y z).mp hyz
    have hw : w = x := function_unique hi.1 hyw ((hri x y).mp hxy)
    have hz : z = x := hr.2.1 z x y hzy hxy
    simpa only [hw,hz] using hwz

/-- Source stabilizer equality at each permutation, keeping both actual carriers. -/
theorem fixing_conjugate {I G r i s t J K S T : M.Carrier .set}
    (hG : ForcingLabelPermutations.Carrier I G)
    (hr : Permutation I r) (hi : Endomap I i) (hri : InverseGraph r i)
    (hs : Permutation I s) (ht : Permutation I t)
    (hc : Conjugate I r i s t) (hImage : Image r J K)
    (hJI : ∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x J →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem x I)
    (hS : ForcingLabelPermutations.Fixing G J S) (hT : ForcingLabelPermutations.Fixing G K T) :
    (Definitional.Project.FirstOrderSemantics.reduct M).mem s S ↔
      (Definitional.Project.FirstOrderSemantics.reduct M).mem t T := by
  rw [hS s,hT t]
  exact ⟨fun h => ⟨(hG t).mpr ht,(fixes_conjugate hr hi hri hc hImage hJI).mp h.2⟩,
    fun h => ⟨(hG s).mpr hs,(fixes_conjugate hr hi hri hc hImage hJI).mpr h.2⟩⟩

def imageSentence : Source.Sentence := ((endomap (0 : Fin 3) 1).imp
  (.ex ((image (1 : Fin 3).castSucc (2 : Fin 3).castSucc (Fin.last 3)).conj
    (Source.SetLanguage.subset (Fin.last 3) (0 : Fin 3).castSucc)))).close

def conjugacySentence : Source.Sentence := ((permutation (0 : Fin 7) 1).imp ((endomap 0 2).imp
  ((inverseGraph 1 2).imp ((conjugate 0 1 2 3 4).imp ((image 1 5 6).imp
    ((Source.SetLanguage.subset 5 0).imp ((fixes 5 3).iff (fixes 6 4)))))))).close

theorem image_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence imageSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hr
  obtain ⟨K,hK,hKI⟩ := exists_image hM ((endomap_semantics (M := M) env 0 1).mp hr)

  refine ⟨K,?_,?_⟩
  · apply (ForcingStabilizerTransport.image_semantics (M := M) (Fin.lastCases K env)
      (1 : Fin 3).castSucc (2 : Fin 3).castSucc (Fin.last 3)).mpr
    simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hK
  · apply (ForcingLabelPermutations.subset_semantics (Fin.lastCases K env) (Fin.last 3) (0 : Fin 3).castSucc).mpr
    simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hKI

theorem conjugacy_models (_hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence conjugacySentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hr hi hri hc him hJI
  have he := fixes_conjugate ((permutation_semantics (M := M) env 0 1).mp hr)
    ((endomap_semantics (M := M) env 0 2).mp hi)
    ((inverseGraph_semantics (M := M) env 1 2).mp hri)
    ((ForcingNameConjugacy.conjugate_semantics (M := M) env 0 1 2 3 4).mp hc)
    ((ForcingStabilizerTransport.image_semantics (M := M) env 1 5 6).mp him)
    ((ForcingLabelPermutations.subset_semantics env 5 0).mp hJI)
  have hl := ForcingLabelPermutations.fixes_semantics (M := M) env 5 3
  have hr := ForcingLabelPermutations.fixes_semantics (M := M) env 6 4
  exact ⟨fun h => hr.mpr (he.mp (hl.mp h)),fun h => hl.mpr (he.mpr (hr.mp h))⟩

theorem image_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence imageSentence) :=
  ModelTransfer.derives (fun _ hM => image_models hM)

theorem conjugacy_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence conjugacySentence) :=
  ModelTransfer.derives (fun _ hM => conjugacy_models hM)

end PPAC.Migration.ForcingLabelConjugacy
