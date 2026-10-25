/- Pinned SupportFilter.subgroupFilter: |J| <= mu is represented by an
internal set injection. Reuses the original source injection formula and the
native function constructors; no external cardinal or choice witness. -/
import PPAC.Migration.ForcingConjugationGraph
import YesMetaZFC.SetTheory.Card.Basic

namespace PPAC.Migration.ForcingSupportSize
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingConditionGraphs
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def MapsTo (S T f : M.Carrier .set) : Prop :=
  FunctionOn S f ∧ ∀ x y, PureKuratowski.PairMember M x y f →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem y T

def Injection (S T f : M.Carrier .set) : Prop :=
  MapsTo S T f ∧ ∀ x y z, PureKuratowski.PairMember M x z f → PureKuratowski.PairMember M y z f → x = y

theorem mapsTo_semantics {m : Nat} (env : Fin m → M.Carrier .set) (f S T : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (Source.SetLanguage.mapsTo f S T) ↔
      MapsTo (env S) (env T) (env f) := by
  rw [Source.SetLanguage.mapsTo, DefinableMinimaChoice.realize_rename]
  simp only [Formula.Realize, functionOn_semantics (M := M), KuratowskiZF.source_edge]
  change (FunctionOn (env S) (env f) ∧ ∀ x y,
    (Definitional.Project.FirstOrderSemantics.reduct M).mem x (env S) →
    PureKuratowski.PairMember M x y (env f) →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem y (env T)) ↔ _
  exact ⟨fun h => ⟨h.1,fun x y he => h.2 x y (function_input h.1 he) he⟩,
    fun h => ⟨h.1,fun x y _ he => h.2 x y he⟩⟩

theorem injection_semantics {m : Nat} (env : Fin m → M.Carrier .set) (f S T : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (Source.SetLanguage.injection f S T) ↔
      Injection (env S) (env T) (env f) := by
  rw [Source.SetLanguage.injection, DefinableMinimaChoice.realize_rename]
  simp only [Formula.Realize, mapsTo_semantics (M := M), KuratowskiZF.source_edge]
  change (MapsTo (env S) (env T) (env f) ∧ ∀ x y z,
    (Definitional.Project.FirstOrderSemantics.reduct M).mem x (env S) →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem y (env S) →
    (PureKuratowski.PairMember M x z (env f) ∧ PureKuratowski.PairMember M y z (env f)) → x = y) ↔ _
  exact ⟨fun h => ⟨h.1,fun x y z hx hy => h.2 x y z (function_input h.1.1 hx)
      (function_input h.1.1 hy) ⟨hx,hy⟩⟩,
    fun h => ⟨h.1,fun x y z _ _ he => h.2 x y z he.1 he.2⟩⟩

theorem native_mapsTo (hM : FirstOrder.Theory.Models M nativeZF) (S T f : M.Carrier .set) :
    MapsTo S T f ↔ (Definitional.Project.FirstOrderSemantics.reduct M).IsSetFunctionFromTo
      (KuratowskiZF.interpretation hM) f S T := by
  constructor
  · intro h
    refine ⟨⟨?_,fun x y z hy hz => function_unique h.1 hy hz⟩,?_,?_⟩
    · intro z hz
      obtain ⟨x,y,_,hc⟩ := h.1.1 z hz
      exact ⟨x,y,hc⟩
    · intro x
      exact ⟨fun hx => by obtain ⟨y,hy,_⟩ := h.1.2 x hx; exact ⟨y,hy⟩,
        fun ⟨y,hy⟩ => function_input h.1 hy⟩
    · intro x hx
      obtain ⟨y,hy,_⟩ := h.1.2 x hx
      exact ⟨y,h.2 x y hy,hy⟩
  · intro h
    refine ⟨⟨?_,?_⟩,fun _ _ he => h.output_mem_of_pairMember he⟩
    · intro z hz
      obtain ⟨x,y,hc⟩ := h.1.1 z hz
      exact ⟨x,y,h.input_mem_of_pairMember ⟨z,hc,hz⟩,hc⟩
    · intro x hx
      obtain ⟨y,_,hy⟩ := h.2.2 x hx
      exact ⟨y,hy,fun z hz => h.1.2 x z y hz hy⟩

theorem native_injection (hM : FirstOrder.Theory.Models M nativeZF) (S T f : M.Carrier .set) :
    Injection S T f ↔ (Definitional.Project.FirstOrderSemantics.reduct M).IsSetInjectionFromTo
      (KuratowskiZF.interpretation hM) f S T :=
  and_congr (native_mapsTo hM S T f) Iff.rfl

def Small (S mu : M.Carrier .set) : Prop := ∃ f, Injection S mu f

def small {m : Nat} (S mu : Fin m) : Formula m :=
  .ex (Source.SetLanguage.injection (Fin.last m) S.castSucc mu.castSucc)

theorem small_semantics {m : Nat} (env : Fin m → M.Carrier .set) (S mu : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (small S mu) ↔ Small (env S) (env mu) := by
  simp only [small,Small,Formula.Realize,injection_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem native_small (hM : FirstOrder.Theory.Models M nativeZF) (S mu : M.Carrier .set) :
    Small S mu ↔ (Definitional.Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual
      (KuratowskiZF.interpretation hM) S mu :=
  exists_congr (native_injection hM S mu)

theorem small_subset (hM : FirstOrder.Theory.Models M nativeZF) {A B mu : M.Carrier .set}
    (hAB : ∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x A →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem x B) (hB : Small B mu) : Small A mu := by
  obtain ⟨f,hf⟩ := (native_small hM B mu).mp hB
  obtain ⟨g,hg⟩ := SetTheory.ZF.exists_inclusionInjection (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) hAB
  exact (native_small hM A mu).mpr (SetTheory.ZF.exists_compositionInjection
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) hg hf)

theorem small_empty (hM : FirstOrder.Theory.Models M nativeZF) (mu : M.Carrier .set)
    {empty : M.Carrier .set} (he : ∀ x, ¬ (Definitional.Project.FirstOrderSemantics.reduct M).mem x empty) : Small empty mu :=
  (native_small hM empty mu).mpr (SetTheory.ZF.exists_inclusionInjection (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) (fun x hx => False.elim (he x hx)))

/-- Restrict the actual inverse-value relation to the image; no choice of preimages. -/
theorem small_image (hM : FirstOrder.Theory.Models M nativeZF) {I r J K mu : M.Carrier .set}
    (hr : Permutation I r) (him : ForcingStabilizerTransport.Image r J K) (hJ : Small J mu) : Small K mu := by
  let env : SetTheory.Env (Definitional.Project.FirstOrderSemantics.reduct M) 1 :=
    { bound := fun _ => r, free := fun _ => r }
  have hv := Definitional.Project.Formula.denote_inverseValue_iff (KuratowskiZF.interpretation hM) env
  obtain ⟨f,hf⟩ := SetTheory.ZF.exists_setInjectionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) (Definitional.Project.BinarySchema.inverseValue PureKuratowskiProject.convention)
    env (source := K) (target := J)
    (fun x hx => by obtain ⟨y,_,hy⟩ := (him x).mp hx; exact ⟨y,(hv x y).mpr hy⟩)
    (fun x _ y z hy hz => hr.2.1 y z x ((hv x y).mp hy) ((hv x z).mp hz))
    (fun x y hx hy => by
      obtain ⟨z,hz,hzx⟩ := (him x).mp hx
      exact (hr.2.1 z y x hzx ((hv x y).mp hy)) ▸ hz)
    (fun x y z _ _ hx hy => function_unique hr.1.1 ((hv x z).mp hx) ((hv y z).mp hy))
  obtain ⟨g,hg⟩ := (native_small hM J mu).mp hJ
  exact (native_small hM K mu).mpr (SetTheory.ZF.exists_compositionInjection
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) hf hg)

def subsetSentence : Source.Sentence := ((Source.SetLanguage.subset (0 : Fin 3) 1).imp
  ((small 1 2).imp (small 0 2))).close

def imageSentence : Source.Sentence := ((permutation (0 : Fin 5) 1).imp
  ((ForcingStabilizerTransport.image 1 2 3).imp ((small 2 4).imp (small 3 4)))).close

theorem subset_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence subsetSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hAB hB
  exact (small_semantics (M := M) env 0 2).mpr (small_subset hM
    ((ForcingLabelPermutations.subset_semantics (M := M) env 0 1).mp hAB) ((small_semantics (M := M) env 1 2).mp hB))

theorem image_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence imageSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hr him hJ
  exact (small_semantics (M := M) env 3 4).mpr (small_image hM
    ((permutation_semantics (M := M) env 0 1).mp hr)
    ((ForcingStabilizerTransport.image_semantics (M := M) env 1 2 3).mp him)
    ((small_semantics (M := M) env 2 4).mp hJ))

theorem subset_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence subsetSentence) :=
  ModelTransfer.derives (fun _ hM => subset_models hM)

theorem image_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence imageSentence) :=
  ModelTransfer.derives (fun _ hM => image_models hM)

end PPAC.Migration.ForcingSupportSize
