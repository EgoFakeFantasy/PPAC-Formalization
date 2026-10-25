/- Pinned Diagrams.Diagram.permute, permute_one, permute_mul and
permute_inv_permute. Consumer: ProductForcing.permuteOrderIso, then
ProductNames.actionHom. A diagram is the entire internal injection D -> I.
Reuse native compositionFunction and existing graph AST; no new function
constructor, monoid axiom, rank cutoff, or external choice of graph values. -/
import PPAC.Migration.ForcingSupportSize

namespace PPAC.Migration.ForcingDiagramAction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingConditionGraphs
open ForcingSupportSize (Injection native_mapsTo injection_semantics)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The donor's exact composition equation is the source pointwise permute_apply. -/
theorem exists_permute (hM : FirstOrder.Theory.Models M nativeZF)
    {D I pi r : M.Carrier .set} (hp : Permutation I pi) (hr : Injection D I r) :
    ∃ s, Injection D I s ∧ CompositionGraph D pi r s := by
  obtain ⟨s, hs, he⟩ := SetTheory.ZF.exists_compositionFunction
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM)
    ((native_mapsTo hM D I r).mp hr.1) ((native_endomap hM I pi).mp hp.1)
  refine ⟨s, ⟨(native_mapsTo hM D I s).mpr hs, ?_⟩, he⟩
  intro x y z hx hy
  obtain ⟨_, a, hxa, haz⟩ := (he x z).mp hx
  obtain ⟨_, b, hyb, hbz⟩ := (he y z).mp hy
  have hab := hp.2.1 a b z haz hbz
  exact hr.2 x y a hxa (hab ▸ hyb)

/-- Uniqueness is existing native relation extensionality, not a new graph kernel. -/
theorem unique (hM : FirstOrder.Theory.Models M nativeZF)
    {D I pi r s t : M.Carrier .set} (hs : Injection D I s) (ht : Injection D I t)
    (hps : CompositionGraph D pi r s) (hpt : CompositionGraph D pi r t) : s = t := by
  exact SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((native_mapsTo hM D I s).mp hs.1).1.1 ((native_mapsTo hM D I t).mp ht.1).1.1
    (fun x y => (hps x y).trans (hpt x y).symm)

theorem permute_one (hM : FirstOrder.Theory.Models M nativeZF)
    {D I e r s : M.Carrier .set} (he : IdentityGraph I e)
    (hr : Injection D I r) (hs : Injection D I s) (ha : CompositionGraph D e r s) : s = r := by
  apply unique hM hs hr ha
  intro x y
  constructor
  · intro hxy
    exact ⟨function_input hr.1.1 hxy, y, hxy, (he y y).mpr ⟨hr.1.2 x y hxy, rfl⟩⟩
  · rintro ⟨_, z, hxz, hzy⟩
    exact ((he z y).mp hzy).2 ▸ hxz

/-- Exact multiplication order of source permute (pi * sigma) r. -/
theorem permute_mul (hM : FirstOrder.Theory.Models M nativeZF)
    {D I pi sigma product r s t v : M.Carrier .set}
    (hr : Injection D I r) (ht : Injection D I t) (hv : Injection D I v)
    (hmul : CompositionGraph I pi sigma product)
    (hfirst : CompositionGraph D sigma r s) (hsecond : CompositionGraph D pi s t)
    (hproduct : CompositionGraph D product r v) : v = t := by
  apply unique hM hv ht hproduct
  intro x z
  constructor
  · intro hxz
    obtain ⟨hx, y, hxy, hyz⟩ := (hsecond x z).mp hxz
    obtain ⟨_, a, hxa, hay⟩ := (hfirst x y).mp hxy
    exact ⟨hx, a, hxa, (hmul a z).mpr ⟨hr.1.2 x a hxa, y, hay, hyz⟩⟩
  · rintro ⟨hx, a, hxa, haz⟩
    obtain ⟨_, y, hay, hyz⟩ := (hmul a z).mp haz
    exact (hsecond x z).mpr ⟨hx, y, (hfirst x y).mpr ⟨hx, a, hxa, hay⟩, hyz⟩

theorem permute_inv_permute (hM : FirstOrder.Theory.Models M nativeZF)
    {D I pi inv r s t : M.Carrier .set} (hp : Permutation I pi)
    (hr : Injection D I r) (ht : Injection D I t) (hi : InverseGraph pi inv)
    (hfirst : CompositionGraph D pi r s) (hsecond : CompositionGraph D inv s t) : t = r := by
  apply unique hM ht hr hsecond
  intro x z
  constructor
  · intro hxz
    obtain ⟨y, hzy, _⟩ := hp.1.1.2 z (hr.1.2 x z hxz)
    have hx := function_input hr.1.1 hxz
    exact ⟨hx, y, (hfirst x y).mpr ⟨hx, z, hxz, hzy⟩, (hi z y).mp hzy⟩
  · rintro ⟨_, y, hxy, hyz⟩
    obtain ⟨_, a, hxa, hay⟩ := (hfirst x y).mp hxy
    exact hp.2.1 a z y hay ((hi z y).mpr hyz) ▸ hxa

def existenceSentence : Source.Sentence :=
  ((permutation (1 : Fin 4) 2).imp ((Source.SetLanguage.injection 3 0 1).imp
    (.ex ((Source.SetLanguage.injection (Fin.last 4) (0 : Fin 4).castSucc (1 : Fin 4).castSucc).conj
      (compositionGraph (0 : Fin 4).castSucc (2 : Fin 4).castSucc (3 : Fin 4).castSucc (Fin.last 4)))))).close

def identitySentence : Source.Sentence :=
  ((identityGraph (1 : Fin 5) 2).imp ((Source.SetLanguage.injection 3 0 1).imp
    ((Source.SetLanguage.injection 4 0 1).imp ((compositionGraph 0 2 3 4).imp (.equal 4 3))))).close

def multiplicationSentence : Source.Sentence :=
  ((Source.SetLanguage.injection (5 : Fin 9) 0 1).imp ((Source.SetLanguage.injection 7 0 1).imp
    ((Source.SetLanguage.injection 8 0 1).imp ((compositionGraph 1 2 3 4).imp
      ((compositionGraph 0 3 5 6).imp ((compositionGraph 0 2 6 7).imp
        ((compositionGraph 0 4 5 8).imp (.equal 8 7)))))))).close

def inverseSentence : Source.Sentence :=
  ((permutation (1 : Fin 7) 2).imp ((Source.SetLanguage.injection 4 0 1).imp
    ((Source.SetLanguage.injection 6 0 1).imp ((inverseGraph 2 3).imp
      ((compositionGraph 0 2 4 5).imp ((compositionGraph 0 3 5 6).imp (.equal 6 4))))))).close

theorem existence_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence existenceSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp hr
  obtain ⟨s, hs, he⟩ := exists_permute hM
    ((permutation_semantics (M := M) env 1 2).mp hp) ((injection_semantics (M := M) env 3 0 1).mp hr)
  refine ⟨s, ?_, ?_⟩
  · apply (injection_semantics (M := M) (Fin.lastCases s env) (Fin.last 4)
      (0 : Fin 4).castSucc (1 : Fin 4).castSucc).mpr
    simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using hs
  · apply (compositionGraph_semantics (M := M) (Fin.lastCases s env)
      (0 : Fin 4).castSucc (2 : Fin 4).castSucc (3 : Fin 4).castSucc (Fin.last 4)).mpr
    simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using he

theorem identity_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence identitySentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env he hr hs ha
  exact permute_one hM ((identityGraph_semantics (M := M) env 1 2).mp he)
    ((injection_semantics (M := M) env 3 0 1).mp hr) ((injection_semantics (M := M) env 4 0 1).mp hs)
    ((compositionGraph_semantics (M := M) env 0 2 3 4).mp ha)

theorem multiplication_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence multiplicationSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hr ht hv hm hf hs hp
  exact permute_mul hM ((injection_semantics (M := M) env 5 0 1).mp hr)
    ((injection_semantics (M := M) env 7 0 1).mp ht) ((injection_semantics (M := M) env 8 0 1).mp hv)
    ((compositionGraph_semantics (M := M) env 1 2 3 4).mp hm)
    ((compositionGraph_semantics (M := M) env 0 3 5 6).mp hf)
    ((compositionGraph_semantics (M := M) env 0 2 6 7).mp hs)
    ((compositionGraph_semantics (M := M) env 0 4 5 8).mp hp)

theorem inverse_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence inverseSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp hr ht hi hf hs
  exact permute_inv_permute hM ((permutation_semantics (M := M) env 1 2).mp hp)
    ((injection_semantics (M := M) env 4 0 1).mp hr) ((injection_semantics (M := M) env 6 0 1).mp ht)
    ((inverseGraph_semantics (M := M) env 2 3).mp hi)
    ((compositionGraph_semantics (M := M) env 0 2 4 5).mp hf)
    ((compositionGraph_semantics (M := M) env 0 3 5 6).mp hs)

theorem existence_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence existenceSentence) :=
  ModelTransfer.derives (fun _ hM => existence_models hM)
theorem identity_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence identitySentence) :=
  ModelTransfer.derives (fun _ hM => identity_models hM)
theorem multiplication_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence multiplicationSentence) :=
  ModelTransfer.derives (fun _ hM => multiplication_models hM)
theorem inverse_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence inverseSentence) :=
  ModelTransfer.derives (fun _ hM => inverse_models hM)

end PPAC.Migration.ForcingDiagramAction
