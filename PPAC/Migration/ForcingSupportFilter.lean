/- Pinned SupportFilter.subgroupFilter/top_mem/upward_closed/conjugate_mem.
This is the actual family of subgroups containing the pointwise stabilizer
of an internally small label set, not a predicate assuming forcing results.
Intersection closure, which needs the infinite support bound, is separate. -/
import PPAC.Migration.ForcingSupportSize

namespace PPAC.Migration.ForcingSupportFilter
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingConditionGraphs
open ForcingLabelPermutations (Carrier carrier Fixing fixing)
open ForcingConjugationGraph (Subgroup subgroup Graph graph)
open ForcingStabilizerTransport (Image image NormalImage normalImage)
open ForcingSupportSize (Small small)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Supported (I G mu K : M.Carrier .set) : Prop := Subgroup I G K ∧ ∃ J S,
  (∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x J →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem x I) ∧ Small J mu ∧ Fixing G J S ∧
  ∀ s, (Definitional.Project.FirstOrderSemantics.reduct M).mem s S →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem s K

def supported {m : Nat} (I G mu K : Fin m) : Formula m := (subgroup I G K).conj (.ex (.ex
  ((Source.SetLanguage.subset (Fin.last m).castSucc I.castSucc.castSucc).conj
    ((small (Fin.last m).castSucc mu.castSucc.castSucc).conj
      ((fixing G.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
        (Source.SetLanguage.subset (Fin.last (m+1)) K.castSucc.castSucc))))))

theorem supported_semantics {m : Nat} (env : Fin m → M.Carrier .set) (I G mu K : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (supported I G mu K) ↔
      Supported (env I) (env G) (env mu) (env K) := by
  simp only [supported,Supported,Formula.Realize,ForcingConjugationGraph.subgroup_semantics (M := M),
    ForcingLabelPermutations.subset_semantics (M := M),ForcingSupportSize.small_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def Filter (I G mu F : M.Carrier .set) : Prop :=
  ∀ K, (Definitional.Project.FirstOrderSemantics.reduct M).mem K F ↔ Supported I G mu K

def filter {m : Nat} (I G mu F : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) F.castSucc).iff
    (supported I.castSucc G.castSucc mu.castSucc (Fin.last m)))

theorem filter_semantics {m : Nat} (env : Fin m → M.Carrier .set) (I G mu F : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (filter I G mu F) ↔
      Filter (env I) (env G) (env mu) (env F) := by
  simp only [filter,Filter,Source.Formula.iff,Formula.Realize,supported_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h K => ⟨(h K).1,(h K).2⟩,fun h K => ⟨(h K).mp,(h K).mpr⟩⟩

theorem exists_filter (hM : FirstOrder.Theory.Models M nativeZF) (I G mu : M.Carrier .set) :
    ∃ F, Filter I G mu F := by
  obtain ⟨power,hPower⟩ := SetTheory.ZF.exists_powerSet (ModelTransfer.project_models_iff.mp hM) G
  let params : Fin 3 → M.Carrier .set := Fin.lastCases mu (Fin.lastCases G (fun _ => I))
  let query := supported (0 : Fin 1).castSucc.castSucc.castSucc (Fin.last 1).castSucc.castSucc
    (Fin.last 2).castSucc (Fin.last 3)
  have sep := (GodelDefOutput.separation_semantics (Definitional.Project.FirstOrderSemantics.reduct M).mem query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨F,hF⟩ := sep params power
  have hq : ∀ K, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases K params) query ↔ Supported I G mu K := by
    intro K
    simpa only [query,params,Fin.lastCases_last,Fin.lastCases_castSucc] using
      supported_semantics (M := M) (Fin.lastCases K params) (0 : Fin 1).castSucc.castSucc.castSucc
        (Fin.last 1).castSucc.castSucc (Fin.last 2).castSucc (Fin.last 3)
  refine ⟨F,fun K => ?_⟩
  exact ⟨fun h => (hq K).mp ((hF K).mp h).2,
    fun h => (hF K).mpr ⟨(hPower K).mpr h.1.1,(hq K).mpr h⟩⟩

theorem unique (hM : FirstOrder.Theory.Models M nativeZF) {I G mu F H : M.Carrier .set}
    (hF : Filter I G mu F) (hH : Filter I G mu H) : F = H :=
  (ModelTransfer.extensionality hM).eq_of_same_members F H (fun K => (hF K).trans (hH K).symm)

theorem top_subgroup (hM : FirstOrder.Theory.Models M nativeZF) {I G : M.Carrier .set}
    (hG : Carrier I G) : Subgroup I G G :=
  ⟨fun _ h => h,ForcingLabelPermutations.identity_mem hM hG,
    fun _ h => ForcingLabelPermutations.inverse_mem hM hG h,
    fun _ _ hr hs => ForcingLabelPermutations.composition_mem hM hG hr hs⟩

theorem top_supported (hM : FirstOrder.Theory.Models M nativeZF) {I G : M.Carrier .set}
    (hG : Carrier I G) (mu : M.Carrier .set) : Supported I G mu G := by
  obtain ⟨empty,he⟩ := SetTheory.KP.exists_empty (SetTheory.ZF.modelsKP (ModelTransfer.project_models_iff.mp hM))
  obtain ⟨S,hS⟩ := ForcingLabelPermutations.exists_fixing hM G empty
  exact ⟨top_subgroup hM hG,empty,S,fun x hx => False.elim (he x hx),
    ForcingSupportSize.small_empty hM mu he,hS,fun s hs => ((hS s).mp hs).1⟩

theorem upward_supported {I G mu K L : M.Carrier .set} (hK : Supported I G mu K)
    (hL : Subgroup I G L)
    (hKL : ∀ s, (Definitional.Project.FirstOrderSemantics.reduct M).mem s K →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem s L) : Supported I G mu L := by
  obtain ⟨_,J,S,hJI,hJ,hS,hSK⟩ := hK
  exact ⟨hL,J,S,hJI,hJ,hS,fun s hs => hKL s (hSK s hs)⟩

theorem conjugate_supported (hM : FirstOrder.Theory.Models M nativeZF) {I G mu r i c K L : M.Carrier .set}
    (hG : Carrier I G) (hr : Permutation I r) (hi : Endomap I i) (hri : InverseGraph r i)
    (hc : Permutation G c) (hcg : Graph I G r i c) (hK : Supported I G mu K) (hKL : Image c K L) :
    Supported I G mu L := by
  obtain ⟨hKSub,J,S,hJI,hJ,hS,hSK⟩ := hK
  obtain ⟨J',hJJ',hJ'I⟩ := ForcingLabelConjugacy.exists_image hM hr.1 (J := J)
  obtain ⟨S',hS'⟩ := ForcingLabelPermutations.exists_fixing hM G J'
  have him := ForcingConjugationGraph.fixing_image hG hr hi hri hc hcg hJJ' hJI hS hS'
  refine ⟨ForcingConjugationGraph.subgroup_image hG hr hri hc hcg hKSub hKL,J',S',hJ'I,
    ForcingSupportSize.small_image hM hr hJJ' hJ,hS',?_⟩
  intro t ht
  obtain ⟨s,hs,hst⟩ := (him t).mp ht
  exact (hKL t).mpr ⟨s,hSK s hs,hst⟩

/-- The actual support-defined family supplies the formerly abstract normal-image clause. -/
theorem normal_image (hM : FirstOrder.Theory.Models M nativeZF) {I G mu F r i c : M.Carrier .set}
    (hG : Carrier I G) (hF : Filter I G mu F) (hr : Permutation I r) (hi : Endomap I i)
    (hri : InverseGraph r i) (hc : Permutation G c) (hcg : Graph I G r i c) : NormalImage F c :=
  fun K L hK hKL => (hF L).mpr (conjugate_supported hM hG hr hi hri hc hcg ((hF K).mp hK) hKL)

def existenceSentence : Source.Sentence := (Formula.ex (filter
  (0 : Fin 3).castSucc (1 : Fin 3).castSucc (2 : Fin 3).castSucc (Fin.last 3))).close

def topSentence : Source.Sentence := ((carrier (0 : Fin 4) 1).imp ((filter 0 1 2 3).imp (.mem 1 3))).close

def upwardSentence : Source.Sentence := ((filter (0 : Fin 6) 1 2 3).imp ((Formula.mem 4 3).imp
  ((subgroup 0 1 5).imp ((Source.SetLanguage.subset 4 5).imp (.mem 5 3))))).close

def normalImageSentence : Source.Sentence := ((carrier (0 : Fin 7) 1).imp ((filter 0 1 2 3).imp
  ((permutation 0 4).imp ((endomap 0 5).imp ((inverseGraph 4 5).imp
    ((permutation 1 6).imp ((graph 0 1 4 5 6).imp (normalImage 3 6)))))))).close

theorem existence_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence existenceSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env
  obtain ⟨F,hF⟩ := exists_filter hM (env 0) (env 1) (env 2)
  refine ⟨F,?_⟩
  apply (filter_semantics (M := M) (Fin.lastCases F env)
    (0 : Fin 3).castSucc (1 : Fin 3).castSucc (2 : Fin 3).castSucc (Fin.last 3)).mpr
  simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hF

theorem top_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence topSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hG hF
  exact (((filter_semantics (M := M) env 0 1 2 3).mp hF) (env 1)).mpr
    (top_supported hM ((ForcingLabelPermutations.carrier_semantics (M := M) env 0 1).mp hG) (env 2))

theorem upward_models (_hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence upwardSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hF hK hL hKL
  have hF' := (filter_semantics (M := M) env 0 1 2 3).mp hF
  exact (hF' (env 5)).mpr (upward_supported ((hF' (env 4)).mp hK)
    ((ForcingConjugationGraph.subgroup_semantics (M := M) env 0 1 5).mp hL)
    ((ForcingLabelPermutations.subset_semantics (M := M) env 4 5).mp hKL))

theorem normalImage_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence normalImageSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hG hF hr hi hri hc hcg
  exact (ForcingStabilizerTransport.normalImage_semantics (M := M) env 3 6).mpr
    (normal_image hM ((ForcingLabelPermutations.carrier_semantics (M := M) env 0 1).mp hG)
      ((filter_semantics (M := M) env 0 1 2 3).mp hF) ((permutation_semantics (M := M) env 0 4).mp hr)
      ((endomap_semantics (M := M) env 0 5).mp hi) ((inverseGraph_semantics (M := M) env 4 5).mp hri)
      ((permutation_semantics (M := M) env 1 6).mp hc) ((ForcingConjugationGraph.graph_semantics (M := M) env 0 1 4 5 6).mp hcg))

theorem existence_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence existenceSentence) :=
  ModelTransfer.derives (fun _ hM => existence_models hM)
theorem top_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence topSentence) :=
  ModelTransfer.derives (fun _ hM => top_models hM)
theorem upward_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence upwardSentence) :=
  ModelTransfer.derives (fun _ hM => upward_models hM)
theorem normalImage_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence normalImageSentence) :=
  ModelTransfer.derives (fun _ hM => normalImage_models hM)

end PPAC.Migration.ForcingSupportFilter
