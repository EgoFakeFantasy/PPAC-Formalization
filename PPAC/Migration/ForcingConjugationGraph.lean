/- Pinned SupportFilter.conjugate_fix/conjugate_mem use the actual map
s |-> r * s * r^-1 on Equiv.Perm I. Construct its internal set graph using
YesMetaZFC's completed definable-function constructor, not an assumed map. -/
import PPAC.Migration.ForcingLabelConjugacy

namespace PPAC.Migration.ForcingConjugationGraph
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open Source.SetLanguage (args3)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingConditionGraphs
open ForcingNameConjugacy (Conjugate conjugate)
open ForcingLabelPermutations (Carrier carrier Fixing fixing)
open ForcingStabilizerTransport (Image image)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Reuse the donor relation-extensionality theorem, with the existing graph bridge. -/
theorem endomap_ext (hM : FirstOrder.Theory.Models M nativeZF) {I s t : M.Carrier .set}
    (hs : Endomap I s) (ht : Endomap I t)
    (he : ∀ x y, PureKuratowski.PairMember M x y s ↔ PureKuratowski.PairMember M x y t) : s = t :=
  SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((native_endomap hM I s).mp hs).1.1 ((native_endomap hM I t).mp ht).1.1 he

/-- Exact coordinate equation for conjugation; every value is an internal graph edge. -/
theorem edges {I r i s t : M.Carrier .set} (hr : Endomap I r) (hri : InverseGraph r i)
    (hc : Conjugate I r i s t) (x y : M.Carrier .set) :
    PureKuratowski.PairMember M x y t ↔ ∃ a b,
      PureKuratowski.PairMember M a x r ∧ PureKuratowski.PairMember M b y r ∧
        PureKuratowski.PairMember M a b s := by
  obtain ⟨mid,_,hsi,hrm⟩ := hc
  constructor
  · intro he
    obtain ⟨_,b,hxb,hby⟩ := (hrm x y).mp he
    obtain ⟨_,a,hxa,hab⟩ := (hsi x b).mp hxb
    exact ⟨a,b,(hri a x).mpr hxa,hby,hab⟩
  · rintro ⟨a,b,hax,hby,hab⟩
    have hx := hr.2 a x hax
    exact (hrm x y).mpr ⟨hx,b,(hsi x b).mpr ⟨hx,a,(hri a x).mp hax,hab⟩,hby⟩

theorem unique (hM : FirstOrder.Theory.Models M nativeZF) {I r i s t u : M.Carrier .set}
    (hr : Endomap I r) (hri : InverseGraph r i) (ht : Endomap I t) (hu : Endomap I u)
    (hc : Conjugate I r i s t) (hd : Conjugate I r i s u) : t = u :=
  endomap_ext hM ht hu (fun x y => (edges hr hri hc x y).trans (edges hr hri hd x y).symm)

/-- Inverse conjugation is obtained from existing composition graphs, then proved exact. -/
theorem reverse (hM : FirstOrder.Theory.Models M nativeZF) {I r i s t : M.Carrier .set}
    (hr : Permutation I r) (hi : Permutation I i) (hri : InverseGraph r i)
    (hs : Permutation I s) (ht : Permutation I t) (hc : Conjugate I r i s t) : Conjugate I i r t s := by
  have hir : InverseGraph i r := fun x y => (hri y x).symm
  obtain ⟨u,hu,hcu⟩ := ForcingNameConjugacy.exists_conjugate hM hi hr ht
  have heq : u = s := by
    apply endomap_ext hM hu.1 hs.1
    intro x y
    constructor
    · intro hxy
      obtain ⟨a,b,hax,hby,hab⟩ := (edges hi.1 hir hcu x y).mp hxy
      obtain ⟨c,d,hca,hdb,hcd⟩ := (edges hr.1 hri hc a b).mp hab
      have hcEq := hr.2.1 c x a hca ((hri x a).mpr hax)
      have hdEq := hr.2.1 d y b hdb ((hri y b).mpr hby)
      simpa only [hcEq,hdEq] using hcd
    · intro hxy
      obtain ⟨a,hxa,_⟩ := hr.1.1.2 x (function_input hs.1.1 hxy)
      obtain ⟨b,hyb,_⟩ := hr.1.1.2 y (hs.1.2 x y hxy)
      exact (edges hi.1 hir hcu x y).mpr ⟨a,b,(hri x a).mp hxa,(hri y b).mp hyb,
        (edges hr.1 hri hc a b).mpr ⟨x,y,hxa,hyb,hxy⟩⟩
  exact heq ▸ hcu

theorem injective (hM : FirstOrder.Theory.Models M nativeZF) {I r i s t u : M.Carrier .set}
    (hr : Permutation I r) (hi : Permutation I i) (hri : InverseGraph r i)
    (hs : Permutation I s) (ht : Permutation I t) (hu : Permutation I u)
    (hc : Conjugate I r i s u) (hd : Conjugate I r i t u) : s = t :=
  unique hM hi.1 (fun x y => (hri y x).symm) hs.1 ht.1
    (reverse hM hr hi hri hs hu hc) (reverse hM hr hi hri ht hu hd)

def value {m : Nat} (I r i s t : Fin m) : Formula m :=
  (permutation I t).conj (conjugate I r i s t)

theorem value_semantics {m : Nat} (env : Fin m → M.Carrier .set) (I r i s t : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (value I r i s t) ↔
      Permutation (env I) (env t) ∧ Conjugate (env I) (env r) (env i) (env s) (env t) := by
  simp only [value,Formula.Realize,permutation_semantics (M := M),ForcingNameConjugacy.conjugate_semantics (M := M)]

def Graph (I G r i c : M.Carrier .set) : Prop :=
  ∀ s t, PureKuratowski.PairMember M s t c ↔
    (Definitional.Project.FirstOrderSemantics.reduct M).mem s G ∧
    (Definitional.Project.FirstOrderSemantics.reduct M).mem t G ∧ Conjugate I r i s t

def graph {m : Nat} (I G r i c : Fin m) : Formula m :=
  .all (.all ((Source.SetLanguage.edge c.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.mem (Fin.last m).castSucc G.castSucc.castSucc).conj
      ((Formula.mem (Fin.last (m+1)) G.castSucc.castSucc).conj
        (conjugate I.castSucc.castSucc r.castSucc.castSucc i.castSucc.castSucc
          (Fin.last m).castSucc (Fin.last (m+1)))))))

theorem graph_semantics {m : Nat} (env : Fin m → M.Carrier .set) (I G r i c : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (graph I G r i c) ↔
      Graph (env I) (env G) (env r) (env i) (env c) := by
  simp only [graph,Graph,Source.Formula.iff,Formula.Realize,KuratowskiZF.source_edge,
    ForcingNameConjugacy.conjugate_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h s t => ⟨(h s t).1,(h s t).2⟩,fun h s t => ⟨(h s t).mp,(h s t).mpr⟩⟩

/-- The completed donor constructor produces the graph; the inverse law proves surjectivity. -/
theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF) {I G r i : M.Carrier .set}
    (hG : Carrier I G) (hr : Permutation I r) (hi : Permutation I i) (hri : InverseGraph r i) :
    ∃ c, Permutation G c ∧ Graph I G r i c := by
  let params : Fin 3 → M.Carrier .set := Fin.lastCases i (Fin.lastCases r (fun _ => I))
  let query := value (0 : Fin 1).castSucc.castSucc.castSucc.castSucc (Fin.last 1).castSucc.castSucc.castSucc
    (Fin.last 2).castSucc.castSucc (Fin.last 3).castSucc (Fin.last 4)
  let env : SetTheory.Env (Definitional.Project.FirstOrderSemantics.reduct M) 3 :=
    { bound := fun j => params j.rev, free := fun _ => I }
  have hRel : ∀ s t, (ProjectSyntax.binary query).denote env s t ↔ Permutation I t ∧ Conjugate I r i s t := by
    intro s t
    rw [ForcingMapConditions.binary_semantics hM query params I s t]
    simpa only [ForcingMapConditions.MapRel,query,params,Fin.lastCases_last,Fin.lastCases_castSucc] using
      value_semantics (M := M) (Fin.lastCases t (Fin.lastCases s params))
        (0 : Fin 1).castSucc.castSucc.castSucc.castSucc (Fin.last 1).castSucc.castSucc.castSucc (Fin.last 2).castSucc.castSucc
          (Fin.last 3).castSucc (Fin.last 4)
  obtain ⟨c,hc,he⟩ := SetTheory.ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) (ProjectSyntax.binary query) env
    (source := G) (target := G)
    (fun s hs => by
      obtain ⟨t,ht,hct⟩ := ForcingNameConjugacy.exists_conjugate hM hr hi ((hG s).mp hs)
      exact ⟨t,(hRel s t).mpr ⟨ht,hct⟩⟩)
    (fun s _ t u ht hu => by
      have ht' := (hRel s t).mp ht
      have hu' := (hRel s u).mp hu
      exact unique hM hr.1 hri ht'.1.1 hu'.1.1 ht'.2 hu'.2)
    (fun s t _ ht => (hG t).mpr ((hRel s t).mp ht).1)
  have hgraph : Graph I G r i c := by
    intro s t
    exact (he s t).trans (and_congr Iff.rfl ((hRel s t).trans (and_congr (hG t).symm Iff.rfl)))
  refine ⟨c,⟨(native_endomap hM G c).mpr hc,?_,?_⟩,hgraph⟩
  · intro s t u hsu htu
    obtain ⟨hsG,huG,hsc⟩ := (hgraph s u).mp hsu
    obtain ⟨htG,_,htc⟩ := (hgraph t u).mp htu
    exact injective hM hr hi hri ((hG s).mp hsG) ((hG t).mp htG) ((hG u).mp huG) hsc htc
  · intro t ht
    have htP := (hG t).mp ht
    obtain ⟨s,hs,hst⟩ := ForcingNameConjugacy.exists_conjugate hM hi hr htP
    have hback := reverse hM hi hr (fun x y => (hri y x).symm) htP hs hst
    exact ⟨s,(hG s).mpr hs,(hgraph s t).mpr ⟨(hG s).mpr hs,ht,hback⟩⟩

theorem graph_unique (hM : FirstOrder.Theory.Models M nativeZF) {I G r i c d : M.Carrier .set}
    (hc : Endomap G c) (hd : Endomap G d) (hcg : Graph I G r i c) (hdg : Graph I G r i d) : c = d :=
  endomap_ext hM hc hd (fun s t => (hcg s t).trans (hdg s t).symm)

/-- Full set-image conclusion of the source conjugate_fix, on the constructed carrier. -/
theorem fixing_image {I G r i c J K S T : M.Carrier .set}
    (hG : Carrier I G) (hr : Permutation I r) (hi : Endomap I i) (hri : InverseGraph r i)
    (hc : Permutation G c) (hcg : Graph I G r i c) (hJK : Image r J K)
    (hJI : ∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x J →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem x I)
    (hS : Fixing G J S) (hT : Fixing G K T) : Image c S T := by
  intro t
  constructor
  · intro ht
    have htG := ((hT t).mp ht).1
    obtain ⟨s,hs,hst⟩ := hc.2.2 t htG
    have hconj := ((hcg s t).mp hst).2.2
    have hiff := ForcingLabelConjugacy.fixing_conjugate hG hr hi hri ((hG s).mp hs)
      ((hG t).mp htG) hconj hJK hJI hS hT
    exact ⟨s,hiff.mpr ht,hst⟩
  · rintro ⟨s,hs,hst⟩
    obtain ⟨hsG,htG,hconj⟩ := (hcg s t).mp hst
    exact (ForcingLabelConjugacy.fixing_conjugate hG hr hi hri ((hG s).mp hsG)
      ((hG t).mp htG) hconj hJK hJI hS hT).mp hs

theorem identity_covariance {I r i e t : M.Carrier .set} (hr : Permutation I r)
    (hri : InverseGraph r i) (he : IdentityGraph I e) (hc : Conjugate I r i e t) : IdentityGraph I t := by
  intro x y
  rw [edges hr.1 hri hc x y]
  constructor
  · rintro ⟨a,b,hax,hby,hab⟩
    have habEq := ((he a b).mp hab).2
    subst b
    exact ⟨hr.1.2 a x hax,function_unique hr.1.1 hax hby⟩
  · rintro ⟨hx,rfl⟩
    obtain ⟨a,ha,hax⟩ := hr.2.2 x hx
    exact ⟨a,a,hax,hax,(he a a).mpr ⟨ha,rfl⟩⟩

theorem inverse_covariance {I r i s t a b : M.Carrier .set} (hr : Endomap I r)
    (hri : InverseGraph r i) (hc : Conjugate I r i s t) (hd : Conjugate I r i a b)
    (hsa : InverseGraph s a) : InverseGraph t b := by
  intro x y
  rw [edges hr hri hc x y,edges hr hri hd y x]
  exact ⟨fun ⟨u,v,hux,hvy,huv⟩ => ⟨v,u,hvy,hux,(hsa u v).mp huv⟩,
    fun ⟨v,u,hvy,hux,hvu⟩ => ⟨u,v,hux,hvy,(hsa u v).mpr hvu⟩⟩

theorem composition_covariance {I r i s t a b u v : M.Carrier .set} (hr : Permutation I r)
    (hri : InverseGraph r i) (hs : Endomap I s)
    (hc : Conjugate I r i s t) (hd : Conjugate I r i a b) (hu : Conjugate I r i u v)
    (hmul : CompositionGraph I s a u) : CompositionGraph I t b v := by
  intro x z
  constructor
  · intro hxz
    obtain ⟨j,k,hjx,hkz,hjk⟩ := (edges hr.1 hri hu x z).mp hxz
    obtain ⟨_,l,hjl,hlk⟩ := (hmul j k).mp hjk
    obtain ⟨y,hly,_⟩ := hr.1.1.2 l (function_input hs.1 hlk)
    exact ⟨hr.1.2 j x hjx,y,(edges hr.1 hri hd x y).mpr ⟨j,l,hjx,hly,hjl⟩,
      (edges hr.1 hri hc y z).mpr ⟨l,k,hly,hkz,hlk⟩⟩
  · rintro ⟨_,y,hxy,hyz⟩
    obtain ⟨j,k,hjx,hky,hjk⟩ := (edges hr.1 hri hd x y).mp hxy
    obtain ⟨l,m,hly,hmz,hlm⟩ := (edges hr.1 hri hc y z).mp hyz
    have hkl := hr.2.1 k l y hky hly
    subst l
    exact (edges hr.1 hri hu x z).mpr ⟨j,m,hjx,hmz,
      (hmul j m).mpr ⟨function_input hr.1.1 hjx,k,hjk,hlm⟩⟩

/-- The source subgroup condition, with operations represented by their actual graphs. -/
def Subgroup (I G K : M.Carrier .set) : Prop :=
  (∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x K →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem x G) ∧
  (∃ e, (Definitional.Project.FirstOrderSemantics.reduct M).mem e K ∧ IdentityGraph I e) ∧
  (∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r K →
    ∃ i, (Definitional.Project.FirstOrderSemantics.reduct M).mem i K ∧ InverseGraph r i) ∧
  (∀ r s, (Definitional.Project.FirstOrderSemantics.reduct M).mem r K →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem s K →
    ∃ t, (Definitional.Project.FirstOrderSemantics.reduct M).mem t K ∧ CompositionGraph I r s t)

def subgroup {m : Nat} (I G K : Fin m) : Formula m :=
  (Source.SetLanguage.subset K G).conj (ForcingLabelPermutations.closed I K)

theorem subgroup_semantics {m : Nat} (env : Fin m → M.Carrier .set) (I G K : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (subgroup I G K) ↔
      Subgroup (env I) (env G) (env K) := by
  simp only [subgroup,Subgroup,Formula.Realize,ForcingLabelPermutations.subset_semantics (M := M),
    ForcingLabelPermutations.closed_semantics (M := M)]

theorem fixing_subgroup (hM : FirstOrder.Theory.Models M nativeZF) {I G J K : M.Carrier .set}
    (hG : Carrier I G) (hK : Fixing G J K)
    (hJI : ∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x J →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem x I) : Subgroup I G K :=
  ⟨fun x hx => ((hK x).mp hx).1,ForcingLabelPermutations.fixing_closed hM hG hK hJI⟩

/-- Conjugation maps subgroups to subgroups, without strengthening filter upward closure. -/
theorem subgroup_image {I G r i c K L : M.Carrier .set}
    (hG : Carrier I G) (hr : Permutation I r) (hri : InverseGraph r i)
    (hc : Permutation G c) (hcg : Graph I G r i c) (hK : Subgroup I G K) (hKL : Image c K L) :
    Subgroup I G L := by
  obtain ⟨hKG,⟨e,he,heId⟩,hInv,hMul⟩ := hK
  refine ⟨?_,?_,?_,?_⟩
  · intro t ht
    obtain ⟨s,_,hst⟩ := (hKL t).mp ht
    exact hc.1.2 s t hst
  · obtain ⟨t,het,_⟩ := hc.1.1.2 e (hKG e he)
    exact ⟨t,(hKL t).mpr ⟨e,he,het⟩,identity_covariance hr hri heId ((hcg e t).mp het).2.2⟩
  · intro t ht
    obtain ⟨s,hs,hst⟩ := (hKL t).mp ht
    obtain ⟨a,ha,hsa⟩ := hInv s hs
    obtain ⟨b,hab,_⟩ := hc.1.1.2 a (hKG a ha)
    exact ⟨b,(hKL b).mpr ⟨a,ha,hab⟩,inverse_covariance hr.1 hri
      ((hcg s t).mp hst).2.2 ((hcg a b).mp hab).2.2 hsa⟩
  · intro t b ht hb
    obtain ⟨s,hs,hst⟩ := (hKL t).mp ht
    obtain ⟨a,ha,hab⟩ := (hKL b).mp hb
    obtain ⟨u,hu,hmul⟩ := hMul s a hs ha
    obtain ⟨v,huv,_⟩ := hc.1.1.2 u (hKG u hu)
    exact ⟨v,(hKL v).mpr ⟨u,hu,huv⟩,composition_covariance hr hri ((hG s).mp (hKG s hs)).1
      ((hcg s t).mp hst).2.2 ((hcg a b).mp hab).2.2 ((hcg u v).mp huv).2.2 hmul⟩

def subgroupSentence : Source.Sentence := ((carrier (0 : Fin 7) 1).imp ((permutation 0 2).imp
  ((inverseGraph 2 3).imp ((permutation 1 4).imp ((graph 0 1 2 3 4).imp
    ((subgroup 0 1 5).imp ((image 4 5 6).imp (subgroup 0 1 6)))))))).close

theorem subgroup_models (_hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence subgroupSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hG hr hri hc hcg hK hKL
  apply (subgroup_semantics (M := M) env 0 1 6).mpr
  exact subgroup_image ((ForcingLabelPermutations.carrier_semantics (M := M) env 0 1).mp hG)
    ((permutation_semantics (M := M) env 0 2).mp hr) ((inverseGraph_semantics (M := M) env 2 3).mp hri)
    ((permutation_semantics (M := M) env 1 4).mp hc) ((graph_semantics (M := M) env 0 1 2 3 4).mp hcg)
    ((subgroup_semantics (M := M) env 0 1 5).mp hK)
    ((ForcingStabilizerTransport.image_semantics (M := M) env 4 5 6).mp hKL)

theorem subgroup_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence subgroupSentence) :=
  ModelTransfer.derives (fun _ hM => subgroup_models hM)

def graphSentence : Source.Sentence := ((carrier (0 : Fin 4) 1).imp ((permutation 0 2).imp
  ((permutation 0 3).imp ((inverseGraph 2 3).imp (.ex
    ((permutation (1 : Fin 4).castSucc (Fin.last 4)).conj
      (graph (0 : Fin 4).castSucc (1 : Fin 4).castSucc (2 : Fin 4).castSucc (3 : Fin 4).castSucc (Fin.last 4)))))))).close

def imageSentence : Source.Sentence := ((carrier (0 : Fin 9) 1).imp ((permutation 0 2).imp
  ((endomap 0 3).imp ((inverseGraph 2 3).imp ((permutation 1 4).imp ((graph 0 1 2 3 4).imp
    ((image 2 5 6).imp ((Source.SetLanguage.subset 5 0).imp ((fixing 1 5 7).imp
      ((fixing 1 6 8).imp (image 4 7 8))))))))))).close

theorem graph_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence graphSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hG hr hi hri
  obtain ⟨c,hc,hcg⟩ := exists_graph hM ((ForcingLabelPermutations.carrier_semantics (M := M) env 0 1).mp hG)
    ((permutation_semantics (M := M) env 0 2).mp hr) ((permutation_semantics (M := M) env 0 3).mp hi)
    ((inverseGraph_semantics (M := M) env 2 3).mp hri)
  refine ⟨c,?_,?_⟩
  · apply (permutation_semantics (M := M) (Fin.lastCases c env) (1 : Fin 4).castSucc (Fin.last 4)).mpr
    simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hc
  · apply (graph_semantics (M := M) (Fin.lastCases c env) (0 : Fin 4).castSucc (1 : Fin 4).castSucc
      (2 : Fin 4).castSucc (3 : Fin 4).castSucc (Fin.last 4)).mpr
    simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hcg

theorem image_models (_hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence imageSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hG hr hi hri hc hcg hJK hJI hS hT
  apply (ForcingStabilizerTransport.image_semantics (M := M) env 4 7 8).mpr
  exact fixing_image ((ForcingLabelPermutations.carrier_semantics (M := M) env 0 1).mp hG)
    ((permutation_semantics (M := M) env 0 2).mp hr) ((endomap_semantics (M := M) env 0 3).mp hi)
    ((inverseGraph_semantics (M := M) env 2 3).mp hri) ((permutation_semantics (M := M) env 1 4).mp hc)
    ((graph_semantics (M := M) env 0 1 2 3 4).mp hcg)
    ((ForcingStabilizerTransport.image_semantics (M := M) env 2 5 6).mp hJK)
    ((ForcingLabelPermutations.subset_semantics (M := M) env 5 0).mp hJI)
    ((ForcingLabelPermutations.fixing_semantics (M := M) env 1 5 7).mp hS)
    ((ForcingLabelPermutations.fixing_semantics (M := M) env 1 6 8).mp hT)

theorem graph_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence graphSentence) :=
  ModelTransfer.derives (fun _ hM => graph_models hM)

theorem image_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence imageSentence) :=
  ModelTransfer.derives (fun _ hM => image_models hM)

end PPAC.Migration.ForcingConjugationGraph
