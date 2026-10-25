/- Pinned CohenForcing.Condition.permuteOrderIso on the entire internal
condition carrier. Its inverse is constructed from the inverse coordinate
permutation. Reverse-inclusion equivalence is inherited from exact images. -/
import PPAC.Migration.ForcingCohenConditions

namespace PPAC.Migration.ForcingCohenOrderAction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingConditionGraphs
open ForcingStabilizerTransport (Image image)
open ForcingCohenConditions (Carrier carrier Condition)
open ForcingCohenCoordinates (Cartesian cartesian Graph graph)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem image_unique (hM : FirstOrder.Theory.Models M nativeZF) {g p q r : M.Carrier .set}
    (hq : Image g p q) (hr : Image g p r) : q = r :=
  (ModelTransfer.extensionality hM).eq_of_same_members q r (fun z => (hq z).trans (hr z).symm)

theorem reverse_image {S g inv p q : M.Carrier .set} (hg : Permutation S g) (hi : InverseGraph g inv)
    (hp : ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z p →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem z S) (him : Image g p q) : Image inv q p := by
  intro z
  constructor
  · intro hz
    obtain ⟨y, hzy, _⟩ := hg.1.1.2 z (hp z hz)
    exact ⟨y, (him y).mpr ⟨z, hz, hzy⟩, (hi z y).mp hzy⟩
  · rintro ⟨y, hy, hyz⟩
    obtain ⟨x, hx, hxy⟩ := (him y).mp hy
    exact hg.2.1 x z y hxy ((hi z y).mpr hyz) ▸ hx

def ActionGraph (X g a : M.Carrier .set) : Prop :=
  ∀ p q, PureKuratowski.PairMember M p q a ↔
    (Definitional.Project.FirstOrderSemantics.reduct M).mem p X ∧
    (Definitional.Project.FirstOrderSemantics.reduct M).mem q X ∧ Image g p q

def actionGraph {m : Nat} (X g a : Fin m) : Formula m :=
  .all (.all ((Source.SetLanguage.edge a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.mem (Fin.last m).castSucc X.castSucc.castSucc).conj
      ((Formula.mem (Fin.last (m+1)) X.castSucc.castSucc).conj
        (image g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))))))

theorem actionGraph_semantics {m : Nat} (env : Fin m → M.Carrier .set) (X g a : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (actionGraph X g a) ↔
      ActionGraph (env X) (env g) (env a) := by
  simp only [actionGraph, ActionGraph, Source.Formula.iff, Formula.Realize, KuratowskiZF.source_edge,
    ForcingStabilizerTransport.image_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]
  exact ⟨fun h p q => ⟨(h p q).1, (h p q).2⟩, fun h p q => ⟨(h p q).mp, (h p q).mpr⟩⟩

theorem exists_action (hM : FirstOrder.Theory.Models M nativeZF) {C B S w X f g : M.Carrier .set}
    (hS : Cartesian C B S) (hX : Carrier S w X) (hf : Permutation C f) (hg : Permutation S g)
    (hgraph : Graph S f g) : ∃ a, Permutation X a ∧ ActionGraph X g a := by
  let params := Source.SetLanguage.args2 X g
  let query := (Formula.mem (Fin.last 3) (0 : Fin 2).castSucc.castSucc).conj
    (image (1 : Fin 2).castSucc.castSucc (Fin.last 2).castSucc (Fin.last 3))
  let env : SetTheory.Env (Definitional.Project.FirstOrderSemantics.reduct M) 2 :=
    { bound := fun j => params j.rev, free := fun _ => X }
  have hRel : ∀ p q, (ProjectSyntax.binary query).denote env p q ↔
      (Definitional.Project.FirstOrderSemantics.reduct M).mem q X ∧ Image g p q := by
    intro p q
    rw [ForcingMapConditions.binary_semantics hM query params X p q]
    simp only [ForcingMapConditions.MapRel, query, Formula.Realize, ForcingStabilizerTransport.image_semantics (M := M),
      params, Fin.lastCases_last, Fin.lastCases_castSucc]
    rfl
  obtain ⟨a, ha, he⟩ := SetTheory.ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) (ProjectSyntax.binary query) env
    (source := X) (target := X)
    (fun p hp => by
      obtain ⟨q, him, hq⟩ := ForcingCohenConditions.exists_permute hM hf hg hgraph ((hX p).mp hp)
      exact ⟨q, (hRel p q).mpr ⟨(hX q).mpr hq, him⟩⟩)
    (fun p _ q r hq hr => image_unique hM ((hRel p q).mp hq).2 ((hRel p r).mp hr).2)
    (fun p q _ hq => ((hRel p q).mp hq).1)
  have hga : ActionGraph X g a := fun p q => (he p q).trans (and_congr Iff.rfl (hRel p q))
  refine ⟨a, ⟨(native_endomap hM X a).mpr ha, ?_, ?_⟩, hga⟩
  · intro p q r hpr hqr
    obtain ⟨hp, _, hpr⟩ := (hga p r).mp hpr
    obtain ⟨hq, _, hqr⟩ := (hga q r).mp hqr
    have hpq := (ForcingCohenConditions.image_subset_iff hg ((hX p).mp hp).1 hpr hqr).mp (fun _ h => h)
    have hqp := (ForcingCohenConditions.image_subset_iff hg ((hX q).mp hq).1 hqr hpr).mp (fun _ h => h)
    exact (ModelTransfer.extensionality hM).eq_of_same_members p q (fun z => ⟨hpq z, hqp z⟩)
  · intro q hq
    obtain ⟨fi, hfi, hf_inv⟩ := exists_inverse hM hf
    obtain ⟨gi, hgi, hgiGraph⟩ := ForcingCohenCoordinates.exists_lift hM hS hfi
    have hgi_inv := ForcingCohenCoordinates.inverse_graph hg.1 hgi.1 hf_inv hgraph hgiGraph
    obtain ⟨p, him, hp⟩ := ForcingCohenConditions.exists_permute hM hfi hgi hgiGraph ((hX q).mp hq)
    have hback := reverse_image hgi (fun x y => (hgi_inv y x).symm) ((hX q).mp hq).1 him
    exact ⟨p, (hX p).mpr hp, (hga p q).mpr ⟨(hX p).mpr hp, hq, hback⟩⟩

def OrderPreserving (a : M.Carrier .set) : Prop :=
  ∀ p q P Q, PureKuratowski.PairMember M p P a → PureKuratowski.PairMember M q Q a →
    ((∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z Q →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem z P) ↔
    (∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z q →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem z p))

def orderPreserving {m : Nat} (a : Fin m) : Formula m :=
  let up : Fin m → Fin (m+4) := fun i => i.castSucc.castSucc.castSucc.castSucc
  let p := (Fin.last m).castSucc.castSucc.castSucc
  let q := (Fin.last (m+1)).castSucc.castSucc
  let P := (Fin.last (m+2)).castSucc
  let Q := Fin.last (m+3)
  .all (.all (.all (.all ((Source.SetLanguage.edge (up a) p P).imp
    ((Source.SetLanguage.edge (up a) q Q).imp
      ((Source.SetLanguage.subset Q P).iff (Source.SetLanguage.subset q p)))))))

theorem orderPreserving_semantics {m : Nat} (env : Fin m → M.Carrier .set) (a : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (orderPreserving a) ↔
      OrderPreserving (env a) := by
  simp only [orderPreserving, OrderPreserving, Source.Formula.iff, Formula.Realize, KuratowskiZF.source_edge,
    ForcingLabelPermutations.subset_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]
  exact ⟨fun h p q P Q hp hq => ⟨(h p q P Q hp hq).1, (h p q P Q hp hq).2⟩,
    fun h p q P Q hp hq => ⟨(h p q P Q hp hq).mp, (h p q P Q hp hq).mpr⟩⟩

theorem graph_order {S w X g a : M.Carrier .set} (hX : Carrier S w X) (hg : Permutation S g)
    (hga : ActionGraph X g a) : OrderPreserving a := by
  intro p q P Q hp hq
  obtain ⟨_, _, hP⟩ := (hga p P).mp hp
  obtain ⟨hq, _, hQ⟩ := (hga q Q).mp hq
  exact ForcingCohenConditions.image_subset_iff hg ((hX q).mp hq).1 hQ hP

def constructionSentence : Source.Sentence :=
  ((cartesian (0 : Fin 7) 1 2).imp ((carrier 2 3 4).imp ((permutation 0 5).imp
    ((permutation 2 6).imp ((graph 2 5 6).imp (.ex
      ((permutation (4 : Fin 7).castSucc (Fin.last 7)).conj
        ((actionGraph (4 : Fin 7).castSucc (6 : Fin 7).castSucc (Fin.last 7)).conj
          (orderPreserving (Fin.last 7)))))))))).close

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence constructionSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hS hX hf hg hgraph
  have hX' := (ForcingCohenConditions.carrier_semantics (M := M) env 2 3 4).mp hX
  have hg' := (permutation_semantics (M := M) env 2 6).mp hg
  obtain ⟨a, ha, hga⟩ := exists_action hM ((ForcingCohenCoordinates.cartesian_semantics (M := M) env 0 1 2).mp hS)
    hX' ((permutation_semantics (M := M) env 0 5).mp hf) hg'
    ((ForcingCohenCoordinates.graph_semantics (M := M) env 2 5 6).mp hgraph)
  have ho := graph_order hX' hg' hga
  refine ⟨a, ?_, ?_, ?_⟩
  · apply (permutation_semantics (M := M) (Fin.lastCases a env) (4 : Fin 7).castSucc (Fin.last 7)).mpr
    simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using ha
  · apply (actionGraph_semantics (M := M) (Fin.lastCases a env)
      (4 : Fin 7).castSucc (6 : Fin 7).castSucc (Fin.last 7)).mpr
    simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using hga
  · apply (orderPreserving_semantics (M := M) (Fin.lastCases a env) (Fin.last 7)).mpr
    simpa only [Fin.lastCases_last] using ho

theorem construction_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence constructionSentence) :=
  ModelTransfer.derives (fun _ hM => construction_models hM)

/-- Discharge the product, carrier and coordinate-graph premises by their actual constructors. -/
theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF) (I K B w : M.Carrier .set)
    {pi : M.Carrier .set} (hp : Permutation I pi) :
    ∃ C S X f g a, Cartesian I K C ∧ Cartesian C B S ∧ Carrier S w X ∧
      Permutation C f ∧ Graph C pi f ∧ Permutation S g ∧ Graph S f g ∧
      Permutation X a ∧ ActionGraph X g a ∧ OrderPreserving a := by
  obtain ⟨C, S, f, g, hC, hS, hf, hfg, hg, hgg⟩ := ForcingCohenCoordinates.exists_coordinates hM I K B hp
  obtain ⟨X, hX⟩ := ForcingCohenConditions.exists_carrier hM S w
  obtain ⟨a, ha, hga⟩ := exists_action hM hS hX hf hg hgg
  exact ⟨C, S, X, f, g, a, hC, hS, hX, hf, hfg, hg, hgg, ha, hga, graph_order hX hg hga⟩

def assemblySentence : Source.Sentence :=
  ((permutation (0 : Fin 5) 4).imp (.ex (.ex (.ex (.ex (.ex (.ex ((cartesian (0 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (1 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 5).castSucc.castSucc.castSucc.castSucc.castSucc).conj
      ((cartesian (Fin.last 5).castSucc.castSucc.castSucc.castSucc.castSucc (2 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 6).castSucc.castSucc.castSucc.castSucc).conj
      ((carrier (Fin.last 6).castSucc.castSucc.castSucc.castSucc (3 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 7).castSucc.castSucc.castSucc).conj
      ((permutation (Fin.last 5).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 8).castSucc.castSucc).conj
      ((graph (Fin.last 5).castSucc.castSucc.castSucc.castSucc.castSucc (4 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 8).castSucc.castSucc).conj
      ((permutation (Fin.last 6).castSucc.castSucc.castSucc.castSucc (Fin.last 9).castSucc).conj
      ((graph (Fin.last 6).castSucc.castSucc.castSucc.castSucc (Fin.last 8).castSucc.castSucc (Fin.last 9).castSucc).conj
      ((permutation (Fin.last 7).castSucc.castSucc.castSucc (Fin.last 10)).conj
      ((actionGraph (Fin.last 7).castSucc.castSucc.castSucc (Fin.last 9).castSucc (Fin.last 10)).conj
      (orderPreserving (Fin.last 10)))))))))))))))))).close

theorem assembly_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence assemblySentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp
  obtain ⟨C, S, X, f, g, a, hC, hS, hX, hf, hfg, hg, hgg, ha, hga, ho⟩ :=
    exists_system hM (env 0) (env 1) (env 2) (env 3) ((permutation_semantics (M := M) env 0 4).mp hp)
  let v : Fin 11 → M.Carrier .set := Fin.lastCases a (Fin.lastCases g (Fin.lastCases f
    (Fin.lastCases X (Fin.lastCases S (Fin.lastCases C env)))))
  refine ⟨C, S, X, f, g, a, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (ForcingCohenCoordinates.cartesian_semantics (M := M) v (0 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (1 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 5).castSucc.castSucc.castSucc.castSucc.castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hC
  · apply (ForcingCohenCoordinates.cartesian_semantics (M := M) v (Fin.last 5).castSucc.castSucc.castSucc.castSucc.castSucc (2 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 6).castSucc.castSucc.castSucc.castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hS
  · apply (ForcingCohenConditions.carrier_semantics (M := M) v (Fin.last 6).castSucc.castSucc.castSucc.castSucc (3 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 7).castSucc.castSucc.castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hX
  · apply (permutation_semantics (M := M) v (Fin.last 5).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 8).castSucc.castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hf
  · apply (ForcingCohenCoordinates.graph_semantics (M := M) v (Fin.last 5).castSucc.castSucc.castSucc.castSucc.castSucc (4 : Fin 5).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last 8).castSucc.castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hfg
  · apply (permutation_semantics (M := M) v (Fin.last 6).castSucc.castSucc.castSucc.castSucc (Fin.last 9).castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hg
  · apply (ForcingCohenCoordinates.graph_semantics (M := M) v (Fin.last 6).castSucc.castSucc.castSucc.castSucc (Fin.last 8).castSucc.castSucc (Fin.last 9).castSucc).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hgg
  · apply (permutation_semantics (M := M) v (Fin.last 7).castSucc.castSucc.castSucc (Fin.last 10)).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using ha
  · apply (actionGraph_semantics (M := M) v (Fin.last 7).castSucc.castSucc.castSucc (Fin.last 9).castSucc (Fin.last 10)).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using hga
  · apply (orderPreserving_semantics (M := M) v (Fin.last 10)).mpr
    simpa only [v, Fin.lastCases_last, Fin.lastCases_castSucc] using ho

theorem assembly_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence assemblySentence) :=
  ModelTransfer.derives (fun _ hM => assembly_models hM)

end PPAC.Migration.ForcingCohenOrderAction
