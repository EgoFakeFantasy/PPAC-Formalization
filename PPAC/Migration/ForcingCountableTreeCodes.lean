/- Pinned AssignedGraphs.CountableHull.exists_closed:296-324.
The whole INTERNAL set of well-founded full omega-branching A-labelled trees.
Finite addresses and their cons/child laws reuse the existing donor proofs.
This module constructs all legal codes and the leaf; grafting/cardinality
are separate remaining source obligations. -/
import PPAC.Migration.ExistingTreeAddresses
import PPAC.Migration.ForcingCountableTreeAlgebra

namespace PPAC.Migration.ForcingCountableTreeCodes
open YesMetaZFC SetTheory SetTheory.Definitional.Project
open ExistingFiniteSequenceBounds ExistingTreeAddresses
open ForcingCountableTreeEvaluation (WellFounded)
universe u
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- Every address child edge, oriented child-to-parent as in the evaluator. -/
def Edges (w S R : M.Domain) : Prop := M.IsSetRelation I R ∧ ∀ t s,
  M.PairMember I t s R ↔ M.mem s S ∧ M.mem t S ∧ Step_d I w s t

def edges {n} (w S R : Term n) : Formula 1 n :=
  .conj (Formula.isRelation 𝒞 R) (.forallE (.forallE (.iff
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest R.weaken.weaken)
    (.conj (.mem .newest S.weaken.weaken) (.conj (.mem (.bound 1) S.weaken.weaken)
      (step_m (𝒞 := 𝒞) w.weaken.weaken .newest (.bound 1)))))))
derive_free_closed edges

theorem edges_semantics {n} (hE : Extensional M) (ρ : Env M n) (w S R : Term n) :
    Formula.satisfies ρ (edges (𝒞 := 𝒞) w S R) ↔ Edges I (w.eval ρ) (S.eval ρ) (R.eval ρ) := by
  simp only [edges, Edges, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_orderedPairMem_iff I, step_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem edges_exists (hZF : M.Models ZF) (w S : M.Domain) : ∃ R, Edges I w S R := by
  obtain ⟨SS, hSS⟩ := ZF.exists_cartesianProduct hZF I S S
  let ρ : Env M 1 := ⟨fun _ => w, fun _ => w⟩
  let φ : UnarySchema 1 := {body := .existsE (.existsE (.conj
    (𝒞.code (.bound 2) (.bound 1) .newest) (step_m (𝒞 := 𝒞) (.bound 3) .newest (.bound 1))))}
  have hφ p : φ.denote ρ p ↔ ∃ t s, I.Codes p t s ∧ Step_d I w s t := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      I.satisfies_code_iff, step_sat_l I hZF.1]
    rfl
  obtain ⟨R, hR⟩ := ZF.separation_exists_d hZF φ ρ SS
  refine ⟨R, ⟨fun p hp => ?_, fun t s => ?_⟩⟩
  · obtain ⟨t, _, s, _, hc⟩ := (hSS p).mp ((hR p).mp hp).1
    exact ⟨t, s, hc⟩
  · constructor
    · rintro ⟨p, hc, hp⟩
      obtain ⟨t', ht, s', hs, hc'⟩ := (hSS p).mp ((hR p).mp hp).1
      obtain ⟨rfl, rfl⟩ := I.injective hc hc'
      obtain ⟨t'', s'', hc'', he⟩ := (hφ p).mp ((hR p).mp hp).2
      obtain ⟨rfl, rfl⟩ := I.injective hc hc''
      exact ⟨hs, ht, he⟩
    · rintro ⟨hs, ht, he⟩
      obtain ⟨p, hp⟩ := I.total t s
      exact ⟨p, hp, (hR p).mpr ⟨(hSS p).mpr ⟨t, ht, s, hs, hp⟩,
        (hφ p).mpr ⟨t, s, hp, he⟩⟩⟩

/-- Source Option A labels: an unlabelled address is a leaf, while a labelled
address has EVERY internal natural child. The internal subset-minimum
condition is used, never host well-foundedness or external finite height. -/
def Tree (w S A z R T labels : M.Domain) : Prop :=
  M.MemberSubset T S ∧ M.mem z T ∧
  (∀ s, M.mem s T → ∀ t, M.mem t S → M.MemberSubset t s → M.mem t T) ∧
  WellFounded I T R ∧ M.IsSetFunction I labels ∧
  (∀ s a, M.PairMember I s a labels → M.mem s T ∧ M.mem a A) ∧
  ∀ s, M.mem s T → ∀ t, M.mem t S → Step_d I w s t →
    (M.mem t T ↔ ∃ a, M.PairMember I s a labels)

def tree {n} (w S A z R T labels : Term n) : Formula 1 n :=
  .conj (Formula.subset T S) (.conj (.mem z T) (.conj
    (Formula.forallMem T (Formula.forallMem S.weaken (.imp
      (Formula.subset .newest (.bound 1)) (.mem .newest T.weaken.weaken))))
    (.conj (ForcingCountableTreeEvaluation.wellFounded (𝒞 := 𝒞) T R)
      (.conj (Formula.isFunction 𝒞 labels) (.conj
        (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest labels.weaken.weaken)
          (.conj (.mem (.bound 1) T.weaken.weaken) (.mem .newest A.weaken.weaken)))))
        (Formula.forallMem T (Formula.forallMem S.weaken (.imp
          (step_m (𝒞 := 𝒞) w.weaken.weaken (.bound 1) .newest)
          (.iff (.mem .newest T.weaken.weaken) (.existsE
            (Formula.orderedPairMem 𝒞 (.bound 2) .newest labels.weaken.weaken.weaken)))))))))))
derive_free_closed tree

theorem tree_semantics {n} (hE : Extensional M) (ρ : Env M n) (w S A z R T labels : Term n) :
    Formula.satisfies ρ (tree (𝒞 := 𝒞) w S A z R T labels) ↔
      Tree I (w.eval ρ) (S.eval ρ) (A.eval ρ) (z.eval ρ) (R.eval ρ) (T.eval ρ) (labels.eval ρ) := by
  simp only [tree, Tree, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_isFunction_iff I hE, Formula.satisfies_orderedPairMem_iff I,
    ForcingCountableTreeEvaluation.wellFounded_semantics I, step_sat_l I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

/-- EXACT set of all legal internal codes, with no imposed external rank cap. -/
def Carrier (w S A z R C : M.Domain) : Prop := ∀ c,
  M.mem c C ↔ ∃ T labels, I.Codes c T labels ∧ Tree I w S A z R T labels

def carrier {n} (w S A z R C : Term n) : Formula 1 n :=
  .forallE (.iff (.mem .newest C.weaken) (.existsE (.existsE (.conj
    (𝒞.code (.bound 2) (.bound 1) .newest)
    (tree (𝒞 := 𝒞) w.weaken.weaken.weaken S.weaken.weaken.weaken A.weaken.weaken.weaken
      z.weaken.weaken.weaken R.weaken.weaken.weaken (.bound 1) .newest)))))
derive_free_closed carrier

theorem carrier_semantics {n} (hE : Extensional M) (ρ : Env M n) (w S A z R C : Term n) :
    Formula.satisfies ρ (carrier (𝒞 := 𝒞) w S A z R C) ↔
      Carrier I (w.eval ρ) (S.eval ρ) (A.eval ρ) (z.eval ρ) (R.eval ρ) (C.eval ρ) := by
  simp only [carrier, Carrier, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    I.satisfies_code_iff, tree_semantics I hE, Definitional.Term.eval_weaken]
  rfl

theorem carrier_exists (hZF : M.Models ZF) (w S A z R : M.Domain) :
    ∃ C, Carrier I w S A z R C := by
  obtain ⟨PS, hPS⟩ := ZF.exists_powerSet hZF S
  obtain ⟨SA, hSA⟩ := ZF.exists_cartesianProduct hZF I S A
  obtain ⟨PF, hPF⟩ := ZF.exists_powerSet hZF SA
  obtain ⟨B, hB⟩ := ZF.exists_cartesianProduct hZF I PS PF
  let ρ : Env M 5 := ((((⟨fun _ => w, fun _ => w⟩ : Env M 1).push S).push A).push z).push R
  let φ : UnarySchema 5 := {body := .existsE (.existsE (.conj
    (𝒞.code (.bound 2) (.bound 1) .newest)
    (tree (𝒞 := 𝒞) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest)))}
  have hφ c : φ.denote ρ c ↔ ∃ T labels, I.Codes c T labels ∧ Tree I w S A z R T labels := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      I.satisfies_code_iff, tree_semantics I hZF.1]
    rfl
  obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ B
  refine ⟨C, fun c => ⟨fun hc => (hφ c).mp ((hC c).mp hc).2, ?_⟩⟩
  intro h
  obtain ⟨T, labels, hc, ht⟩ := h
  have hlPF : M.mem labels PF := (hPF labels).mpr (by
    intro p hp
    obtain ⟨s, a, hpa⟩ := ht.2.2.2.2.1.1 p hp
    have hsa := ht.2.2.2.2.2.1 s a ⟨p, hpa, hp⟩
    exact (hSA p).mpr ⟨s, ht.1 s hsa.1, a, hsa.2, hpa⟩)
  exact (hC c).mpr ⟨(hB c).mpr ⟨T, (hPS T).mpr ht.1, labels, hlPF, hc⟩, (hφ c).mpr ⟨T, labels, hc, ht⟩⟩

/-- Existing donor proof that no direct child address is the empty sequence. -/
theorem tree_step_not_empty_l {ω s e : M.Domain} (he : ∀ p, ¬ M.mem p e) : ¬ Step_d I ω s e := by
  rintro ⟨a, n, m, h⟩
  obtain ⟨p, _, hp⟩ := h.last_value
  exact he p hp

theorem leaf_exists (hZF : M.Models ZF) {w S A z R : M.Domain}
    (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S) (hz : ∀ p, ¬ M.mem p z) (hzw : M.mem z w)
    (hR : Edges I w S R) : ∃ T, (∀ s, M.mem s T ↔ s = z) ∧ Tree I w S A z R T z := by
  obtain ⟨T, hT⟩ := KP.exists_singleton (ZF.modelsKP hZF) z
  have hzS : M.mem z S := (hS z).mpr ⟨z, hzw, ds_empty_fun_l I hz⟩
  have htS : M.MemberSubset T S := fun s hs => (hT s).mp hs ▸ hzS
  have hwf : WellFounded I T R := by
    intro Y hY hne
    obtain ⟨s, hs⟩ := hne
    refine ⟨s, hs, fun t ht he => ?_⟩
    have et := (hT t).mp (hY t ht)
    exact tree_step_not_empty_l I hz (et ▸ ((hR.2 t s).mp he).2.2)
  refine ⟨T, hT, htS, (hT z).mpr rfl, ?_, hwf, (ds_empty_fun_l I (X := A) hz).1, ?_, ?_⟩
  · intro s hs t _ hts
    have es := (hT s).mp hs
    apply (hT t).mpr
    apply hZF.1.eq_of_same_members
    intro p
    exact iff_of_false (fun hp => hz p (es ▸ hts p hp)) (hz p)
  · intro s a hsa
    obtain ⟨p, _, hp⟩ := hsa
    exact (hz p hp).elim
  · intro s _ t _ hst
    constructor
    · intro ht
      exact (tree_step_not_empty_l I hz ((hT t).mp ht ▸ hst)).elim
    · rintro ⟨a, p, _, hp⟩
      exact (hz p hp).elim


def LeafCode (z c : M.Domain) : Prop := ∃ T, I.Codes c T z ∧ ∀ s, M.mem s T ↔ s = z

def leafCode {n} (z c : Term n) : Formula 1 n := .existsE (.conj
  (𝒞.code c.weaken .newest z.weaken)
  (.forallE (.iff (.mem .newest (.bound 1)) (Formula.extensionalEq .newest z.weaken.weaken))))
derive_free_closed leafCode

theorem leafCode_semantics {n} (hE : Extensional M) (ρ : Env M n) (z c : Term n) :
    Formula.satisfies ρ (leafCode (𝒞 := 𝒞) z c) ↔ LeafCode I (z.eval ρ) (c.eval ρ) := by
  simp only [leafCode, LeafCode, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    I.satisfies_code_iff, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken]
  rfl

/-- Full finite address space, all child edges, all valid trees, and a real leaf code. -/
theorem construction (hZF : M.Models ZF) {w : M.Domain} (hw : M.IsOmega w) (A : M.Domain) :
    ∃ S z R C, ExistingFiniteSequenceBounds.Fseq_space_d I w w S ∧ (∀ p, ¬ M.mem p z) ∧ M.mem z w ∧
      Edges I w S R ∧ Carrier I w S A z R C ∧ ∃ c, M.mem c C ∧ LeafCode I z c := by
  obtain ⟨S, hS⟩ := ExistingFiniteSequenceBounds.fseq_space_exists_l I hZF hw w
  obtain ⟨z, hz, hzw⟩ := hw.1.1
  obtain ⟨R, hR⟩ := edges_exists I hZF w S
  obtain ⟨C, hC⟩ := carrier_exists I hZF w S A z R
  obtain ⟨T, hT, ht⟩ := leaf_exists I hZF hS hz hzw hR
  obtain ⟨c, hc⟩ := I.total T z
  exact ⟨S, z, R, C, hS, hz, hzw, hR, hC, c, (hC c).mpr ⟨T, z, hc, ht⟩, T, hc, hT⟩

/-- All legal internal trees and the source none/leaf term exist in native ZF. -/
def constructionSentence (𝒞 : OrderedPairConvention) : Sentence where
  formula := Formula.forallClosure 2 (.imp (Formula.isOmega (.bound 0))
    (.existsE (.existsE (.existsE (.existsE (.conj
      (ExistingFiniteSequenceBounds.fseq_space_m (𝒞 := 𝒞) (.bound 4) (.bound 4) (.bound 3))
      (.conj (.forallE (.neg (.mem .newest (.bound 3)))) (.conj (.mem (.bound 2) (.bound 4))
        (.conj (edges (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 1))
          (.conj (carrier (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 5) (.bound 2) (.bound 1) .newest)
            (.existsE (.conj (.mem .newest (.bound 1))
              (leafCode (𝒞 := 𝒞) (.bound 3) .newest)))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]

include I in
theorem construction_models (hZF : M.Models ZF) : M.SatisfiesSentence (constructionSentence 𝒞) := by
  apply (Structure.satisfiesSentence_iff M _).mpr
  intro free
  apply (Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Formula.satisfies_imp_iff, Formula.satisfies_isOmega_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, ExistingFiniteSequenceBounds.fseq_space_sat_l I hZF.1,
    Formula.satisfies_forall_iff, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff,
    edges_semantics I hZF.1, carrier_semantics I hZF.1, leafCode_semantics I hZF.1]
  exact fun hw => construction I hZF hw _

open YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
attribute [local implicit_reducible] SetTheory.signature FirstOrderSemantics.reduct

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (fo_sentence (constructionSentence PureKuratowskiProject.convention)) := by
  apply ModelTransfer.derives
  intro M hM
  exact (FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) _).mpr
    (construction_models (KuratowskiZF.interpretation hM) (ModelTransfer.project_models_iff.mp hM))

end PPAC.Migration.ForcingCountableTreeCodes
