/- Pinned AssignedGraphs.CountableHull.exists_closed:323-324: evaluation of
an omega-ary graft. Preserve the actual child index through prepend, pull the
new evaluation back to each old tree, and identify its root argument graph. -/
import PPAC.Migration.ForcingCountableTreeValues

namespace PPAC.Migration.ForcingCountableTreeGraftValues
open YesMetaZFC SetTheory SetTheory.Definitional.Project
open ExistingTreeAddresses ForcingCountableTreeCodes ForcingCountableTreeGraft
open ForcingCountableTreeValues
open ForcingChainBound (Values rel rel_semantics)
universe u
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- The last value recovers the INDEX forgotten by the unlabelled child relation. -/
theorem end_iff_step_value (hE : Extensional M) {w s t n x : M.Domain}
    (hs : M.IsSetFunctionFromTo I s n w) :
    Fseq_end_d I w t s x ↔ Step_d I w s t ∧ M.PairMember I n x t := by
  constructor
  · intro he
    obtain ⟨k, l, h⟩ := he
    have e := h.prefix_sequence.2.2.2.eq hE hs.2.1
    subst l
    exact ⟨⟨x, k, n, h⟩, h.last_value⟩
  · rintro ⟨⟨a, k, l, h⟩, hx⟩
    have e := h.prefix_sequence.2.2.2.eq hE hs.2.1
    subst l
    have e := h.source.2.2.1.2 n a x h.last_value hx
    subst a
    exact ⟨k, n, h⟩

/-- Prepending one common head preserves each child INDEX, not just adjacency. -/
theorem cons_end (hZF : M.Models ZF) {w z i s t u v n m x : M.Domain}
    (hw : M.IsOmega w) (hz : ∀ p, ¬ M.mem p z) (hi : M.mem i w)
    (hn : M.mem n w) (hm : M.mem m w) (hs : M.IsSetFunctionFromTo I s n w)
    (ht : M.IsSetFunctionFromTo I t m w) (hu : Cons_d I z i s u) (hv : Cons_d I z i t v) :
    Fseq_end_d I w v u x ↔ Fseq_end_d I w t s x := by
  obtain ⟨j, _, hjn, huf⟩ := cons_type_l I hZF hw hz hi hn hs hu
  have hlast : M.PairMember I j x v ↔ M.PairMember I n x t := by
    refine (hv.2 j x).trans ⟨?_, fun hx => Or.inr ⟨n, hx, hjn⟩⟩
    rintro (⟨e, _⟩ | ⟨l, hx, hjl⟩)
    · exact (hz n (e ▸ hjn.predecessor_mem)).elim
    · have e := Structure.SuccessorOf.predecessor_eq hZF.1 ((hw.isOrdinal hZF).mem hn) hjn hjl
      exact e.symm ▸ hx
  rw [end_iff_step_value I hZF.1 huf, end_iff_step_value I hZF.1 hs,
    cons_step_l I hZF hw hz hi hi hn hm hs ht hu hv, hlast]
  simp only [true_and, eq_self]

/-- A direct child of the empty address is precisely its one-entry code. -/
theorem root_end (hZF : M.Models ZF) {w S z i t : M.Domain}
    (hw : M.IsOmega w) (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S)
    (hz : ∀ p, ¬ M.mem p z) (hzw : M.mem z w) (hi : M.mem i w) :
    Fseq_end_d I w t z i ↔ Cons_d I z i z t := by
  have h0 := ds_empty_fun_l I (X := w) hz
  have hzS := (hS z).mpr ⟨z, hzw, h0⟩
  have back {v} (hv : Cons_d I z i z v) : Fseq_end_d I w v z i :=
    (end_iff_step_value I hZF.1 h0).mpr ⟨(cons_root_l I hZF hw hS hz hzw hi hzS hv).mpr rfl,
      (hv.2 z i).mpr (Or.inl ⟨rfl, rfl⟩)⟩
  refine ⟨fun he => ?_, back⟩
  obtain ⟨_, v, _, _, _, hv⟩ := cons_exists_l I hZF hw hz hi hzw h0
  exact fseq_end_rebuild_l I hZF.1 (back hv) he ▸ hv

/-- Restrict a whole-tree evaluation to one indexed copy of an old tree. -/
def Pullback (z i U X V W : M.Domain) : Prop := M.IsSetFunctionFromTo I W U X ∧
  ∀ s x, M.PairMember I s x W ↔ M.mem s U ∧ ∃ t, Cons_d I z i s t ∧ M.PairMember I t x V

def pullback {n} (z i U X V W : Term n) : Formula 1 n :=
  .conj (Formula.isFunctionFromTo 𝒞 W U X) (.forallE (.forallE (.iff
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest W.weaken.weaken)
    (.conj (.mem (.bound 1) U.weaken.weaken) (.existsE (.conj
      (cons_m (𝒞 := 𝒞) z.weaken.weaken.weaken i.weaken.weaken.weaken (.bound 2) .newest)
      (Formula.orderedPairMem 𝒞 .newest (.bound 1) V.weaken.weaken.weaken)))))))
derive_free_closed pullback

theorem pullback_semantics {n} (hE : Extensional M) (ρ : Env M n) (z i U X V W : Term n) :
    Formula.satisfies ρ (pullback (𝒞 := 𝒞) z i U X V W) ↔
      Pullback I (z.eval ρ) (i.eval ρ) (U.eval ρ) (X.eval ρ) (V.eval ρ) (W.eval ρ) := by
  simp only [pullback, Pullback, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, cons_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem pullback_exists (hZF : M.Models ZF) {w S A z R C H a T F i U G X V : M.Domain}
    (hw : M.IsOmega w) (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S)
    (hz : ∀ p, ¬ M.mem p z) (hC : Carrier I w S A z R C) (hH : M.IsSetFunctionFromTo I H w C)
    (hG : Graft I z H a T F) (hc : Sub I H i U G) (hV : M.IsSetFunctionFromTo I V T X) :
    ∃ W, Pullback I z i U X V W := by
  obtain ⟨hi, hU⟩ := sub_valid I hC hH hc
  let ρ : Env M 3 := ((⟨fun _ => z, fun _ => z⟩ : Env M 1).push i).push V
  let φ : BinarySchema 3 := {body := .existsE (.conj
    (cons_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 2) .newest)
    (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 3)))}
  have hφ s x : φ.denote ρ s x ↔ ∃ t, Cons_d I z i s t ∧ M.PairMember I t x V := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      cons_sat_l I hZF.1, Formula.satisfies_orderedPairMem_iff I]
    rfl
  obtain ⟨W, hW, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := U) (target := X)
    (by
      intro s hs
      obtain ⟨n, hn, hsf⟩ := (hS s).mp (hU.1 s hs)
      obtain ⟨_, t, _, _, _, ht⟩ := cons_exists_l I hZF hw hz hi hn hsf
      have htT := (hG.1 t).mpr (Or.inr ⟨s, G, i, U, hc, hs, ht⟩)
      obtain ⟨x, _, hx⟩ := hV.2.2 t htT
      exact ⟨x, (hφ s x).mpr ⟨t, ht, hx⟩⟩)
    (by
      intro s _ x y hx hy
      obtain ⟨t, ht, hx⟩ := (hφ s x).mp hx
      obtain ⟨u, hu, hy⟩ := (hφ s y).mp hy
      exact hV.1.2 t x y hx (cons_unique_l I hZF.1 hu ht ▸ hy))
    (by
      intro s x _ hx
      obtain ⟨t, _, hx⟩ := (hφ s x).mp hx
      exact hV.output_mem_of_pairMember hx)
  exact ⟨W, hW, fun s x => (he s x).trans (and_congr_right fun _ => hφ s x)⟩

/-- Actual indexed argument graphs agree inside each shifted subtree. -/
theorem pullback_arguments (hZF : M.Models ZF) {w S A z R C H a T F i U G X V W s t g : M.Domain}
    (hw : M.IsOmega w) (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S)
    (hz : ∀ p, ¬ M.mem p z) (hR : Edges I w S R) (hC : Carrier I w S A z R C)
    (hH : M.IsSetFunctionFromTo I H w C) (hG : Graft I z H a T F) (hc : Sub I H i U G)
    (hV : M.IsSetFunctionFromTo I V T X) (hW : Pullback I z i U X V W)
    (hs : M.mem s U) (ht : Cons_d I z i s t) :
    Arguments I w X V t g ↔ Arguments I w X W s g := by
  obtain ⟨hi, hU⟩ := sub_valid I hC hH hc
  obtain ⟨k, hk, hsf⟩ := (hS s).mp (hU.1 s hs)
  have htS := (shift_type I hZF hw hS hz hC hH ⟨i, U, hc, hs, ht⟩).1
  have core n y : (∃ v, Fseq_end_d I w v t n ∧ M.PairMember I v y V) ↔
      ∃ r, Fseq_end_d I w r s n ∧ M.PairMember I r y W := by
    constructor
    · rintro ⟨v, he, hy⟩
      have hvT := hV.input_mem_of_pairMember hy
      have hvS : M.mem v S := by
        rcases (hG.1 v).mp hvT with e | ⟨r, G', hr⟩
        · exact (tree_step_not_empty_l I hz (e ▸ (show Step_d I w t v from ⟨n, he⟩))).elim
        · exact (shift_type I hZF hw hS hz hC hH hr).1
      obtain ⟨r, hr, hv, _⟩ := graft_child I hZF hw hS hz hR hC hH hG hc hs ht hvT
        ((hR.2 v t).mpr ⟨htS, hvS, n, he⟩)
      obtain ⟨m, hm, hrf⟩ := (hS r).mp (hU.1 r hr)
      exact ⟨r, (cons_end I hZF hw hz hi hk hm hsf hrf ht hv).mp he,
        (hW.2 r y).mpr ⟨hr, v, hv, hy⟩⟩
    · rintro ⟨r, he, hy⟩
      obtain ⟨hr, v, hv, hy⟩ := (hW.2 r y).mp hy
      obtain ⟨m, hm, hrf⟩ := (hS r).mp (hU.1 r hr)
      exact ⟨v, (cons_end I hZF hw hz hi hk hm hsf hrf ht hv).mpr he, hy⟩
  exact and_congr_right (fun _ => forall_congr' fun n => forall_congr' fun y =>
    iff_congr Iff.rfl (and_congr Iff.rfl (core n y)))

/-- Pullback satisfies the SAME leaf/base and labelled operation equations. -/
theorem pullback_evaluation (hZF : M.Models ZF) {w S A z R C H a T F i U G X op base V W : M.Domain}
    (hw : M.IsOmega w) (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S)
    (hz : ∀ p, ¬ M.mem p z) (hR : Edges I w S R) (hC : Carrier I w S A z R C)
    (hH : M.IsSetFunctionFromTo I H w C) (hG : Graft I z H a T F) (hc : Sub I H i U G)
    (hV : Evaluation I w T X F op base V) (hW : Pullback I z i U X V W) :
    Evaluation I w U X G op base W := by
  refine ⟨hW.1, fun s x hx => ?_⟩
  obtain ⟨hs, t, ht, hx⟩ := (hW.2 s x).mp hx
  have hl := graft_labels I hZF hw hS hz hC hH hG ⟨i, U, hc, hs, ht⟩
  rcases hV.2 t x hx with ⟨hn, he⟩ | ⟨b, g, hb, hg, hop⟩
  · exact Or.inl ⟨fun ⟨b, hb⟩ => hn ⟨b, (hl b).mpr hb⟩, he⟩
  · exact Or.inr ⟨b, g, (hl b).mp hb,
      (pullback_arguments I hZF hw hS hz hR hC hH hG hc hV.1 hW hs ht).mp hg, hop⟩

/-- The new root sees exactly the composition of H with the existing root evaluator. -/
theorem root_arguments (hZF : M.Models ZF) {w S A z R C H a T F X op base E V g f : M.Domain}
    (hw : M.IsOmega w) (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S)
    (hz : ∀ p, ¬ M.mem p z) (hzw : M.mem z w) (hR : Edges I w S R)
    (hC : Carrier I w S A z R C) (hH : M.IsSetFunctionFromTo I H w C)
    (hG : Graft I z H a T F) (hE : Roots I w X op base z C E)
    (hV : Evaluation I w T X F op base V) (hg : Arguments I w X V z g)
    (hf : M.IsSetFunctionFromTo I f w X)
    (hcomp : ∀ n y, M.PairMember I n y f ↔ ∃ c, M.PairMember I n c H ∧ M.PairMember I c y E) :
    g = f := by
  have forward n y (hy : M.PairMember I n y g) : M.PairMember I n y f := by
    obtain ⟨hn, t, ht, hy⟩ := (hg.2 n y).mp hy
    obtain ⟨c, hc, hnc⟩ := hH.2.2 n hn
    obtain ⟨U, G, hcode, hU⟩ := (hC c).mp hc
    have hsub : Sub I H n U G := ⟨c, hnc, hcode⟩
    obtain ⟨W, hW⟩ := pullback_exists I hZF hw hS hz hC hH hG hsub hV.1
    have hEval := pullback_evaluation I hZF hw hS hz hR hC hH hG hsub hV hW
    have hzy : M.PairMember I z y W := (hW.2 z y).mpr
      ⟨hU.2.1, t, (root_end I hZF hw hS hz hzw hn).mp ht, hy⟩
    exact (hcomp n y).mpr ⟨c, hnc, (hE.2 c y).mpr ⟨hc, U, G, W, hcode, hEval, hzy⟩⟩
  apply hg.1.1.1.eq_of_pairMember_iff hZF.1 hf.1.1
  intro n y
  refine ⟨forward n y, fun hy => ?_⟩
  obtain ⟨v, _, hv⟩ := hg.1.2.2 n (hf.input_mem_of_pairMember hy)
  exact hf.1.2 n v y (forward n v hv) hy ▸ hv

/-- The literal source node equation, with its supplied internal argument function. -/
theorem root_operation (hZF : M.Models ZF) {w S A z R C H a T F X op base E V f x : M.Domain}
    (hw : M.IsOmega w) (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S)
    (hz : ∀ p, ¬ M.mem p z) (hzw : M.mem z w) (hR : Edges I w S R)
    (hC : Carrier I w S A z R C) (hH : M.IsSetFunctionFromTo I H w C)
    (hG : Graft I z H a T F) (hE : Roots I w X op base z C E)
    (hV : Evaluation I w T X F op base V) (hx : M.PairMember I z x V)
    (hf : M.IsSetFunctionFromTo I f w X)
    (hcomp : ∀ n y, M.PairMember I n y f ↔ ∃ c, M.PairMember I n c H ∧ M.PairMember I c y E) :
    Values I op a f x := by
  rcases hV.2 z x hx with ⟨hn, _⟩ | ⟨b, g, hb, hg, hop⟩
  · exact (hn ⟨a, (graft_root I hZF hw hS hz hC hH hG a).mpr rfl⟩).elim
  · have e := (graft_root I hZF hw hS hz hC hH hG b).mp hb
    subst b
    exact root_arguments I hZF hw hS hz hzw hR hC hH hG hE hV hg hf hcomp ▸ hop

/-- Construct the actual graft code and its value under ONE fixed root evaluator. -/
theorem evaluated_graft (hZF : M.Models ZF) {w S A z R C H a X op base E f : M.Domain}
    (hw : M.IsOmega w) (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S)
    (hz : ∀ p, ¬ M.mem p z) (hzw : M.mem z w) (hR : Edges I w S R)
    (hC : Carrier I w S A z R C) (hH : M.IsSetFunctionFromTo I H w C) (ha : M.mem a A)
    (hE : Roots I w X op base z C E) (hf : M.IsSetFunctionFromTo I f w X)
    (hcomp : ∀ n y, M.PairMember I n y f ↔ ∃ c, M.PairMember I n c H ∧ M.PairMember I c y E) :
    ∃ T F c x, Graft I z H a T F ∧ I.Codes c T F ∧ M.mem c C ∧
      M.PairMember I c x E ∧ Values I op a f x := by
  obtain ⟨T, F, c, hG, hcode, hc⟩ := closed I hZF hw hS hz hzw hR hC hH ha
  obtain ⟨x, _, hx⟩ := hE.1.2.2 c hc
  obtain ⟨U, G, V, hcode', hV, hvx⟩ := ((hE.2 c x).mp hx).2
  obtain ⟨rfl, rfl⟩ := I.injective hcode hcode'
  exact ⟨T, F, c, x, hG, hcode, hc, hx,
    root_operation I hZF hw hS hz hzw hR hC hH hG hE hV hvx hf hcomp⟩

def evaluatedGraft {n} (z H a C E op f : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE (.conj
    (graft (𝒞 := 𝒞) z.weaken.weaken.weaken.weaken H.weaken.weaken.weaken.weaken
      a.weaken.weaken.weaken.weaken (.bound 3) (.bound 2)) (.conj
    (𝒞.code (.bound 1) (.bound 3) (.bound 2)) (.conj
    (.mem (.bound 1) C.weaken.weaken.weaken.weaken) (.conj
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest E.weaken.weaken.weaken.weaken)
    (rel (𝒞 := 𝒞) op.weaken.weaken.weaken.weaken a.weaken.weaken.weaken.weaken
      f.weaken.weaken.weaken.weaken .newest))))))))
derive_free_closed evaluatedGraft

theorem evaluatedGraft_semantics {n} (hExt : Extensional M) (ρ : Env M n) (z H a C E op f : Term n) :
    Formula.satisfies ρ (evaluatedGraft (𝒞 := 𝒞) z H a C E op f) ↔
      ∃ T F c x, Graft I (z.eval ρ) (H.eval ρ) (a.eval ρ) T F ∧ I.Codes c T F ∧ M.mem c (C.eval ρ) ∧
        M.PairMember I c x (E.eval ρ) ∧ Values I (op.eval ρ) (a.eval ρ) (f.eval ρ) x := by
  simp only [evaluatedGraft, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    graft_semantics I hExt, I.satisfies_code_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_orderedPairMem_iff I, rel_semantics I, Definitional.Term.eval_weaken]
  rfl

/-- All internal omega-families and argument graphs, on the same full tree carrier. -/
def graftSentence (𝒞 : OrderedPairConvention) : Sentence where
  formula := Formula.forallClosure 13 (.imp (Formula.isOmega (.bound 0))
    (.imp (ExistingFiniteSequenceBounds.fseq_space_m (𝒞 := 𝒞) (.bound 0) (.bound 0) (.bound 1))
    (.imp (.forallE (.neg (.mem .newest (.bound 4))))
    (.imp (.mem (.bound 3) (.bound 0))
    (.imp (edges (𝒞 := 𝒞) (.bound 0) (.bound 1) (.bound 4))
    (.imp (carrier (𝒞 := 𝒞) (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5))
    (.imp (roots (𝒞 := 𝒞) (.bound 0) (.bound 6) (.bound 7) (.bound 8) (.bound 3) (.bound 5) (.bound 9))
    (.imp (Formula.isFunctionFromTo 𝒞 (.bound 10) (.bound 0) (.bound 5))
    (.imp (.mem (.bound 11) (.bound 2))
    (.imp (Formula.isFunctionFromTo 𝒞 (.bound 12) (.bound 0) (.bound 6))
    (.imp (Formula.isComposition 𝒞 (.bound 12) (.bound 9) (.bound 10))
    (evaluatedGraft (𝒞 := 𝒞) (.bound 3) (.bound 10) (.bound 11) (.bound 5) (.bound 9)
      (.bound 7) (.bound 12)))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]

include I in
theorem graft_models (hZF : M.Models ZF) : M.SatisfiesSentence (graftSentence 𝒞) := by
  apply (Structure.satisfiesSentence_iff M _).mpr
  intro free
  apply (Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Formula.satisfies_imp_iff, Formula.satisfies_isOmega_iff,
    ExistingFiniteSequenceBounds.fseq_space_sat_l I hZF.1,
    Formula.satisfies_forall_iff, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff,
    edges_semantics I hZF.1, carrier_semantics I hZF.1, roots_semantics I hZF.1,
    Formula.satisfies_isFunctionFromTo_iff I hZF.1, evaluatedGraft_semantics I hZF.1]
  intro hw hS hz hzw hR hC hE hH ha hf hcomp
  have he : ∀ n y, M.PairMember I n y (bound 12) ↔
      ∃ c, M.PairMember I n c (bound 10) ∧ M.PairMember I c y (bound 9) := by
    simp only [Formula.isComposition, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_orderedPairMem_iff I,
      Definitional.Term.eval_weaken] at hcomp
    exact hcomp
  exact evaluated_graft I hZF hw hS hz hzw hR hC hH ha hE hf he

open YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
attribute [local implicit_reducible] SetTheory.signature FirstOrderSemantics.reduct

theorem graft_kernel_certificate : FirstOrder.Derives nativeZF []
    (fo_sentence (graftSentence PureKuratowskiProject.convention)) := by
  apply ModelTransfer.derives
  intro M hM
  exact (FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) _).mpr
    (graft_models (KuratowskiZF.interpretation hM) (ModelTransfer.project_models_iff.mp hM))

end PPAC.Migration.ForcingCountableTreeGraftValues
