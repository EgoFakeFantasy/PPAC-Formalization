/- Pinned AssignedGraphs.CountableHull.exists_closed:296-324.
The SAME full internal tree evaluator, its bounded range, and the actual
indexed graft equation. Source choose is realized by least numbered preimages;
no object Choice, externally standard omega, or assumed closure premise. -/
import PPAC.Migration.ForcingCountableTreeGraftValues
import PPAC.Migration.ExistingOrdinalImage

namespace PPAC.Migration.ForcingCountableHull
open YesMetaZFC SetTheory SetTheory.Definitional.Project
open ForcingCountableTreeCodes ForcingCountableTreeValues
open ForcingChainBound (Values rel rel_semantics)
open ExistingOrdinalImage (Ord_image_d ord_image_m ord_image_sat_l)
universe u
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- A tree with least ordinal number among all trees having this root value. -/
def LeastTree (J E x c : M.Domain) : Prop := ∃ n,
  M.PairMember I c n J ∧ M.PairMember I c x E ∧ ∀ m, Ord_image_d I J E x m → ¬ M.mem m n

def leastTree {n} (J E x c : Term n) : Formula 1 n := .existsE (.conj
  (Formula.orderedPairMem 𝒞 c.weaken .newest J.weaken) (.conj
  (Formula.orderedPairMem 𝒞 c.weaken x.weaken E.weaken) (.forallE (.imp
    (ord_image_m (𝒞 := 𝒞) J.weaken.weaken E.weaken.weaken x.weaken.weaken .newest)
    (.neg (.mem .newest (.bound 1)))))))
derive_free_closed leastTree

theorem leastTree_semantics {n} (ρ : Env M n) (J E x c : Term n) :
    Formula.satisfies ρ (leastTree (𝒞 := 𝒞) J E x c) ↔
      LeastTree I (J.eval ρ) (E.eval ρ) (x.eval ρ) (c.eval ρ) := by
  simp only [leastTree, LeastTree, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    ord_image_sat_l I, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  rfl

/-- Use the existing numbered-fiber formula and native internal well-order minimum. -/
theorem leastTree_exists (hZF : M.Models ZF) {mu C Y J E x : M.Domain}
    (hmu : M.IsOrdinal mu) (hJ : M.IsSetInjectionFromTo I J C mu)
    (hs : M.IsSetSurjectiveOnto I E C Y) (hx : M.mem x Y) : ∃ c, LeastTree I J E x c := by
  let ρ : Env M 3 := ((⟨fun _ => J, fun _ => J⟩ : Env M 1).push E).push x
  let φ : UnarySchema 3 := {body := ord_image_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) .newest}
  obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF φ ρ mu
  have hd n : M.mem n D ↔ M.mem n mu ∧ Ord_image_d I J E x n :=
    (hD n).trans (and_congr_right fun _ => ord_image_sat_l I _ _ _ _ _)
  obtain ⟨c, hc, hcx⟩ := hs x hx
  obtain ⟨n, hn, hcn⟩ := hJ.1.2.2 c hc
  obtain ⟨m, hm, hmin⟩ := hmu.wellOrder.least D (fun j hj => ((hd j).mp hj).1)
    ⟨n, (hd n).mpr ⟨hn, c, hcn, hcx⟩⟩
  obtain ⟨hmMu, d, hdm, hdx⟩ := (hd m).mp hm
  refine ⟨d, m, hdm, hdx, fun k hk hkm => ?_⟩
  have hkMu := hk.elim fun c hc => hJ.1.output_mem_of_pairMember hc.1
  rcases hmin k ((hd k).mpr ⟨hkMu, hk⟩) with e | hmk
  · exact hmu.wellOrder.linear.irrefl m hmMu (hZF.1.eq_of_same_members k m (fun x => (e x).symm) ▸ hkm)
  · exact hmu.wellOrder.linear.irrefl m hmMu (hmu.wellOrder.linear.trans m hmMu k hkMu m hmMu hmk hkm)

theorem leastTree_unique (hE : Extensional M) {mu C J E x c d : M.Domain}
    (hmu : M.IsOrdinal mu) (hJ : M.IsSetInjectionFromTo I J C mu)
    (hc : LeastTree I J E x c) (hd : LeastTree I J E x d) : c = d := by
  obtain ⟨n, hcn, hcx, hn⟩ := hc
  obtain ⟨m, hdm, hdx, hm⟩ := hd
  rcases hmu.wellOrder.linear.compare n (hJ.1.output_mem_of_pairMember hcn)
      m (hJ.1.output_mem_of_pairMember hdm) with e | hnm | hmn
  · exact hJ.2 c d n hcn (hE.eq_of_same_members m n (fun x => (e x).symm) ▸ hdm)
  · exact (hm n ⟨c, hcn, hcx⟩ hnm).elim
  · exact (hn m ⟨d, hdm, hdx⟩ hmn).elim

/-- Source choose, including the necessary E(K(x))=x equation, as one internal graph. -/
theorem subtree_section (hZF : M.Models ZF) {mu C Y J E : M.Domain}
    (hmu : M.IsOrdinal mu) (hJ : M.IsSetInjectionFromTo I J C mu)
    (hE : M.IsSetFunctionFromTo I E C Y) (hs : M.IsSetSurjectiveOnto I E C Y) :
    ∃ K, M.IsSetFunctionFromTo I K Y C ∧ ∀ x c, M.PairMember I x c K → M.PairMember I c x E := by
  let ρ : Env M 2 := (⟨fun _ => J, fun _ => J⟩ : Env M 1).push E
  let φ : BinarySchema 2 := {body := leastTree (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) .newest}
  have hφ x c : φ.denote ρ x c ↔ LeastTree I J E x c := by
    simp only [φ, BinarySchema.denote, leastTree_semantics I]
    rfl
  obtain ⟨K, hK, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := Y) (target := C)
    (by
      intro x hx
      obtain ⟨c, hc⟩ := leastTree_exists I hZF hmu hJ hs hx
      exact ⟨c, (hφ x c).mpr hc⟩)
    (fun x _ c d hc hd => leastTree_unique I hZF.1 hmu hJ ((hφ x c).mp hc) ((hφ x d).mp hd))
    (by
      intro x c _ hc
      obtain ⟨_, _, hcx, _⟩ := (hφ x c).mp hc
      exact hE.input_mem_of_pairMember hcx)
  refine ⟨K, hK, fun x c hc => ?_⟩
  obtain ⟨_, _, hcx, _⟩ := (hφ x c).mp ((he x c).mp hc).2
  exact hcx

/-- Literal source closure under all internal omega-indexed operations. -/
def Hull (w A X op base mu Y : M.Domain) : Prop := M.MemberSubset Y X ∧
  M.CardinalLessOrEqual I Y mu ∧ M.mem base Y ∧ ∀ a f, M.mem a A →
    M.IsSetFunctionFromTo I f w Y → ∀ x, Values I op a f x → M.mem x Y

def hull {n} (w A X op base mu Y : Term n) : Formula 1 n := .conj (Formula.subset Y X)
  (.conj (Formula.cardinalLessOrEqual 𝒞 Y mu) (.conj (.mem base Y)
    (.forallE (.forallE (.imp (.mem (.bound 1) A.weaken.weaken)
      (.imp (Formula.isFunctionFromTo 𝒞 .newest w.weaken.weaken Y.weaken.weaken)
        (.forallE (.imp (rel (𝒞 := 𝒞) op.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
          (.mem .newest Y.weaken.weaken.weaken)))))))))
derive_free_closed hull

theorem hull_semantics {n} (hE : Extensional M) (ρ : Env M n) (w A X op base mu Y : Term n) :
    Formula.satisfies ρ (hull (𝒞 := 𝒞) w A X op base mu Y) ↔
      Hull I (w.eval ρ) (A.eval ρ) (X.eval ρ) (op.eval ρ) (base.eval ρ) (mu.eval ρ) (Y.eval ρ) := by
  simp only [hull, Hull, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_cardinalLessOrEqual_iff I hE, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    rel_semantics I, Definitional.Term.eval_weaken]
  rfl

/-- The source range construction, with its leaf and node witnesses actually supplied. -/
theorem range_closed (hZF : M.Models ZF) {w S A z R C X op base mu E : M.Domain}
    (hw : M.IsOmega w) (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S)
    (hz : ∀ p, ¬ M.mem p z) (hzw : M.mem z w) (hR : Edges I w S R)
    (hC : Carrier I w S A z R C) (hleaf : ∃ c, M.mem c C ∧ LeafCode I z c)
    (hmu : M.IsOrdinal mu) (hbound : M.CardinalLessOrEqual I C mu)
    (ho : ForcingCountableTreeAlgebra.Operation I w A X op) (hE : Roots I w X op base z C E) :
    ∃ Y, Hull I w A X op base mu Y := by
  obtain ⟨Y, hY⟩ := ZF.exists_range_of_setFunction hZF I hE.1.1 hE.1.2.1
  have hYX : M.MemberSubset Y X := fun x hx =>
    ((hY x).mp hx).elim fun c hc => hE.1.output_mem_of_pairMember hc
  have hEY : M.IsSetFunctionFromTo I E C Y := ⟨hE.1.1, hE.1.2.1, fun c hc => by
    obtain ⟨x, _, hx⟩ := hE.1.2.2 c hc
    exact ⟨x, (hY x).mpr ⟨c, hx⟩, hx⟩⟩
  have hsurj : M.IsSetSurjectiveOnto I E C Y := by
    intro x hx
    obtain ⟨c, hc⟩ := (hY x).mp hx
    exact ⟨c, hE.1.input_mem_of_pairMember hc, hc⟩
  have hYbound := ExistingOrdinalImage.ordinal_image_bound_l I hZF hmu hbound hEY hsurj
  obtain ⟨J, hJ⟩ := hbound
  obtain ⟨K, hK, hsection⟩ := subtree_section I hZF hmu hJ hEY hsurj
  refine ⟨Y, hYX, hYbound, ?_, ?_⟩
  · obtain ⟨c, hc, hleaf⟩ := hleaf
    obtain ⟨x, _, hx⟩ := hE.1.2.2 c hc
    have e := root_leaf I hz hleaf ((hE.2 c x).mp hx).2
    exact e ▸ (hY x).mpr ⟨c, hx⟩
  · intro a f ha hf x hx
    have hfX : M.IsSetFunctionFromTo I f w X := ⟨hf.1, hf.2.1, fun n hn => by
      obtain ⟨y, hy, hny⟩ := hf.2.2 n hn
      exact ⟨y, hYX y hy, hny⟩⟩
    obtain ⟨H, hH, he⟩ := ZF.exists_compositionFunction hZF I hf hK
    have hcomp n y : M.PairMember I n y f ↔ ∃ c, M.PairMember I n c H ∧ M.PairMember I c y E := by
      constructor
      · intro hny
        obtain ⟨c, _, hyc⟩ := hK.2.2 y (hf.output_mem_of_pairMember hny)
        exact ⟨c, (he n c).mpr ⟨hf.input_mem_of_pairMember hny, y, hny, hyc⟩, hsection y c hyc⟩
      · rintro ⟨c, hnc, hcy⟩
        obtain ⟨_, v, hnv, hvc⟩ := (he n c).mp hnc
        exact hEY.1.2 c v y (hsection v c hvc) hcy ▸ hnv
    obtain ⟨_, _, c, y, _, _, _, hcy, hop⟩ := ForcingCountableTreeGraftValues.evaluated_graft
      I hZF hw hS hz hzw hR hC hH ha hE hfX hcomp
    exact ho.2 a f y x hop hx ▸ (hY y).mpr ⟨c, hcy⟩

/-- The source full hull: no carrier, evaluator, section, or closure hypothesis remains. -/
theorem exists_closed (hZF : M.Models ZF) {w A X op base mu P : M.Domain}
    (hw : M.IsOmega w) (hmu : M.IsInfiniteCardinal I w mu)
    (hA : M.CardinalLessOrEqual I A mu) (hP : M.IsFunctionSpace I P w mu)
    (hp : M.CardinalLessOrEqual I P mu)
    (ho : ForcingCountableTreeAlgebra.Operation I w A X op) (hb : M.mem base X) :
    ∃ Y, Hull I w A X op base mu Y := by
  obtain ⟨S, z, R, C, hS, hz, hzw, hR, hC, hleaf⟩ := ForcingCountableTreeCodes.construction I hZF hw A
  have hbound := ForcingCountableTreeCardinality.cardinal_le I hZF hw hmu hS hC hA hP hp
  obtain ⟨E, hE⟩ := roots_exists I hZF hw hS hR hC ho hb
  exact range_closed I hZF hw hS hz hzw hR hC hleaf hmu.1.1 hbound ho hE

/-- Original omega<=mu, mu^omega=mu, |A|<=mu hypotheses and full internal closure. -/
def hullSentence (𝒞 : OrderedPairConvention) : Sentence where
  formula := Formula.forallClosure 6 (.imp (Formula.isOmega (.bound 0))
    (.imp (Formula.isInfiniteCardinal 𝒞 (.bound 0) (.bound 5))
    (.imp (Formula.isCardinalExponentiation 𝒞 (.bound 5) (.bound 5) (.bound 0))
    (.imp (Formula.cardinalLessOrEqual 𝒞 (.bound 1) (.bound 5))
    (.imp (ForcingCountableTreeAlgebra.operationFormula (𝒞 := 𝒞) (.bound 0) (.bound 1) (.bound 2) (.bound 3))
    (.imp (.mem (.bound 4) (.bound 2))
    (.existsE (hull (𝒞 := 𝒞) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) .newest))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
    Formula.isInfiniteCardinal, Formula.isCardinalExponentiation, Formula.isFunctionSpace]

open YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
attribute [local implicit_reducible] SetTheory.signature FirstOrderSemantics.reduct

theorem hull_models {N : FirstOrder.Structure.{0,0,0,u} ℒ} (hN : FirstOrder.Theory.Models N nativeZF) :
    (FirstOrderSemantics.reduct N).SatisfiesSentence (hullSentence PureKuratowskiProject.convention) := by
  have hZF := ModelTransfer.project_models_iff.mp hN
  let J := KuratowskiZF.interpretation hN
  apply (Structure.satisfiesSentence_iff _ _).mpr
  intro free
  apply (Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Formula.satisfies_imp_iff, Formula.satisfies_isOmega_iff,
    Formula.satisfies_isInfiniteCardinal_iff J hZF.1, Formula.satisfies_isCardinalExponentiation_iff J hZF.1,
    Formula.satisfies_cardinalLessOrEqual_iff J hZF.1, ForcingCountableTreeAlgebra.operation_semantics J hZF.1,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, hull_semantics J hZF.1]
  intro hw hmu hPow hA ho hb
  obtain ⟨P, hP⟩ := ZF.exists_functionSpace hZF J (bound 0) (bound 5)
  obtain ⟨Pmu, hPmu⟩ := (ConstructionConcreteCardinals.normalize_power hN hPow hP).2.symm hZF J
  exact exists_closed J hZF hw hmu hA hP ⟨Pmu, hPmu.1⟩ ho hb

theorem hull_kernel_certificate : FirstOrder.Derives nativeZF []
    (fo_sentence (hullSentence PureKuratowskiProject.convention)) := by
  apply ModelTransfer.derives
  intro N hN
  exact (FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hN) _).mpr (hull_models hN)

end PPAC.Migration.ForcingCountableHull
