/- Pinned AssignedGraphs.CountableHull.exists_closed:301-318: bound the
WHOLE internally well-founded countable-branching term carrier, without a
height restriction. Reuse existing address countability, Cantor--Bernstein,
function-space transport and fixed countable powers. -/
import PPAC.Migration.ForcingCountableTreeGraft
import PPAC.Migration.ConstructionConcreteCardinals

namespace PPAC.Migration.ForcingCountableTreeCardinality
open YesMetaZFC SetTheory SetTheory.Definitional.Project
open ExistingTreeAddresses ForcingCountableTreeCodes
universe u
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- The FULL internal finite omega-address space is equinumerous with omega. -/
theorem addresses_equinumerous (hZF : M.Models ZF) {w S : M.Domain} (hw : M.IsOmega w)
    (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S) : M.Equinumerous I S w := by
  obtain ⟨idW, hIdW⟩ := ZF.exists_identityBijection hZF I w
  have hSW := ExistingFiniteSequenceBounds.fseq_bound_l I hZF hw
    ⟨ExistingCardinalBounds.omega_cardinal_l I hZF hw, idW, hIdW.1⟩ ⟨idW, hIdW.1⟩ hS
  obtain ⟨z, hz, hzw⟩ := hw.1.1
  let ρ : Env M 1 := ⟨fun _ => z, fun _ => z⟩
  let φ : BinarySchema 1 := {body := cons_m (𝒞 := 𝒞) (.bound 2) (.bound 1) (.bound 2) .newest}
  have hφ i t : φ.denote ρ i t ↔ Cons_d I z i z t := by
    simp only [φ, BinarySchema.denote, cons_sat_l I hZF.1]
    rfl
  have hWS : M.CardinalLessOrEqual I w S := by
    apply ZF.exists_setInjectionFromTo_of_denote hZF I φ ρ
    · intro i hi
      obtain ⟨_, t, _, _, _, ht⟩ := cons_exists_l I hZF hw hz hi hzw (ds_empty_fun_l I hz)
      exact ⟨t, (hφ i t).mpr ht⟩
    · intro i _ t r ht hr
      exact cons_unique_l I hZF.1 ((hφ i t).mp ht) ((hφ i r).mp hr)
    · intro i t hi ht
      obtain ⟨n, hn, _, htf⟩ := cons_type_l I hZF hw hz hi hzw (ds_empty_fun_l I hz) ((hφ i t).mp ht)
      exact (hS t).mpr ⟨n, hn, htf⟩
    · intro i j t _ _ hi hj
      exact (cons_injective_l I hZF hw hz hzw hzw (ds_empty_fun_l I hz) (ds_empty_fun_l I hz)
        ((hφ i t).mp hi) ((hφ j t).mp hj)).1
  exact ZF.equinumerous_of_cardinalLessOrEqual hZF I hSW hWS

/-- Three marks distinguish absent address, leaf and actual label number. -/
def Value (J zero leaf node dummy T F s p : M.Domain) : Prop :=
  (¬ M.mem s T ∧ I.Codes p zero dummy) ∨
  (M.mem s T ∧ (¬ ∃ a, M.PairMember I s a F) ∧ I.Codes p leaf dummy) ∨
  ∃ a b, M.PairMember I s a F ∧ M.PairMember I a b J ∧ I.Codes p node b

def value {n} (J zero leaf node dummy T F s p : Term n) : Formula 1 n :=
  .disj (.conj (.neg (.mem s T)) (𝒞.code p zero dummy)) (.disj
    (.conj (.mem s T) (.conj (.neg (.existsE (Formula.orderedPairMem 𝒞 s.weaken .newest F.weaken)))
      (𝒞.code p leaf dummy)))
    (.existsE (.existsE (.conj (Formula.orderedPairMem 𝒞 s.weaken.weaken (.bound 1) F.weaken.weaken)
      (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest J.weaken.weaken)
        (𝒞.code p.weaken.weaken node.weaken.weaken .newest))))))
derive_free_closed value

theorem value_semantics {n} (ρ : Env M n)
    (J zero leaf node dummy T F s p : Term n) :
    Formula.satisfies ρ (value (𝒞 := 𝒞) J zero leaf node dummy T F s p) ↔
      Value I (J.eval ρ) (zero.eval ρ) (leaf.eval ρ) (node.eval ρ) (dummy.eval ρ)
        (T.eval ρ) (F.eval ρ) (s.eval ρ) (p.eval ρ) := by
  simp only [value, Value, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_mem_iff, I.satisfies_code_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  rfl

theorem value_total {w S A z R T F J mu zero leaf node dummy : M.Domain}
    (hT : Tree I w S A z R T F) (hJ : M.IsSetFunctionFromTo I J A mu) (s : M.Domain) :
    ∃ p, Value I J zero leaf node dummy T F s p := by
  classical
  by_cases hs : M.mem s T
  · by_cases hl : ∃ a, M.PairMember I s a F
    · obtain ⟨a, ha⟩ := hl
      obtain ⟨b, _, hb⟩ := hJ.2.2 a (hT.2.2.2.2.2.1 s a ha).2
      obtain ⟨p, hp⟩ := I.total node b
      exact ⟨p, Or.inr (Or.inr ⟨a, b, ha, hb, hp⟩)⟩
    · obtain ⟨p, hp⟩ := I.total leaf dummy
      exact ⟨p, Or.inr (Or.inl ⟨hs, hl, hp⟩)⟩
  · obtain ⟨p, hp⟩ := I.total zero dummy
    exact ⟨p, Or.inl ⟨hs, hp⟩⟩

theorem value_unique {w S A z R T F J zero leaf node dummy s p q : M.Domain}
    (hT : Tree I w S A z R T F) (hJ : M.IsSetFunction I J)
    (hp : Value I J zero leaf node dummy T F s p)
    (hq : Value I J zero leaf node dummy T F s q) : p = q := by
  rcases hp with ⟨hs, hp⟩ | ⟨hs, hn, hp⟩ | ⟨a, b, ha, hb, hp⟩ <;>
    rcases hq with ⟨ht, hq⟩ | ⟨ht, hm, hq⟩ | ⟨c, d, hc, hd, hq⟩
  · exact I.unique hp hq
  · exact (hs ht).elim
  · exact (hs (hT.2.2.2.2.2.1 s c hc).1).elim
  · exact (ht hs).elim
  · exact I.unique hp hq
  · exact (hn ⟨c, hc⟩).elim
  · exact (ht (hT.2.2.2.2.2.1 s a ha).1).elim
  · exact (hm ⟨a, ha⟩).elim
  · have e := hT.2.2.2.2.1.2 s a c ha hc
    subst c
    have e := hJ.2 a b d hb hd
    subst d
    exact I.unique hp hq

theorem value_typed {w A T F J mu zero leaf node dummy D s p : M.Domain}
    (hJ : M.IsSetFunctionFromTo I J A mu) (hD : M.IsCartesianProduct I D w mu)
    (h0 : M.mem zero w) (h1 : M.mem leaf w) (h2 : M.mem node w) (hd : M.mem dummy mu)
    (hp : Value I J zero leaf node dummy T F s p) : M.mem p D := by
  rcases hp with ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨a, b, _, hb, hp⟩
  · exact (hD p).mpr ⟨zero, h0, dummy, hd, hp⟩
  · exact (hD p).mpr ⟨leaf, h1, dummy, hd, hp⟩
  · exact (hD p).mpr ⟨node, h2, b, hJ.output_mem_of_pairMember hb, hp⟩

/-- The encoding recovers both the node set and every actual label edge. -/
theorem value_reflects {w S A z R T F U G J mu zero leaf node dummy s p : M.Domain}
    (hT : Tree I w S A z R T F) (hU : Tree I w S A z R U G)
    (hJ : M.IsSetInjectionFromTo I J A mu) (h01 : zero ≠ leaf) (h02 : zero ≠ node) (h12 : leaf ≠ node)
    (hp : Value I J zero leaf node dummy T F s p)
    (hq : Value I J zero leaf node dummy U G s p) :
    (M.mem s T ↔ M.mem s U) ∧ ∀ a, M.PairMember I s a F ↔ M.PairMember I s a G := by
  rcases hp with ⟨hs, hp⟩ | ⟨hs, hn, hp⟩ | ⟨a, b, ha, hb, hp⟩ <;>
    rcases hq with ⟨ht, hq⟩ | ⟨ht, hm, hq⟩ | ⟨c, d, hc, hd, hq⟩
  · exact ⟨iff_of_false hs ht, fun a => iff_of_false
      (fun h => hs (hT.2.2.2.2.2.1 s a h).1) (fun h => ht (hU.2.2.2.2.2.1 s a h).1)⟩
  · exact (h01 (I.injective hp hq).1).elim
  · exact (h02 (I.injective hp hq).1).elim
  · exact (h01 (I.injective hq hp).1).elim
  · exact ⟨iff_of_true hs ht, fun a => iff_of_false (fun h => hn ⟨a, h⟩) (fun h => hm ⟨a, h⟩)⟩
  · exact (h12 (I.injective hp hq).1).elim
  · exact (h02 (I.injective hq hp).1).elim
  · exact (h12 (I.injective hq hp).1).elim
  · have e := (I.injective hp hq).2
    subst d
    have e := hJ.2 a c b hb hd
    subst c
    refine ⟨iff_of_true (hT.2.2.2.2.2.1 s a ha).1 (hU.2.2.2.2.2.1 s a hc).1, fun x => ⟨?_, ?_⟩⟩
    · intro hx
      exact (hT.2.2.2.2.1.2 s x a hx ha).symm ▸ hc
    · intro hx
      exact (hU.2.2.2.2.1.2 s x a hx hc).symm ▸ ha

def Encoding (S D J zero leaf node dummy T F K : M.Domain) : Prop :=
  M.IsSetFunctionFromTo I K S D ∧ ∀ s p, M.PairMember I s p K ↔
    M.mem s S ∧ Value I J zero leaf node dummy T F s p

def encoding {n} (S D J zero leaf node dummy T F K : Term n) : Formula 1 n :=
  .conj (Formula.isFunctionFromTo 𝒞 K S D) (.forallE (.forallE (.iff
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest K.weaken.weaken)
    (.conj (.mem (.bound 1) S.weaken.weaken)
      (value (𝒞 := 𝒞) J.weaken.weaken zero.weaken.weaken leaf.weaken.weaken node.weaken.weaken
        dummy.weaken.weaken T.weaken.weaken F.weaken.weaken (.bound 1) .newest)))))
derive_free_closed encoding

theorem encoding_semantics {n} (hE : Extensional M) (ρ : Env M n)
    (S D J zero leaf node dummy T F K : Term n) :
    Formula.satisfies ρ (encoding (𝒞 := 𝒞) S D J zero leaf node dummy T F K) ↔
      Encoding I (S.eval ρ) (D.eval ρ) (J.eval ρ) (zero.eval ρ) (leaf.eval ρ) (node.eval ρ)
        (dummy.eval ρ) (T.eval ρ) (F.eval ρ) (K.eval ρ) := by
  simp only [encoding, Encoding, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, value_semantics I, Definitional.Term.eval_weaken]
  rfl

theorem encoding_exists (hZF : M.Models ZF) {w S A z R T F J mu zero leaf node dummy D : M.Domain}
    (hT : Tree I w S A z R T F) (hJ : M.IsSetFunctionFromTo I J A mu)
    (hD : M.IsCartesianProduct I D w mu) (h0 : M.mem zero w) (h1 : M.mem leaf w)
    (h2 : M.mem node w) (hd : M.mem dummy mu) :
    ∃ K, Encoding I S D J zero leaf node dummy T F K := by
  let ρ : Env M 7 := ((((((⟨fun _ => J, fun _ => J⟩ : Env M 1).push zero).push leaf).push node).push dummy).push T).push F
  let φ : BinarySchema 7 := {body := (value (𝒞 := 𝒞) (.bound 8) (.bound 7) (.bound 6) (.bound 5)
    (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)}
  have hφ s p : φ.denote ρ s p ↔ Value I J zero leaf node dummy T F s p := by
    simp only [φ, BinarySchema.denote, value_semantics I]
    rfl
  obtain ⟨K, hK, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := S) (target := D)
    (fun s _ => by obtain ⟨p, hp⟩ := value_total I hT hJ s; exact ⟨p, (hφ s p).mpr hp⟩)
    (fun s _ p q hp hq => value_unique I hT hJ.1 ((hφ s p).mp hp) ((hφ s q).mp hq))
    (fun s p _ hp => value_typed I hJ hD h0 h1 h2 hd ((hφ s p).mp hp))
  exact ⟨K, hK, fun s p => (he s p).trans (and_congr_right fun _ => hφ s p)⟩

theorem encoding_unique (hE : Extensional M) {S D J zero leaf node dummy T F K L : M.Domain}
    (hK : Encoding I S D J zero leaf node dummy T F K)
    (hL : Encoding I S D J zero leaf node dummy T F L) : K = L :=
  hK.1.1.1.eq_of_pairMember_iff hE hL.1.1.1 (fun s p => (hK.2 s p).trans (hL.2 s p).symm)

theorem encoding_injective (hE : Extensional M) {w S A z R T F U G D J mu zero leaf node dummy K : M.Domain}
    (hT : Tree I w S A z R T F) (hU : Tree I w S A z R U G)
    (hJ : M.IsSetInjectionFromTo I J A mu) (h01 : zero ≠ leaf) (h02 : zero ≠ node) (h12 : leaf ≠ node)
    (hK : Encoding I S D J zero leaf node dummy T F K)
    (hL : Encoding I S D J zero leaf node dummy U G K) : T = U ∧ F = G := by
  have same s (hs : M.mem s S) : (M.mem s T ↔ M.mem s U) ∧
      ∀ a, M.PairMember I s a F ↔ M.PairMember I s a G := by
    obtain ⟨p, _, hp⟩ := hK.1.2.2 s hs
    exact value_reflects I hT hU hJ h01 h02 h12 ((hK.2 s p).mp hp).2 ((hL.2 s p).mp hp).2
  constructor
  · apply hE.eq_of_same_members
    intro s
    exact ⟨fun hs => (same s (hT.1 s hs)).1.mp hs, fun hs => (same s (hU.1 s hs)).1.mpr hs⟩
  · apply hT.2.2.2.2.1.1.eq_of_pairMember_iff hE hU.2.2.2.2.1.1
    intro s a
    exact ⟨fun ha => (same s (hT.1 s (hT.2.2.2.2.2.1 s a ha).1)).2 a |>.mp ha,
      fun ha => (same s (hU.1 s (hU.2.2.2.2.2.1 s a ha).1)).2 a |>.mpr ha⟩


/-- One internal injection for the WHOLE tree carrier, not a family of external codes. -/
theorem carrier_injection (hZF : M.Models ZF) {w S A z R C D J mu zero leaf node dummy Space : M.Domain}
    (hC : Carrier I w S A z R C) (hJ : M.IsSetInjectionFromTo I J A mu)
    (hD : M.IsCartesianProduct I D w mu) (hSpace : M.IsFunctionSpace I Space S D)
    (h0 : M.mem zero w) (h1 : M.mem leaf w) (h2 : M.mem node w) (hd : M.mem dummy mu)
    (h01 : zero ≠ leaf) (h02 : zero ≠ node) (h12 : leaf ≠ node) : M.CardinalLessOrEqual I C Space := by
  let ρ : Env M 7 := ((((((⟨fun _ => S, fun _ => S⟩ : Env M 1).push D).push J).push zero).push leaf).push node).push dummy
  let φ : BinarySchema 7 := {body := .existsE (.existsE (.conj (𝒞.code (.bound 3) (.bound 1) .newest)
    (encoding (𝒞 := 𝒞) (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5)
      (.bound 4) (.bound 1) .newest (.bound 2))))}
  have hφ c K : φ.denote ρ c K ↔ ∃ T F, I.Codes c T F ∧ Encoding I S D J zero leaf node dummy T F K := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      I.satisfies_code_iff, encoding_semantics I hZF.1]
    rfl
  have valid {c T F} (hc : M.mem c C) (he : I.Codes c T F) : Tree I w S A z R T F := by
    obtain ⟨U, G, he', hU⟩ := (hC c).mp hc
    obtain ⟨rfl, rfl⟩ := I.injective he he'
    exact hU
  apply ZF.exists_setInjectionFromTo_of_denote hZF I φ ρ (source := C) (target := Space)
  · intro c hc
    obtain ⟨T, F, he, hT⟩ := (hC c).mp hc
    obtain ⟨K, hK⟩ := encoding_exists I hZF hT hJ.1 hD h0 h1 h2 hd
    exact ⟨K, (hφ c K).mpr ⟨T, F, he, hK⟩⟩
  · intro c _ K L hK hL
    obtain ⟨T, F, he, hK⟩ := (hφ c K).mp hK
    obtain ⟨U, G, he', hL⟩ := (hφ c L).mp hL
    obtain ⟨rfl, rfl⟩ := I.injective he he'
    exact encoding_unique I hZF.1 hK hL
  · intro c K _ hK
    obtain ⟨_, _, _, hK⟩ := (hφ c K).mp hK
    exact (hSpace K).mpr hK.1
  · intro c d K hc hd hK hL
    obtain ⟨T, F, he, hK⟩ := (hφ c K).mp hK
    obtain ⟨U, G, he', hL⟩ := (hφ d K).mp hL
    obtain ⟨rfl, rfl⟩ := encoding_injective I hZF.1 (valid hc he) (valid hd he') hJ h01 h02 h12 hK hL
    exact I.unique he he'

/-- Source tree-size estimate; only an actual function-space bound is consumed. -/
theorem cardinal_le (hZF : M.Models ZF) {w S A z R C mu P : M.Domain}
    (hw : M.IsOmega w) (hmu : M.IsInfiniteCardinal I w mu)
    (hS : ExistingFiniteSequenceBounds.Fseq_space_d I w w S) (hC : Carrier I w S A z R C)
    (hA : M.CardinalLessOrEqual I A mu) (hP : M.IsFunctionSpace I P w mu)
    (hp : M.CardinalLessOrEqual I P mu) : M.CardinalLessOrEqual I C mu := by
  obtain ⟨zero, hz, hzw⟩ := hw.1.1
  obtain ⟨leaf, hLeaf, hLeafW⟩ := hw.1.2 zero hzw
  obtain ⟨node, hNode, hNodeW⟩ := hw.1.2 leaf hLeafW
  have h01 : zero ≠ leaf := by intro e; subst leaf; exact hz zero hLeaf.predecessor_mem
  have h02 : zero ≠ node := by intro e; subst node; exact hz leaf hNode.predecessor_mem
  have h12 : leaf ≠ node := by intro e; subst node; exact KP.mem_irrefl_d (ZF.modelsKP hZF) leaf hNode.predecessor_mem
  obtain ⟨Wmu, hWmu⟩ := hmu.2
  obtain ⟨dummy, hd, _⟩ := hWmu.1.2.2 zero hzw
  obtain ⟨J, hJ⟩ := hA
  obtain ⟨D, hD⟩ := ZF.exists_cartesianProduct hZF I w mu
  obtain ⟨idMu, hIdMu⟩ := ZF.exists_identityBijection hZF I mu
  obtain ⟨Dmu, hDmu⟩ := ExistingCardinalBounds.infinite_product_l I hZF hw hmu hmu.2 ⟨idMu, hIdMu.1⟩ hD
  obtain ⟨Space, hSpace⟩ := ZF.exists_functionSpace hZF I S D
  obtain ⟨SW, hSW⟩ := addresses_equinumerous I hZF hw hS
  obtain ⟨SpaceP, hSpaceP⟩ := ZF.exists_functionSpaceTransportInjection hZF I hSpace hP hSW hDmu
  obtain ⟨CSpace, hCSpace⟩ := carrier_injection I hZF hC hJ hD hSpace hzw hLeafW hNodeW hd h01 h02 h12
  obtain ⟨CP, hCP⟩ := ZF.exists_compositionInjection hZF I hCSpace hSpaceP
  obtain ⟨Pmu, hPmu⟩ := hp
  exact ZF.exists_compositionInjection hZF I hCP hPmu

/-- Exact source fixed-point hypotheses bound all internally well-founded tree codes. -/
def boundSentence (𝒞 : OrderedPairConvention) : Sentence where
  formula := Formula.forallClosure 7 (.imp (Formula.isOmega (.bound 0))
    (.imp (Formula.isInfiniteCardinal 𝒞 (.bound 0) (.bound 6))
    (.imp (Formula.isCardinalExponentiation 𝒞 (.bound 6) (.bound 6) (.bound 0))
    (.imp (Formula.cardinalLessOrEqual 𝒞 (.bound 2) (.bound 6))
    (.imp (ExistingFiniteSequenceBounds.fseq_space_m (𝒞 := 𝒞) (.bound 0) (.bound 0) (.bound 1))
    (.imp (carrier (𝒞 := 𝒞) (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5))
    (Formula.cardinalLessOrEqual 𝒞 (.bound 5) (.bound 6))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
    Formula.isInfiniteCardinal, Formula.isCardinalExponentiation, Formula.isFunctionSpace]

open YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
attribute [local implicit_reducible] SetTheory.signature FirstOrderSemantics.reduct

/-- Consume the already proved fixed-power normalization without rebuilding it. -/
theorem bound_models {N : FirstOrder.Structure.{0,0,0,u} ℒ} (hN : FirstOrder.Theory.Models N nativeZF) :
    (FirstOrderSemantics.reduct N).SatisfiesSentence (boundSentence PureKuratowskiProject.convention) := by
  have hZF := ModelTransfer.project_models_iff.mp hN
  let J := KuratowskiZF.interpretation hN
  apply (Structure.satisfiesSentence_iff _ _).mpr
  intro free
  apply (Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Formula.satisfies_imp_iff, Formula.satisfies_isOmega_iff,
    Formula.satisfies_isInfiniteCardinal_iff J hZF.1, Formula.satisfies_isCardinalExponentiation_iff J hZF.1,
    Formula.satisfies_cardinalLessOrEqual_iff J hZF.1, ExistingFiniteSequenceBounds.fseq_space_sat_l J hZF.1,
    carrier_semantics J hZF.1]
  intro hw hmu hPow hA hS hC
  obtain ⟨P, hP⟩ := ZF.exists_functionSpace hZF J (bound 0) (bound 6)
  obtain ⟨Pmu, hPmu⟩ := (ConstructionConcreteCardinals.normalize_power hN hPow hP).2.symm hZF J
  exact cardinal_le J hZF hw hmu hS hC hA hP ⟨Pmu, hPmu.1⟩

theorem bound_kernel_certificate : FirstOrder.Derives nativeZF []
    (fo_sentence (boundSentence PureKuratowskiProject.convention)) := by
  apply ModelTransfer.derives
  intro N hN
  exact (FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hN) _).mpr (bound_models hN)

end PPAC.Migration.ForcingCountableTreeCardinality
